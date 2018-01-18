module Subs
--
-- $Id: Subs.hs,v 1.25 2005/02/25 14:04:11 marku Exp $
--
-- Defines substitution-related functions over Z terms.
-- These functions should be applied only to unfolded terms
-- (so ZESchema, ZTheta expressions etc. are not handled here).
--
-- Exports ZExpr and ZPred as instances of SubsTerm, which is a
-- type class containing functions for performing substitution,
-- determining free variables, etc.
--
-- Note that 'substitute sub vs term' takes a set of variables, vs, as well
-- as the substitution, sub.  This varset must include all free variables
-- of the entire term that the substituted term will be placed inside
-- (including free vars of 'term' itself), plus any bound variables
-- that 'term' is within the scope of.  This allows the substitute
-- function to preserve the 'no-repeated-bound-vars' invariant.
(
   Substitution,
   SubsTerm,
   substitute,   -- Hugs does not export this automatically
   free_vars,    -- Hugs does not export this automatically
   uniquify,     -- Restores the no-repeated-bound-vars invariant
   choose_fresh_var,
   rename_lhsvars,  -- only for use by Unfold really.

   VarSet,
   varset,
   varset_from_zvars,
   empty_varset,
   union_varset,
   inter_varset,
   diff_varset,
   subseteq_varset,
   in_varset,
   show_varset,

   avoid_variables
)
where

import AST
import FiniteSets

type Substitution = [(ZVar,ZExpr)]

-- Optional Precondition checking
-- Define pre f msg val = val to turn this off.
pre f msg val = val
pre False msg val = error ("Precondition Error: " ++ msg)
pre True  msg val = val

class SubsTerm t where
  substitute :: Substitution -> VarSet -> t -> t
  free_vars  :: t -> VarSet   -- result is all ZVar's
  uniquify   :: VarSet -> t -> t
  uniquify   = substitute []

instance SubsTerm ZExpr where
  substitute = presubstitute sub_expr
  free_vars  = fvars_expr

instance SubsTerm ZPred where
  substitute = presubstitute sub_pred
  free_vars  = fvars_pred

presubstitute f sub vs term =
    pre ((termvars `diff_varset` domvars) `subseteq_varset` vs)
	("subs does not include all free vars: " ++ argmsg)
	(f (make_subinfo sub (union_varsets (vs:ranvars))) term)
    where
    ranvars = map (free_vars . snd) sub
    domvars = varset_from_zvars (map fst sub)
    termvars = free_vars term
    argmsg = "\n\t" ++ show term ++
	     "\n\t" ++ show sub ++
	     "\n\t{" ++ show_varset vs ++ "}"


----------------------------------------------------------------------
-- VarSet ADT
--
-- To get more typechecking, here we create a copy of the FinSet
-- ADT, restricted to handling just (ZVar _) terms.
----------------------------------------------------------------------
newtype VarSet = VarSet FinSet   -- but containing only (ZVar _) terms.
		 deriving (Eq,Show)

-- Now we promote all the relevant FinSet operations to VarSet.
varset  :: [ZExpr] -> VarSet
varset vs
  = if bad == [] then VarSet (set vs) else error "non-vars in varset"
  where
  bad = filter (not . isZVar) vs
  isZVar (ZVar _) = True
  isZVar _        = False

varset_from_zvars  :: [ZVar] -> VarSet
varset_from_zvars = VarSet . set . map ZVar

empty_varset = VarSet emptyset

union_varsets :: [VarSet] -> VarSet
union_varsets vs = VarSet (gen_union [s | VarSet s <- vs])

-- binary operations
union_varset    (VarSet a) (VarSet b) = VarSet (union a b)
inter_varset    (VarSet a) (VarSet b) = VarSet (inter a b)
diff_varset     (VarSet a) (VarSet b) = VarSet (diff a b)
subseteq_varset (VarSet a) (VarSet b) = subset a b

in_varset        v         (VarSet b) = v `mem` b
show_varset     (VarSet vs) = show_zvars [v | ZVar v <- vs]


----------------------------------------------------------------------
-- SubstitutionInfo ADT
--
-- It is convenient to pass around more information than just the
-- substitution, so we pass around this SubstitutionInfo type,
-- which contains the substitution, plus the set of variables
-- which must be avoided when choosing new local variables.
-- This 'avoid' set must contain:
--
--    * all free variables of the entire term that surrounds the
--      term that substitute is being applied to
--      (usually none, because most complete terms have no free vars).
--      Note: This is slightly stronger than necessary -- it could be
--      just the free vars minus the domain of the substitution.
--
--    * all outer bound variables of the entire term
--      (so that the substitution preserves the uniquify invariant
--       -- no repeated bound variable names on any path into the term)
--
--    * all free variables in the range of the substitution
--      (because we must avoid capturing these)
----------------------------------------------------------------------
type SubstitutionInfo = (Substitution, VarSet)

make_subinfo :: Substitution -> VarSet -> SubstitutionInfo
make_subinfo sub vs = (sub, vs)

subs_sub :: SubstitutionInfo -> Substitution
subs_sub (sub,_) = sub

subs_domain :: SubstitutionInfo -> [ZVar]
subs_domain (sub,_) = map fst sub

subs_range :: SubstitutionInfo -> [ZExpr]
subs_range (sub,_) = map snd sub

subs_avoid :: SubstitutionInfo -> VarSet
subs_avoid (_,vs) = vs

subs_add :: SubstitutionInfo -> (ZVar,ZExpr) -> SubstitutionInfo
subs_add (sub,vs) (x,e) =
    ((x,e):sub, vs `union_varset` extras)
    where
    extras  = varset_from_zvars [x] `union_varset` free_vars e

subs_remove :: SubstitutionInfo -> ZVar -> SubstitutionInfo
subs_remove (sub,vs) x = (filter (\ (v,_) -> v /= x) sub, vs)




sub_expr :: SubstitutionInfo -> ZExpr -> ZExpr
sub_expr subs e@(ZUniverse)   = e
sub_expr subs e@(ZVar v)      = maybe e id (lookup v (fst subs))
sub_expr subs e@(ZGiven _)    = e
sub_expr subs e@(ZGivenSet _) = e
sub_expr subs e@(ZInt _)      = e
sub_expr subs (ZGenerator r e) = ZGenerator r (sub_expr subs e)
sub_expr subs e@(ZPowerSet{}) = e{baseset=sub_expr subs (baseset e)}
sub_expr subs e@(ZFuncSet{})  = e{domset=sub_expr subs (domset e),
				  ranset=sub_expr subs (ranset e)}
sub_expr subs (ZCross es)     = ZCross (map (sub_expr subs) es)
sub_expr subs (ZTuple es)     = ZTuple (map (sub_expr subs) es)
sub_expr subs (ZCall e1 e2)   = ZCall (sub_expr subs e1) (sub_expr subs e2)
sub_expr subs (ZSetDisplay es) = ZSetDisplay (map (sub_expr subs) es)
sub_expr subs (ZSeqDisplay es) = ZSeqDisplay (map (sub_expr subs) es)
sub_expr subs (ZSetComp gfs (Just e)) = ZSetComp gfs2 (Just e2)
  where
  (gfs2,e2) = sub_genfilt sub_expr subs gfs e
sub_expr subs (ZLambda gfs e) = ZLambda gfs2 e2
  where
  (gfs2,e2) = sub_genfilt sub_expr subs gfs e
sub_expr subs (ZMu gfs (Just e)) = ZMu gfs2 (Just e2)
  where
  (gfs2,e2) = sub_genfilt sub_expr subs gfs e
--sub_expr subs (ZELet defs e)  = ZELet defs2 e2
--  where
--  (defs2, e2) = sub_letdef sub_expr subs defs e
sub_expr subs (ZIf_Then_Else p e1 e2) = ZIf_Then_Else p' e1' e2'
  where
  p'  = sub_pred subs p
  e1' = sub_expr subs e1
  e2' = sub_expr subs e2
sub_expr subs (ZSelect e v) = ZSelect (sub_expr subs e) v
  -- Note that e.v = (\lambda [u:U;v:V] @ v) e      (when e:[u:U;v:V])
  --               = \{ u:U; v:V @ (\lblot u==u,v==v \rblot, v) \}
  --    Field names:                       ^    ^
  --    Variable names: ^    ^                ^    ^         ^
  -- This makes it clear that v is local to this set comprehension,
  -- so is not free within 'e.v' and should not be renamed!
sub_expr subs e@(ZReln _)     = e
sub_expr subs e@(ZFunc1 _)    = e
sub_expr subs e@(ZFunc2 _)    = e
sub_expr subs e@(ZStrange _)  = e
sub_expr subs e@(ZFSet _)     = e  -- contains no vars at all
sub_expr subs e@(ZIntSet _ _) = e
sub_expr subs (ZBinding bs)   = ZBinding [(v,sub_expr subs e)|(v,e) <- bs]
sub_expr subs e@(ZFree0 _)    = e
sub_expr subs (ZFree1 n e)    = ZFree1 n (sub_expr subs e)
sub_expr subs e@(ZFreeType _ _) = e   -- has no free variables
sub_expr subs e = error ("substitute should not see: " ++ show e)

sub_pred :: SubstitutionInfo -> ZPred -> ZPred
sub_pred subs p@(ZFalse{})     = p
sub_pred subs p@(ZTrue{})      = p
sub_pred subs (ZAnd p1 p2)     = ZAnd (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZOr p1 p2)      = ZOr  (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZImplies p1 p2) = ZImplies (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZIff p1 p2)     = ZIff (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZNot p)         = ZNot (sub_pred subs p)
sub_pred subs (ZExists gfs p)  = ZExists gfs2 p2
  where
  (gfs2,p2) = sub_genfilt sub_pred subs gfs p
sub_pred subs (ZExists_1 gfs p)= ZExists_1 gfs2 p2
  where
  (gfs2,p2) = sub_genfilt sub_pred subs gfs p
sub_pred subs (ZForall gfs p)  = ZForall gfs2 p2
  where
  (gfs2,p2) = sub_genfilt sub_pred subs gfs p
--sub_pred subs (ZPLet defs p)   = ZPLet defs2 p2
--  where
--  (defs2, p2) = sub_letdef sub_pred subs defs p
sub_pred subs (ZEqual e1 e2)  = ZEqual (sub_expr subs e1) (sub_expr subs e2)
sub_pred subs (ZMember e1 e2) = ZMember (sub_expr subs e1) (sub_expr subs e2)
sub_pred subs p = error ("substitute should not see: " ++ show p)


--sub_letdef :: (SubstitutionInfo -> term -> term)
--              -> SubstitutionInfo -> [(ZVar,ZExpr)] -> VarSet -> term
--              -> ([(ZVar,ZExpr)], term)
--sub_letdef subfunc subs0 defs0 t_vars t
--  = (zip lhs2 rhs2, subfunc subs2 t)
--  where
--  (lhs,rhs) = unzip defs0
--  subs1 = subs0 `subs_remove` lhs
--  dont_capture = subs_range_vars subs1
--  clash = varset_from_zvars lhs `inter_varset` dont_capture
--  inuse = t_vars `union_varset` dont_capture
--  (lhs2, extrasubs) = rename_lhsvars clash inuse lhs
--  subs2 = subs1 `subs_union` extrasubs
--  rhs2  = map (sub_expr subs0) rhs

-- rename_lhsvars clash inuse vars
-- This chooses new names for each v in vars that is also in clash.
-- The new names are chosen to avoid inuse.
rename_lhsvars :: VarSet -> VarSet -> [ZVar] -> ([ZVar], Substitution)
rename_lhsvars (VarSet []) inuse lhs = (lhs,[]) -- optimize the common case
rename_lhsvars clash inuse [] = ([], [])
rename_lhsvars clash inuse (v:vs)
  | ZVar v `in_varset` clash = (v2:vs2, (v,ZVar v2):subs2)
  | otherwise                = (v:vs2,  subs2)
  where
  (vs2, subs2) = rename_lhsvars clash inuse2 vs
  v2 = choose_fresh_var inuse (get_zvar_name v)
  inuse2 = varset_from_zvars [v2] `union_varset` inuse


-- This is the most complex part of substitution.
-- The scope rules for [ZGenFilt] lists are fairly subtle (see AST.hs)
-- and on top of those, we have to do a substitution, being careful
-- (as usual!) to rename any of the bound variables that might capture
-- variables in the range of the substitution.  This is enough to
-- make life exciting...
--
-- The 'subfunc' argument is either sub_pred or sub_expr.
-- It is passed as a parameter so that this function can work on
-- [ZGenFilt] lists that are followed by either kind of term.
-- (An earlier version used the type class 'substitute', and avoided
--  having this parameter, but GHC 4.02 did not like that).
--
sub_genfilt :: (SubstitutionInfo -> term -> term)
	       -> SubstitutionInfo -> [ZGenFilt] -> term
	       -> ([ZGenFilt], term)
sub_genfilt subfunc subs0 gfs0 t =
    (gfs, subfunc finalsubs t)
    where
    (gfs,finalsubs) = sub_genfilt2 subs0 gfs0

sub_genfilt2 :: SubstitutionInfo -> [ZGenFilt]
	     -> ([ZGenFilt], SubstitutionInfo)
sub_genfilt2 subs0 [] =
    ([], subs0)
sub_genfilt2 subs0 (Evaluate x e t:gfs0) =
    (Evaluate x2 e2 t2 : gfs, subs)
    where
    e2 = sub_expr subs0 e
    t2 = sub_expr subs0 t
    subs1 = subs0 `subs_remove` x
    (x2,subs2) =
	if ZVar x `in_varset` subs_avoid subs1
	   then (fresh, subs1 `subs_add` (x,ZVar fresh))
	   else (x,subs1)
    fresh = choose_fresh_var (subs_avoid subs1) (get_zvar_name x)
    (gfs, subs) = sub_genfilt2 subs2 gfs0
sub_genfilt2 subs0 (Choose x e:gfs0) =
    (Choose x2 (sub_expr subs0 e) : gfs, subs)
    where
    subs1 = subs0 `subs_remove` x
    (x2,subs2) =
	if ZVar x `in_varset` subs_avoid subs1
	   then (fresh, subs1 `subs_add` (x,ZVar fresh))
	   else (x,subs1)
    fresh = choose_fresh_var (subs_avoid subs1) (get_zvar_name x)
    (gfs, subs) = sub_genfilt2 subs2 gfs0
sub_genfilt2 subs0 (Check p:gfs0) =
    (Check (sub_pred subs0 p) : gfs, subs)
    where
    (gfs, subs) = sub_genfilt2 subs0 gfs0

-- This renames any bound variables that are in 'clash', to avoid
-- capture problems.  (It only renames the defining occurrence of the
-- variables, not all the places where they are used, but it returns
-- a substitution which will do that when it is applied later).
-- To ensure that the new variable name is fresh, it is chosen to not
-- conflict with any of the variable in 'inuse'.
--
-- This function could almost be implemented using map, but we use a
-- recursive defn so that as each fresh variable is chosen, it can be
-- added to the set of 'inuse' variables.
--
rename_bndvars :: VarSet -> VarSet -> [ZGenFilt] -> ([ZGenFilt],Substitution)
rename_bndvars (VarSet []) _ gfs = (gfs,[]) -- optimize a common case
rename_bndvars clash inuse [] = ([],[])
rename_bndvars clash inuse (c@(Evaluate v e t):gfs0)
  | ZVar v `in_varset` clash = (Evaluate v2 e t:gfs, (v,ZVar v2):subs)
  | otherwise                = (c:gfs_easy, subs_easy)
  where
  (gfs, subs)           = rename_bndvars clash inuse2 gfs0
  (gfs_easy, subs_easy) = rename_bndvars clash inuse gfs0
  v2 = choose_fresh_var inuse (get_zvar_name v)
  inuse2 = varset_from_zvars [v2] `union_varset` inuse
rename_bndvars clash inuse (c@(Choose v e):gfs0)
  | ZVar v `in_varset` clash = (Choose v2 e:gfs, (v,ZVar v2):subs)
  | otherwise                = (c:gfs, subs)
  where
  (gfs, subs) = rename_bndvars clash inuse2 gfs0
  v2 = choose_fresh_var inuse (get_zvar_name v)
  inuse2 = varset_from_zvars [v2] `union_varset` inuse
rename_bndvars clash inuse (c@(Check _):gfs0)
  = (c:gfs, subs)
  where
  (gfs, subs) = rename_bndvars clash inuse gfs0



-- TODO: an more efficient algorithm might be to keep track
--   of the bound vars on the way in, and only generate those
--   that are not in that set.  This is what Zeta does, and it
--   might produce less garbage.
fvars_expr :: ZExpr -> VarSet
fvars_expr ZUniverse        = empty_varset
fvars_expr e@(ZVar v)       = varset [e]
fvars_expr (ZGiven _)       = empty_varset
fvars_expr (ZGivenSet _)    = empty_varset
fvars_expr (ZInt _)         = empty_varset
fvars_expr (ZGenerator r e) = fvars_expr e
fvars_expr (ZPowerSet{baseset=e})
			    = fvars_expr e
fvars_expr (ZFuncSet{domset=e1,ranset=e2})
			    = fvars_expr e1 `union_varset` fvars_expr e2
fvars_expr (ZCross es)      = union_varsets (map fvars_expr es)
fvars_expr (ZTuple es)      = union_varsets (map fvars_expr es)
fvars_expr (ZCall e1 e2)    = fvars_expr e1 `union_varset` fvars_expr e2
fvars_expr (ZSetDisplay es) = union_varsets (map fvars_expr es)
fvars_expr (ZSeqDisplay es) = union_varsets (map fvars_expr es)
fvars_expr (ZSetComp gfs (Just e))
			    = fvars_genfilt gfs (fvars_expr e)
fvars_expr (ZLambda gfs e)  = fvars_genfilt gfs (fvars_expr e)
fvars_expr (ZMu gfs (Just e))=fvars_genfilt gfs (fvars_expr e)
fvars_expr (ZELet defs e)
  = rhsvars `union_varset` (fvars_expr e `diff_varset` bndvarset)
  where
  (bndvars, rhss) = unzip defs
  bndvarset = varset (map ZVar bndvars)
  rhsvars = union_varsets (map fvars_expr rhss)
fvars_expr (ZIf_Then_Else p e1 e2)
  = fvars_pred p `union_varset` fvars_expr e1 `union_varset` fvars_expr e2

fvars_expr (ZSelect e v)    = fvars_expr e
fvars_expr (ZReln _)        = empty_varset
fvars_expr (ZFunc1 _)       = empty_varset
fvars_expr (ZFunc2 _)       = empty_varset
fvars_expr (ZStrange _)     = empty_varset
fvars_expr (ZFSet _)        = empty_varset
fvars_expr (ZIntSet _ _)    = empty_varset
fvars_expr (ZBinding bs)    = union_varsets (map (fvars_expr . snd) bs)
fvars_expr (ZFree0 _)       = empty_varset
fvars_expr (ZFree1 n e)     = fvars_expr e
fvars_expr (ZFreeType _ _)  = empty_varset  -- has no free variables
fvars_expr e  = error ("free_vars should not see: " ++ show e)


fvars_pred :: ZPred -> VarSet
fvars_pred (ZFalse{})       = empty_varset
fvars_pred (ZTrue{})        = empty_varset
fvars_pred (ZAnd p1 p2)     = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZOr p1 p2)      = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZImplies p1 p2) = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZIff p1 p2)     = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZNot p)         = fvars_pred p
fvars_pred (ZExists gfs p)  = fvars_genfilt gfs (fvars_pred p)
fvars_pred (ZExists_1 gfs p)= fvars_genfilt gfs (fvars_pred p)
fvars_pred (ZForall gfs p)  = fvars_genfilt gfs (fvars_pred p)
fvars_pred (ZPLet defs p)
  = rhsvars `union_varset` (fvars_pred p `diff_varset` bndvarset)
  where
  (bndvars, rhss) = unzip defs
  bndvarset = varset (map ZVar bndvars)
  rhsvars = union_varsets (map fvars_expr rhss)
fvars_pred (ZEqual e1 e2)   = fvars_expr e1 `union_varset` fvars_expr e2
fvars_pred (ZMember e1 e2)  = fvars_expr e1 `union_varset` fvars_expr e2
fvars_pred p = error ("freevars should not see: " ++ show p)


fvars_genfilt :: [ZGenFilt] -> VarSet -> VarSet
fvars_genfilt gfs inner = foldr adjust inner gfs
    where
    adjust (Choose x t) inner =
	(inner `diff_varset` varset_from_zvars [x])
	 `union_varset` free_vars t
    adjust (Check p) inner =
	inner `union_varset` free_vars p
    adjust (Evaluate x e t) inner =
	(inner `diff_varset` varset_from_zvars [x])
	  `union_varset` (free_vars e `union_varset` free_vars t)


-- returns a ZVar that does not appear in the given list of zvars.
choose_fresh_var :: VarSet -> String -> ZVar
choose_fresh_var vs s
  = head [v|d <- decors, let v = make_zvar s d, not (ZVar v `in_varset` vs)]

decors0 = [[d] | d <- ["_1","_2","_3","_4","_5","_6","_7","_8","_9"]]
decors  = [[]] ++ [d2++d | d2 <- decors, d <- decors0]


avoid_variables :: Env -> VarSet
avoid_variables = varset_from_zvars . map fst . local_values
