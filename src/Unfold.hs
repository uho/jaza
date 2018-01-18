module Unfold
--
-- $Id: Unfold.hs,v 1.50 2005/02/25 14:04:11 marku Exp $
--
-- This module defines functions for unfolding schema expressions
-- and unfolding global constants etc.  An expression/predicate that has
-- been unfolded has:
--
--  * all Maybe components filled out (with a Just value).
--     (eg. all set comprehensions have the '@result' part filled in.)
--  * no ZTheta terms (they have been replaced by bindings)
--  * all toolkit constants/functions in ZReln/ZFunc1/ZFunc2/ZStrange form.
--  * no references to global names or other schemas etc.
--  * no free variables (except schema field names, if it is a schema)
--  * no schema operators or schemas in expressions or predicates.
--  * all schema text ([ZGenFilt] lists) have been flattened out
--      with all 'Include'd schemas unfolded.
--  * every (a \mapsto b) is replaced by ZTuple [a,b]
--
-- All such unfold results are wrapped up in the 'ErrorOr' type,
-- to report errors like undefined names, illegal constructs etc.
--
-- It then goes through a second stage (uniquify) which ensures
-- that all nested bound variable names are distinct.  This is what
-- allows us to change from the usual Z scope rules to the scope
-- rules described in AST.hs.
-- Example:  (\forall x:\nat @ (\forall x:\nat @ P))
-- becomes:  (\forall x:\nat @ (\forall x_1:\nat @ P[x:=x_1]))
--
-- NOTE: the substitute function must be applied only to terms
--       that have been 'uniquified'.  So whenever the first unfold stage
--       needs to do a substitution, it 'uniquifies' the term first.
--       The subspred and subsexpr functions do this.

(
   module AST,    -- The data structures to be unfolded.
   ErrorOr(..),   -- Because evaluation results are wrapped in this.
   unfoldexpr,
   unfoldpred,
   unfoldsexpr,
   schema_rename, -- for assigning some fields of a schema
   schema_set,     -- converts a schema into a set of bindings
   make_schema_name -- determines how \Delta and \Xi schemas are named.
)
where

import AST
import Errors
import FiniteSets(emptyset)
import List
import Maybe
import Subs

unfoldexpr :: Env -> ZExpr  -> ErrorOr ZExpr
unfoldexpr env e =
    do  (_,ue) <- doUnfold (unfexpr e) env
	return (uniquify_expr (avoid_variables env) ue)

unfoldpred :: Env -> ZPred  -> ErrorOr ZPred
unfoldpred env p =
    do  (_,up) <- doUnfold (unfpred p) env
	return (uniquify_pred (avoid_variables env) up)

unfoldsexpr :: Env -> ZSExpr  -> ErrorOr [ZGenFilt]
unfoldsexpr env se =
    do  (_,ZSchema ugfs) <- doUnfold (unfsexpr se) env
	let (ugfs2, _, sub) = uniquify_gfs (avoid_variables env) ugfs
	if  sub == []
	    then return ugfs
	    else fail ("schema field names clash with global names: "
		       ++ show_zvars (map fst sub))

schema_rename :: Env -> [ZGenFilt] -> [ZReplace] -> ErrorOr [ZGenFilt]
schema_rename env gfs renam =
    do  (_,gfs2) <- doUnfold (replace_schema gfs renam) env
	return gfs2


show_zexpr :: ZExpr -> String
show_zexpr = show    -- until we get a proper formatter

-- A variable for use by the unfolder.
-- This is used only in places where other 'x' variables cannot be captured.
ux = make_zvar "x" []


-- A visitor for unfolding terms.
--  * In the Env structure, 'locals' is a stack of all the local
--    variables that are in scope.  Each variable x is mapped to
--    (ZVar x), so that the result of unfolding is to leave the
--    local variable in the expression.  You should use only
--    the pushNames function to add names to the Env.
--  * The range of 'global_values' is ZExprs that are already
--    unfolded.
newtype UnfoldVisitor a = UnfoldVisitor{doUnfold :: Env -> ErrorOr(Env,a)}

instance Show a => Show (UnfoldVisitor a) where
    show u = show (doUnfold u (empty_env []))

instance Monad UnfoldVisitor  where
    return a = UnfoldVisitor (\s -> return(s,a))
    fail msg = UnfoldVisitor (\s -> IllFormed [MStr msg])
    g >>= h =  UnfoldVisitor (\s -> res s)
	       where
	       -- we use the ErrorOr monad here
	       res env = do  (env2,a1) <- doUnfold g env
			     doUnfold (h a1) env2

instance Visitor UnfoldVisitor where
    visitExpr   = unfexpr
    visitSExpr  = unfsexpr
    visitPred   = unfpred
    visitBinder = unfBinder
    setEnv e  = UnfoldVisitor (\ _ -> return (e,()))
    currEnv   = UnfoldVisitor (\ env -> return (env,env))

-- This returns the first NON-error solution.
orElse :: UnfoldVisitor a -> UnfoldVisitor a -> UnfoldVisitor a
orElse a b =
    do  env <- currEnv
	case doUnfold a env of
	    good@Ok{} -> UnfoldVisitor (\_ -> good)
	    otherwise -> b


-- Within the UnfoldVisitor env, each local var v is mapped to (ZVar v)
pushNames :: [ZVar] -> UnfoldVisitor ()
pushNames vs = pushLocals [(v,ZVar v) | v <- vs]

-- This lifts any ErrorOr operation to the UnfoldVisitor level
unfoldError :: ErrorOr a -> UnfoldVisitor a
unfoldError (Ok a) = return a
unfoldError err = UnfoldVisitor (\s -> sameError err)

unftypecheck :: Bool -> String -> UnfoldVisitor ()
unftypecheck b msg = unfoldError (typecheck b msg)





-- This returns local variables unchanged, and
-- returns the value of each global variable.
-- Names that are not either of these should be toolkit constants,
-- so are translated to the appropriate constant (as defined in AST.hs).
-- If none of the above cases apply, we have an illegal variable reference.
--
-- Note that we look up the global environment for explicit definitions
-- of \Delta S and \Xi S *before* returning their default meaning.
-- This allows user-supplied definitions to override the default.
--
-- This function sometimes returns a schema (ZESchema ...) but unfoldexpr
-- always catches those and does further processing (e.g., to turn a
-- schema into a set of bindings).   TODO: clean this up?
unfold_name :: ZVar -> UnfoldVisitor ZExpr
unfold_name n =
    lookupVar n
    `orElse` unfoldToolkit n
    `orElse` unfoldDeltaXi n
    where
    unfoldToolkit n
	| is_unprimed_zvar n = lookup_toolkit (get_zvar_name n)
	| otherwise = unfoldError (IllFormed [])
    unfoldDeltaXi n | get_zvar_decor n == ["Delta"] =
      do let sname = get_zvar_name n
	 let delta = ZSchema [ Include (ZSRef (ZSPlain sname) [] []),
			       Include (ZSRef (ZSPlain sname) ["'"] []) ]
	 ZSchema gfs <- unfsexpr delta
	 return (ZESchema (ZSchema gfs))
    unfoldDeltaXi n | get_zvar_decor n == ["Xi"] =
      do let sname  = get_zvar_name n
	 let unprimed = ZSRef (ZSPlain sname) [] []
	 let primed   = ZSRef (ZSPlain sname) ["'"] []
	 let xi = ZSchema [ Include unprimed,
			    Include primed,
			    Check (ZEqual (ZTheta primed) (ZTheta unprimed)) ]
	 ZSchema gfs <- unfsexpr xi
	 return (ZESchema (ZSchema gfs))
    unfoldDeltaXi n = unfoldError (IllFormed [MStr "unknown name: ",
					      MExpr (ZVar n)])




unfexpr :: ZExpr -> UnfoldVisitor ZExpr
unfexpr (ZVar v) =
    -- The parser cannot determine if an expression like "s'" is a
    -- reference to an ordinary variable s, or a schema reference to
    -- a schema called s (it does not know which names are schemas).
    -- It returns all such ambiguous names (possibly decorated) as
    -- ZVar, never as ZSRef, so here we correct this by translating
    -- (ZVar s') into a schema reference, whenever s is a schema name.
    do  env <- currEnv
	let sref = ZSRef (ZSPlain (get_zvar_name v)) (get_zvar_decor v) []
	if envIsSchema env (get_zvar_name v)
	    then unfexpr (ZESchema sref)
	    else unfold_name v
unfexpr (ZESchema sexpr) =
    do  ZSchema ugfs <- unfsexpr sexpr
	return (schema_set ugfs)
unfexpr e@(ZCall e1 e2) =
    do  v1 <- unfexpr e1
	v2 <- unfexpr e2
	process_call v1 v2
unfexpr (ZSetDisplay [ZESchema se@(ZSRef _ _ _)]) =
    -- Here we fix a syntactic ambiguity of Z by translating {S}
    -- (where S is a schema) from a set display into a set comprehension.
    unfexpr (ZSetComp [Include se] Nothing)
unfexpr (ZSetDisplay es@[ZVar v]) =
    do  env <- currEnv
	let sref = ZSRef (ZSPlain (get_zvar_name v)) (get_zvar_decor v) []
	if envIsSchema env (get_zvar_name v)
	   then unfexpr (ZSetComp [Include sref] Nothing)
	   else do {ues <- mapM visitExpr es; return (ZSetDisplay ues)}
unfexpr (ZSetComp gf Nothing) =
    do  env <- currEnv
	result <- characteristic_tuple gf
	unfexpr (ZSetComp gf (Just result))
unfexpr (ZLambda gf e) =
    do  env <- currEnv
	argpattern <- characteristic_tuple gf
	unfexpr (ZSetComp gf (Just (ZTuple [argpattern,e])))
unfexpr (ZMu gf Nothing) =
    do  env <- currEnv
	result <- characteristic_tuple gf
	unfexpr (ZMu gf (Just result))
unfexpr (ZELet defs e) =
    do  ues <- mapM traverseZVarExpr defs
	-- e is in the scope of names, unlike defs
	ue <- localEnv (pushNames (map fst defs) >> unfexpr e)
	subsexpr ues ue
unfexpr (ZTheta (ZSRef name decors [])) =
    -- Remember, \theta is not compositional: \theta S' /= (\theta S)'
    -- So, we have to go inside the schema reference and catch the
    -- unfolded schema *before* it is primed.
    do  ZSchema ugfs <- unfsexpr (ZSRef name [] [])
	let names = genfilt_names ugfs
	let decnames = map (\v -> decorate_zvar v decors) names
	-- Now we lookup the decorated names.
	-- Local names will be returned unchanged, globals will be unfolded.
	values <- sequence (map unfold_name decnames)
	let binding = sort (zip names values)
	return (ZBinding binding)
unfexpr (ZTheta (ZSRef name decors (r:rs))) =
    unfoldError (Impossible
		 [MStr "\\theta with renaming is not implemented yet."])
unfexpr e@(ZBinding bs) =
    do  let (names,es) = unzip bs
	unfoldError (misccheck (length (nub names) == length names)
		     ("repeated names in binding: " ++ show_zexpr e))
	ues <- sequence (map unfexpr es)
	return (ZBinding (sort (zip names ues)))
unfexpr e =
    traverseExpr e  -- all other cases



unfpred :: ZPred -> UnfoldVisitor ZPred
unfpred (ZPre se) =
    unfpred (ZPSchema (ZS1 ZSPre se))
unfpred (ZPLet defs p) =
    do  ues <- mapM traverseZVarExpr defs
	-- p is in the scope of names, unlike defs
	up <- localEnv (pushLocals ues >> unfpred p)
	-- unfpred has already unfolded ues within p,
	-- so we can just return this 'up'.
        return up
unfpred (ZEqual e1 e2) =
    do  r1 <- unfexpr e1
	r2 <- unfexpr e2
	unfold_equal r1 r2
unfpred (ZPSchema se) =
   do  ZSchema ugfs <- unfsexpr se
       let names = genfilt_names ugfs
       -- Now we unfold the names in the curr env.
       -- Local names will be returned unchanged, globals will be unfolded.
       values <- sequence (map unfold_name names)
       let subs = [(v,val) | (v,val) <- zip names values,
			     ZVar v /= val ]
       let pred = foldl1 ZAnd (map mkpred ugfs)
       subspred subs pred
  where
  mkpred (Choose v s) = ZMember (ZVar v) s
  mkpred (Check p)    = p
unfpred p =
    traversePred p  -- all other cases


-- Unfolding schema text ([ZGenFilt]) is tricky.
-- The scope of the declared variables includes the predicates,
-- but not the other declarations.
-- So we pass around *two* environments:
--   1. genv (an explicit argument) is the env global to this ZGenFilt list.
--      This is used for the traversal of types and schema
--      inclusions, which are outside the scope of the ZGenFilt list.
--   2. The current env is extended by the names declared along this
--      ZGenFilt list, up to the current point.
--      This is used for the traversal of predicates, which
--      are inside the scope of the ZGenFilt list.
--
-- Precondition: input [ZGenFilt] should not contain Evaluate terms.
-- Postcondition: everything is unfolded.

unfBinder :: [ZGenFilt] -> ZTerm -> UnfoldVisitor ([ZGenFilt],ZTerm,Env)
unfBinder gfs zt =
    localEnv unf
    where
    unf = do  genv <- currEnv
	      ugfss <- mapM (unfGenFilt genv) gfs
	      -- now we concat the results, preserving the order,
	      -- removing duplicates and checking schema compatibility.
	      ugfs <- concatCompat ugfss [] []
	      uzt <- visitTerm zt
	      env <- currEnv
	      return (ugfs,uzt,env)

unfGenFilt genv (Choose v t) =
    do  t2 <- withEnv genv (visitExpr t)
	pushNames [v]
	return [Choose v t2]
unfGenFilt genv (Check p) =
    do  p2 <- visitPred p
	return (flattenConjuncts p2)
unfGenFilt genv (Include se) =
    do  ZSchema ugfs <- withEnv genv (visitSExpr se)
	pushNames (genfilt_names ugfs)
	return ugfs





-- This visitor method must cover ALL possibilities.
-- (the default schema expression method just raises an error)
-- The result will always be of the form:  ZSchema unfolded_gfs
unfsexpr :: ZSExpr -> UnfoldVisitor ZSExpr
unfsexpr (ZSchema gfs)
  = do	(ugfs, _, _) <- visitBinder gfs ZNull
	return (ZSchema ugfs)
unfsexpr (ZSRef n decors replaces0)
  = do	ZESchema (ZSchema ugfs) <- unfold_name (make_schema_name n)
	ugfs2 <- decorate_schema ugfs decors
	-- Finally, we apply the renamings/assignments.
	-- First we unfold the expressions in the assignments
	replaces <- sequence (map unfold_replace replaces0)
	ugfs3 <- replace_schema ugfs2 replaces
	return (ZSchema ugfs3)
unfsexpr (ZS1 ZSPre e)
  = do  ZSchema ugfs <- unfsexpr e
	let hide = [d | d@(Choose v _) <- ugfs,
		    is_primed_zvar v || is_output_zvar v]
	schema_quant ZExists hide ugfs
unfsexpr (ZS1 ZSNot e)
  = fail ("schema negation not implemented yet: " ++ show e)
unfsexpr (ZS2 op e1 e2)
  = do  ZSchema ue1 <- unfsexpr e1
	ZSchema ue2 <- unfsexpr e2
	ugfs <- unfoldsop2 op ue1 ue2
	return (ZSchema ugfs)
unfsexpr (ZSHide e vs)
  = do  ZSchema ue <- unfsexpr e
	vsdecls <- sequence (map (getdecl ue) vs)  -- strict schema compat.
	schema_quant ZExists vsdecls ue
  where
  getdecl ue var = do let matches = [d | d@(Choose v _) <- ue, v==var]
		      unftypecheck (matches /= [])
			  ("cannot hide unknown variable: " ++ show_zvar var)
		      return (head matches)
unfsexpr (ZSExists gfs se)
  = do  (ugfs,ZSExpr(ZSchema use),_) <- visitBinder gfs (ZSExpr se)
	schema_quant ZExists ugfs use
unfsexpr (ZSExists_1 gfs se)
  = do  (ugfs,ZSExpr(ZSchema use),_) <- visitBinder gfs (ZSExpr se)
	schema_quant ZExists_1 ugfs use
unfsexpr (ZSForall gfs se)
  = do  (ugfs,ZSExpr(ZSchema use),_) <- visitBinder gfs (ZSExpr se)
	schema_quant ZForall ugfs use


----------------------------------------------------------------------
-- Unfolding of schema operators
----------------------------------------------------------------------

-- This implements binary schema operators.
-- Pre: the two schema arguments have already been unfolded.
unfoldsop2 ZSAnd s1 s2
  = do  schema_compatible "conjunction" s1 s2
	return (schema_merge s1 s2)
unfoldsop2 ZSOr s1 s2
  = do  let (d1,p1) = schema_sig s1
	let (d2,p2) = schema_sig s2
	schema_compatible "disjunction" d1 d2
	-- TODO: this must normalize the decls to base types first.
	--   (for the non-shared declarations, at least)
	return (schema_merge d1 d2 ++
		[Check (ZOr (schema_pred p1) (schema_pred p2))])
unfoldsop2 ZSImplies s1 s2
  = do  let (d1,p1) = schema_sig s1
	let (d2,p2) = schema_sig s2
	schema_compatible "implication" d1 d2
	-- TODO: this must normalize the decls to base types first.
	--   (for the non-shared declarations, at least)
	return (schema_merge d1 d2 ++
		[Check (ZImplies (schema_pred p1) (schema_pred p2))])
unfoldsop2 ZSIff s1 s2
  = do  let (d1,p1) = schema_sig s1
	let (d2,p2) = schema_sig s2
	schema_compatible "iff" d1 d2
	-- TODO: this must normalize the decls to base types first.
	--   (for the non-shared declarations, at least)
	return (schema_merge d1 d2 ++
		[Check (ZIff (schema_pred p1) (schema_pred p2))])
unfoldsop2 ZSProject s1 s2
  = fail ("TODO: schema projection operator")
unfoldsop2 ZSSemi s1 s2
  = schema_localize is_primed_zvar s1 is_unprimed_zvar s2
unfoldsop2 ZSPipe s1 s2
  = schema_localize is_output_zvar s1 is_input_zvar s2


-- This implements schema piping and sequential composition.
-- It looks for any names in s1 and s2 that have a common basename
-- and that satisfy the tests vartest1/vartest2 respectively, then
-- unifies and hides those names.
-- Pre: s1 and s2 have been unfolded.
schema_localize vartest1 s1 vartest2 s2 =
    do  let (d1,p1) = schema_sig s1
	let (d2,p2) = schema_sig s2
	let hide = [((v1,t1),(v2,t2))
		    | Choose v1 t1 <- d1, vartest1 v1,
		      Choose v2 t2 <- d2, vartest2 v2,
		      get_zvar_name v1 == get_zvar_name v2]
	let bad = filter (\ ((_,t1),(_,t2)) -> t1 /= t2) hide
	unftypecheck (bad == [])
		  ("types clash in schema composition: " ++ show bad)
	let rem1 = [d | d@(Choose v _) <- d1,
			not (v `elem` (map (fst . fst) hide))]
	let rem2 = [d | d@(Choose v _) <- d2,
			not (v `elem` (map (fst . snd) hide))]
	schema_compatible ">>/;" rem1 rem2
	-- all checking completed, now construct the result
	localEnv (pushNames (genfilt_names (d1++d2))
		  >> rest hide (rem1,p1) (rem2,p2))
    where
    hidden_name v = make_zvar (get_zvar_name v) ["_i"]
    subsCheck sub (Check p) = subspred sub p >>= (return . Check)
    rest hide (rem1,p1) (rem2,p2) =
     do let hdecls = map (\ ((v,t),_) -> Choose (hidden_name v) t) hide
	let subs1 = map (\ ((v,_),_) -> (v,ZVar (hidden_name v))) hide
	let subs2 = map (\ (_,(v,_)) -> (v,ZVar (hidden_name v))) hide
	hp1 <- mapM (subsCheck subs1) p1
	hp2 <- mapM (subsCheck subs2) p2
	let hidden = hdecls ++ schema_merge hp1 hp2
	return (schema_merge rem1 rem2 ++ [Check (ZExists hidden ztrue)])


schema_compatible :: String -> [ZGenFilt] -> [ZGenFilt] -> UnfoldVisitor ()
schema_compatible opname s1 s2
  = do  let clash = [x | x@(Choose v1 t1) <- s1,
			 Choose v2 t2 <- s2,
			 v1 == v2,
			 t1 /= t2]  -- strict schema compat. here
	unftypecheck (clash == [])
		  ("schema " ++ opname ++ " causes field clash: "
		    ++ show clash)

-- This splits a schema into (signature, predicates)
-- Pre: the schema has been unfolded (but not been optimized).
--      In other words, it contains only Check/1 and Choose/2 terms.
schema_sig :: [ZGenFilt] -> ([ZGenFilt], [ZGenFilt])
schema_sig gfs
  = ([x | x@(Choose _ _) <- gfs], [x | x@(Check _) <- gfs])

-- This merges two [ZGenFilt] lists, taking care to remove duplicates.
-- Pre: the two input lists do not already contain duplicates.
schema_merge gfs1 gfs2
  = gfs1 ++ (gfs2 \\ gfs1)


-- Turns a list of (Check _) terms into a single predicate.
schema_pred ps = foldr ZAnd ztrue [p | Check p <- ps]


schema_quant :: ([ZGenFilt] -> ZPred -> ZPred)
	     -> [ZGenFilt] -> [ZGenFilt] -> UnfoldVisitor ZSExpr
schema_quant q bndgfs s
  = do  let (bnddecls,_) = schema_sig bndgfs
	let (decls,preds) = schema_sig s
	let missing = bnddecls \\ decls  -- strict schema compat. here.
	unftypecheck (missing == [])
	  ("missing decls within schema quantification: " ++ show missing)
	let remainingdecls = decls \\ bnddecls
	-- TODO: check that these bound variables are distinct from all
	--       variables from surrounding scopes.
	let inner = q bndgfs (schema_pred preds)
	return (ZSchema (remainingdecls ++ [Check inner]))

unfold_replace :: ZReplace -> UnfoldVisitor ZReplace
unfold_replace r@(ZRename _ _) =
    return r
unfold_replace (ZAssign v e) =
    do  e2 <- unfexpr e
	return (ZAssign v e2)


decorate_schema :: [ZGenFilt] -> [ZDecor] -> UnfoldVisitor [ZGenFilt]
decorate_schema gfs [] = return gfs
decorate_schema gfs decors
  = do  let currsig = genfilt_names gfs
	let newsig = map (\n -> decorate_zvar n decors) currsig
	let sub = zip currsig (map ZVar newsig)
	let allvars = zip (currsig ++ newsig) (repeat ZUniverse)
	localEnv (pushNames (currsig++newsig)
		  >> mapM (decorate_gf decors sub) gfs)
  where
  decorate_gf d sub (Choose v e) = return (Choose (decorate_zvar v d) e)
  decorate_gf d sub (Check p)    = subspred sub p >>= (return . Check)
  decorate_gf d sub x            = error ("decorate_gf got: " ++ show x)


-- TODOTODO: make this generic Visitor code!
--         SIMILARLY FOR ALL SCHEMA UNFOLD OPS?
-- This renames/assigns schema fields.
-- Both arguments must be fully unfolded beforehand, and the
-- [ZGenFilt] argument must contain only Check and Choose constructs.
replace_schema :: [ZGenFilt] -> [ZReplace] -> UnfoldVisitor [ZGenFilt]
replace_schema ugfs []   -- optimize the simple special case
  = return ugfs
replace_schema ugfs replaces
  = do  let subs = map mksubs replaces
	-- Well-formedness checks on replaces:
	-- 1: No duplicated names in domain of subs.
	let dom_subs = map fst subs
	unftypecheck (length (nub dom_subs) == length subs)
	   ("repeated names in rename list: " ++ show_zvars dom_subs)
	-- 2: Every name in dom of subs is also in the schema
      -- NOTE: Feb 2005, removed this because it is not required by Z std.
      --       Relaxing it allows [a',b':T];[b:T] to work (a' is an output)
      --       which is nice, because less framing schemas are needed.      
	-- let missing = dom_subs \\ genfilt_names ugfs
	-- unftypecheck (missing==[])
	--    ("cannot replace non-existing names: " ++ show_zvars missing)
	-- process the assignments
	let assigned = [(c,val)|c@(Choose v vt) <- ugfs,
			   ZAssign v2 val <- replaces, v == v2]
	let membertests = [Check (ZMember val s)
			     | (Choose v s,val) <- assigned]
	-- process the renamings
	let rest = ugfs \\ (map fst assigned)
	let rest2 = map (renamefields replaces) rest
	-- Now check that no clashes have been introduced.
	schema_compatible "rename" rest2 rest2
	-- Note: to satisfy the usual scoping rules, the membertests must
	--       come before any names are declared, because the types in
	--       membertests are global to this whole [ZGenFilt].
	-- TODO: the above is no longer true after uniquify pass!
	rest3 <- localEnv (pushNames (genfilt_names rest2)
			   >> mapM (subp subs) (nub rest2))
	return (membertests ++ rest3)
  where
  mksubs (ZRename old new) = (old, ZVar new)
  mksubs (ZAssign v value) = (v, value)
  renamefields replaces (Choose v s) = Choose (renamefield1 replaces v) s
  renamefields _        gf           = gf
  renamefield1 replaces v = head([v2|ZRename v1 v2 <- replaces, v==v1]++[v])
  subp subs c@(Choose _ _) = return c
  subp subs (Check p)      = subspred subs p >>= (return . Check)
  subp subs c              = error ("subp got: " ++ show c)



----------------------------------------------------------------------
-- Constants/functions/relations of Z and its standard Toolkit
----------------------------------------------------------------------
lookup_toolkit :: (Monad m) => String -> m ZExpr
-- constants
lookup_toolkit "\\emptyset" = return zemptyset
lookup_toolkit "\\nat"      = return (ZIntSet (Just 0) Nothing)
lookup_toolkit "\\nat_1"    = return (ZIntSet (Just 1) Nothing)
lookup_toolkit "\\num"      = return (ZIntSet Nothing  Nothing)
lookup_toolkit "<"          = return (ZReln ZLessThan)
lookup_toolkit "\\leq"      = return (ZReln ZLessThanEq)
lookup_toolkit ">"          = return (ZReln ZGreaterThan)
lookup_toolkit "\\geq"      = return (ZReln ZGreaterThanEq)
lookup_toolkit "\\subset"   = return (ZReln ZSubset)
lookup_toolkit "\\subseteq" = return (ZReln ZSubsetEq)
lookup_toolkit "\\prefix"   = return (ZReln ZPrefix)
lookup_toolkit "\\suffix"   = return (ZReln ZSuffix)
lookup_toolkit "\\inseq"    = return (ZReln ZInSeq)
lookup_toolkit "\\partition"= return (ZReln ZPartition)

-- prefix functions
lookup_toolkit "\\dom"      = return (ZFunc1 ZDom)
lookup_toolkit "\\ran"      = return (ZFunc1 ZRan)
lookup_toolkit "\\#"        = return (ZFunc1 ZSizeof)
lookup_toolkit "\\bigcup"   = return (ZFunc1 ZBigCup)
lookup_toolkit "\\bigcap"   = return (ZFunc1 ZBigCap)
lookup_toolkit "max"        = return (ZFunc1 ZMax)
lookup_toolkit "min"        = return (ZFunc1 ZMin)
lookup_toolkit "first"      = return (ZFunc2 ZFirst)
lookup_toolkit "second"     = return (ZFunc2 ZSecond)
lookup_toolkit "succ"
  = return (ZSetComp [Choose ux (ZIntSet Nothing Nothing)]
	  (Just (ZTuple [ZVar ux,ZCall (ZFunc2 ZPlus)
				       (ZTuple [ZVar ux,ZInt 1])])))
lookup_toolkit "rev"        = return (ZFunc1 ZRev)
lookup_toolkit "head"       = return (ZFunc1 ZHead)
lookup_toolkit "last"       = return (ZFunc1 ZLast)
lookup_toolkit "tail"       = return (ZFunc1 ZTail)
lookup_toolkit "front"      = return (ZFunc1 ZFront)
lookup_toolkit "squash"     = return (ZFunc1 ZSquash)
lookup_toolkit "\\dcat"     = return (ZFunc1 ZDCat)
lookup_toolkit "\\negate"   = return (ZFunc1 ZNegate) -- unary minus
-- infix functions
lookup_toolkit "\\mapsto"   = return (ZFunc2 ZMapsto) -- becomes a pair.
lookup_toolkit "\\upto"     = return (ZFunc2 ZUpto)
lookup_toolkit "+"          = return (ZFunc2 ZPlus)
lookup_toolkit "-"          = return (ZFunc2 ZMinus)
lookup_toolkit "\\setminus" = return (ZFunc2 ZSetMinus)
lookup_toolkit "\\cup"      = return (ZFunc2 ZUnion)
lookup_toolkit "\\cat"      = return (ZFunc2 ZCat)
lookup_toolkit "*"          = return (ZFunc2 ZTimes)
lookup_toolkit "\\div"      = return (ZFunc2 ZDiv)
lookup_toolkit "\\mod"      = return (ZFunc2 ZMod)
lookup_toolkit "\\cap"      = return (ZFunc2 ZInter)
lookup_toolkit "\\extract"  = return (ZFunc2 ZExtract)
lookup_toolkit "\\filter"   = return (ZFunc2 ZFilter)
lookup_toolkit "\\comp"     = return (ZFunc2 ZComp)
lookup_toolkit "\\circ"     = return (ZFunc2 ZCirc)
lookup_toolkit "\\dres"     = return (ZFunc2 ZDRes)
lookup_toolkit "\\oplus"    = return (ZFunc2 ZOPlus)
lookup_toolkit "\\rres"     = return (ZFunc2 ZRRes)
lookup_toolkit "\\ndres"    = return (ZFunc2 ZNDRes)
lookup_toolkit "\\nrres"    = return (ZFunc2 ZNRRes)
lookup_toolkit "\\relimg"   = return (ZFunc2 ZRelImg)    -- actually mixfix
-- postfix functions
lookup_toolkit "\\inv"      = return (ZFunc1 ZInv)       -- R~
lookup_toolkit "\\star"     = return (ZFunc1 ZStar)      -- R*
lookup_toolkit "\\plus"     = return (ZFunc1 ZClosure)   -- R+
-- infix generics
lookup_toolkit "\\rel"      = return zfunc{is_function=False}
lookup_toolkit "\\pfun"     = return zfunc
lookup_toolkit "\\fun"      = return zfunc{is_total=True}
lookup_toolkit "\\pinj"     = return zfunc{is_one2one=True}
lookup_toolkit "\\inj"      = return zfunc{is_total=True,is_one2one=True}
lookup_toolkit "\\psurj"    = return zfunc{is_onto=True}
lookup_toolkit "\\surj"     = return zfunc{is_total=True,is_onto=True}
lookup_toolkit "\\bij"      = return zfunc{is_total=True,
				       is_one2one=True,
				       is_onto=True}
lookup_toolkit "\\ffun"     = return zfunc{is_finite=True}
lookup_toolkit "\\finj"     = return zfunc{is_finite=True,is_one2one=True}

-- prefix generics
lookup_toolkit "\\power"    = return zset
lookup_toolkit "\\power_1"  = return zset{is_non_empty=True}
lookup_toolkit "\\finset"   = return zset{is_finite=True}
lookup_toolkit "\\finset_1" = return zset{is_finite=True,is_non_empty=True}
lookup_toolkit "\\id"       = return (ZFunc1 ZId)
lookup_toolkit "\\seq"      = return zseq
lookup_toolkit "\\seq_1"    = return zseq{is_non_empty=True}
lookup_toolkit "\\iseq"     = return zseq{is_one2one=True}

lookup_toolkit "iter"       = return (ZStrange ZIter)
lookup_toolkit "\\disjoint" = return (ZStrange ZDisjoint)

lookup_toolkit "sum"        = return (ZFunc1 ZSum)

lookup_toolkit n = fail ("unknown toolkit function: " ++ n)


-- This is just a placeholder (will be filled in by mkcall below)
badset = ZGiven "program err: missing base type"

zset = ZPowerSet{ baseset=badset,
		  is_non_empty=False,
		  is_finite  =False}
zfunc = zrelations{domset=badset, ranset=badset, is_function=True}

zseq = zfunc{is_sequence=True,
	     is_finite=True,
	     -- domset should really be 1..#s, but setting the
	     -- is_sequence flag will cause this to be checked anyway.
	     domset=ZIntSet (Just 1) Nothing
	    }

------------------------------------------------------------------------
-- Utility functions for unfolding
------------------------------------------------------------------------

-- The Z syntax ensures that the \power, \seq and the function and
-- relation constructors always have the correct number of arguments,
-- so we can safely handle those cases during the unfold process.
illegal_call f arg = unfoldError (IllFormed [MStr "illegal call: ",
					     MExpr (ZCall f arg)])

process_call :: ZExpr -> ZExpr -> UnfoldVisitor ZExpr
process_call set@ZPowerSet{} arg
    | baseset set == badset = return set{baseset=arg}
    | otherwise             = illegal_call set arg
process_call func@ZFuncSet{} arg@(ZTuple [d,r])
    | domset func == badset &&
      ranset func == badset = return func{domset=d, ranset=r}
    | otherwise             = illegal_call func arg
process_call func@ZFuncSet{} arg  -- must be: \seq arg
    | is_sequence func &&
      ranset func == badset = return func{ranset=arg}
    | otherwise             = illegal_call func arg
process_call (ZFunc2 ZMapsto) args@(ZTuple [_,_]) =
    -- this is the identity function, but only for pairs.
    return args
process_call (ZFunc1 ZId) arg =
    -- id is a prefix generic, so should always have a set/type
    -- argument in a correctly typed specification.
    return (ZSetComp [Choose ux arg] (Just (ZTuple [ZVar ux,ZVar ux])))
process_call (ZFunc2 ZUpto) (ZTuple [ZInt lo, ZInt hi]) =
    -- this is just a minor optimization.  Do it now rather than later.
    return (ZIntSet (Just lo) (Just hi))
process_call r1 r2 =
    return (ZCall r1 r2)


characteristic_tuple :: [ZGenFilt] -> UnfoldVisitor ZExpr
characteristic_tuple gfs
  = do  reps <- mapM rep gfs
	char_tuple (concat reps)
  where
  rep (Choose v t) = return [ZVar v]
  rep (Check _)    = return []
  rep (Include se) = sex_to_binding se
  char_tuple [] =
      unfoldError (IllFormed
	   [MStr "empty declaration.  Cannot compute characteristic tuple."])
  char_tuple [e] = return e
  char_tuple es  = return (ZTuple es)
  sex_to_binding se
    = do  ZSchema ugfs <- unfsexpr se
	  let names = genfilt_names ugfs
	  return [ZBinding (sort [(v,ZVar v)|v <- names])]


-- The \Delta and \Xi names are encoded into ZVar's as decorations
-- (to avoid complicating all the lookup data structures with \Delta+\Xi).
make_schema_name :: ZSName -> ZVar
make_schema_name (ZSPlain n) = make_zvar n []
make_schema_name (ZSDelta n) = make_zvar n ["Delta"]
make_schema_name (ZSXi n) = make_zvar n ["Xi"]


schema_set :: [ZGenFilt] -> ZExpr
-- This converts a schema into a set of bindings.
schema_set gfs =
    ZSetComp gfs (Just (ZBinding bs))
    where
    bs = sort (map (\v -> (v, ZVar v)) (genfilt_names gfs))


flattenConjuncts :: ZPred -> [ZGenFilt]
flattenConjuncts (ZAnd p1 p2) = flattenConjuncts p1 ++ flattenConjuncts p2
flattenConjuncts p            = [Check p]


-- TODO: could move this into a more general simplify phase.
unfold_equal e1@(ZBinding b1) e2@(ZBinding b2)
  | dom1==dom2  = return (foldr1 ZAnd (map (uncurry ZEqual) (zip ran1 ran2)))
  | otherwise   = unfoldError (IllFormed [MStr "incompatible bindings: ",
					  MExpr e1, MStr " = ",MExpr e2])
  where
  (dom1,ran1) = unzip b1
  (dom2,ran2) = unzip b2
unfold_equal e1 e2 = return (ZEqual e1 e2)


concatCompat :: [[ZGenFilt]] -> [ZGenFilt] -> [ZGenFilt]
		-> UnfoldVisitor [ZGenFilt]
-- Basically, concatCompat gfss [] [] returns concat gfss
--
-- However, it also removes all duplicates that appear in several
-- entries of gfss.  (It does not remove dups within each entry).
-- Order is preserved (the first occurence of each item is output).
-- It also checks schema-compatibility between each group in gfss.
-- The second and third arguments are caches for the decls/preds
-- that we have seen so far.  They are usually initialised to [].

concatCompat [] _ _ = return []
concatCompat (gfs:gfss) chooses checks =
    do  schema_compatible "schema inclusion" gfs chooses
	let uniqgfs = filter notseen gfs
	let (decls,preds) = partition isDecl uniqgfs
	res2 <- concatCompat gfss (decls++chooses) (preds++checks)
	return (uniqgfs ++ res2)
    where
    notseen g@Choose{} = not (g `elem` chooses)
    notseen g@Check{}  = not (g `elem` checks)
    isDecl g@Choose{} = True
    isDecl _          = False



-- Use these whenever you want to perform a substitution on a term
-- that is being unfolded during Stage 1.
-- (See the comments at the top of this file).

subsexpr :: Substitution -> ZExpr -> UnfoldVisitor ZExpr
subsexpr subs e =
    do  env <- currEnv
	let avoid1 = avoid_variables env
	let avoid2 = avoid1 `union_varset` varset_from_zvars (map fst subs)
	return (substitute subs avoid1 (uniquify_expr avoid2 e))
subspred :: Substitution -> ZPred -> UnfoldVisitor ZPred
subspred subs p =
    do  env <- currEnv
	let avoid1 = avoid_variables env
	let avoid2 = avoid1 `union_varset` varset_from_zvars (map fst subs)
	return (substitute subs avoid1 (uniquify_pred avoid2 p))


------------------------------------------------------------------------
-- Stage 2  (uniquify)
------------------------------------------------------------------------
--
-- These functions take unfolded terms and rename some of the
-- local variables so that no local variable is repeated on any
-- path into the term.  In other words, the output terms do not
-- contain any nested variables that have the same name.  The
-- rest of the animator relies upon this property.
--
-- These work in quite a subtle way: the new names (if any are required)
-- are chosen on the way into the term (top-down) so that inner terms
-- can avoid those new names as well as the old names.  However, the
-- actual renaming is done on the way OUT (bottom-up), so that the
-- substitution function is only ever applied to terms that do not
-- contain nested local variables with identical names.
--
-- NOTE: these uniquify_* functions SHOULD NOT BE EXPORTED, or applied
--       to terms later in the animator, because they assume that the
--       input terms have the usual Z scope rules, which are different
--       to the scope rules elsewhere in the animator.

type UQEnv = VarSet

avoid_vars :: Env -> VarSet
avoid_vars env =
    varset_from_zvars (map fst (local_values env) ++
		       map fst (global_values env))

uniquify_expr :: UQEnv -> ZExpr -> ZExpr
uniquify_expr env e@(ZVar _) = e
uniquify_expr env e@(ZInt _) = e
uniquify_expr env e@(ZGiven _) = e
uniquify_expr env e@(ZFree0 _) = e
uniquify_expr env (ZFree1 n e) = ZFree1 n (uniquify_expr env e)
uniquify_expr env (ZTuple es) = ZTuple (uniquify_exprs env es)
uniquify_expr env (ZBinding bs) = ZBinding [(v,uniquify_expr env e)
					    | (v,e) <- bs]
uniquify_expr env (ZSetDisplay es) = ZSetDisplay (uniquify_exprs env es)
uniquify_expr env (ZSeqDisplay es) = ZSeqDisplay (uniquify_exprs env es)
uniquify_expr env e@(ZFSet _) = e
uniquify_expr env e@(ZIntSet _ _) = e
uniquify_expr env (ZGenerator r e) = ZGenerator r (uniquify_expr env e)
uniquify_expr env (ZCross es) = ZCross (uniquify_exprs env es)
uniquify_expr env (ZFreeType name branches) =
    ZFreeType newname (map unqbranch branches)
    where
    clash = varset_from_zvars [name] `inter_varset` env
    ([newname],sub) = rename_lhsvars clash env [name]
    env2 = env `union_varset` varset_from_zvars [newname]
    unqbranch e@(ZBranch0 _) = e
    unqbranch (ZBranch1 s e) = ZBranch1 s (substitute sub env2
					     (uniquify_expr env2 e))
uniquify_expr env e@ZPowerSet{baseset=b} =
    e{baseset=uniquify_expr env b}
uniquify_expr env e@ZFuncSet{domset=d,ranset=r} =
    e{domset=uniquify_expr env d, ranset=uniquify_expr env r}
uniquify_expr env (ZSetComp gf (Just e)) = ZSetComp gf2 (Just e2)
    where
    (gf2, env2, sub) = uniquify_gfs env gf
    e2 = substitute sub env2 (uniquify_expr env2 e)
uniquify_expr env e@(ZGivenSet _) = e
uniquify_expr env ZUniverse = ZUniverse
uniquify_expr env (ZCall e1 e2) =
    ZCall (uniquify_expr env e1)
	  (uniquify_expr env e2)
uniquify_expr env e@(ZReln _) = e
uniquify_expr env e@(ZFunc1 _) = e
uniquify_expr env e@(ZFunc2 _) = e
uniquify_expr env e@(ZStrange _) = e
uniquify_expr env (ZMu gf (Just e)) = ZMu gf2 (Just e2)
    where
    (gf2, env2, sub) = uniquify_gfs env gf
    e2 = substitute sub env2 (uniquify_expr env2 e)
uniquify_expr env (ZIf_Then_Else p e1 e2) =
    ZIf_Then_Else (uniquify_pred env p)
		  (uniquify_expr env e1)
		  (uniquify_expr env e2)
uniquify_expr env (ZSelect e v) = ZSelect (uniquify_expr env e) v

uniquify_exprs env = map (uniquify_expr env)

uniquify_gfs :: UQEnv -> [ZGenFilt] -> ([ZGenFilt], UQEnv, Substitution)
uniquify_gfs env gfs =
    (map uq gfs, env2, sub)
    where
    names = genfilt_names gfs
    mustrename = varset_from_zvars names `inter_varset` env
    (names2,sub) = rename_lhsvars mustrename env names
    namemap = zip names names2
    env2 = env `union_varset` varset_from_zvars names2
    -- This is the crucial part:  We do NOT rename any free variables
    -- within the types (the e part of 'Choose v e') because they are
    -- not captured by the bound variables, but we do still use env2 to force
    -- their bound variables to be distinct from all of 'names' and 'names2'.
    -- The Check predicates are within the scope of the bound variables,
    -- so their free variables are renamed, after using env2 to ensure
    -- that their bound variables are distinct from 'names' and 'names2' etc.
    uq (Choose v e) = Choose (fromJust (lookup v namemap))
			     (uniquify_expr env2 e)
    uq (Check p) = Check (substitute sub env2 (uniquify_pred env2 p))


uniquify_pred :: UQEnv -> ZPred -> ZPred
uniquify_pred env f@ZFalse{} =
    f
uniquify_pred env t@ZTrue{} =
    t
uniquify_pred env (ZAnd p1 p2) =
    ZAnd (uniquify_pred env p1) (uniquify_pred env p2)
uniquify_pred env (ZOr p1 p2) =
    ZOr (uniquify_pred env p1) (uniquify_pred env p2)
uniquify_pred env (ZImplies p1 p2) =
    ZImplies (uniquify_pred env p1) (uniquify_pred env p2)
uniquify_pred env (ZIff p1 p2) =
    ZIff (uniquify_pred env p1) (uniquify_pred env p2)
uniquify_pred env (ZNot p1) =
    ZNot (uniquify_pred env p1)
uniquify_pred env (ZExists gfs p) =
    ZExists gfs2 p2
    where
    (gfs2, env2, sub) = uniquify_gfs env gfs
    p2 = substitute sub env2 (uniquify_pred env2 p)
uniquify_pred env (ZExists_1 gfs p)=
    ZExists_1 gfs2 p2
    where
    (gfs2, env2, sub) = uniquify_gfs env gfs
    p2 = substitute sub env2 (uniquify_pred env2 p)
uniquify_pred env (ZForall gfs p) =
    ZForall gfs2 p2
    where
    (gfs2, env2, sub) = uniquify_gfs env gfs
    p2 = substitute sub env2 (uniquify_pred env2 p)
uniquify_pred env (ZEqual e1 e2) =
    ZEqual (uniquify_expr env e1) (uniquify_expr env e2)
uniquify_pred env (ZMember e1 e2) =
    ZMember (uniquify_expr env e1) (uniquify_expr env e2)

