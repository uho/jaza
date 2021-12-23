module Reorder
(
  find_facts,
  reorder_gfs,
  range   -- just for testing
)
where
import AST
import SetSize
import Subs
import List
-- import MyDebug

import Parse

type UsefulFacts = [(ZPred,VarSet)]
-- TODO:  add rules for deriving these extra facts:
--      <x,y,z> \partition E    becomes: x \subseteq E and y \subseteq E... ?
--
--      x \prefix E
--      x \suffix E
--      x \inseq E
--      x \cat y \cat z = E  => x \in (? \prefix E) &
--                              y \in (? \inseq E) &
--                              z \in (? \suffix E) &
--
--      # x = E       becomes:  x \in 'sets of size' E  ???
-- TODO:  eliminate more redundant predicates
--        (after they have been moved into the type)
--
-- TODO: include the rule a=b  => a \subseteq b & b \subseteq a
--       (but only for cases where we know a or b is a set,and
--        try to avoid generating these weaker rules if we are also
--        generating a=b).

find_facts :: [ZVar] -> (ZExpr -> VarSet) -> [ZGenFilt] -> UsefulFacts
-- This returns constraints that may be helpful to reduce searching.
-- The goal is to move filters earlier, into the types (the generators).
--
-- More precisely: find_facts vars freevarfunc gfs
-- deduces from gfs facts that have the following form:
--
--    v = E
-- or
--    v \in E
--
-- where v is in vars, E is an expression that does not involve v,
--
-- It is allowable (and common) for returned fact to be a weakened
-- consequence of one of the ZGenFilt terms.  The theorems that
-- justify each weakening are shown in the function cases below.
-- For example:
--
--    thm: a \cup b \subset rhs  =>  a \subset rhs & b \subset rhs
--
-- means that if 'A \cup B \subset S' appears as a Check predicate,
-- then we can deduce that 'A \subset S' must be true, which is useful
-- if A is a variable (or if it can be further analyzed, like 'x \cup y')
-- and S does not contain that variable, etc.
--
-- Each fact is returned as a ZPred (with v on the LHS of the relation).
-- Together with each fact, the set of free variables of the RHS
-- expression is returned, as calculated by 'freevarfunc'.
-- Some callers may pass 'const empty_varset' for freevarfunc,
-- if they know that every RHS expression is a value (which cannot
-- have any free variables).
--
-- Pre: Include terms in gfs should be expanded and ZAnd predicates
--      should have been flattened out into separate Check predicates.
--
find_facts vars fv gfs = concatMap (find_facts2 vars fv) (simplify_gfs gfs)

find_facts2 vars fv (Check (ZEqual e1 e2)) =
    eq_facts vars fv e1 e2 ++ eq_facts vars fv e2 e1
find_facts2 vars fv (Check (ZMember (ZVar v) e2)) =
    makefact vars fv v e2 (ZMember (ZVar v) e2)
find_facts2 vars fv (Check (ZMember (ZTuple [a,b]) (ZReln r))) =
    -- thm: a < b  => a in (? < b) & b in (? > a)
    mem_facts vars fv a r b ++
    (if invertible r
	then mem_facts vars fv b (invert r) a
	else [])
find_facts2 vars fv (Check (ZMember (ZTuple [a,b]) e2)) =
    -- thm: (a,b) \in rhs  =>  a \in \dom rhs & b \in \ran rhs
    find_facts2 vars fv (Check (ZMember a (ZCall (ZFunc1 ZDom) e2))) ++
    find_facts2 vars fv (Check (ZMember b (ZCall (ZFunc1 ZRan) e2)))
find_facts2 _ _ _ =
    []

mem_facts vars fv (ZCall (ZFunc2 ZUnion) (ZTuple [a,b])) ZSubset rhs =
    -- thm: a \cup b \subset rhs  =>  a \subset rhs & b \subset rhs
    mem_facts vars fv a ZSubset rhs ++
    mem_facts vars fv b ZSubset rhs
mem_facts vars fv (ZCall (ZFunc2 ZUnion) (ZTuple [a,b])) ZSubsetEq rhs =
    -- thm: a \cup b \subseteq rhs  =>  a \subset rhs & b \subseteq rhs
    mem_facts vars fv a ZSubsetEq rhs ++
    mem_facts vars fv b ZSubsetEq rhs
mem_facts vars fv (ZSetDisplay es) r rhs
    | r == ZSubset || r == ZSubsetEq
      -- thm: \{a,b,...\} \subset[eq] rhs  =>  a \in rhs & b \in rhs & ...
      = concat [makefact vars fv v rhs (ZMember e rhs) | e@(ZVar v) <- es]
mem_facts vars fv (ZSetDisplay es) ZSubsetEq rhs =
    -- thm: \{a,b,...\} \subset rhs  =>  a \in rhs & b \in rhs & ...
    concat [mem_facts vars fv e ZSubsetEq rhs| e <- es]
mem_facts vars fv lhs@(ZVar v) r rhs =
    makefact vars fv v rhs (ZMember lhs (ZGenerator r rhs))
mem_facts vars fv _ _ _ =
    []


makefact :: [ZVar] -> (ZExpr -> VarSet) -> ZVar -> ZExpr -> ZPred
	    -> UsefulFacts
-- This is a helper function that discards facts that are recursive,
-- or do not involve interesting variables.
makefact vars fv v e fact
    | v `elem` vars && not (ZVar v `in_varset` evars)
	= [(fact, evars)]
    | otherwise
	= []
    where
    evars = fv e


zcall2 :: ZExpr -> ZFunc2 -> ZExpr -> ZExpr
zcall2 a f b = ZCall (ZFunc2 f) (ZTuple [a,b])


eq_facts ::  [ZVar] -> (ZExpr -> VarSet) -> ZExpr -> ZExpr -> UsefulFacts
eq_facts vars fv e1@(ZVar v) e2 =
    -- thm: v=e2  =>  v=e2
    makefact vars fv v e2 (ZEqual e1 e2)
eq_facts vars fv (ZCall (ZFunc2 ZPlus) (ZTuple [a,b])) rhs =
    -- thm: a+b=rhs  =>  a=rhs-b & b=rhs-a
    eq_facts vars fv a (zcall2 rhs ZMinus b) ++
    eq_facts vars fv b (zcall2 rhs ZMinus a)
eq_facts vars fv (ZCall (ZFunc2 ZMinus) (ZTuple [a,b])) rhs =
    -- thm: a-b=rhs  =>  a=rhs+b & b=a-rhs
    eq_facts vars fv a (zcall2 rhs ZPlus b) ++
    eq_facts vars fv b (zcall2 a ZMinus rhs)
eq_facts vars fv (ZCall (ZFunc1 ZDom) (ZVar v)) e2 =
    -- thm: dom v = e2  =>  v in (e2 <-> ZUniverse)
    makefact vars fv v e2 (ZMember (ZVar v) zrelations{domset=e2})
eq_facts vars fv (ZCall (ZFunc1 ZRan) (ZVar v)) e2 =
    -- thm: ran v = e2  =>  v in (ZUniverse <-> e2)
    makefact vars fv v e2 (ZMember (ZVar v) zrelations{ranset=e2})
eq_facts vars fv (ZTuple es1) (ZTuple es2) =
    -- thm: (a,b,c) = (d,e,f)  =>  a=d & b=e & c=f
    concat (zipWith (eq_facts vars fv) es1 es2)
eq_facts vars fv (ZTuple [e1,e2]) rhs =
    -- thm: (a,b = rhs  =>  a=fst(rhs)  & b=snd(rhs)
    eq_facts vars fv e1 (ZCall (ZFunc2 ZFirst) rhs) ++
    eq_facts vars fv e2 (ZCall (ZFunc2 ZSecond) rhs)
eq_facts vars fv (ZBinding es1) (ZBinding es2) =
    -- thm: <x==a,y==b>=<x==c,y==d>  =>  a=c & b=d
    -- If the spec is type correct, domains of vals and patts
    -- will be identical.  If the spec is not type correct, we
    -- just use any names that happen to be in common.
    -- (We could raise an error, but this function doesn't return errors!)
    concat [eq_facts vars fv e1 e2
	    | ((n1,e1),(n2,e2)) <- zip es1 es2, n1==n2]
eq_facts vars fv (ZBinding bs) rhs =
    -- thm: <x==a,y==b>=rhs  =>  a=rhs.x & b=rhs.y
    concat [eq_facts vars fv e (ZSelect rhs v) | (v,e) <- bs]
eq_facts vars fv _ _ =
    []


invertible :: ZReln -> Bool
invertible ZLessThan      = True
invertible ZLessThanEq    = True
invertible ZGreaterThan   = True
invertible ZGreaterThanEq = True
invertible _              = False

invert :: ZReln -> ZReln
invert ZLessThan      = ZGreaterThan
invert ZGreaterThan   = ZLessThan
invert ZLessThanEq    = ZGreaterThanEq
invert ZGreaterThanEq = ZLessThanEq


reorder_gfs :: [ZGenFilt] -> UsefulFacts -> [ZGenFilt]
-- first stage ensures we only have Choose and Check terms.
-- This makes the following processing simpler.
reorder_gfs gfs facts = result
    --debug2 "REORDER="(gfs++[Check ZFalse{reason=[]}]
    --		      ++gfs2++[Check ZFalse{reason=[]}]
    --		      ++result) result
    where
    gfs2   = simplify_gfs gfs
    result = reorder_gfs3 gfs2 facts


reorder_gfs2 :: [ZGenFilt] -> UsefulFacts -> [ZGenFilt]
reorder_gfs2 []  _  =
    []
reorder_gfs2 gfs facts
    | not(null usefuleqs) =
	eqgen (head usefuleqs)
	++ reorder_gfs3 (gfs \\ (eqused (head usefuleqs))) facts
    | not(null usefulmem) =
	let (v,t,es) = snd (minimum usefulmem) in
	[Choose v (bigcap (filter (/= ZUniverse) (t:es)))]
	++ reorder_gfs3 (gfs \\ (Choose v t : concatMap (memused v) (t:es)))
			facts
    | not(null choices) =
	-- output an arbitrary (Choose _ _) term.
	head choices : reorder_gfs3 (gfs \\ [head choices]) facts
    | otherwise =
	-- output any remaining predicates
	gfs
  where
  bigcap []  = ZUniverse
  bigcap [s] = s
  bigcap ss  = ZCall (ZFunc1 ZBigCap) (ZSetDisplay ss)
  bndvars = varset_from_zvars (genfilt_names gfs)
  usefuleqs = [(v,e,t) |
	       Choose v t <- gfs,
	       (ZEqual (ZVar v2) e,fvars) <- facts,
	       v2==v,
	       fvars `inter_varset` bndvars == empty_varset,
	       free_vars t `inter_varset` bndvars == empty_varset]
  eqgen (v,e,t) = [Evaluate v e t]
  eqused (v,e,t) = [Choose v t,
		    Evaluate v e t,
		    Check (ZEqual (ZVar v) e),
		    Check (ZEqual e (ZVar v))]
  usefulmem = [(searchsize (t:es), (v,t,es)) |
	       Choose v t <- gfs,
	       let es = [e |
			 (ZMember (ZVar v2) e,fvars) <- facts,
			 v2 == v,
			 fvars `inter_varset` bndvars == empty_varset]
	       ]
  choices = [c | c@(Choose _ _) <- gfs]
  memused v s@(ZGenerator r e) =
      [Check (ZMember (ZVar v) s),
       Check (ZMember (ZTuple [ZVar v,e]) (ZReln r))] ++
      [Check (ZMember (ZTuple [e,ZVar v]) (ZReln (invert r))) | invertible r]
  memused v s = [Check (ZMember (ZVar v) s)]


-- This works in mutual recursion with reorder_gfs2.
-- It outputs all predicates that do not depend upon the
-- remaining Choose variables.
reorder_gfs3 :: [ZGenFilt] -> UsefulFacts -> [ZGenFilt]
reorder_gfs3 gfs facts =
    preds ++ reorder_gfs2 (gfs \\ preds) facts
    where
    bndvars = varset_from_zvars (genfilt_names gfs)
    preds = filter (does_not_depend_upon bndvars) gfs
    does_not_depend_upon vs (Check p)
	= free_vars p `inter_varset` vs == empty_varset
    does_not_depend_upon vs _
	= False


-- Unfolds (Evaluate _ _ _) entries and complex intersection types.
-- This makes analysis of the ZGenFilt list much easier.
simplify_gfs :: [ZGenFilt] -> [ZGenFilt]
simplify_gfs gfs = concatMap expand gfs
    where
    expand (Choose x (ZCall (ZFunc1 ZBigCap) (ZSetDisplay (t:tt))))
	   -- flatten any complex intersection types created by optimise
                            = [Choose x t] ++ map (makemem x) tt
    expand t@(Choose _ _)   = [t]
    expand t@(Check _)      = [t]
    expand (Evaluate x e t) = expand (Choose x t) ++ [Check (ZEqual (ZVar x) e)]
    expand t                = error ("reorder_gfs should not see: "
					  ++ show t)
    makemem x (ZGenerator r e) = Check (ZMember (ZTuple [ZVar x,e]) (ZReln r))
    makemem x t = Check (ZMember (ZVar x) t)


searchsize :: [ZExpr] -> SetSize
-- This takes a list of set expressions and estimates the
-- size of the intersection of those sets.  This is used purely
-- for comparison with other such results.  It may return an
-- estimate below the true size of the set.
-- Pre: length es > 0
--searchsize es = 100 - length es

searchsize es =
    maxSize - filters
    where
    maxSize = minimum (map (max_size (empty_env [])) (range es:es))
    filters = fromInteger(toInteger(length es - 1))


-- looks for minimum and maximum integer constants in a list of expressions
range :: [ZExpr] -> ZExpr
range es = ZIntSet lo hi
    where
    lo = maximum( Nothing : map findMin es)
    hi = head( dropWhile (==Nothing) (sort(map findMax es)) ++ [Nothing])


findMax (ZIntSet lo hi) = hi
findMax (ZGenerator ZLessThanEq (ZInt k)) = Just k
findMax (ZGenerator ZLessThan (ZInt k)) = Just (k-1)
findMax _ = Nothing

findMin (ZIntSet lo hi) = lo
findMin (ZGenerator ZGreaterThanEq (ZInt k)) = Just k
findMin (ZGenerator ZGreaterThan (ZInt k)) = Just (k+1)
findMin _ = Nothing
