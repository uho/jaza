module Eval
--
-- $Id: Eval.hs,v 1.76 2005/06/15 19:30:42 marku Exp $
--
-- This module defines the basic evaluation functions for:
--
--     expressions  (which evaluate to ZValue data structures)
--     predicates   (which evaluate to Bool values)
--     schemas      (which evaluate to sets of bindings)
--
-- All such evaluation results are wrapped up in the 'ErrorOr' type,
-- to show whether the result is an error or an Ok result.
-- These evaluation functions return closed terms (no free variables).
(
   module AST,    -- The data structures to be evaluated.
   ErrorOr(..),   -- Because evaluation results are wrapped in this.
   isOk, fromOk,

   evalexpr,      -- :: ZExpr -> Env -> ErrorOr ZValue
   evalpred,      -- :: ZPred -> Env -> ErrorOr Bool
   evalsetcomplazy, -- :: [ZGenFilt] -> Env -> [ErrorOr ZValue]

   -- This forces an evaluated expression into finite form, if possible.
   forceexpr      -- :: ZValue -> Env -> ZValue
)
where

import AST
import Errors
import SetSize
import qualified FiniteSets
import qualified List
import qualified Monad
import Maybe
import Subs
import Reorder

----------------------------------------------------------------------
-- Coercion Functions
----------------------------------------------------------------------
--
-- Since the ZExpr (ZValue) data structures often have several
-- alternative ways of representing a given value, these coercion
-- functions transform between the representations, or return an
-- error if that is not possible or would be too slow/large.
--
-- The coercion functions all take an environment as an argument,
-- since that may tell them how hard to work at the coercion.
-- They report a CoercionError if they could not do what was asked.
-- This usually just means that the coercion was too hard!

show_zval :: ZValue -> String
show_zval = show


coerr :: String -> ZValue -> ErrorOr a
coerr expected actual
  = Impossible [MStr "cannot convert: ",MExpr actual,
		MStr ("  into  " ++ expected)]


-- Call this before you generate a ZFSet.
checkZFSetsize :: Env -> SetSize -> ZValue -> ErrorOr ()
checkZFSetsize env size val
  | size <= fromInteger(max_set_size env) =
      Ok ()
  | otherwise =
      TooBig (SetSizeError size (max_set_size env)) [MExpr val]


coerceZInt :: Env -> ZValue -> ErrorOr ZInt
coerceZInt _ (ZInt i) = Ok i
coerceZInt _ zv       = coerr "int" zv


-- This checks that a value is a finite set, containing just integers.
coerceZInts :: Env -> ZValue -> ErrorOr [ZInt]
coerceZInts env v =
    do  fs <- coerceZFSet env v
	is <- sequence (map (coerceZInt env) (FiniteSets.set2list fs))
	return is


coerceZTuple :: Env -> ZValue -> ErrorOr [ZValue]
coerceZTuple _ (ZTuple v)  = Ok v
coerceZTuple _ zv          = coerr "tuple" zv


coerceZSeq :: Env -> ZValue -> ErrorOr [ZValue]
coerceZSeq _ (ZSeqDisplay s) = return s
coerceZSeq env val =
    do  set <- coerceZFSet env val
	if FiniteSets.is_seq set
	   then return (map pair_snd (FiniteSets.set2list set))
	   else coerr "sequence" val

-- same as coerceZSeq, but requires it to be non-empty.
coerceZSeq1 :: Env -> ZValue -> ErrorOr [ZValue]
coerceZSeq1 env s =
    do  seq <- coerceZSeq env s
	if seq == []
	   then Undefined [MStr "non-empty sequence required"]
	   else return seq


coerceZFSet :: Env -> ZValue -> ErrorOr FiniteSets.FinSet
coerceZFSet env (ZFSet v)
  = Ok v
coerceZFSet env e@(ZGenerator r v)
  = do  checkZFSetsize env (max_size env e) e
	values <- zgenerate env r v
	typecheck (all isCanonical values)
	      "generator produced non-canonical value"
	return (FiniteSets.set values)
coerceZFSet env (ZFreeType n bs)
  = do  sets <- sequence (map (branch2set env) bs)
	return (FiniteSets.set (concat sets))
  where
  -- Note: recursive free types will cause an error, because they will
  --       end up calling coerceZFSet on (ZVar n), which is caught below.
  branch2set env (ZBranch0 v)   = return (FiniteSets.set [ZFree0 v])
  branch2set env (ZBranch1 v e) =
      do  s <- coerceZFSet env e
	  return (map (ZFree1 v) s)
coerceZFSet env (ZVar v)
  -- The only way we should get to an unevaluated ZVar is if the
  -- above case for free types was applied to a recursive free type.
  = fail ("cannot make set from: " ++ show v ++ "  (a recursive freetype?)")
coerceZFSet env e@(ZIntSet (Just lo) (Just hi))
  = do  checkZFSetsize env (fromInteger (max 0 (hi - lo + 1))) e
	return (FiniteSets.set_from_ordered_list (map ZInt [lo..hi]))
coerceZFSet env s@ZPowerSet{}
  = do  base <- coerceZFSet env (baseset s)
	checkZFSetsize env (two_power (fromIntegral (FiniteSets.card base))) s
	let empty = FiniteSets.set [zemptyset]
	if is_non_empty s
	   then return (FiniteSets.powerset base `FiniteSets.diff` empty)
	   else return (FiniteSets.powerset base)
coerceZFSet env e@(ZCross es)
  = do  sets <- sequence (map (coerceZFSet env) es)
	let sizes = map (fromIntegral . FiniteSets.card) sets
	checkZFSetsize env (product sizes) e
	return (FiniteSets.set (map ZTuple (cross_product sets)))
coerceZFSet env zv@(ZSeqDisplay s0) =
    do  s <- sequence(map (canonexpr True env) s0)
	let pairs = [ZTuple [ZInt i, a] | (i,a) <- zip [1..] s]
        return (FiniteSets.set_from_ordered_list pairs)
coerceZFSet env zv@(ZSetDisplay vs0) =
    do  vs <- sequence(map (canonexpr True env) vs0)
	return (FiniteSets.set vs)
coerceZFSet env e@(ZSetComp _ _) =
    do  set <- evalsetcomp e env
	if isZFSet set
	   then let ZFSet s = set in return s
	   else coerr "finite set" set
coerceZFSet env zv = coerr "finite set" zv


cross_product :: [[ZValue]] -> [[ZValue]]
cross_product [s] = [[v] | v <- s]
cross_product (s:ss) = [(v:vs)|v<-s, vs<- cross_product ss]

all_subsets :: [a] -> [[a]]
all_subsets []     = [[]]
all_subsets (x:xs) = powxs ++ [ x:ys | ys <- powxs ]
    where powxs = all_subsets xs


zgenerate :: Env -> ZReln -> ZValue -> ErrorOr [ZValue]
-- This returns a list of all the values in the generator.
-- The list will not contain duplicates, but is not necessarily sorted.
zgenerate env ZLessThan      (ZInt i) = return (map ZInt [i-1,i-2..])
zgenerate env ZLessThanEq    (ZInt i) = return (map ZInt [i,i-1..])
zgenerate env ZGreaterThan   (ZInt i) = return (map ZInt [i+1,i+2..])
zgenerate env ZGreaterThanEq (ZInt i) = return (map ZInt [i,i+1..])
zgenerate env ZSubset s =
    do  base <- coerceZFSet env s
	-- NOTE: all_subsets returns the largest set last, so we use 'init'.
	return (map (ZFSet . FiniteSets.set) (init (all_subsets base)))
zgenerate env ZSubsetEq s =
    do  base <- coerceZFSet env s
	return (map (ZFSet . FiniteSets.set) (all_subsets base))
zgenerate env ZPrefix s =
    do  seq <- coerceZSeq env s
	return (map ZSeqDisplay (List.nub (List.inits seq)))
zgenerate env ZSuffix s =
    do  seq <- coerceZSeq env s
	return (map ZSeqDisplay (List.nub (List.tails seq)))
zgenerate env ZInSeq s =
    do  seq <- coerceZSeq env s
	-- Here we return smaller sublists first.
	let lists = [take len (drop start seq) |
		     len <- [0..length seq],
		     start <- [0..length seq - len]]
	return (map ZSeqDisplay (List.nub lists))
zgenerate env r s = Impossible [MStr "cannot generate solutions from: ",
				MExpr (ZGenerator r s)]


coerceZFReln :: Env -> ZValue -> ErrorOr FiniteSets.FinReln
coerceZFReln env zv
  = do  s <- coerceZFSet env zv
	if FiniteSets.is_reln s
	   then return s
	   else coerr "finite relation" (ZFSet s)


coerceZFFunc :: Env -> ZValue -> ErrorOr FiniteSets.FinFunc
coerceZFFunc env zv
  = do  s <- coerceZFSet env zv
	if FiniteSets.is_func s
	   then return s
	   else coerr "finite function" (ZFSet s)


coerceZBinding :: Env -> ZValue -> ErrorOr [(ZVar,ZValue)]
coerceZBinding env (ZBinding bs) = Ok bs
coerceZBinding env zv            = coerr "binding" zv



evalexpr :: ZExpr -> Env -> ErrorOr ZValue
-- First, some ZExpr's that are already fully evaluated.
evalexpr e@ZUniverse env
  = return e
evalexpr e@(ZGiven _) env
  = return e
evalexpr e@(ZGivenSet _) env
  = return e
evalexpr e@(ZInt _) env
  = return e
evalexpr e@(ZReln _) env
  = return e
evalexpr e@(ZFunc1 _) env
  = return e
evalexpr e@(ZFunc2 _) env
  = return e
evalexpr e@(ZStrange _) env
  = return e
evalexpr e@(ZFSet _) env
  = return e
evalexpr e@(ZIntSet _ _) env
  = return e
evalexpr e@(ZFree0 _) env
  = return e
evalexpr (ZFree1 s e) env
  = do  v <- evalexpr e env
	return (ZFree1 s v)
evalexpr e@(ZFreeType _ _) env
  -- Free types are evaluated lazily later, not now.
  -- This is to avoid infinite recursion over recursive free types.
  -- Note that free types never contain free variables, so it is
  -- safe to return just e here, rather than a closure (e,env).
  = return e
evalexpr (ZVar v) env
  = envLookupVar v env    -- MARKU temp change from envLookupLocal for freetype
evalexpr (ZGenerator r e) env
  = do  v <- evalexpr e env
	return (make_generator r v)
    where
    make_generator ZLessThan (ZInt i)      = ZIntSet Nothing      (Just (i-1))
    make_generator ZLessThanEq (ZInt i)    = ZIntSet Nothing      (Just i)
    make_generator ZGreaterThan (ZInt i)   = ZIntSet (Just (i+1)) Nothing
    make_generator ZGreaterThanEq (ZInt i) = ZIntSet (Just i)     Nothing
    make_generator r v = ZGenerator r v
evalexpr e@ZPowerSet{} env
  = do  v <- evalexpr (baseset e) env
	if v==zemptyset
	   then return (make_empty_powerset e)
	   else return e{baseset=v}
evalexpr e@ZFuncSet{} env
  = do  dom <- evalexpr (domset e) env
	ran <- evalexpr (ranset e) env
	if dom==zemptyset || ran==zemptyset
	   then return (make_empty_powerset e)
	   else return e{domset=dom,ranset=ran}
evalexpr (ZCross zes) env
  = do  vs <- evalexprs zes env
	return (ZCross vs)
evalexpr (ZTuple zes) env
  = do  vals <- evalexprs zes env
	return (ZTuple vals)
evalexpr (ZBinding pairs) env
  = do  let (names, zes) = unzip pairs
	vs <- evalexprs zes env
	assertcheck (List.sort names == names) "binding not sorted"
	return (ZBinding (zip names vs))
evalexpr (ZCall f arg) env
  = do  fv <- evalexpr f env
	argv <- evalexpr arg env
	applyfunc env fv argv
evalexpr (ZSetDisplay zes) env
  = do  vals <- evalexprs zes env
	return (FiniteSets.make_zfset vals)
evalexpr (ZSeqDisplay zes) env
  = do  vals <- evalexprs zes env
	-- We could convert <a,b,c> to {(1,a),(2,b),(3,c)} etc., if
	--  a, b and c are all canonical.  But it is easier to
	--  keep all explicit sequences as Haskell-like lists.
	--  (It will be coerced later if necessary).
	return (ZSeqDisplay vals)
evalexpr e@(ZSetComp _ _) env =
    -- If a set comprehension is too hard to evaluate the first time
    -- around, we return it in ZSetComp form.  The context may be able
    -- to do something else, or it may just try to force the evaluation
    -- by calling evalsetcomp directly (perhaps with different size limits).
    let try1 = evalsetcomp e env in
    if isOk try1
       then try1
       else return (substitute (local_values env) (avoid_variables env) e)
evalexpr e@(ZMu gfs (Just ze)) env
  -- This is similar to evaluating a set comprehension, but it
  -- must give a singleton set.  Otherwise, we return an error.
  | notOk errenvs
    = sameError errenvs
  | not (unique_env envs)
    -- gen_and_filter never returns the same environment twice,
    -- so we should get a single env back if the ZMu is well-formed.
    = undef e
  | otherwise
    = evalexpr ze (head envs)
  where
  errenvs = sequence (gen_and_filter gfs env)
  envs    = fromOk errenvs
evalexpr (ZIf_Then_Else p e1 e2) env
  = do  p <- evalpred p env
	if p
	   then evalexpr e1 env
	   else evalexpr e2 env
evalexpr (ZSelect e n) env
  = do  ZBinding b <- evalexpr e env
	let res = lookup n b
	typecheck (res /= Nothing) ("illegal field selection: ." ++ show n)
	let Just val = res
	return val
evalexpr (ZESchema _) env
  = asserterror "ZESchema should be removed before evaluation"
evalexpr (ZLambda _ _) env
  = asserterror "ZLambda should be removed before evaluation"
evalexpr (ZTheta _) env
  = asserterror "ZTheta should be removed before evaluation"
evalexpr e env
  = Impossible [MStr "evaluator cannot handle: ", MExpr e]


evalexprs :: [ZExpr] -> Env -> ErrorOr [ZValue]
evalexprs es env = sequence (map (\e -> evalexpr e env) es)


-- This takes a ZPowerSet or ZFuncSet and evaluates it under the
-- assumption that its basetype is empty (or the dom/ran is empty).
make_empty_powerset :: ZValue -> ZValue
make_empty_powerset orig
    | is_non_empty orig  -- no functions
	= zemptyset
    | otherwise   -- just the empty function/set
	  = ZFSet (FiniteSets.set [zemptyset])


-- This tries to evaluate a set comprehension, but returns
-- a search error if it is too big.
evalsetcomp :: ZExpr -> Env -> ErrorOr ZValue
evalsetcomp e env =
    do  let env2 = set_max_search_space (max_set_size env) env
        vals <- (sequence . snd . evalsetcomplazy e) env2
        return (FiniteSets.make_zfset vals)

-- This evaluates a set comprehension, returning a lazy stream of results.
-- Precondition: sdecls contains only Choose, Check and Evaluate terms.
evalsetcomplazy :: ZExpr -> Env -> (Int, [ErrorOr ZValue])
evalsetcomplazy (ZSetComp gfs (Just bs)) env =
    (maxDepth, map (Monad.join . (evalexpr bs $?)) solns)
    where
    (maxDepth,solns) = gen_and_filter2 0 gfs env


applyfunc :: Env -> ZValue -> ZValue -> ErrorOr ZValue
applyfunc env e@(ZFSet f) arg =
    do  canonarg <- canonexpr True env arg
	FiniteSets.ferrapply (undef (ZCall e arg)) Ok f canonarg
applyfunc env (ZFunc1 f) arg
  = applyfunc1 env f arg
applyfunc env f@(ZStrange ZIter) arg
  -- iter is a curried function (two args), so we must
  -- return the incomplete call, and wait for the second arg.
  = Ok (ZCall f arg)
applyfunc env (ZCall (ZStrange ZIter) n) arg
  = do  i <- coerceZInt env n
	s <- coerceZFReln env arg
	do_iter i s
  where
  maxiter = 100 -- for efficiency, we only handle -maxiter..+maxiter
  do_iter :: ZInt -> ZFSet -> ErrorOr ZValue
  do_iter i s
      | i == 0  -- cannot implement 0 without type inference
	= Impossible [MStr "(iter 0 ...) not implemented yet"]
      | 0 < i && i <= maxiter
	= return (ZFSet (FiniteSets.iter s (fromIntegral i)))
      | -maxiter <= i && i < 0
	= return (ZFSet (FiniteSets.iter (FiniteSets.inverse s)
			   (fromIntegral (- i))))
      | otherwise
	= Impossible [MStr ("iter " ++ show i ++ "...) is too large."),
		      MStr ("  Max power is " ++ show maxiter)]
applyfunc env (ZFunc2 f) (ZTuple [a,b])
  = applyfunc2 env f a b
applyfunc env (ZFunc2 f) arg
  = Impossible [MStr "cannot evaluate to a pair: ", MExpr arg]
applyfunc env e@(ZSeqDisplay s) (ZInt i)
  | 0 < i && i <= (fromIntegral (length s))
      = Ok (s!!(fromIntegral(i-1)))
  | otherwise
      = undef (ZCall e (ZInt i))
applyfunc env s@(ZSetComp gfs e@(Just (ZTuple [argpatt,result]))) argval
  -- The set comprehension (maybe from a lambda) is being used as a function.
  --
  -- (The following code is similar to the 'zmember value (ZSetComp ...)'
  --    code, except here we only know half the member (argval)).
  --
  -- Since the (alleged) function has not been evaluated into ZFSet form,
  -- we know it must be big or difficult.
  -- We match argval against argpatt, then evaluate the ZSetComp again.
  -- If it returns a unique result, the function application is legal!
  -- If it returns no/multiple results, Undef is the correct answer.
  = do  let eqcheck = Check (ZEqual argpatt argval)
	let newgfs = gfs ++ [eqcheck]
	let facts = find_facts (genfilt_names gfs) free_vars newgfs
	-- facts will match argval with some/all of the gfs vars.
	-- (which will reduce the size of the set when we evaluate it).
	misccheck (not (null facts))
		  ("cannot match argument in: " ++ show (ZCall s argval))
	-- In general it is necessary to put 'eqcheck' inside the
	-- set comprehension, even though we've derived facts from it.
	-- Example: { x:\nat @ ((x,1), x) }  applied to  (1,2)
	let newgfs2 = reorder_gfs newgfs facts
	s2 <- evalexpr (ZSetComp newgfs2 (Just result)) env
	unique_result s2
  where
  unique_result (ZFSet [v])       = Ok v
  unique_result (ZFSet _)         = err -- Too few/many results
  unique_result (ZSetDisplay [v]) = Ok v
  unique_result (ZSetDisplay _)   = err -- Too few/many results
  unique_result v = do {s <- coerceZFSet env v; unique_result (ZFSet s)}
  err = undef (ZCall s argval)
applyfunc env f arg
  -- getting desperate here, we try to force it into a finite set
  = do  pairs <- coerceZFSet env f
	FiniteSets.ferrapply (undef (ZCall f arg)) Ok pairs arg
-- MiscError ("don't know how to apply function: " ++ show_zval f)


----------------------------------------------------------------------
--   Unary Toolkit Functions
----------------------------------------------------------------------
applyfunc1 :: Env -> ZFunc1 -> ZValue -> ErrorOr ZValue
applyfunc1 env ZDom (ZSetComp gfs (Just (ZTuple [a,b])))
  -- Note that gfs still calculates b, to ensure that it is defined.
  = return (ZSetComp gfs (Just a))
applyfunc1 env ZDom val
  = do  s <- error_context (coerceZFSet env val) 
	     [MStr " during dom of ",MExpr val]
	return (ZFSet (FiniteSets.dom s))
applyfunc1 env ZRan (ZSetComp gfs (Just (ZTuple [a,b])))
  -- Note that gfs still calculates a, to ensure that it is defined.
  = return (ZSetComp gfs (Just b))
applyfunc1 env ZRan val
  = do  s <- error_context (coerceZFSet env val) 
	     [MStr " during ran of ",MExpr val]
	return (ZFSet (FiniteSets.ran s))
applyfunc1 env ZBigCap (ZSetDisplay ss) =
    zintersect env ss
applyfunc1 env ZBigCap s =
    do  values <- coerceZFSet env s
	fsets <- sequence (map (coerceZFSet env) values)
	if fsets == []
	   then Impossible [MStr "generalized intersection of {} not implemented (1)"]
	   else return (ZFSet (FiniteSets.gen_inter fsets))
applyfunc1 env ZBigCup s =
    do  values <- coerceZFSet env s
	fsets <- sequence (map (coerceZFSet env) values)
	return (ZFSet (FiniteSets.gen_union fsets))
applyfunc1 env ZSucc (ZInt i)   = Ok (ZInt (i+1))
applyfunc1 env ZNegate (ZInt i) = Ok (ZInt (- i))

applyfunc1 env ZHead v   = seq1_func env v head
applyfunc1 env ZTail v   = seq1_func env v (ZSeqDisplay . tail)
applyfunc1 env ZLast v   = seq1_func env v last
applyfunc1 env ZFront v  = seq1_func env v (ZSeqDisplay . init)
applyfunc1 env ZRev v =
    do  seq <- coerceZSeq env v
	return (ZSeqDisplay (reverse seq))

applyfunc1 env ZMax (ZIntSet Nothing (Just hi)) =
    return (ZInt hi)
applyfunc1 env ZMax (ZIntSet (Just lo) (Just hi))
    | lo <= hi = return (ZInt hi)
applyfunc1 env ZMax e@(ZIntSet _ _) =
    undef (ZCall (ZFunc1 ZMax) e)
applyfunc1 env ZMax v =
    do  is <- coerceZInts env v
	return (ZInt (maximum is))

applyfunc1 env ZMin (ZIntSet (Just lo) Nothing) =
    return (ZInt lo)
applyfunc1 env ZMin (ZIntSet (Just lo) (Just hi))
    | lo <= hi   = return (ZInt lo)
applyfunc1 env ZMin e@(ZIntSet _ _) =
    undef (ZCall (ZFunc1 ZMin) e)
applyfunc1 env ZMin v =
    do  is <- coerceZInts env v
	return (ZInt (minimum is))

applyfunc1 env ZInv (ZSetComp gfs (Just (ZTuple [a,b])))
  = return (ZSetComp gfs (Just (ZTuple [b,a])))
applyfunc1 env ZInv val
  = do s <- coerceZFReln env val
       return (ZFSet (FiniteSets.inverse s))
applyfunc1 env ZClosure val
  = do s <- coerceZFReln env val
       return (ZFSet (FiniteSets.transclosure s))

-- This is an extension of Z, for a student assignment (424 module 3).
applyfunc1 env ZSum (ZFSet [])
 = return (ZInt 0)
applyfunc1 env ZSum f
 = do  pairs <- coerceZFFunc env f
       let ints = [p | p@(ZTuple [_,ZInt _]) <- pairs]
       let rest = (List.\\) pairs ints
       typecheck (rest == []) ("sum of non-integer function: " ++ show rest)
       return (ZInt (sum [i | ZTuple [_,ZInt i] <- pairs]))

applyfunc1 env ZSizeof (ZIntSet (Just lo) (Just hi))
 = Ok (ZInt (maximum [0,hi - lo + 1]))
applyfunc1 env ZSizeof e@(ZIntSet _ _)
 = undef (ZCall (ZFunc1 ZSizeof) e) -- all other integer ranges are infinite!
applyfunc1 env ZSizeof val
 = do  s <- coerceZFSet env val
       return (ZInt (fromIntegral (FiniteSets.card s)))

applyfunc1 env ZSquash val
 = do  s <- coerceZFSet env val
       check_squashable 1 (FiniteSets.set2list s)
       return (ZSeqDisplay (map pair_snd (FiniteSets.set2list s)))

applyfunc1 env ZDCat val
 = do  s <- coerceZSeq env val
       ss <- sequence (map (coerceZSeq env) s)
       return (ZSeqDisplay (concat ss))

applyfunc1 env f a
 = Impossible [MStr "Unimplemented unary function call: ",
	       MExpr (ZCall (ZFunc1 f) a)]

seq1_func :: Env -> ZValue -> ([ZValue] -> ZValue) -> ErrorOr ZValue
seq1_func env v func =
    do  seq <- coerceZSeq1 env v
	return (func seq)

-- This checks that the domain of a set can be squashed into a sequence
check_squashable :: ZInt -> [ZValue] -> ErrorOr ()
check_squashable n [] = Ok ()
check_squashable n (ZTuple [ZInt i,_] : vs)
    | n <= i = check_squashable (i+1) vs
    | otherwise = Undefined [MStr "squash applied to non-function.  ",
			     MStr "Repeated domain value: ", MExpr (ZInt i)]
check_squashable n (val : _) =
    Impossible [MStr "squash could not evaluate this to an (int,_) pair: ",
		MExpr val]

----------------------------------------------------------------------
--   Binary Toolkit Functions
----------------------------------------------------------------------
applyfunc2 :: Env -> ZFunc2 -> ZValue -> ZValue -> ErrorOr ZValue

applyfunc2 env ZUpto (ZInt a) (ZInt b)
 | a > b     = Ok zemptyset
 | otherwise = Ok (ZIntSet (Just a) (Just b))

applyfunc2 env ZPlus (ZInt a) (ZInt b)
 = Ok (ZInt (a+b))
applyfunc2 env ZMinus (ZInt a) (ZInt b)
 = Ok (ZInt (a-b))
applyfunc2 env ZTimes (ZInt a) (ZInt b)
 = Ok (ZInt (a*b))
applyfunc2 env ZDiv e1@(ZInt a) e2@(ZInt b)
 -- Haskell `div` truncates towards -infinity, like the Z div.
 | b == 0    = undef (ZCall (ZFunc2 ZDiv) (ZTuple [e1,e2]))
 | otherwise = Ok (ZInt (a `div` b))
applyfunc2 env ZMod e1@(ZInt a) e2@(ZInt b)
 -- Haskell `mod` truncates towards -infinity, like the Z mod.
 | b == 0    = undef (ZCall (ZFunc2 ZMod) (ZTuple [e1,e2]))
 | otherwise = Ok (ZInt (a `mod` b))

applyfunc2 env ZUnion a b
 = do  as <- coerceZFSet env a
       bs <- coerceZFSet env b
       return (ZFSet (FiniteSets.union as bs))
applyfunc2 env ZInter a b
 = zintersect env (flatten_zfunc2 ZInter a ++ flatten_zfunc2 ZInter b)
applyfunc2 env ZSetMinus a b
 = do  as <- coerceZFSet env a
       bs <- coerceZFSet env b
       return (ZFSet (FiniteSets.diff as bs))
applyfunc2 env ZDRes a b
  = do  sa <- coerceZFSet env a
	rb <- coerceZFReln env b
	return (ZFSet (FiniteSets.domres sa rb))
applyfunc2 env ZRRes a b
  = do  ra <- coerceZFReln env a
	sb <- coerceZFSet env b
	return (ZFSet (FiniteSets.ranres ra sb))
applyfunc2 env ZNDRes a b
  = do  sa <- coerceZFSet env a
	rb <- coerceZFReln env b
	return (ZFSet (FiniteSets.domsub sa rb))
applyfunc2 env ZNRRes a b
  = do  ra <- coerceZFReln env a
	sb <- coerceZFSet env b
	return (ZFSet (FiniteSets.ransub ra sb))
applyfunc2 env ZOPlus a b
  = do  ra <- coerceZFReln env a
	rb <- coerceZFReln env b
	return (ZFSet (FiniteSets.override ra rb))
applyfunc2 env ZRelImg a b
  = do  ra <- coerceZFReln env a
	sb <- coerceZFSet env b
	return (ZFSet (FiniteSets.image ra sb))
applyfunc2 env ZComp a b
  = do  sa <- coerceZFReln env a
	sb <- coerceZFReln env b
	return (ZFSet (FiniteSets.semi sa sb))
applyfunc2 env ZCirc a b
  = applyfunc2 env ZComp b a


applyfunc2 env ZCat a b
  = do  sa <- coerceZSeq env a
	sb <- coerceZSeq env b
	return (ZSeqDisplay (sa++sb))

applyfunc2 env ZExtract a b
 = do  -- this operator requires 'b' to be a sequence,
       -- so we coerce it to a ZSeqDisplay to ensure that it is
       -- correctly typed (as well as making evaluation easier).
       seq <- coerceZSeq env b
       seq2 <- Monad.filterM (\(i,val) -> zmember env (ZInt i) a)
			     (zip [1..] seq)
       return (ZSeqDisplay (map snd seq2))

applyfunc2 env ZFilter a b
 = do  -- this operator requires 'a' to be a sequence,
       -- so we coerce it to a ZSeqDisplay to ensure that it is
       -- correctly typed (as well as making evaluation easier).
       seq <- coerceZSeq env a
       seq2 <- Monad.filterM (\val -> zmember env val b) seq
       return (ZSeqDisplay seq2)

applyfunc2 env ZFirst  a b
  = Ok a
applyfunc2 env ZSecond a b
  = Ok b

applyfunc2 env f a b
  = Impossible [MStr "Unimplemented binary function call: ",
		MExpr (ZCall (ZFunc2 f) (ZTuple [a,b]))]

-- This flattens out nested occurrences of a given ZFunc2 operator.
flatten_zfunc2 :: ZFunc2 -> ZExpr -> [ZExpr]
flatten_zfunc2 f e@(ZCall (ZFunc2 f2) (ZTuple [x,y]))
    | f==f2 = flatten_zfunc2 f x ++ flatten_zfunc2 f y
    | otherwise = [e]
flatten_zfunc2 _ e = [e]

----------------------------------------------------------------------
-- gen_and_filter decls env.
--
-- Given 'decls' (a list of declarations and filter predicates),
-- this returns a list of environments.  Each environment returned
-- is the original environment, 'env', extended by exactly the names
-- that are declared in decls.  Furthermore, the values of those
-- names have been proved to satisfy the filter predicates
-- and the type constraints in 'decls'.
--
-- gen_and_filter has the useful property that it never returns duplicate
-- environments.  That is, every environment that it returns is different
-- to the previous environments that it has returned.
-- Other parts of the evaluator (e.g. ZMu) rely on this property.
-- We will have to be careful to preserve this property when adding
-- more ways of converting types into sequences of values
-- (currently coerceZFSet removes duplicates).
-- This property means testing the result of gen_and_filter for
-- uniqueness is easy -- check that no errors were returned, then
-- call unique_env, which just checks for a singleton list:

unique_env :: [Env] -> Bool
unique_env [_] = True
unique_env _   = False


gen_and_filter :: [ZGenFilt] -> Env -> [ErrorOr Env]
gen_and_filter gfs env = snd(gen_and_filter2 0 gfs env)

-- this returns (maximum_depth_reached, list_of_solutions)
gen_and_filter2 :: Int -> [ZGenFilt] -> Env -> (Int, [ErrorOr Env])
gen_and_filter2 depth [] env
  = (depth, [Ok env])
gen_and_filter2 depth (Choose v ze : gfs) env
  | notOk fset = (depth, [sameError fset])
  | notOk env2 = (depth, [sameError env2])
  | maxs==[]   = (depth, [])
  | otherwise  = (maximum maxs, concat solns)
  where
  zeval = error_context (evalexpr ze env) [MStr " while choosing ",MVars [v]]
  fset = Monad.join (coerceZFSet env $? zeval)
  env2 = multiply_search_space v (FiniteSets.card (fromOk fset)) env
  extend_env val = envPushLocal v val (fromOk env2)
  values = FiniteSets.set2list (fromOk fset)
  (maxs,solns) = unzip(map (gen_and_filter2 (depth+1) gfs . extend_env) values)  
gen_and_filter2 depth (Check zp : gfs) env
  | b == Ok True       = gen_and_filter2 (depth+1) gfs env 
  | b == Ok False      = (depth, [])
  | isUndef b &&
    falseCheck gfs env = (depth, [])
  | otherwise          = (depth, [sameError b])
  where
  b = error_context (evalpred zp env)
	  [MStr " while checking ",MPred zp]
gen_and_filter2 depth (Evaluate v e t : gfs) env
  | notOk val
      = (depth, [error_context (sameError val) 
                  [MStr " while evaluating ",MVars [v]]])
  | b == Ok False
      = (depth, [])
  | isUndef b && falseCheck gfs newenv
      = (depth, [])
  | b == Ok True
      = gen_and_filter2 (depth+1) gfs newenv
  | otherwise
      = (depth, [error_context (sameError b) 
                  [MStr " while checking ",MPred vt]])
  where
  val = evalexpr e env
  newenv = envPushLocal v (fromOk val) env
  vt = ZMember (fromOk val) t
  b = evalpred vt env


-- This returns True if one of the Check predicates at the front
-- of gfs (before any Choose/Evaluate terms introduce variables)
-- can be evaluated to False.
falseCheck :: [ZGenFilt] -> Env -> Bool
falseCheck (Check p:gfs) env
    | evalpred p env == Ok False = True
    | otherwise = falseCheck gfs env
falseCheck _ env = False

evalpred :: ZPred -> Env -> ErrorOr Bool
evalpred ZFalse{} env
  = Ok False
evalpred ZTrue{} env
  = Ok True
evalpred (ZAnd a b) env
  = zand (evalpred a env) (evalpred b env)
evalpred (ZOr a b) env
  = zor (evalpred a env) (evalpred b env)
evalpred (ZImplies a b) env
  = zor (not $? evalpred a env) (evalpred b env)
evalpred (ZIff a b) env
  = ((==) $? evalpred a env) ?$? evalpred b env
evalpred (ZNot a) env
  = not $? evalpred a env
evalpred (ZExists gfs zp) env
  -- Here we do not want to be strict in passing all errors through.
  -- Instead, we can be lazy, so we avoid trying all possible values.
  -- We scan through the list of returned results from the head:
  --   If we see an (Ok True) we can return it immediately.
  --   If we see (Ok False), we need to keep searching.
  --   If we see any error, we can carry on hoping for an (Ok True)
  --   but if we do not find one, we must return an error.
  = (exists . map (Monad.join . (evalpred zp $?)) . gen_and_filter gfs) env
    where
	exists []            = Ok False   -- no choice satisfied zp
	exists (Ok False:xs) = exists xs  -- keep searching
	exists (Ok True:_)   = Ok True    -- found a solution!
	exists (err:xs)
	    = let rest = exists xs in
		  if rest == Ok True
		     then rest
		     else mergeErrors err rest
evalpred (ZExists_1 gfs zp) env
  -- This is similar to ZExists, but we check that there is exactly
  -- one True.  We still use the lazy evalution, in order to return
  -- sooner if we find multiple Trues.  We do not allow any undefined
  -- results, because they could be either True or False.
  --
  -- Note: The description of Exists_1 is a little ambiguous in
  --       Spivey's ZRM2 (page 70).  It states that:
  --
  --       "(\exists_1 S @ P) is true if there is exactly one such way
  --        of giving values to the variables introduced by S."
  --
  --       This suggests that gfs must produce exactly one environment.
  --       But Spivey says "(\exists_1 S | P @ Q) <=> (\exists_1 S @ P /\ Q)",
  --       so we allow gfs to have produce many environments, but
  --       require exactly one of those environments to satisfy zp.
  --
  = (exists0 . map (Monad.join . (evalpred zp $?)) . gen_and_filter gfs) env
    where
	exists0 []            = Ok False   -- no choice satisfied zp
	exists0 (Ok False:xs) = exists0 xs  -- keep searching
	exists0 (Ok True:xs)  = exists1 xs -- found first solution!
	exists0 (err:_)       = err -- return errors/Undef immediately
	exists1 []            = Ok True    -- only one True was found.
	exists1 (Ok False:xs) = exists1 xs -- keep searching
	exists1 (Ok True:xs)  = Ok False   -- this is the second True.
	exists1 (err:_)       = err -- return errors/Undef immediately
evalpred (ZForall gfs zp) env
  -- The inverse of ZExists.  Same lazy evaluation is used.
  = (forall0 . map (Monad.join . (evalpred zp $?)) . gen_and_filter gfs) env
    where
	forall0 []            = Ok True    -- all choices satisfied zp
	forall0 (Ok True:xs)  = forall0 xs  -- keep searching
	forall0 (Ok False:_)  = Ok False   -- found a countercase!
	forall0 (err:xs)      = let rest = forall0 xs in
				if rest == Ok False
				   then rest
				   else mergeErrors err rest
evalpred (ZEqual a b) env
  = do  va <- evalexpr a env
	vb <- evalexpr b env
	zequal env va vb
evalpred (ZMember a b) env
  = do  va <- evalexpr a env
	vb <- evalexpr b env
	zmember env va vb
evalpred e env
  = Impossible [MStr "evaluator cannot handle: ", MPred e]



-- Note carefully how these predicate operators are not strict
-- with respect to errors.
-- They are one of the few places where an Ok result can sometimes
-- be returned, even though one argument has detected an error.

zand :: ErrorOr Bool -> ErrorOr Bool -> ErrorOr Bool
zand (Ok False) _          = Ok False
zand _          (Ok False) = Ok False
zand (Ok True)  (Ok True)  = Ok True
zand err1       (Ok True)  = err1
zand (Ok True)  err2       = err2
zand err1       err2       = mergeErrors err1 err2

zor :: ErrorOr Bool -> ErrorOr Bool -> ErrorOr Bool
zor (Ok True)  _          = Ok True
zor _          (Ok True)  = Ok True
zor (Ok False) (Ok False) = Ok False
zor err1       (Ok False) = err1
zor (Ok False) err2       = err2
zor err1       err2       = mergeErrors err1 err2



-- This is just like the standard monadic 'sequence', except that
-- it returns the first (Ok False) result.
sequence_and :: [ErrorOr Bool] -> ErrorOr Bool
sequence_and []           = return True
sequence_and (Ok False:_) = return False
sequence_and (Ok True:vs) = sequence_and vs
sequence_and (err:_)      = sameError err


------------------------------------------------------------
-- Z Toolkit functions and basic logical operators
------------------------------------------------------------

-- TODO: These need to be extended to handle more kinds of ZValues
--   (Could do extensional equality test over sets, etc.)
zequal :: Env -> ZValue -> ZValue -> ErrorOr Bool
zequal env (ZIntSet lo1 hi1) (ZIntSet lo2 hi2)
  = return (lo1 == lo2 && hi1 == hi2)
zequal env (ZBinding b1) (ZBinding b2)
  = do  let (n1,vals1) = unzip b1
	let (n2,vals2) = unzip b2
	typecheck (n1 == n2)
	   ("incompatible bindings: "
	    ++ show_zvars n1 ++ "  "
	    ++ show_zvars n2)
	sequence_and (zipWith (zequal env) vals1 vals2)
zequal env (ZFree1 n1 val1) (ZFree1 n2 val2)
  | n1==n2    = zequal env val1 val2
  | otherwise = return False
zequal env (ZTuple vals1) v2
  = do  vals2 <- coerceZTuple env v2
	sequence_and (zipWith (zequal env) vals1 vals2)
zequal env v1 (ZTuple vals2)
  = do  vals1 <- coerceZTuple env v1
	sequence_and (zipWith (zequal env) vals1 vals2)
zequal env a b
  -- an infinite set cannot be equal to a finite set
  | isOk afin && isOk bfin
    && fromOk afin /= fromOk bfin = return False
  where
  afin = zfiniteset a
  bfin = zfiniteset a
zequal env a b
  -- an empty set cannot be equal to a non-empty set
  | a == ZFSet [] && isOk bnonempty && fromOk bnonempty = return False
  | b == ZFSet [] && isOk anonempty && fromOk anonempty = return False
  where
  anonempty = znon_empty a
  bnonempty = znon_empty b
--
-- This last case actually handles most kinds of values,
-- because it works on all Canonical values, plus more...
-- As a last resort, we try coercing both values to sets.
-- This may seem strange, since the values being compared for
-- equality may not be sets at all, but in fact, most other common
-- kinds of values will have been caught by the isCanonical case,
-- or the above cases.
zequal env a b
  | identical &&
    isDefined a         = Ok True
  | isCanonical a &&
    isCanonical b       = Ok identical
  | isOk sa && isOk sb  = Ok (sa == sb)
  | otherwise           = Impossible [MStr "cannot evaluate: ",
				      MPred (ZEqual a b)]
  where
  identical = a==b
  sa = coerceZFSet env a
  sb = coerceZFSet env b


zmember :: Env -> ZValue -> ZValue -> ErrorOr Bool
zmember env _ ZUniverse
  = return True
zmember env (ZGiven s) (ZGivenSet name)
  -- We have no way of knowing which given set s belongs to!
  -- So we always return True.  This is correct if the spec is type correct.
  = return True
zmember env v s@(ZSetDisplay vs)
  | not (isDefined v)
      = Impossible [MStr "not sure if this is defined: ",MExpr v]
  | any ((== Ok True).(zequal env v)) vs
      = Ok True
  | all ((== Ok False).(zequal env v)) vs
      = Ok False
  | otherwise
      = Impossible [MStr "cannot evaluate: ",MPred (ZMember v s),
		    MStr ",  because some members are hard to evaluate"]
zmember env v (ZFSet vs)
  | isCanonical v
      = return (v `FiniteSets.mem` vs)     -- fastest test
  | otherwise
      = zmember env v (ZSetDisplay vs)
zmember env (ZInt v) (ZIntSet lo hi)
  = Ok ((lo == Nothing || fromJust lo <= v) &&
	(hi == Nothing || v <= fromJust hi))
zmember env v (ZStrange ZDisjoint)
  = do  (disjoint, _) <- zdisjoint env v
	return disjoint
zmember env (ZTuple [a,b]) (ZReln r)
  = zreln env r a b
zmember env (ZTuple vs) (ZCross sets)
  = sequence_and (zipWith (zmember env) vs sets)
zmember env val s@(ZSetComp gfs (Just e))
  -- we get to this point because s is too big.
  | facts == [] = Impossible [MStr "cannot unify member with set output in: ",
			      MPred (ZMember val s)]
  | notOk s2  = sameError s2
  | otherwise = zmember env val (fromOk s2)
  where
  facts = find_facts (genfilt_names gfs) (const empty_varset)
		     [Check (ZEqual e val)]
  newgfs = reorder_gfs gfs facts
  s2 = evalsetcomp (ZSetComp newgfs (Just e)) env
zmember env v1 (ZGenerator r v2)
  = zreln env r v1 v2
zmember env s pset@ZPowerSet{}
  = sequence_and
      ([zsubseteq env s (baseset pset)] ++
       [znon_empty s | is_non_empty pset] ++
       [zfiniteset s | is_finite pset])
zmember env s f@ZFuncSet{}
  = do  pairs <- coerceZFReln env s
	let dom = FiniteSets.dom pairs
	let ran = FiniteSets.ran pairs
	let b = (is_function f `implies` FiniteSets.is_func pairs) &&
		(is_non_empty f `implies` not(pairs == FiniteSets.emptyset)) &&
		(is_sequence f `implies` FiniteSets.is_seq pairs) &&
		(is_one2one f `implies` (FiniteSets.card pairs ==
					  FiniteSets.card ran))
		-- all ZFSet's are finite, so we do not check is_finite.
	sequence_and
	  ( [Ok b] ++
	    [zsubseteq env (ZFSet dom) (domset f) | not (is_total f)] ++
	    [zsubseteq env (ZFSet ran) (ranset f) | not (is_onto f)] ++
	    [zequal env (ZFSet dom) (domset f) | is_total f] ++
	    [zequal env (ZFSet ran) (ranset f) | is_onto f]
	  )
zmember env (ZFree0 n) (ZFreeType tname bs)
  = Ok (elem (ZBranch0 n) bs)
zmember env (ZFree1 branch v) t@(ZFreeType tname bs)
  = do  let matches = [x | x@(ZBranch1 n _) <- bs, n==branch]
	if null matches
	   then Ok False
	   else do  let ZBranch1 _ s = head matches
		    -- Because FreeTypes can be infinitely recursive,
		    --  we evaluate them lazily.
		    evalpred (ZMember v s) (envPushLocal tname t env)
zmember env v s
  | isCanonical v = do fset <- coerceZFSet env s
		       return (v `FiniteSets.mem` fset)
  | otherwise     = Impossible [MStr "cannot evaluate ",MExpr v,
				MStr " enough to determine membership"]


zreln :: Env -> ZReln -> ZValue -> ZValue -> ErrorOr Bool
zreln env ZLessThan      (ZInt a) (ZInt b) = Ok (a < b)
zreln env ZLessThanEq    (ZInt a) (ZInt b) = Ok (a <= b)
zreln env ZGreaterThan   (ZInt a) (ZInt b) = Ok (a > b)
zreln env ZGreaterThanEq (ZInt a) (ZInt b) = Ok (a >= b)
zreln env ZSubset a@(ZIntSet _ _) b@(ZIntSet _ _)
  = do  sub <- zsubseteq env a b
	return (sub && a /= b)
zreln env ZSubset a b
  = do  sub <- zsubseteq env a b
	if not sub
	   then return False
	   else do sa <- coerceZFSet env a
		   sb <- coerceZFSet env b
		   return (sa /= sb)
zreln env ZSubsetEq a b =
    zsubseteq env a b
zreln env ZPartition a b =
    do  bset <- coerceZFSet env b
	(disjoint, aset) <- zdisjoint env a
	return (disjoint &&
		FiniteSets.card bset == FiniteSets.card aset)
zreln env ZPrefix a b =
    do  sa <- coerceZSeq env a
	sb <- coerceZSeq env b
	return (List.isPrefixOf sa sb)
zreln env ZSuffix a b =
    do  sa <- coerceZSeq env a
	sb <- coerceZSeq env b
	return (List.isSuffixOf sa sb)
zreln env ZInSeq a b =
    do  sa <- coerceZSeq env a
	sb <- coerceZSeq env b
	return (or [List.isSuffixOf sa prefix | prefix <- List.inits sb])
zreln env rel _ _
  = Impossible [MStr ("unimplemented relation: " ++ show rel)]


zsubseteq :: Env -> ZValue -> ZValue -> ErrorOr Bool
zsubseteq env (ZIntSet lo hi) (ZIntSet lo2 hi2)
  = Ok (  (lo2==Nothing || lo /= Nothing && fromJust lo2 <= fromJust lo)
       && (hi2==Nothing || hi /= Nothing && fromJust hi <= fromJust hi2))
zsubseteq env (ZFSet s1) (ZFSet s2)
  = return (FiniteSets.subset s1 s2)
zsubseteq env v1 v2
  = do  s1 <- coerceZFSet env v1
	check_membership env (FiniteSets.set2list s1) v2
  where
  check_membership env [] _ = Ok True
  check_membership env (v:vs) s
      = do  mem <- zmember env v s
	    if mem
	       then check_membership env vs s
	       else return False


zdisjoint :: Env -> ZValue -> ErrorOr (Bool, ZFSet)
zdisjoint env aval =
    do	amap <- coerceZFFunc env aval
	asets <- sequence (map (getzfset . pair_snd) amap)
	let asize = sum(map FiniteSets.card asets)
	let aunion = FiniteSets.gen_union asets
	return (asize == FiniteSets.card aunion, aunion)
    where
    -- The above coercions mean that these values are all in canonical
    -- form, so should all be ZFSet values.
    getzfset (ZFSet s) = return s
    getzfset _ = fail "strange value in first argument of partition/disjoint"


-- This returns True iff the given ZValue is obviously a non-empty set.
znon_empty :: ZValue -> ErrorOr Bool
znon_empty (ZUniverse)        = Ok True
znon_empty (ZFSet s)          = Ok (not (FiniteSets.emptyset == s))
znon_empty (ZIntSet (Just lo) (Just hi))
			      = Ok (lo < hi)
znon_empty (ZIntSet _ _)      = Ok True  -- it is infinite
znon_empty (ZSetDisplay vals) = Ok (not (null vals))
znon_empty (ZSeqDisplay vals) = Ok (not (null vals))
znon_empty (ZCross ss)        = sequence_and (map znon_empty ss)
znon_empty e@(ZFreeType f bs)
  | null leaves = Impossible [MStr "cannot decide if free type is non-empty: ",
			      MExpr e]
  | otherwise   = Ok True
  where
  leaves = [n | ZBranch0 n <- bs]
-- TODO: the next two should be relaxed (eg. not(is_non_empty s))
-- TODO: add a ZGenerator case
znon_empty s@ZPowerSet{} = znon_empty (baseset s)
znon_empty s@ZFuncSet{}  = sequence_and [znon_empty (domset s),
					 znon_empty (ranset s)]
znon_empty s = Impossible [MStr "cannot decide is_non_empty: ",MExpr s]


-- This returns True iff the given ZValue is obviously a finite set.
zfiniteset :: ZValue -> ErrorOr Bool
zfiniteset (ZUniverse)       = Ok False
zfiniteset (ZFSet _)         = Ok True
zfiniteset (ZIntSet (Just _) (Just _))
			     = Ok True
zfiniteset (ZIntSet _ _)     = Ok False
zfiniteset (ZCross ss)       = sequence_and (map zfiniteset ss)
zfiniteset (ZSetDisplay _)   = Ok True
zfiniteset (ZSeqDisplay _)   = Ok True
zfiniteset e@(ZGenerator r v)= Ok ((max_size dummy_eval_env e) < Huge)
zfiniteset s@ZPowerSet{}     = zfiniteset (baseset s)
zfiniteset s@ZFuncSet{}      = sequence_and [zfiniteset (domset s),
					     zfiniteset (ranset s)]
zfiniteset (ZFreeType f bs)
  = sequence_and (map zfiniteset [e | ZBranch1 n e <- bs])
zfiniteset s = Impossible [MStr "cannot decide is_finite: ", MExpr s]


------------------------------------------------------------
-- Z Toolkit functions
------------------------------------------------------------
-- Intersection of sets is a key operation, since we rely on
-- it on reduce the size of search spaces.
-- zintersect takes a list of (any kind of) set values and
-- returns their intersection.
zintersect :: Env -> [ZValue] -> ErrorOr ZValue
zintersect env ss =
    -- Phase 1 is to combine all similar-data-structure sets,
    -- using algorithms specific to each kind.
    let -- Intersect all the ZFSets
	fsets = [s | s@(ZFSet _) <- ss]
	fset = if null fsets
		  then ZUniverse
		  else ZFSet (FiniteSets.gen_inter [fs | ZFSet fs <- fsets])
	-- Intersect all the integer ranges
	ranges   = [r | r@(ZIntSet _ _) <- ss]
	(lows,highs) = unzip [(lo,hi) | ZIntSet lo hi <- ranges]
	lo  = nothing_or maximum lows
	hi  = nothing_or minimum highs
	range = if lo==Nothing && hi==Nothing
		   then ZUniverse
		   else ZIntSet lo hi
	-- TODO: intersect all the 'ZFuncSet's  (and 'PowerSet's?)
	-- rels     = [r | s@ZFuncSet{} <- ss]
	-- TODO: do something special with any 'ZGenerator's.
	-- Collect any remaining sets (these will be used as filters)
	others = (List.\\) ss (ranges ++ fsets) in   -- ++ rels)
    zintersect2 env (filter (/= ZUniverse) (fset : range : List.sort others))
--zintersect env ss =
--    do  fsets <- sequence_and (map (coerceZFSet env) ss)
--	if fsets == []
--	   then MiscError "generalized intersection of {} not implemented (2)"
--           else return (ZFSet (FiniteSets.gen_inter fsets))

zintersect2 :: Env -> [ZValue] -> ErrorOr ZValue
--zintersect2 env ss = Impossible [MStr "BIGCAP: ", MExpr (ZSetDisplay ss)]
zintersect2 env [] =
    Impossible [MStr "generalized intersection of {} is not implemented (3)"]
zintersect2 env [s] =
    return s
zintersect2 env (s@(ZIntSet Nothing _):ss) =
    zintersect2 env (ss ++ [s])
zintersect2 env (s@(ZIntSet _ Nothing):ss) =
    zintersect2 env (ss ++ [s])
zintersect2 env (s:ss) =
    -- Phase 2: choose the smallest set, and use it as a generator.
    --     TODO: sort (s:ss) on the estimated size...
    do  fset <- error_context (coerceZFSet env s)
		[MStr " in bigcap {",MExpr s,MStr ",...}"]
	filtered <- sequence (map (inall ss env) (FiniteSets.set2list fset))
	return (ZFSet (FiniteSets.set_from_ordered_list
			 [v | (v,True) <- filtered]))
    where
    inall :: [ZValue] -> Env -> ZValue -> ErrorOr (ZValue,Bool)
    inall sets env v =
	do  mem <- sequence_and (map (zmember env v) sets)
	    return (v,mem)


nothing_or :: ([a] -> b) -> [Maybe a] -> Maybe b
nothing_or f maybes =
    let justs = catMaybes maybes in
    if null(justs) then Nothing else Just (f justs)


-- a convenience function to make code more readable.
implies p q = (not p) || q


-- This forces an evaluated expression into finite form, if possible.
-- For example:  finite cross products, powersets etc are enumerated fully
-- if possible.  If this is not possible, the original expression is returned.
--
-- canonexpr True always makes the result canonical.
-- canonexpr False leaves some things (like sequences) in the same form.
forceexpr :: Env -> ZValue -> ZValue
forceexpr env e
    | isOk canon = fromOk canon
    | otherwise  = e
    where
    canon = canonexpr False env e

canonexpr :: Bool -> Env -> ZValue -> ErrorOr ZValue
canonexpr canon env e
    | isCanonical e = return e
canonexpr canon env (ZFree1 name val) =
    do  cval <- canonexpr canon env val
	return (ZFree1 name cval)
canonexpr canon env (ZTuple vs) =
    do  cvs <- mapM (canonexpr canon env) vs
	return (ZTuple cvs)
canonexpr canon env (ZBinding vs) =
    do  defns <- mapM (canondefn canon env) vs
        return (ZBinding defns)
canonexpr canon env (ZSetDisplay vs) =
    do  cvs <- mapM (canonexpr canon env) vs
	return (FiniteSets.make_zfset cvs)
canonexpr False env v@(ZSeqDisplay vs) =
    do  cvs <- mapM (canonexpr False env) vs
	return (ZSeqDisplay cvs)  -- leave it as a sequence
-- Last resort: we assume it is a set, and try to coerce it.
-- (we could be more sophisticated here and look inside ZCall etc...)
canonexpr canon env v
    | isOk vals = return (ZFSet (fromOk vals))
    | otherwise = error_context (sameError vals)
		  [MStr "in canonexpr: ",MExpr v]
    where vals = coerceZFSet env v


canondefn :: Bool -> Env -> (a,ZValue) -> ErrorOr (a,ZValue)
canondefn canon env (name,val) =
    do  cval <- canonexpr canon env val
	return (name,cval)
