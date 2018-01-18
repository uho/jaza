module SetSize
--
-- $Id: SetSize.hs,v 1.4 2005/03/26 13:07:43 marku Exp $
--
-- This module defines functions for estimating the maximum size of a set.
-- This is useful for heuristic purposes (controlling search space,
-- deciding which generator is best etc.)
--
-- Note that, even if the max size of a set is reported to be small,
-- a large search space may need to be searched to evaluate it,
-- because max_size does not look inside predicates (and a predicate
-- can contain quantifiers which may require a huge/infinite search).
(
    SetSize,
    unknown_size, -- :: SetSize
    max_size,     -- :: Env -> ZExpr -> SetSize
    two_power     -- :: SetSize -> SetSize
)
where

import AST
import Errors
import qualified FiniteSets


-- sizes larger than this are converted to Huge.
huge = 1000000000000000000000000

-- SetSize represents the non-negative integers, bounded by 'huge',
-- and extended with an approximation of 'infinity'.
--
-- We make it an instance of the Num and Ord classes so that
-- arithmetic on set sizes is easy.

instance Num SetSize where
    Huge + _ = Huge
    _ + Huge = Huge
    (Approx a) + (Approx b)
	| a + b < huge = Approx (a+b)
	| otherwise = Huge

    Huge       - _          = Huge
    _          - Huge       = Approx 0
    (Approx a) - (Approx b) = Approx ((a - b) `max` 0)

    Huge       * (Approx 0) = Approx 0
    Huge       * _          = Huge
    (Approx 0) * Huge       = Approx 0
    _          * Huge       = Huge
    (Approx a) * (Approx b)
	| a * b < huge = Approx (a*b)
	| otherwise = Huge

    negate s = s
    abs s = s
    signum (Approx 0) = (Approx 0)
    signum _          = (Approx 1)

    fromInteger i
	| i < 0 = error ("cannot convert " ++ show i ++ " to SetSize")
	| i < huge = Approx i
	| otherwise = Huge


-- two_power b = 2^b
two_power :: SetSize -> SetSize
two_power (Approx b)
  | b < 0     = error ("max_size saw 2**" ++ show b)
  | b > 100   = Huge  -- should be okay for about a hundred years!
  | otherwise = Approx (2^b)
two_power s   = s


unknown_size = Huge   -- means it is too hard to work out.


-- Note: max_size needs only to handle ZExpr terms that might return sets.
--       Eg. 'max_size .. (ZInt 3)' should never be called.
--
max_size :: Env -> ZExpr -> SetSize

max_size env ZUniverse = Huge
max_size env (ZVar v)
    | isOk val  = max_size env (fromOk val)
    | otherwise = unknown_size
    where
    val = envLookupVar v env
max_size env (ZGivenSet _) = unknown_size
max_size env e@ZPowerSet{} =
    max 0 (estimate - (if is_non_empty e then 1 else 0))
    where
    estimate = two_power (max_size env (baseset e))
max_size env (ZGenerator r v)  = zgenerator_size r v
max_size env e@ZFuncSet{}      = unknown_size
max_size env (ZCross es)       = product (map (max_size env) es)
max_size env (ZCall f arg)     = unknown_size
max_size env (ZSetDisplay es)  = Approx (fromIntegral (length es))
max_size env (ZSeqDisplay es)  = Approx (fromIntegral (length es))
max_size env (ZSetComp gfs _)  = max_size_gfs env gfs (Approx 1)
max_size env (ZLambda gfs e)   = unknown_size
max_size env (ZMu gfs _)       = unknown_size
max_size env (ZELet defs e)    = max_size env e
max_size env (ZIf_Then_Else p e1 e2) = max_size env e1 `max` max_size env e2
max_size env (ZSelect e v)    = unknown_size
max_size env (ZReln _)        = Huge
max_size env (ZFunc1 _)       = Huge
max_size env (ZFunc2 _)       = Huge
max_size env (ZStrange _)     = Huge
max_size env (ZFSet s)        = fromIntegral (FiniteSets.card s)
max_size env (ZIntSet Nothing _) = Huge
max_size env (ZIntSet _ Nothing) = Huge
max_size env (ZIntSet (Just lo) (Just hi)) = fromIntegral (hi - lo + 1)
max_size env (ZFreeType name bs) =
    foldl1 (+) (map branchsize bs)
    where
    branchsize (ZBranch0 _) = 1
    branchsize (ZBranch1 _ e) = max_size (envPushLocal name ints env) e
    -- a recursive call to 'name' means an infinite set (= ints)
    ints = ZIntSet Nothing Nothing
max_size env _ = unknown_size

max_size_gfs :: Env -> [ZGenFilt] -> SetSize -> SetSize
max_size_gfs env gfs Huge =
    Huge  -- no point looking further.
max_size_gfs env [] s =
    s
max_size_gfs env (Choose _ t : gfs) s =
    max_size_gfs env gfs (max_size env t * s)
max_size_gfs env (Check _ : gfs) s =
    max_size_gfs env gfs s -- could reduce s slightly here to reflect filter?
max_size_gfs env (Evaluate _ _ _ : gfs) s =
    max_size_gfs env gfs s


-- This returns an estimate of the number of values
-- represented by a ZGenerator term.
zgenerator_size :: ZReln -> ZValue -> SetSize
zgenerator_size ZLessThan _ = Huge
zgenerator_size ZLessThanEq _ = Huge
zgenerator_size ZGreaterThan _ = Huge
zgenerator_size ZGreaterThanEq _ = Huge
zgenerator_size ZSubset s = (zgenerator_size ZSubsetEq s - 1) `max` 0
zgenerator_size ZSubsetEq s =
    let -- limit search space to 100, because 2^100 is large enough!
	tmpenv = set_max_search_space 30 dummy_eval_env in
    two_power (max_size tmpenv s)
zgenerator_size ZPrefix s = max_size dummy_eval_env s + 1
zgenerator_size ZSuffix s = zgenerator_size ZPrefix s
zgenerator_size ZInSeq s  = ssize * ssize + 1     -- N^2 + 1  TODO improve?
    where
    ssize = max_size dummy_eval_env s
zgenerator_size r v = error ("zgenerator_size " ++ show r
			     ++ " not implemented yet.")
