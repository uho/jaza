module Optimize
--
-- $Id: Optimize.hs,v 1.24 2005/03/26 15:20:53 marku Exp $
--
-- This module defines functions for optimizing terms
-- (mostly the ZGenFilt lists in schemas, set expressions and quantifiers)
-- into forms that can be more efficently evaluated.
-- It attempts to evaluate some predicates immediately (at 'compile time')
-- and also applies the one-point rule to quantifiers.
--
-- These optimizers should only be applied to terms that are
-- fully unfolded.  They are all total functions that never
-- produce errors (in the worst case, they leave the term unchanged).
--
-- It is not entirely clear that it is worth making this a separate
-- stage from evaluation:
--
-- Advantages of separate optimization stage:
--
--   * The optimization functions do not produce (evaluation) errors
--     which makes them easier to understand.
--
--   * It is easier to look at the result of optimization, before evaluating.
--
--   * It is closer to the compile/runtime distinction, which
--     should make it easier to generate Haskell (or C) code for
--     each schema evaluation, rather than the interpreter-style
--     of Eval.hs.
--
--   * One-point rule is never needed during evaluation (yet!).
--
--   * Evaluation has the nice property that every expression it
--     returns has no free vars (but this can make expression sizes
--     explode!).  Optimization does not have this property.
--
-- Disadvantages:
--
--   * opt_expr/pred has to scan over the structure of exprs/preds
--     in a very similar way to the eval functions.
--     Similarly, Eval.zand/zor are very similar to Optimize.opt_zand/zor etc.
--
--   * Optimization wants to call eval sometimes (see try_eval below),
--     but evaluator would also benefit from calling optimizer
--     in some cases (e.g., after modifying [ZGenFilt] of a set comprehension).
--     So, mutual recursion would be nice, but is not possible
--     with current Haskell when they are in separate modules.
--
-- An alternative would be to have just evaluate, but with options
-- to make it work harder or not.
-- We would start with one that does no searching, and just returns
-- hard expressions unchanged.  This is almost like the current opt_expr.
-- (But this approach would mean we reevaluate expressions several times,
--  even when they are evaluated as much as possible already.  This is
--  perhaps getting too close to a general rewriting/thm.proving style.).
--
  ( opt_expr,
    opt_pred,
    opt_schema
  )
where

import AST
import Subs
import Reorder
import List
import Unfold
import Eval

-- This does the same as opt_expr, but first it restores
-- the uniquify invariant (no repeated nested vars).
-- You MUST call this instead of opt_expr whenever new bound
-- variables have been added around the expr.  For example, if you change
-- the d in (\mu d @ e) by adding new names, then you must call
-- (uniq_opt_expr env2 e) where env2 is the original env plus
-- the new names in the new d.
--
uniq_opt_expr :: Env -> ZExpr -> ZExpr
uniq_opt_expr env e = opt_expr env (uniquify (avoid_variables env) e)


-- Interfaces to the optimiser
opt_expr :: Env -> ZExpr -> ZExpr
opt_expr env e = optResult (setEnv env >> visitExpr e)

opt_pred :: Env -> ZPred -> ZPred
opt_pred env p = optResult (setEnv env >> visitPred p)

opt_schema :: Env -> [ZGenFilt] -> ZExpr
opt_schema env gfs = optResult (setEnv env >> visitExpr (schema_set gfs))


-- True means the current term is in an existential context.
-- This means that we can flatten nested existential vars.
-- This is put inside the OptVisitor monad, because we want to
-- use it inside the nested levels of exists etc., in the middle
-- of optGfsM, after the recursive calls to optExpr/Pred, 
-- but before reordering of the local ZGenFilt list.
--
-- TODO: perhaps generalise this to Ex/All/Other and think about when
--       it is correct to flatten out universal vars too.
--
type Context = Bool


newtype OptVisitor a =
    OptVisitor{unWrapOptV :: (Env,Context) -> (Env,Context,a)}

instance Monad OptVisitor  where
    return a = OptVisitor (\(e,c) -> (e,c,a))
    fail msg = OptVisitor (\(e,c) -> (e,c,error msg))
    g >>= h =
	OptVisitor (\(e,c) -> (let (e2,c2,res) = unWrapOptV g (e,c) in
			       unWrapOptV (h res) (e2,c2)))

instance Visitor OptVisitor where
    visitPred = optPredM
    visitExpr = optExprM
    -- By default, visitBinder turns off the context-is-existential flag.
    -- Use (optGfsM True) instead when you want to turn it on.
    visitBinder = optGfsM False
    setEnv e  = OptVisitor (\(_,c) -> (e,c,()))
    currEnv   = OptVisitor (\(env,c) -> (env,c,env))


-- a utility procedure for starting and stopping an OptVisitor
optResult :: OptVisitor a -> a
optResult ov = res
    where (_,_,res) = unWrapOptV ov (empty_env [], False)


-- get and set methods for context information within OptVisitor.
getContext :: OptVisitor Context
getContext = OptVisitor (\(e,c) -> (e,c,c))

setContext :: Context -> OptVisitor ()
setContext c = OptVisitor (\(e,_) -> (e,c,()))


-- This optimizes the expression for more efficient evaluation.
optExprM :: ZExpr -> OptVisitor ZExpr
optExprM (ZSetComp gfs Nothing) =
    error ("NOTHING CASE! = " ++ show gfs)
--optExprM (ZSetComp gfs@[Choose _ (ZIntSet _ _),Check (ZExists _ _)] (Just e)) =
--    do  setContext True
--	(gfs2,ZExpr e2,_) <- optGfsM True gfs (ZExpr e)
--	return (error ("gfs="++show gfs++"\n"
--		       ++ "gfs2=" ++ show gfs2 ++ "\n"
--		       ++ "e = " ++ show e ++ "\n"))
optExprM (ZSetComp gfs (Just e)) =
    do  (gfs2,ZExpr e2,_) <- optGfsM True gfs (ZExpr e)
	return (ZSetComp gfs2 (Just e2))
optExprM e =
    traverseExpr e  -- handle all other cases


-- This optimizes the predicate for more efficient evaluation.
optPredM :: ZPred -> OptVisitor ZPred
optPredM (ZAnd p q) =
    do  p2 <- visitPred p
	q2 <- visitPred q
	return (opt_zand p2 q2)
optPredM (ZOr p q) =
    do  p2 <- visitPred p
	q2 <- visitPred q
	return (opt_zor p2 q2)
optPredM (ZImplies p q) =
    do  p2 <- visitPred p
	q2 <- visitPred q
	return (opt_zimp p2 q2)
optPredM (ZIff p q) =
    do  p2 <- visitPred p
	q2 <- visitPred q
	return (opt_ziff p2 q2)
optPredM (ZNot p) =
    do  p2 <- visitPred p
	return (opt_znot p2)
optPredM (ZExists gfs p) =
    do  c <- getContext
	-- call optGfsM c, not visitBinder, so the context is unchanged.
        (gfs2,_,env) <- optGfsM c (gfs ++ cnf c p) ZNull
	let avoid = avoid_variables env
	return (one_point avoid opt_zand ZExists [] gfs2 ztrue)
optPredM (ZExists_1 gfs p) =
    do  (gfs2,_,env) <- visitBinder (gfs ++ cnf False p) ZNull
	let avoid = avoid_variables env
	return (one_point avoid opt_zand ZExists_1 [] gfs2 ztrue)
optPredM (ZForall gfs p) =
    -- Here we apply the theorem: (All d @ p) = (All d | not(p) @ false)
    do  (gfs2,_,env) <- visitBinder (gfs ++ cnf False (ZNot p)) ZNull
	let avoid = avoid_variables env
	return (one_point avoid opt_zimp ZForall [] gfs2 zfalse)
optPredM (ZEqual a b) =
    do  a2 <- visitExpr a
	b2 <- visitExpr b
	return (try_evalp (ZEqual a2 b2))
optPredM (ZMember a (ZSetComp gfs (Just res))) =
    -- Theorem: x \in \{D|P@V\}  <=>  (\exists D|P @ x=V)
    -- TODO: this is one of the conforming semantics that the Z
    -- standard allows, but is it implied by the standard?
    optPredM (ZExists gfs (ZEqual a res))
optPredM (ZMember a b) =
    do  a2 <- visitExpr a
	b2 <- visitExpr b
	return (try_evalp (ZMember a2 b2))
optPredM p =
    traversePred p  -- handle other cases


-- This is the interesting part, where most optimization happens.
--
-- The basic strategy is to find some (Choose v t) which is followed by
-- an equality v=e (or e=v) where e does not depend upon any local
-- variables that have remain in the [ZGenFilt] list.  (In other words,
-- whose values will not have been fixed by the time e is evaluated).
-- We transform this (Choose v t) into (Evaluate v e t).
--
-- TODO: give preference to the v that has the most predicates
--       that can follow it.
optGfsM :: Context -> [ZGenFilt] -> ZTerm -> OptVisitor ([ZGenFilt],ZTerm,Env)
optGfsM newContext gfs zt =
    do  origenv <- currEnv
	origContext <- getContext
	setContext newContext

	-- First we flatten any conjuncts
	-- (and also ZExists, if the Context c is True)
	-- It is sometimes better to do this first, before the types
	-- within the nested exists are optimized (becoming more complex).
	c <- getContext
	let gfs2 = cnfpreds c gfs

	-- Now extend the environment, which is used only for
	-- avoiding names, so it is okay to have too many names in it.
	-- In fact, we want avoid all these names in subterms, so that
	-- we can freely reorder the decls/preds.
	pushBinder gfs2

	-- Now we recurse into all the subterms, optimising them
	gfs3 <- mapM visitGenFilt gfs2

	-- Now flatten again, in case one_point has added conjuncts.
	let gfs4 = cnfpreds c gfs3

	-- Now we try to optimise and reorder this ZGenFilt list.
	let eqs = find_facts (genfilt_names gfs4) free_vars gfs4
	let gfs5 = reorder_gfs gfs4 eqs

	-- Now visit any term inside the binder
	zt2 <- visitTerm zt

	env <- currEnv
	setEnv origenv
	setContext origContext
	return (gfs5,zt2,env)


-- This implements the "one point" rule for any quantifier.
-- Example:  (\exists [x==3:\num; p(x); y:\num] y+x=5)
-- becomes:  3 \in \num \land p(3) \land (\exists [y:\num] y+3=5)
--
one_point :: VarSet
	     -> (ZPred -> ZPred -> ZPred)
	     -> ([ZGenFilt] -> ZPred -> ZPred)
	     -> Substitution -> [ZGenFilt] -> ZPred -> ZPred
one_point env op quant subs [] inner
  = substitute subs env inner
one_point env op quant subs (Evaluate v e t:gfs) inner
  = op (ZMember e2 t2) (one_point env op quant subs2 gfs inner)
  where
  e2 = substitute subs env e
  t2 = substitute subs env t
  subs2 = (v,e2) : subs
one_point env op quant subs (Check p:gfs) inner
  = op p2 (one_point env op quant subs gfs inner)
  where
  p2 = substitute subs env p
one_point env op quant subs gfs inner
  = substitute subs env (quant gfs inner)


-- The following functions basically implement the standard truth tables,
-- so that if part of a predicate happens to be ZTrue or ZFalse,
-- a simplified predicate is returned.
opt_zand t@ZTrue{}   p          = p
opt_zand p           t@ZTrue{}  = p
opt_zand f@ZFalse{}  p          = f
opt_zand p           f@ZFalse{} = f
opt_zand p           q          = ZAnd p q

opt_zor  t@ZTrue{}   p          = t
opt_zor  p           t@ZTrue{}  = t
opt_zor  f@ZFalse{}  p          = p
opt_zor  p           f@ZFalse{} = p
opt_zor  p           q          = ZOr p q

opt_zimp t@ZTrue{}   p          = p
opt_zimp p           t@ZTrue{}  = t
opt_zimp f@ZFalse{}  p          = ZTrue{reason=map ZNot (reason f)}
opt_zimp p           f@ZFalse{} = opt_znot p
opt_zimp p           q          = ZImplies p q

opt_ziff t@ZTrue{}   p          = p
opt_ziff p           t@ZTrue{}  = p
opt_ziff f@ZFalse{}  p          = opt_znot p
opt_ziff p           f@ZFalse{} = opt_znot p
opt_ziff p           q          = ZIff p q

opt_znot t@ZTrue{}      = ZFalse{reason=map ZNot (reason t)}
opt_znot f@ZFalse{}     = ZTrue{reason=map ZNot (reason f)}
opt_znot (ZNot p)       = p
-- De Morgan rules
opt_znot (ZAnd p q)     = opt_zor (opt_znot p) (opt_znot q)
opt_znot (ZOr p q)      = opt_zand (opt_znot p) (opt_znot q)
opt_znot (ZImplies p q) = opt_zand p (opt_znot q)
opt_znot (ZExists gfs p)= ZForall gfs (opt_znot p)
opt_znot (ZForall gfs p)= ZExists gfs (opt_znot p)
opt_znot p              = ZNot p

-- This tries to evaluate a predicate (at compile/optimize time),
-- in case it contains just constants (or is obviously true/false, etc.).
-- This is important, because after initial state values have been
-- substituted into a schema, predicates that have no free vars are common.
try_evalp p
  | answer == Ok True  = ZTrue{reason=[p]}
  | answer == Ok False = ZFalse{reason=[p]}
  | otherwise          = p
  where
  answer = evalpred p dummy_eval_env


cnf :: Context -> ZPred -> [ZGenFilt]
-- Converts the predicate towards conjunctive normal form,
-- by flattening conjunctions etc. However, it avoids duplicating
-- formulae, so generally only goes part of the way to CNF form.
-- If Context is true, then it also flattens nested \exists.
cnf _ ZTrue{}             = []
cnf c (ZExists gfs p) | c = cnfpreds c gfs ++ cnf c p
cnf c (ZAnd p1 p2)        = cnf c p1 ++ cnf c p2
cnf c (ZNot p)            = cnf2 (opt_znot p)
    where
    cnf2 (ZNot p) = [Check (ZNot p)]
    cnf2 p        = cnf c p
cnf _ p                   = [Check p]


-- applies cnf to all predicates in a ZGenFilt list.
cnfpreds :: Context -> [ZGenFilt] -> [ZGenFilt]
cnfpreds c gfs = concatMap cnfpred gfs
    where
    cnfpred (Check p) = cnf c p
    cnfpred gf        = [gf]
