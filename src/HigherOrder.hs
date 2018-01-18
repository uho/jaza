module Main
-- Experiments with Higher-Order mappings over terms.
-- This version defines eval by overriding pass.
--
-- Changed to call-by-name.
--    This is NECESSARY to get the fix-point combinator working.
--    Args are now wrapped in thunks before being pushed on the env.
--    (Room for minor optimisation here: the env of each term pushed
--      onto the main env is always the tail of that main env.)
--    Also Lambda terms are returned as thunks.
--
-- Conclusions:
-- ============
-- We define an IO monad that is an EvalMonad.
-- We can have a hierarchy of EvalMonad classes, adding more features
--   (such as environments, extra kinds of actions/results).
-- We can pass arbitrary env-like info through a traversal.
--   Compile-time constant info could be stored in the instance TYPE.
--   Updatable info must be stored in the instance (cf. env).
-- We can accumulate arbitrary results.
-- Environment updates and eval-with-temporary-env are easy to do.
--   (see withEnv and pushVar examples below)
-- Similar to the Visitor pattern in Java, our class must have one
--   'traverse' function for each type of term.  However, we only need
--   one for each BASE type (the subtypes can be matched via patterns)
--   whereas Java needs a separate method for every subtype too
--   (if we want to avoid losing any type information).
--   This makes our code slightly more extensible than the Java visitors.
--
-- TODO:
--  Change the instance type to have named fields.
--  See if [a] can be lifted to EvalMonad?  (But still be overridable)
--  Can we return ErrorOr Term in some instances, but not others?
--  Can we return a completely different type?
--  How much work is it to construct instances?
--    Can we construct instances incrementally (reuse parent code)?
--  Try de Bruijn indices?
--
--  Measure speed slowdown
--  With Hugs98 Feb 2001:  (K reductions/ K cells)
--     N       SimpleEval[]          ev             evc
--     10         4.7     8          15      28
--     20        16.0    27          49      92
--     30        33.5    57         102     192
--     40        58      98         175     329
--     50        89     150         268     502
--     80       221     373         664    1242
--    160       865    1456        2582    4826
--    320      3419    5754       10181   19021    same redns, 16% less cells
--
-- With GHC 5.00.1  (eg. time evsimple 100 +RTS -sstderr)
--     N    SimpleEval[]       ev                evc
--          secs    Kbytes     secs    Kbytes    secs  Kbytes
--     100  0.02      1180     0.08      8213
--     200  0.080     4529     0.30     31997
--     400  0.310    17850     1.36    126333
--     800  1.54     70928      6.6    502096    5.8   305416 (with newtype)
--  1 1600  7.66    282833     34.6   2001963
--  2 1600                     28.76  1725128   26.9  1216142
--  ? 1600  7.9     241827     32.5   1725128   26.9  1216142
--  3 1600                     28.1   1694119
--  4 1600                     28.5   1742828
--  5 1600  7.13    282832
--
-- where 2 = 1 with newtype rather than 'data'
--       3 = 2 but with eval covering all cases (rather than calling pass)
--       4 = 3 + recursive calls call eval directly (not via traverseTerm)
--       5 = 1 with no Add typechecks.

where

import System

main :: IO ()
main = mainevc

mainsimple =
    do  args <- getArgs
	if null args
	   then putStrLn "Args: number-to-sum-up-to"
	   else putStrLn (show (simpleEval [] (App sum0 (Con (read(head args))))))

mainev =
    do  args <- getArgs
	if null args
	   then putStrLn "Args: number-to-sum-up-to"
	   else (ev (App sum0 (Con (read(head args))))) >> return ()

mainevc =
    do  args <- getArgs
	if null args
	   then putStrLn "Args: number-to-sum-up-to"
	   else (evc(App sum0 (Con (read(head args))))) >> return ()


eg1 = traverseTerm (App a1 Incr) :: StateMonad Term
eg1b = traverseTerm (App a1 (Con 3)) :: StateMonad Term
-- these both give errors, because no methods are defined.

eg2 = traverseTerm (App a1 Incr) :: StateMonad2 Term
-- gives: ([],Con 1)
eg2b = traverseTerm (App a1 (Con 3)) :: StateMonad2 Term
-- gives: ([],Con 4)

-- These give the same results as above,
-- but also print trace messages using the IO monad!
eg2p = let StateMonad2p m = traverseTerm (App a1 Incr) in m []
eg2bp = let StateMonad2p m = traverseTerm (App a1 (Con 3)) in m []


-- Evaluate a term
ev :: Term -> IO (Env,Term)
ev t =
    do  let StateMonad2 m = traverseTerm t
	let (env,t2) = m []
	putStrLn (pp t2 ++ "  " ++ ppenv env)
	return (env,t2)

-- Evaluate a term using the continuation-based monad.
evc :: Term -> IO Term
evc t =
    do  let EnvMonad m = traverseTerm t
	let Id t2 = m (\ t env -> Id t) []
	putStrLn (pp t2) -- ++ "  " ++ ppenv env)
	return (t2)

-- Evaluate a term with tracing (same traversal code, but different type)
evt :: Term -> IO (Env,Term)
evt t =
    do  let StateMonad2p m = traverseTerm t
	(env,t) <- m []
	return (env,t)

-- This should return 3  (0+1+2)
s2 = ev (App sum0 (Con 2))

eg3 = traverseTerm (App a1 Incr) :: StateMonad3 Term
eg3b = traverseTerm (App a1 (Con 3)) :: StateMonad3 Term
-- this does something completely different: increments all the constants!


-- Goal: have the same standard code traversing the term tree,
--       and be able to override this for each kind of traversal.
--
-- Impl: The standard code is parameterised by a monad.
--       Each traversal defines a monad for the kinds of state/errors
--       that it needs.
--
--       The overriding is done by carrying around the
--       traversal functions in the monad, and each recursive call
--       calls these functions.



-- This class extends monad to have the standard features
-- we expect while evaluating/manipulating expressions.
class (Monad m) => EvalMonad m where
    incr :: m ()     -- all traversals must support this state updator.
    -- these defines the traversal!
    traverseTerm :: Term -> m Term
    --traversePred :: Pred -> m Pred

-- Here is the default term traversal code.
-- Note that each recursive call looks up the correct method
-- in the current EvalMonad.
pass :: (EvalMonad m) => Term -> m Term
pass (Var x)   = return (Var x)
pass (Con i)   = return (Con i)
pass (Incr)    = incr >> return (Con 0)
pass (Add u v) = do u' <- traverseTerm u
		    v' <- traverseTerm v
		    return (Add u' v')
pass (Lam x b) = do b' <- traverseTerm b
		    return (Lam x b')
-- no default rule for Thunk.
-- Eval creates thunks, so it defines the first rule for them.
pass (App u v) = do u' <- traverseTerm u
		    v' <- traverseTerm v
		    return (App u' v')
pass (IfZero c a b) = do c' <- traverseTerm c
			 a' <- traverseTerm a
			 b' <- traverseTerm b
			 return (IfZero c a b)



-----------------------------------------------------------------
-- Example monads
-----------------------------------------------------------------
-- Here is a monad that does not define a method suite.
-- So this gives an error when it is used with eval/pass.
data StateMonad a = StateMonad (Int -> (Int,a))

instance (Show a) => Show (StateMonad a) where
    show (StateMonad f) = show (f 0)

instance Monad StateMonad  where
    return a = StateMonad (\s -> (s,a))
    fail msg = StateMonad (\s -> (s,error msg))
    (StateMonad f) >>= g = StateMonad (\a -> (let (s,a1) = f a in
					      (let StateMonad g' = g a1 in
					       g' s)))

instance EvalMonad StateMonad where
    incr = StateMonad (\s -> (s+1,()))



-- Here is a monad that evaluates the term.
----------------------------------------------------
class (EvalMonad m) => EvalEnvMonad m where
    lookupVar :: String -> m Term
    pushVar   :: String -> Term -> m a -> m a
    currEnv   :: m Env         -- returns the current environment
    withEnv   :: Env -> m a -> m a  -- uses the given environment
    pushVar v t m = do env <- currEnv; withEnv ((v,t):env) m


newtype StateMonad2 a = StateMonad2{unWrap2 :: Env -> (Env,a)}

instance (Show a) => Show (StateMonad2 a) where
    show m = show (unWrap2 m [])

instance Monad StateMonad2  where
    return a = StateMonad2 (\s -> (s,a))
    fail msg = StateMonad2 (\s -> (s,error msg))
    g >>= h =
	StateMonad2 (\a -> (let (s,a1) = unWrap2 g a in
			    unWrap2 (h a1) s))

instance EvalMonad StateMonad2 where
    incr = StateMonad2 (\s -> (s,()))
    traverseTerm = eval

instance EvalEnvMonad StateMonad2 where
    lookupVar v =
	StateMonad2 (\env -> (env, lookup2 env))
	where
	lookup2 env = maybe (error ("undefined var: " ++ v)) id (lookup v env)
    currEnv =
	StateMonad2 (\env -> (env,env))
    withEnv tmp m =
	StateMonad2 (\env -> let (_,t) = unWrap2 m tmp in (env,t))


-- This code overrides most clauses of pass, to do evaluation.
eval :: (EvalEnvMonad m) => Term -> m Term
eval (Var x)   =
    do e <- currEnv
       t <- lookupVar x
       traverseTerm t
eval (Add u v) =
    do {Con u' <- traverseTerm u;
	Con v' <- traverseTerm v;
	return (Con (u'+v'))}
eval (Thunk t e) =
    withEnv e (traverseTerm t)
eval f@(Lam x b) =
    do  env <- currEnv
	return (Thunk f env)  -- return a closure!
eval (App u v) =
    do {u' <- traverseTerm u;
	-- call-by-name, so we do not evaluate the argument v
	apply u' v
       }
eval (IfZero c a b) =
    do {val <- traverseTerm c;
	if val == Con 0
	   then traverseTerm a
	   else traverseTerm b}
-- Experiment: inline pass here to see if overriding takes time.
--eval (Con i)   = return (Con i)
--eval (Incr)    = incr >> return (Con 0)
eval t = pass t   -- call the parent method explicitly!

--apply :: Term -> Term -> StateMonad2 Term
apply (Thunk (Lam x b) e) a =
    do  orig <- currEnv
	withEnv e (pushVar x (Thunk a orig) (traverseTerm b))
apply a b         = fail ("bad application: " ++ pp a ++
			      "  [ " ++ pp b ++ " ].")


-- A variation of the above monad that uses continuation style (faster?).
-- This suggestion from Ralf Hinze, 20 Oct 2001.
----------------------------------------------------
type CPS a answer =  (a -> answer) -> answer

newtype EnvMonad m a =
    EnvMonad{ unWrap2c :: (forall ans . CPS a (Env -> m ans)) }

instance (Monad m) => Monad (EnvMonad m) where
    return a = EnvMonad(\ cont -> cont a)
    m >>= k  = EnvMonad(\ cont -> unWrap2c m (\ a -> unWrap2c (k a) cont))
    fail s   = lift (fail s)

lift :: (Monad m) => m a -> EnvMonad m a
lift m = EnvMonad (\ cont inp -> m >>= \ a -> cont a inp)

run :: (Monad m) => EnvMonad m a -> (Env -> m a)
run parser inp = unWrap2c parser (\ a rest -> return a) inp


instance EvalMonad Id where
    incr = return ()
    traverseTerm t = Id t

instance (EvalMonad m) => EvalMonad (EnvMonad m) where
    incr = return ()
    traverseTerm = eval

instance (EvalMonad m) => EvalEnvMonad (EnvMonad m) where
    lookupVar v =
	EnvMonad (\ cont env -> cont (lookup2 env) env)
	where
	lookup2 env = maybe (error ("undefined var: " ++ v)) id (lookup v env)
    currEnv =
	EnvMonad (\ cont env -> cont env env)
    withEnv tmpenv m =
	EnvMonad (\ cont env -> unWrap2c m (\ a _ -> cont a env) tmpenv)


-- Here is an extension of the above monad that prints trace messages
---------------------------------------------------------------------
data StateMonad2p a = StateMonad2p (Env -> IO (Env,a))

--instance (Show a) => Show (StateMonad2p a) where
--    show (StateMonad2p f) = show (f [])

instance Monad StateMonad2p  where
    return a = StateMonad2p (\s -> return (s,a))
    fail msg = StateMonad2p (\s -> do {putStrLn ("Error: "++msg);
				       return (s,error "failed")})
    (StateMonad2p g) >>= h =
	StateMonad2p (\a ->
		      do (s,a1) <- g a
			 let StateMonad2p h' = h a1
			 h' s)

instance Functor StateMonad2p  where
    fmap f (StateMonad2p m) = StateMonad2p (\e -> do {(e2,r2) <- m e;
						     return (e2,f r2)})

instance EvalMonad StateMonad2p where
    incr = StateMonad2p (\s -> do {putStrLn "INCR!"; return(s,())})
    traverseTerm t = StateMonad2p (\env -> do{ putStrLn (traceMsg t env);
					       let {(StateMonad2p m) = eval t};
					       m env } )
--    traverseTerm t =
--	StateMonad2p (\env -> do{ putStrLn (traceMsg t env);
--				  let {StateMonad2p m = termMethod methods t};
--				  m env})
	    where
	    traceMsg t env = " >> " ++ pp t ++ "     "-- ++ take 50 (ppenv env)



instance EvalEnvMonad StateMonad2p where
    lookupVar v =
	StateMonad2p (\env -> check (lookup v env) v env)
	where
	check (Just t) v env = return (env,t)
	check Nothing  v env = do  putStrLn ("Error: undefined var: " ++ v
					     ++ ".   Env: " ++ show env)
				   return (env,(Con 0))
    currEnv =
	StateMonad2p (\env -> return (env,env))
    withEnv tmp (StateMonad2p m) =
	StateMonad2p (\env -> do {(_,t) <- m tmp; return (env,t)})



-- Here is a monad that increments all the constants
----------------------------------------------------
data StateMonad3 a = StateMonad3 (Int -> (Int,a))

instance (Show a) => Show (StateMonad3 a) where
    show (StateMonad3 f) = show (f 0)

instance Monad StateMonad3  where
    return a = StateMonad3 (\s -> (s,a))
    fail msg = StateMonad3 (\s -> (s,error msg))
    (StateMonad3 g) >>= h =
	StateMonad3 (\a -> (let (s,a1) = g a in
			    (let StateMonad3 h' = h a1 in
			     h' s)))

instance EvalMonad StateMonad3 where
    incr = StateMonad3 (\s -> (s+1,()))
    traverseTerm = incrCon

incrCon :: EvalMonad m => Term -> m Term
incrCon (Con i) = return (Con (i+1))
incrCon t       = pass t


----------------------------------------------------------------------
-- A directly recursive Eval, with explicit environment
----------------------------------------------------------------------
-- A trivial monad so that we can use monad syntax.
newtype Id a = Id a

instance Monad Id where
    return t = Id t
    fail = error
    (Id t) >>= f = f t

instance Show a => Show (Id a) where
    show (Id t) = show t

simpleEval :: Env -> Term -> Id Term
simpleEval env (Var v) =
    simpleEval env (maybe (error ("undefined var: " ++ v)) id (lookup v env))
simpleEval env e@(Con _) =
    return e
simpleEval env e@Incr =
    return (Con 0)
simpleEval env (Add u v) =
    do {Con u' <- simpleEval env u;
	Con v' <- simpleEval env v;
	return (Con (u' + v'))}
    where
    addCons (Con a) (Con b) = return (Con (a+b))
    addCons (Con _) b = fail ("type error in second arg of Add: " ++ pp b)
    addCons a (Con _) = fail ("type error in first arg of Add: " ++ pp a)
simpleEval env f@(Lam x b) =
    return (Thunk f env)  -- return a closure!
simpleEval env (App u v) =
    do {u' <- simpleEval env u;
	-- call-by-name, so we do not evaluate the argument v
	simpleApply env u' v
       }
simpleEval env (IfZero c a b) =
    do {val <- simpleEval env c;
	if val == Con 0
	   then simpleEval env a
	   else simpleEval env b}
simpleEval env (Thunk t e) =
    simpleEval e t

simpleApply :: Env -> Term -> Term -> Id Term
simpleApply env (Thunk (Lam x b) e) a =
    simpleEval env2 b
    where
    env2 = (x, Thunk a env) : e
simpleApply env a b         = fail ("bad application: " ++ pp a ++
			      "  [ " ++ pp b ++ " ].")
------------------------------------------------------------
-- Data structures
------------------------------------------------------------
--instance Show (a -> b) where
--    show f = "<function>"


data Term
    = Var String
    | Con Int
    | Incr
    | Add Term Term
    | Lam String Term
    | App Term Term
    | IfZero Term Term Term
    -- the following terms are used internally
    | Thunk Term Env  -- a closure
    deriving (Eq,Read,Show)

type Env = [(String,Term)]

ppenv env = "[" ++ concatMap (\(v,t) -> v ++ "=" ++ pp t ++ ", ") env ++ "]"


pp :: Term -> String
pp = ppn 0

-- Precedences:
--   0 = Lam and If (contents never bracketed)
--   1 = Add
--   2 = App
--   3 = atomic and bracketed things
ppn :: Int -> Term -> String
ppn _ (Var v) = v
ppn _ (Con i) = show i
ppn _ (Incr)  = "INCR"
ppn n (Lam v t) = bracket n 0 ("@" ++ v ++ ". " ++ ppn (-1) t)
ppn n (Add a b) = bracket n 1 (ppn 1 a ++ " + " ++ ppn 1 b)
ppn n (App a b) = bracket n 2 (ppn 2 a ++ " " ++ ppn 2 b)
ppn n (IfZero c a b) = bracket n 0
    ("IF " ++ ppn 0 c ++ " THEN " ++ ppn 0 a ++ " ELSE " ++ ppn 0 b)
ppn n (Thunk t e) = bracket n 0 (ppn 3 t ++ "::" ++ ppenv e)

bracket outer this t | this <= outer = "(" ++ t ++ ")"
		     | otherwise     = t
------------------------------------------------------------
-- Test Data
------------------------------------------------------------
x  = (Var "x")
y  = (Var "y")
a1 = (Lam "x" (Add (Var "x") (Con 1)))
aa = (Lam "x" (Add (Var "x") (Var "x")))

-- These should all return 1
iftrue = (IfZero (Con 0) (Con 1) (Con 2))
iffalse = (IfZero (Con 1) (Con 2) (Con 1))

sum0 :: Term
sum0 = (App fix partialSum0)
partialSum0 = (Lam "sum"
		  (Lam "n"
		   (IfZero (Var "n")
		    (Con 0)
		    (Add (Var "n") (App (Var "sum") nMinus1)))))
nMinus1 = (Add (Var "n") (Con (-1)))

lfxx :: Term
lfxx = (Lam "x" (App (Var "F") (App (Var "x") (Var "x"))))

-- This is the fix point combinator:  Y
fix :: Term
fix = (Lam "F" (App lfxx lfxx))
