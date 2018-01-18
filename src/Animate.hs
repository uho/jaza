module Animate
-- This module defines the Animator data structure, and
-- various operations on it.  Text and Graphical User Interfaces
-- should be built on top of this module.
( Animator,
  animator0,        -- initial animator state
  settings, get_setting, set_setting,  -- for customizing animator
  Answer(..),       -- most Animator results are returned using this
  errstr,           -- convenience function for creating a string ErrorMsg.
  isUndefMsg,       -- recognises the 'undefined result' message
  isDone,           -- tests an animator result to see if it succeeded
  pushpara, pushfile, poppara, resetanimator, -- extending/deleting the spec.
  evalexpression, evalpredicate, showpredicate,
  writebztt,        -- writes a state machine to a file in BZTT syntax.
  execschema,       -- does one operation, from scratch.
  compose_schema,   -- does one operation, starting from current state
  currstate, showstate, popstate, -- manipulate the current output state
  showspec,         -- shows summary of whole spec
  showunfolded,     -- shows one definition (in unfolded form)
  showcode,         -- shows schema that is/has just executed
  SyntaxError       -- from Errors module
)
where

import AST
import Parse
import Unfold
import Optimize
import Eval
import BZTT
import Errors
import Char

-- This data structure contains all the internal state of the animator.
-- We use named fields so that it can easily be extended with new fields.
data Animator
  = Anim {spec::[ZParaInfo],  -- a stack of definitions, most recent at head
	  ops::[OpResult],    -- most recent result at the front.
          lasteval::EvalInfo, -- info about most recent eval/evalp/do/;
	  undo_depth::Int,    -- maximum length of 'ops'.  Must be > 0.
	  setsize::Integer,   -- maximum set size for data.
	  searchsize::Integer -- maximum search space size.
	 }

-- Information about the most recent expr/pred/schema evaluation.
data EvalInfo
  = NoEval
  | PredEval ZPred   -- the optimised predicate code
  | ExprEval ZExpr   -- the optimised expression code
  | SchemaEval Int   -- the number of clauses that succeeded.
  deriving (Show,Eq)


-- This is the list of setting keywords that is currently supported.
settings = ["undo","setsize","searchsize"]

get_setting :: String -> Animator -> Integer
get_setting "undo" anim = fromIntegral (undo_depth anim)
get_setting "setsize" anim = setsize anim
get_setting "searchsize" anim = searchsize anim

set_setting :: String -> Integer -> Animator -> (Animator,Answer)
-- Pre: 0 <= val
set_setting "undo" val anim
    | 0 <= val && val <= 1000 =
	(anim{undo_depth = fromInteger val}, Done "")
    | otherwise =
	(anim, errstr "undo depth is limited to 0..1000")
set_setting "setsize" val anim = (anim{setsize=val}, Done "")
set_setting "searchsize" val anim = (anim{searchsize=val}, Done "")

evalenv :: Animator -> Env
evalenv anim =
    -- TODO: cache these environments within anim?
    ( set_max_search_space (searchsize anim)
    . set_max_set_size (setsize anim)
    . uenv
    . spec
    )
    anim


currstate :: Animator -> Int
currstate Anim{ops=[]} = -1
currstate Anim{ops=os} = statenumber (head os)

setcurrstate :: Int -> Animator -> Animator
-- Pre: this should only be called when ops is non-empty.
setcurrstate i anim@Anim{ops=(o:os)} = anim{ops=(o{statenumber=i} : os)}

statelist :: Animator -> [ErrorOr ZValue]
-- Pre: this should only be called when ops is non-empty.
statelist anim = states (head (ops anim))


push_op :: String -> ZExpr -> [ErrorOr ZValue] -> Animator -> Animator
-- an internal function that pushes a schema evaluation onto the
-- stack of statelists.  Since the stack has a maximum undo depth, this
-- may discard an earlier undo step.
push_op name code ss anim
  = anim{ops = take (undo_depth anim + 1) (newstate:ops anim)}
  where
  newstate = OpResult{opname=name,opcode=code,states=ss,statenumber= -1}


-- This data structure stores information about the results of
-- a schema operation.
data OpResult
  = OpResult
	{ opname::String, -- the name of the schema being evaluated
	  opcode::ZExpr,  -- the schema that is being/has been evaluated
			  -- (this will always be a ZSetComp expression)
	  states::[ErrorOr ZValue], -- results of current schema evaluation
	  statenumber::Int -- the number of the currently selected state
			   -- (-1 if no state selected)
	 }

data ZParaInfo
  = ZParaDefn{origpara::ZPara, defname::ZVar, defunfolded::ZExpr}
  | ZParaPred{origpara::ZPara, predunfolded::ZPred}
  | ZParaMachine{origpara::ZPara,
		 defname::ZVar
		  -- umachState::[ZGenFilt],
		  -- umachInit ::[ZGenFilt],
		  -- umachOps  ::[(String,[ZGenFilt])]
		 }


uenv :: [ZParaInfo] -> Env
uenv ps =
    empty_env (defs ++ branches)
    where
    x = string_to_zvar "x"
    defs = [(defname p, defunfolded p) | p@(ZParaDefn{}) <- ps]
    branches = concat [map mkbranch bs |
		       ZParaDefn{defunfolded=ZFreeType n bs} <- ps]
    mkbranch (ZBranch0 s) =
	(s, ZFree0 s)
    mkbranch (ZBranch1 s dom) =
	-- a function, expressed as a set comprehension
	(s, ZSetComp [Choose x dom] (Just (ZTuple[ZVar x, ZFree1 s (ZVar x)])))


animator0
  = Anim{spec=[],
	 ops=[],
	 lasteval=NoEval,
	 undo_depth=1,  -- one level of undo.
	 setsize=1000,
	 searchsize=100000
	}


-- Most animator functions return one of these responses.
-- In fact, functions whose names start with 'show...' only return this.

data Answer
  = Done String
  | ErrorMsg ErrorMsg
  | ErrorLocns [SyntaxError]   -- (Line, Column, String) triples
  | Value ZValue
  | Pred ZPred
  | BoolValue Bool
  | Defn ZPara
  | SchemaCode String ZExpr Int   -- optimized code of a schema

errstr s = ErrorMsg [MStr s]

undefmsg = MStr "Result is Undefined.  Reason: "
isUndefMsg (m:_) = m == undefmsg
isUndefMsg _     = False

isDone :: Answer -> Bool
isDone (Done _) = True
isDone _        = False


pushpara :: String -> Animator -> (Animator,Answer)
pushpara s anim
  | isOk result = (anim{spec=spec2}, Done msg)
  | otherwise   = (anim, answerErrorOr result)
  where
  result = do para <- parseZpara s
	      spec2 <- process_paras (spec anim) para
	      return (spec2, length para)
  (spec2, ndefs) = fromOk result
  msg  = "Added " ++ show(ndefs) ++ " definition" ++
	 (if ndefs > 1 then "s." else ".")

-- This is like pushpara, but processes an entire file.
-- If there are no errors, it pushes the entire file onto the current spec.
-- If there are errors anywhere in the file, none of the definitions in
-- the file are added.  That is, a load that gives errors does nothing.
-- TODO: incorporate filename into the syntax error messages.
pushfile :: String -> String -> Animator -> (Animator,Answer)
pushfile filename contents anim
  | isOk result = (anim{spec=spec2}, Done msg)
  | otherwise   = (anim, answerErrorOr result)
  where
  result = do para <- parseZspec contents
	      spec2 <- process_paras (spec anim) para
	      return (spec2, length para)
  (spec2, ndefs) = fromOk result
  msg  = "Added " ++ show(ndefs) ++ " definition" ++
	 (if ndefs > 1 then "s." else ".")


poppara :: Animator -> (Animator,Answer)
poppara anim
  | null (spec anim) = (anim, errstr "Specification is empty")
  | otherwise        = (newanim, Done msg)
  where
  msg = "Popped: " ++ fmtpara (head (spec anim))
  newanim = anim{spec=tail (spec anim)}


resetanimator :: Animator -> (Animator,Answer)
resetanimator anim
  = (animator0, Done "Specification is now empty.")


-- Evaluates a given Z expression.
-- This does not currently update the animator state,
-- but may do in the future.
evalexpression :: String -> Animator -> (Animator,Answer)
evalexpression s anim
  | isOk value
    = (anim{lasteval=ExprEval(fromOk oexpr)}, Value(fromOk value))
  | isOk oexpr && not(isOk value)
    = (anim{lasteval=ExprEval(fromOk oexpr)}, answerErrorOr value)
  | otherwise
    = (anim, answerErrorOr value)
  where
  env = evalenv anim
  oexpr = 
    do  expr <- parseZexpr s
	uexpr <- unfoldexpr env expr
	return (opt_expr env uexpr)
  value =
    do  e <- oexpr
	val <- evalexpr e env
	return (forceexpr env val)


-- Evaluates a given Z predicate.
-- This does not currently update the animator state,
-- but may do in the future.
evalpredicate :: String -> Animator -> (Animator,Answer)
evalpredicate s anim
  | isOk value
    = (anim{lasteval=PredEval(fromOk opred)}, BoolValue(fromOk value))
  | isOk opred && not(isOk value)
    = (anim{lasteval=PredEval(fromOk opred)}, answerErrorOr value)
  | otherwise
    = (anim, answerErrorOr value)
  where
  env = evalenv anim
  opred =
    do  pred <- parseZpred s
	upred <- unfoldpred env pred
	return (opt_pred env upred)
  value =
    do  p <- opred
	evalpred p env


-- This is the same as evalpredicate, but it displays the actual
-- (optimized) predicate, rather than evaluating it.
showpredicate :: String -> Animator -> (Animator,Answer)
showpredicate s anim
  | isOk result  = (anim, Pred (fromOk result))
  | otherwise    = (anim, answerErrorOr result)
  where
  result = do pred <- parseZpred s
	      let env = evalenv anim
	      upred <- unfoldpred env pred
	      return (opt_pred env upred)


-- Write a given state machine out to a file in BZTT syntax.
writebztt :: [String] -> Animator -> IO (Animator,Answer)
writebztt [machname,file] anim
  | isOk machine =
      do  writeFile file (unlines (fromOk machine))
	  return (anim, Done ("Written to file " ++ file ))
  | otherwise =
      return (anim, answerErrorOr machine)
  where
  machine =
      do let sexpr = ZSRef (ZSPlain machname) [] []
	 let env = evalenv anim
	 usexpr <- unfoldsexpr env sexpr
	 bzMachine machname usexpr env
writebztt _ anim = return (anim,ErrorMsg [MStr "illegal args"])


-- Executes a given schema or schema expression.
-- The result list is stored in the Animator state, so that future
-- calls can step through the results one by one.
execschema :: String -> Animator -> (Animator,Answer)
execschema s anim
  | isOk result = (newanim, Done msg)
  | otherwise   = (anim, answerErrorOr result)
  where
  result = do sexpr <- parseZsexpr s
	      let env = evalenv anim
	      usexpr <- unfoldsexpr env sexpr
	      let opts = opt_schema env usexpr
	      return (opts, evalsetcomplazy opts env)
  (op,(maxDepth,states)) = fromOk result
  newanim = push_op s op states anim{lasteval=SchemaEval maxDepth}
  msg = "Do 'next' to see first answer"


-- Executes a given schema or schema expression, using the
-- current output state as the input for the operation.
-- Any missing inputs (or initial state variables) are read via
-- the IO command that is passed into this function.
-- The result list is stored in the Animator state, so that future
-- calls can step through the results one by one.
compose_schema :: (String -> IO String) -> String -> Animator
	       -> IO (Animator,Answer)
compose_schema reader sname anim
  | currstate anim < 0 || null(s0) || notOk(head s0)
    = return (anim, errstr "No current state")
  | notOk ugfs1
    = return (anim, answerErrorOr ugfs1)
  | notOk ugfs2
    = return (anim, answerErrorOr ugfs2)
  | otherwise
    = do errvals <- sequence (map (get . show_zvar) needed)
	 let vals = sequence errvals
	 if notOk vals
	    then return (anim, answerErrorOr vals)
	    else let inputs2 = [ZAssign n v|(n,v)<-zip needed (fromOk vals)]
		 in return (stage2 env sname (fromOk ugfs2) inputs2 anim)
  where
  s0 = drop (currstate anim) (statelist anim)
  ZBinding bs = fromOk (head s0)
  env = evalenv anim
  ugfs1 = do sexpr <- parseZsexpr sname
	     unfoldsexpr env sexpr
  names1 = genfilt_names (fromOk ugfs1)
  -- Partition the current state variables into those that will
  -- be used as inputs to the next operation, and the others.
  -- (the other are added to the schema as outputs, so that the
  -- schema manipulation checks their types etc.)
  inputs = [ZAssign n val
	   | (n',val) <- bs,
	     is_primed_zvar n',
	     let n = unprime_zvar n',
	     n `elem` names1 ]
  others = concat [[Choose n' ZUniverse, Check(ZEqual (ZVar n') val)]
		     | (n',val) <- bs,
		       is_primed_zvar n',
		       let n = unprime_zvar n',
		       not(n `elem` names1) ]
  ugfs2 = schema_rename env (fromOk ugfs1 ++ others) inputs
  -- These are the names of the remaining unknown inputs.
  needed = [v | Choose v _ <- fromOk ugfs2,
	        (is_unprimed_zvar v || is_input_zvar v)]
  -- Here is an interactive reader for those input values.
  get :: String -> IO (ErrorOr ZExpr)
  get var = do  str <- reader var
		let str2 = dropWhile isSpace str
		if null(str2)
		   then return (IllFormed [MStr "no input value provided"])
		   else return (do { e0 <- parseZexpr str2;
				     e1 <- unfoldexpr env e0;
				     return (opt_expr env e1) })

stage2 :: Env -> String -> [ZGenFilt] -> [ZReplace] -> Animator
	  -> (Animator,Answer)
stage2 env name ugfs assign anim
  | notOk ugfs2  = (anim, answerErrorOr ugfs2)
  | otherwise    = (newanim, Done "Do 'next' to see first answer")
  where
  ugfs2 = schema_rename env ugfs assign
  opt = opt_schema env (fromOk ugfs2)
  (maxDepth,states) = evalsetcomplazy opt env
  newanim = push_op name opt states anim{lasteval=SchemaEval maxDepth}


showstate :: Int -> Animator -> (Animator, Answer)
showstate n anim
  | null(ops anim) = (anim, errstr "No current operation")
  | null(statelist anim)
		   = (setcurrstate 0 anim, errstr "No solutions")
  | n < 0          = (setcurrstate 0 anim, errstr "No earlier solutions")
  | cs == []       = (setcurrstate last anim, errstr "No more solutions")
  | notOk(head cs) = (setcurrstate n anim, answerErrorOr (head cs))
  | otherwise      = (setcurrstate n anim, Value (fromOk (head cs)))
  where
  -- We are careful here to only calculate length of statelist when
  -- we know that the whole list has been evaluated already (cs==[]).
  cs = drop n (statelist anim)
  last = length (statelist anim) - 1


popstate :: Animator -> (Animator, Answer)
popstate anim@Anim{ops=(o:os)}
  = (anim{ops=os,lasteval=evalinfo os},
      Done ("undone operation: " ++ opname o))
  where
  -- the previous evaluation was successful, so depth is the maximum
  evalinfo [] = NoEval
  evalinfo (OpResult{opcode=ZSetComp gfs _}:_) = SchemaEval (length gfs)
popstate anim
  = (anim, errstr "no operations to undo")


showspec :: Animator -> Answer
showspec = Done . unlines . map fmtpara . reverse . spec


showunfolded :: String -> Animator -> Answer
showunfolded s anim
  | isOk result = Value (defunfolded (fromOk result))
  | otherwise   = answerErrorOr result
  where
  result = do zvar <- parseZident s
	      def <- get_info zvar anim
	      return def


-- Display the optimized code of the most recent execution
showcode :: Animator -> Answer
showcode Anim{lasteval=NoEval}
  = errstr "no recent evaluation"
showcode anim@Anim{lasteval=SchemaEval depth}
  = SchemaCode name code depth
  where
  name = opname (head (ops anim))
  code = opcode (head (ops anim))
showcode Anim{lasteval=PredEval optpred}
  = Pred optpred
showcode Anim{lasteval=ExprEval optexpr}
  = Value optexpr

----------------------------------------------------------------------
-- The remaining functions are usually private to this module
----------------------------------------------------------------------
answerErrorOr :: ErrorOr t -> Answer
answerErrorOr (SyntaxErrors errs)
  = ErrorLocns errs
answerErrorOr (Undefined msg)
  = ErrorMsg (undefmsg : msg)
answerErrorOr (TooBig info msg)
  = ErrorMsg (MStr ("Problem: " ++ show info) : MNewLine : msg)
answerErrorOr (Impossible msg)
  = ErrorMsg (MStr "Problem: " : msg)
answerErrorOr (IllFormed msg)
  = ErrorMsg (MStr "Specification Error: " : msg)



-- This is for showing a summary of a Z paragraph
fmtpara :: ZParaInfo -> String
fmtpara p
  = s ++ if null rest then "" else "..."
  where
  (s,rest) = splitAt 65 (show (origpara p))

get_info :: ZVar -> Animator -> ErrorOr ZParaInfo
get_info s anim
  | null matches   = IllFormed [MStr ("no such definition: " ++ show_zvar s)]
  | otherwise      = Ok (head matches)
  where
  matches = [p | p@ZParaDefn{defname=n} <- spec anim, n==s]


-- process_paras spec newp.
--
--  This pushes new paragraphs (newp) onto the existing specification (spec).
--
process_paras :: [ZParaInfo] -> [ZPara] -> ErrorOr [ZParaInfo]
process_paras spec []
  = return spec
process_paras spec (p@(ZGivenSetDecl s) : ps)
  = do	let newp = ZParaDefn{origpara=p,
			     defname=s,
			     defunfolded=ZGivenSet s}
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (p@(ZSchemaDef name se) : ps)
  = do  gfs <- unfoldsexpr (uenv spec) se
	let newp = ZParaDefn{origpara=p,
			     defname=make_schema_name name,
			     defunfolded=(ZESchema (ZSchema gfs))}
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (p@ZMachineDef{} : ps)
  = do  let e = uenv spec
	state <- unfoldsexpr e . sref . machState $ p
	init <- unfoldsexpr e . sref . machInit $ p
	ops <- mapM (unfoldsexpr e . sref) (machOps p)
	-- TODO: check typing conditions of machine
	let newp = ZParaMachine{origpara=p,
				defname=string_to_zvar (machName p)}
	let newspec = newp:spec
	process_paras newspec ps
	where
	sref name = ZSRef (ZSPlain name) [] []
process_paras spec (p@(ZAbbreviation n e) : ps)
  = do  ue <- unfoldexpr (uenv spec) e
	let newp = ZParaDefn{origpara=p,
			     defname=n,
			     defunfolded=ue}
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (p@(ZFreeTypeDef n bs) : ps)
  = do  ue <- unfoldexpr (uenv spec) (ZFreeType n bs)
	let newp = ZParaDefn{origpara=p,
			     defname=n,
			     defunfolded=ue}
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (p@(ZPredicate pred) : ps)
  = do  upred <- unfoldpred (uenv spec) pred
	let newp = ZParaPred{origpara=p,
			     predunfolded=upred}
	process_paras (newp:spec) ps
process_paras spec (para : ps)
  = fail ("Not implemented yet: " ++ show para)


adddefn :: ZParaInfo -> [ZParaInfo] -> ErrorOr [ZParaInfo]
adddefn def spec
    | defname def `elem` [n | ZParaDefn{defname=n} <- spec]
      = fail ("redeclaration of: " ++ show_zvar(defname def))
    | otherwise
      = return (def:spec)
