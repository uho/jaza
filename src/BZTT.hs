module BZTT
-- This module translates a Z state machine into BZTT Prolog syntax
-- for use in test-generation tools and animators etc.
--
-- TODO: would this be easier if less was unfolded beforehand?
--       (for example, theorems about pre Op = ...)
--       And would allow us to generate and use definitions.
-- TODO: think about how to output any axiomatic stuff.
(
  bzMachine
)
where

import AST
import Subs
import Optimize
import Eval
import qualified FiniteSets
import Errors
import List
import Char
import CLPSType
import CLPSWrite

type ZMachine = [ZGenFilt]

type BZPMachine = [BZPClause]
type BZPClause  = String
type BZPVarType = (ZVar,String)   -- (var,basetype) pairs

data Operation
    = Operation
      { zopName    :: String,         -- in original Z form
        opName     :: String,         -- in BZP form
	initVars   :: [BZPVarType],
	finalVars  :: [BZPVarType],
	inputVars  :: [BZPVarType],
	outputVars :: [BZPVarType],
	prePreds   :: [CLPSTerm],
	postPreds  :: [CLPSTerm]
	}
       deriving (Eq,Show)


bzMachine :: String -> ZMachine -> Env -> ErrorOr BZPMachine
bzMachine name0 mach env =
    do  name <- clps_const (string_to_zvar name0)
	let (allops,rest) = partition isOp mach
	allops2 <- mapM getOp allops
	misccheck (null rest)
	    ("non-schema fields not allowed in machine, yet: " ++ show rest)
	let (states,allops3) = partition ((=="state") . zopName) allops2
	let (inits,ops)      = partition ((=="init") . zopName) allops3
	misccheck (length states == 1) "no state field in machine"
	misccheck (length inits == 1)  "no init field in machine"
	let state        = head states
	let init         = head inits
	misccheck (null(finalVars init))  "init contains primed vars"
	misccheck (null(inputVars init))  "init contains input vars"
	misccheck (null(outputVars init)) "init contains output vars"
	misccheck (null(postPreds state)) "init contains primed predicates?"
	let stateVars    = initVars state
	let stateInvar   = prePreds state
	misccheck (null(finalVars state))  "state contains primed vars"
	misccheck (null(inputVars state))  "state contains input vars"
	misccheck (null(outputVars state)) "state contains output vars"
	misccheck (not(null stateInvar))   "empty state invariant"
	misccheck (null(postPreds state))  "state contains primed predicates?"
	mapM (checkSig (sort (map fst stateVars))) ops
	let header = [take 60 (repeat '%'),
		      "%  BZP specification, generated from Z " ++
		         name0 ++ " schema.", 
		      take 60 (repeat '%')]
	specClauses      <- genSpec name
	setClauses       <- genSets name rest env
	variableClauses  <- genVars name stateVars
	invariantClauses <- genInvar name stateInvar
	initClauses      <- genInit name (prePreds init)
	opClauses        <- mapM (genOp name) ops
	return (header ++ [""] ++
		specClauses ++ [""] ++
		setClauses ++ [""] ++
		variableClauses ++ [""] ++
		invariantClauses ++ [""] ++
		initClauses ++
		concat opClauses)


checkSig sVars op =
    do  misccheck (sort(map fst (initVars op)) == sVars)
		("op " ++ zopName op ++ " does not have correct unprimed vars")
	misccheck (sort(map fst (finalVars op)) == map prime_zvar sVars)
		("op " ++ zopName op ++ " does not have correct primed vars")


genSpec spec =
    return [bzpSpec spec]

-- This defines all free type enumerations.
-- (so that, elsewhere, we can just output the name of the freetype)
genSets spec rest env =
    do  sets <- mapM declfreetype freetypes
	return (concat sets)
    where
    freetypes = [(n,bs) | (n,ZFreeType _ bs) <- global_values env]
    declfreetype (n,bs) 
	| all isBranch0 bs
	  = genFreeType spec n [b | ZBranch0 b <- bs]
	| otherwise
	  = fail ("free type " ++ show_zvar n ++ " contains non-simple branches")

genFreeType spec name members =
    do  let values = tail (concat ["," ++ safe_zvar b | b <- members])
	return [bzpDecl spec BZPStatic (name,"set(atom)"),
		bzpPred spec BZPProperty (safe_zvar name)
		   (safe_zvar name ++ " = {" ++ values ++ "}")]

genVars spec stateVars =
    -- Pre: all statevars should be undecorated.
    return (map (bzpDecl spec BZPVariable) stateVars)


genInvar spec invarpreds =
    return [bzpPred spec BZPInvariant ("inv"++show i) p
	    | (i,p) <- zip [1..] invarpreds]


genInit spec initpreds =
    return [bzpPred spec BZPInitialisation ("init"++show i) p
	    | (i,p) <- zip [1..] initpreds]


genOp spec op =
    return (["", bzpOp spec (opName op)] ++
	    map (bzpDecl spec (BZPInput (opName op))) (inputVars op) ++
	    map (bzpDecl spec (BZPOutput (opName op))) (outputVars op) ++
	    [bzpPred spec (BZPPre (opName op)) ("pre" ++ show i) p 
	      | (i,p) <- zip [1..] (prePreds op)] ++
	    [bzpPred spec (BZPPost (opName op)) ("post" ++ show i) p 
	      | (i,p) <- zip [1..] (postPreds op)])


isOp :: ZGenFilt -> Bool
-- identifies the operations (including state/init schemas) in a machine
isOp (Choose n (ZSetComp _ (Just (ZBinding b)))) =
    and [ZVar v == v2 | (v,v2) <- b]
isOp _ = False


getOp :: ZGenFilt -> ErrorOr Operation
-- extracts the interesting components of an operation.
getOp (Choose n (ZSetComp gfs (Just (ZBinding b))))
  | null(get_zvar_decor n) =
      do  let allvars = map fst b
          -- WARNING: this assumes that gfs has not been optimised,
          --  (which might add extra variables into gfs, or change
          --   Choose into Evaluate etc.)   allvars would be a safer 
	  -- way of knowing the exported fields of this schema.
	  let allpreds = genfilt_allpreds gfs
	  let tenv = extend_typeenv emptyTypeEnv gfs
	  let getvars p = sequence [bzpVarType tenv v t 
					| Choose v t <- gfs, p v]
	  initialvars<- getvars is_unprimed_zvar
	  finalvars  <- getvars is_primed_zvar
	  inputvars  <- getvars is_input_zvar
	  outputvars <- getvars is_output_zvar
	  --
	  -- Now we split an operation into a Pre/Post pair.
	  -- This is done syntactically at the moment.
	  let prevars = varset_from_zvars(map fst (initialvars ++ inputvars))
	  let isPrePred p = free_vars p `subseteq_varset` prevars
          let (pre,post) = partition isPrePred allpreds
          pres <- mapM (clps_pred tenv) pre
	  posts <- mapM (clps_pred tenv) post
	  return Operation{ zopName = show_zvar n,
	                    opName  = fromOk (clps_const n),
			    initVars   = initialvars,
			    finalVars  = finalvars,
			    inputVars  = inputvars,
			    outputVars = outputvars,
			    prePreds   = pres,
			    postPreds  = posts}
getOp _ = fail "machine operations cannot be decorated"


bzpVarType :: TypeEnv -> ZVar -> ZExpr -> ErrorOr BZPVarType
bzpVarType tenv v t =
    do  let t2 = infer_type tenv t
	-- infer_type gives the type of the type, so we must
	-- remove one set(...) wrapper to get the type of the elements.
	t3 <- element_type v t2 
	ts <- show_clpstype t3
	return (v,ts)

element_type :: ZVar -> CLPSType -> ErrorOr CLPSType
element_type v (Type_Setof t) = return t
element_type v t = fail (show_zvar v ++ " has a strange type: " ++ show t)

commaSep :: [String] -> [String]
-- puts a comma at the end of each line, except the last!
commaSep [] = []
commaSep lines = map (++",") (init lines) ++ [last lines]


indent :: [String] -> [String]
indent = map ("    "++)



---------------------------------------------------------------------
-- Low level construction functions for BZP constructs
---------------------------------------------------------------------
-- types of parameters
type SpecName = String   -- already converted into safe BZP form
type OpName   = String

bzpSpec :: SpecName -> BZPClause
bzpDecl :: SpecName -> BZPDeclKind -> BZPVarType -> BZPClause
bzpPred :: SpecName -> BZPPredKind -> String -> CLPSTerm -> BZPClause
bzpOp   :: SpecName -> OpName -> BZPClause

data BZPDeclKind = BZPParameter
		 | BZPStatic
		 | BZPConstant
		 | BZPVariable
		 | BZPInput OpName
		 | BZPOutput OpName
		 | BZPDefinition
		   deriving Eq


data BZPPredKind = BZPConstraint
		 | BZPProperty
		 | BZPInvariant
		 | BZPPre OpName
		 | BZPPost OpName
		 | BZPInitialisation
		 | BZPAssertion
		   deriving Eq

bzpSpec name = "specification(" ++ name ++ ")."

bzpDecl spec kind (v,t) =
    "declaration(" ++ spec ++ ", " ++
		   show kind ++ ", " ++
		   safe_zvar v ++ ", " ++
		   t ++ ")." 

bzpPred spec kind name p =
    "predicat(" ++ spec ++ ", " ++
    show kind ++ ", " ++
    name ++ ", " ++
    show_clpsterm p ++ ")." 

bzpOp spec op =
    "operation(" ++ spec ++ ", " ++ op ++ ")."


instance Show BZPDeclKind where
    show BZPParameter = "parameter"
    show BZPStatic = "static"
    show BZPConstant = "constant"
    show BZPVariable = "variable"
    show (BZPInput op) = "input("++op++")"
    show (BZPOutput op) = "output("++op++")"
    show BZPDefinition = "definition"


instance Show BZPPredKind where
    show BZPConstraint = "constraint"
    show BZPProperty = "static"
    show BZPInvariant = "invariant"
    show (BZPPre op) = "pre("++op++")"
    show (BZPPost op) = "post("++op++")"
    show BZPInitialisation = "initialisation"
    show BZPAssertion = "assertion"
