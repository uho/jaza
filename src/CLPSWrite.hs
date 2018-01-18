module CLPSWrite
-- This module converts unfolded Jaza terms into CLPS-BZ format.
(
  TypeEnv,
  preds2TypeEnv,
  emptyTypeEnv,
  clps_expr,
  clps_pred,
  clps_var,
  clps_const,
  safe_zvar,  -- a lower-level function that gives a safe Prolog atom
  CLPSTerm,
  show_clpsterm,
  put_clpsterm,
  genfilt_allpreds   -- converts [ZGenFilt] to a list of ZPreds.
)
where

import AST
import Errors
import List
import Eval
import CLPSType
import Char

emptyTypeEnv :: TypeEnv
emptyTypeEnv = []

-- This infers some type information from a pred.
preds2TypeEnv :: TypeEnv -> [ZPred] -> TypeEnv
preds2TypeEnv env []     = env
preds2TypeEnv env (p:ps) = preds2TypeEnv (extendEnv env p) ps
    where
    extendEnv env (ZMember (ZVar v) set) = extend_typeenv env [Choose v set]
    extendEnv env p = env


-- Currently CLPS terms are stored as strings, but this representation
-- should not be relied on outside this module, since it is likely to change.

type CLPSTerm = String

show_clpsterm :: CLPSTerm -> String
show_clpsterm = id

put_clpsterm :: CLPSTerm -> IO ()
put_clpsterm = putStr


todo s = fail (s ++ " not yet implemented in Z->CLPS-BZ translator.")


clps_expr :: TypeEnv -> ZExpr -> ErrorOr CLPSTerm
clps_expr env ZUniverse        = todo "ZUniverse"
clps_expr env (ZVar v)         = clps_var v
clps_expr env (ZGiven g)       = clps_const (string_to_zvar g)
clps_expr env (ZGivenSet v)    = clps_var v
clps_expr env (ZInt i)         = clps_int i
clps_expr env (ZGenerator r e) = todo ("ZGenerator" ++ show r)

clps_expr env e@(ZPowerSet{}) =
    clps_op (opname ++ one) [clps_expr env(baseset e)]
    where
    opname = if is_finite e then "fin" else "pow"
    one = ['1'|is_non_empty e]

clps_expr env e@ZFuncSet{}
    | is_sequence e
      && not(is_onto e)
      && not(is_total e)
	  = clps_op seqtype [clps_expr env (ranset e)]
    | is_non_empty e
	= fail ("no non-empty function space in CLPS: "
		++ show e)
    | is_finite e
	= fail ("no finite function space in CLPS: "
		++ show e)  -- TODO: maybe ignore this?
    | otherwise
	= clps_op opname (map (clps_expr env) [domset e, ranset e])
    where
    seqtype = ['i' | is_one2one e] ++ "seq" ++ ['1' | is_non_empty e]
    opname = arrow (is_function e) (is_total e) (is_onto e)
		   (is_one2one e)
    --    func  total onto  1-1
    arrow False False False False = "<->"  -- relation.
    arrow True  False False False = "+->"  -- partial function.
    arrow True  True  False False = "-->"  -- total function.
    arrow True  False False True  = ">+>"  -- partial injection.
    arrow True  True  False True  = ">->"  -- total injection.
    arrow True  False True  False = "+->>" -- partial surjection.
    arrow True  True  True  False = "-->>" -- total surjection.
    arrow True  False True  True  = "+->>" -- partial bijection.
    arrow True  True  True  True  = "-->>" -- total bijection.
    arrow _     _     _     _     = error ("Strange relation type: "
					 ++ show e)

-- Note: We turn longer tuples into nested pairs (right associative).
clps_expr env (ZCross [a,b]) =
    clps_op "*" (map (clps_expr env) [a,b])
clps_expr env (ZCross (e:es)) =
    clps_op "*" (map (clps_expr env) [e,ZCross es])
clps_expr env (ZTuple [a,b]) =
    clps_pair (clps_expr env a) (clps_expr env b)
clps_expr env (ZTuple (e:es)) =
    clps_pair (clps_expr env e) (clps_expr env (ZTuple es))

clps_expr env (ZCall (ZFunc1 f) arg) =
    clps_zfunc1 f [clps_expr env arg]
clps_expr env (ZCall (ZFunc2 f) (ZTuple [a,b])) =
    clps_zfunc2 f (map (clps_expr env) [a,b])
clps_expr env (ZCall func arg) =
    clps_op "@" (map (clps_expr env) [func,arg])
-- CLPS does not allow duplicates within enumerated sets,
-- so we convert them into the union of singleton sets.
-- (This is not necessary for ZFSet, because it contains no duplicates).
clps_expr env (ZSetDisplay []) =
    clps_set []
clps_expr env (ZSetDisplay [e]) =
    clps_set [clps_expr env e]
-- Note could optimise this so that constants go into one set,
--      but reducer should this.
clps_expr env (ZSetDisplay (e:es)) =
    clps_zfunc2 ZUnion [clps_set [clps_expr env e],
			clps_expr env (ZSetDisplay es)]
clps_expr env (ZSeqDisplay es) =
    todo "ZSeqDisplay"
clps_expr env (ZSetComp gfs (Just e))
  | e == char_tuple locals =
    Impossible [MStr "CLPS-BZ does not support {V|P} yet."]
    -- clps_quant "SetCompTODO" ... (see exists/forall for how to do this)
  | otherwise =
    Impossible [MStr "CLPS-BZ does not support {V|P.E} yet."]
    where
    locals = genfilt_names gfs
    body   = foldr1 ZAnd (genfilt_allpreds gfs)
    char_tuple [] = error "{|P} has no characteristic tuple."
    char_tuple [e] = ZVar e
    char_tuple es  = ZTuple (map ZVar es)

clps_expr env (ZMu gfs (Just e)) =
    todo "ZMu"

clps_expr env (ZIf_Then_Else p e1 e2) =
    todo "if then else for expressions"
    where
    p'  = clps_pred env p
    e1' = clps_expr env e1
    e2' = clps_expr env e2
clps_expr env (ZSelect e v) =
    todo "ZSelect"
clps_expr env (ZFSet s) =
    clps_set (map (clps_expr env) s) -- has no duplicates
clps_expr env (ZIntSet (Just lo) (Just hi)) =
    clps_op ".." (map clps_int [lo,hi])
clps_expr env (ZIntSet (Just 0) Nothing) =
    fail "You must change 'nat' to a finite integer range"
clps_expr env (ZIntSet (Just 1) Nothing) =
    fail "You must change 'nat_1' to a finite integer range"
    -- clps_var (string_to_zvar "nat1")
clps_expr env (ZIntSet Nothing Nothing) =
    -- clps_var (string_to_zvar "int")
    fail ("No CLPS-BZ translation for int.  Use a finite integer range.")
clps_expr env (ZBinding bs) =
    todo "ZBinding"
clps_expr env (ZFree0 n) =
    clps_const n
clps_expr env (ZFree1 n e) =
    todo "ZFree1"
clps_expr env e@(ZFreeType _ _)
    | e2 == e = fail ("Cannot evaluate free type: " ++ show e)
    | otherwise = clps_expr env e2
    where
    e2 = forceexpr dummy_eval_env e
clps_expr env e = fail ("No CLPS-BZ translation for: " ++ show e)


clps_zfunc1 :: ZFunc1 -> [ErrorOr CLPSTerm] -> ErrorOr CLPSTerm
clps_zfunc1 ZDom    = clps_op "dom"
clps_zfunc1 ZRan    = clps_op "ran"
clps_zfunc1 ZSizeof = clps_op "card"
clps_zfunc1 ZInv    = clps_op "~"
clps_zfunc1 ZBigCup = clps_op "union"
clps_zfunc1 ZBigCap = clps_op "inter"
clps_zfunc1 ZNegate = clps_op "-"
clps_zfunc1 ZMax    = clps_op "max"
clps_zfunc1 ZMin    = clps_op "min"
clps_zfunc1 ZStar   = clps_op "closure"
clps_zfunc1 ZClosure= clps_op "closure1"
clps_zfunc1 f = const (fail ("Error: no CLPS-BZ translation for " ++ show f))

clps_zfunc2 :: ZFunc2 -> [ErrorOr CLPSTerm] -> ErrorOr CLPSTerm
clps_zfunc2 ZUpto   = clps_op ".."
clps_zfunc2 ZPlus   = clps_op "+"
clps_zfunc2 ZMinus  = clps_op "-"
clps_zfunc2 ZTimes  = clps_op "*"
clps_zfunc2 ZDiv    = clps_op "/"
clps_zfunc2 ZMod    = clps_op "mod"
clps_zfunc2 ZUnion  = clps_op "\\\\/"
clps_zfunc2 ZInter  = clps_op "/\\\\"
clps_zfunc2 ZSetMinus = clps_op "minus"
clps_zfunc2 ZComp   = clps_op "comp"
clps_zfunc2 ZCirc   = clps_op "circ"
clps_zfunc2 ZDRes   = clps_op "</"
clps_zfunc2 ZRRes   = clps_op "/>"
clps_zfunc2 ZNDRes  = clps_op "<</"
clps_zfunc2 ZNRRes  = clps_op "/>>"
clps_zfunc2 ZRelImg = clps_op "img"
clps_zfunc2 ZOPlus  = clps_op "<+"
-- No BZP equivalent for these yet?
--clps_zfunc2 ZFirst  = clps_op "dom"
--clps_zfunc2 ZSecond = clps_op "ran"
clps_zfunc2 f = const (fail ("Error: no CLPS-BZ translation for " ++ show f))

clps_zreln :: ZReln -> [ErrorOr CLPSTerm] -> ErrorOr CLPSTerm
clps_zreln ZLessThan        = clps_op "<"
clps_zreln ZLessThanEq      = clps_op "=<"
clps_zreln ZGreaterThan     = clps_op ">"
clps_zreln ZGreaterThanEq   = clps_op ">="
clps_zreln ZSubset          = clps_op "<<:"
clps_zreln ZSubsetEq        = clps_op "<:"
-- TODO: (translate into simpler predicates?)
-- clps_zreln ZPartition       = clps_op "<:"
clps_zreln r = const (fail ("Error: no CLPS-BZ translation for " ++ show r))



clps_pred :: TypeEnv -> ZPred -> ErrorOr CLPSTerm
clps_pred env ZFalse{}         = return "1=0"
clps_pred env ZTrue{}          = return "1=1"
clps_pred env (ZAnd p1 p2)     = clps_op "&" (map (clps_pred env) [p1,p2])
clps_pred env (ZOr p1 p2)      = clps_op "or" (map (clps_pred env) [p1,p2])
clps_pred env (ZImplies p1 p2) = clps_op "=>" (map (clps_pred env) [p1,p2])
clps_pred env (ZIff p1 p2)     = clps_op "<=>" (map (clps_pred env) [p1,p2])
clps_pred env (ZNot p)         = clps_op "not" [clps_pred env p]
clps_pred env (ZExists gfs p)  =
    do  let (locals,ztypes) = unzip [(n,t) | Choose n t <- gfs]
	let ltypes = map (infer_base_type env) ztypes
	let body = foldr1 ZAnd (genfilt_allpreds gfs)
	let clps_body = clps_pred env body
	let clps_p = clps_pred (extend_typeenv env gfs) p
	clps_quant "exists" locals ltypes (clps_op "&" [clps_body,clps_p])
clps_pred env (ZExists_1 gfs p)= todo "ZExists1"
clps_pred env (ZForall gfs p)  =
    do  let (locals,ztypes) = unzip [(n,t) | Choose n t <- gfs]
	let ltypes = map (infer_base_type env) ztypes
	let guard  = foldr1 ZAnd (genfilt_allpreds gfs)
	let clps_guard = clps_pred env guard
	let clps_p = clps_pred (extend_typeenv env gfs) p
	clps_quant "all" locals ltypes (clps_op "=>" [clps_guard,clps_p])
clps_pred env e@(ZEqual e1 e2) =
    do  let typ = infer_unify_types env [e1,e2]
	op <- clps_equals typ e
	clps_op op (map (clps_expr env) [e1,e2])
clps_pred env (ZMember (ZTuple [a,b]) (ZReln r)) =
    clps_zreln r (map (clps_expr env) [a,b])
clps_pred env (ZMember e1 e2) =
    clps_op ":" (map (clps_expr env) [e1,e2])
clps_pred env p =
    fail ("No CLPS-BZ translation for: " ++ show p)


clps_equals (Type_Error msg) e =
    fail ("type error: " ++ msg ++ "\n  in: " ++ show e)
    -- DEBUG: return ("<<<" ++ msg ++ "\n  in equality: " ++ show e ++ ">>>")
clps_equals Type_Int         e = return "="
clps_equals Type_Bool        e = return "<=>"
clps_equals Type_Given       e = return "="
clps_equals Type_Free        e = return "="
clps_equals (Type_Tuple _)   e = return "="
clps_equals (Type_Setof _)   e = return "="
clps_equals (Type_Unknown msg) e = return "="   -- this handles all types?
--    fail ("cannot infer type of: " ++ show e ++ "\n  " ++ msg)
--    -- DEBUG: return ("<<<Cannot infer type of: " ++ show e ++ msg ++ ">>>")
clps_equals t                e = fail ("strange type inferred: " ++ show t)



genfilt_allpreds :: [ZGenFilt] -> [ZPred]
genfilt_allpreds = concatMap getpred
    where
    getpred (Check p) = [p]
    getpred (Choose x typ) = [ZMember (ZVar x) typ]
    getpred (Evaluate x val typ) = [ZEqual (ZVar x) val, ZMember (ZVar x) typ]
----------------------------------------------------------------------
-- Lower-level functions for constructing clps terms.
----------------------------------------------------------------------

clps_int :: ZInt -> ErrorOr CLPSTerm
clps_int i = return (show i)

clps_const :: ZVar -> ErrorOr CLPSTerm
clps_const name = return (safe_zvar name)

clps_var :: ZVar -> ErrorOr CLPSTerm
clps_var (n,["'"]) = return ("prime(" ++ safe_zvar (n,[]) ++ ")")
clps_var name = return (safe_zvar name)

safe_zvar :: ZVar -> String
safe_zvar (v,ds) = "b_" ++ (filter safechar v) ++ concatMap safedecor ds
    where
    safechar ch  = isAlphaNum ch || ch == '_'
    safedecor "'" = "__prime"   -- NB. single prime case is handled above.
    safedecor "!" = "__out"
    safedecor "?" = "__in"
    safedecor dec = dec  -- should be _<digit>

clps_pair :: ErrorOr CLPSTerm -> ErrorOr CLPSTerm -> ErrorOr CLPSTerm
clps_pair a b =
    do  aval <- a
	bval <- b
	return ("(" ++ aval ++ " /-> " ++ bval ++ ")")

-- This outputs literal sets like {1,3,5}.
-- It must only be used when the set contains no duplicates.
clps_set :: [ErrorOr CLPSTerm] -> ErrorOr CLPSTerm
clps_set elems =
    do  elemvals <- sequence elems
	return ("{" ++ concat (intersperse ", " elemvals) ++ "}")

-- quantifier-like constructs: [Quant,BoundVars,Predicate]
clps_quant :: String -> [ZVar] -> [CLPSType] -> ErrorOr CLPSTerm 
	   -> ErrorOr CLPSTerm
clps_quant q locals ltypes prederr =
    do  pred <- prederr
	locals2 <- mapM clps_var locals
	ltypes2 <- mapM show_clpstype ltypes
	let bound = concat (intersperse "," locals2)
	let btypes = concat (intersperse "," ltypes2)
	return (q ++ "([" ++ bound ++ "], "  ++
		     "[" ++ btypes ++ "], " ++ pred ++ ")")


-- Output a term in prefix form.
-- Useful for expressions and predicates.
-- Example:  clps_op "+" [a,b] gives:  '+'(a,b)
clps_op :: String -> [ErrorOr CLPSTerm] -> ErrorOr CLPSTerm
clps_op op args =
    do  argvals <- sequence args
	return (mkop op ++ "(" ++ concat(intersperse ", " argvals) ++ ")")
    where
    mkop (c:s) | isLower c = c:s
	       | otherwise = "'" ++ (c:s) ++ "'"
