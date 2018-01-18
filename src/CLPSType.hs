module CLPSType
-- This module does crude base-type inference on ZExprs.
where
import Maybe
import Errors
import AST

data CLPSType =
    Type_Error String |
    Type_Unknown String |
    Type_Int |
    Type_Bool |
    Type_Given |
    Type_Free |
    Type_Tuple [CLPSType] |
    Type_Setof CLPSType
    deriving (Show,Eq,Ord)

type TypeEnv = [(ZVar,CLPSType)]


show_clpstype :: CLPSType -> ErrorOr String
show_clpstype (Type_Error msg) = fail msg
show_clpstype (Type_Unknown msg) = fail ("Type unknown: " ++ msg)
show_clpstype Type_Int = return "nat" -- TEMPORARY, UNTIL BZ-TT REDUCER int.
-- show_clpstype Type_Int = return "nat"   -- TODO: Use this instead
show_clpstype Type_Bool = return "bool" 
show_clpstype Type_Given = return "atom" 
show_clpstype Type_Free = return "atom" 
show_clpstype (Type_Tuple [a,b]) =
    do  sa <- show_clpstype a
	sb <- show_clpstype b
	return ("pair(" ++ sa ++ ", " ++ sb ++ ")")
show_clpstype (Type_Tuple (a:bs)) | not (null bs) =
    do  sa <- show_clpstype a
	sb <- show_clpstype (Type_Tuple bs)
	return ("pair(" ++ sa ++ ", " ++ sb ++ ")")
show_clpstype (Type_Setof t) =
    do  st <- show_clpstype t
	return ("set(" ++ st ++ ")")
show_clpstype t = fail ("No CLPS-BZ type for: " ++ show t)


extend_typeenv :: TypeEnv -> [ZGenFilt] -> TypeEnv
extend_typeenv env gfs = reverse newenv ++ env
    where
    newenv = [(z,infer_base_type env t) | Choose z t <- gfs]


-----------------------------------------------------------------
-- total access functions for extracting subparts of a compound type.
-----------------------------------------------------------------
set_elem_type :: CLPSType -> CLPSType
set_elem_type (Type_Setof t)   = t
set_elem_type (Type_Unknown m) = Type_Unknown m
set_elem_type t                = Type_Error "set type required"

tuple_elem_type :: Int -> CLPSType -> CLPSType
tuple_elem_type i (Type_Tuple ts)  = ts!!i
tuple_elem_type i (Type_Unknown m) = Type_Unknown m
tuple_elem_type i t                = Type_Error "tuple type required"

dom_elem_type :: CLPSType -> CLPSType
dom_elem_type = tuple_elem_type 0 . set_elem_type

ran_elem_type :: CLPSType -> CLPSType
ran_elem_type = tuple_elem_type 1 . set_elem_type

seq_elem_type = ran_elem_type

-----------------------------------------------------------------
-- constructor functions for building compound types.
-----------------------------------------------------------------
setof :: CLPSType -> CLPSType
setof t = Type_Setof t

tupleof :: [CLPSType] -> CLPSType
tupleof ts = Type_Tuple ts

relof :: CLPSType -> CLPSType -> CLPSType
relof dom ran = Type_Setof (Type_Tuple [dom,ran])

seqof :: CLPSType -> CLPSType
seqof t = Type_Setof (Type_Tuple [Type_Int,t])



-----------------------------------------------------------------
-- misc. functions for manipulating lists of types.
-----------------------------------------------------------------
unify_types :: [CLPSType] -> CLPSType
unify_types = foldr unify_type (Type_Unknown "empty list")

-- returns the first non-error type in a list
unify_type (Type_Error e)   _                 = Type_Error e
unify_type _                (Type_Error e)    = Type_Error e
unify_type (Type_Unknown m) (Type_Unknown m2) = Type_Unknown m
unify_type t1               (Type_Unknown _)  = t1
unify_type (Type_Unknown _) t2                = t2
-- Now both types are known and non-error, so they should be compatible.
unify_type (Type_Setof t) (Type_Setof t2) = setof (unify_type t t2)
unify_type (Type_Tuple ts) (Type_Tuple ts2) = tupleof ts'
    where
    ts' = [unify_type t t2 | (t,t2) <- zip ts ts2]
unify_type t1 t2
    | t1==t2 = t1
    | otherwise = Type_Error ("Incompatible types:\n    " ++ show t1
			      ++ "\n    " ++ show t2)


infer_unify_types :: TypeEnv -> [ZExpr] -> CLPSType
-- infers the element-type of a list of identically-typed expressions
infer_unify_types env es =
    unify_types (map (infer_type env) es)


--------------------------------------------------------------------
-- Simple type inference for ZExpr.
--------------------------------------------------------------------
-- This converts a type to its base type.
infer_base_type :: TypeEnv -> ZExpr -> CLPSType
infer_base_type env t = set_elem_type (infer_type env t)

-- This infers the type of an expression.
-- It should not be applied to Z types (use infer_base_type instead)
infer_type :: TypeEnv -> ZExpr -> CLPSType
infer_type env (ZVar v) =
    fromMaybe (Type_Unknown ("no type for: " ++ show_zvar v))
	      (lookup v env)
infer_type env (ZGiven g)       = Type_Given
infer_type env (ZGivenSet v)    = setof Type_Given
infer_type env (ZInt i)         = Type_Int
infer_type env e@(ZPowerSet{})  = setof (infer_type env (baseset e))
infer_type env e@(ZFuncSet{})   = setof (setof (tupleof [d,r]))
    where
    d = infer_base_type env (domset e)
    r = infer_base_type env (ranset e)
infer_type env (ZCross es) =
    setof (tupleof (map (infer_base_type env) es))
infer_type env (ZTuple es) =
    tupleof (map (infer_type env) es)
infer_type env (ZCall (ZFunc1 f) arg) =
    type_zfunc1 f (infer_type env arg)
infer_type env (ZCall (ZFunc2 f) (ZTuple [a,b])) =
    type_zfunc2 f [infer_type env a, infer_type env b]
infer_type env (ZCall func arg) =
    ran_elem_type (infer_type env func)
infer_type env (ZSetDisplay es) =
    setof (infer_unify_types env es)
infer_type env (ZSeqDisplay es) =
    seqof t
    where
    t = infer_unify_types env es
infer_type env (ZSetComp gfs (Just e)) =
    setof (infer_type (extend_typeenv env gfs) e)
infer_type env (ZMu gfs (Just e)) =
    infer_type (extend_typeenv env gfs) e
infer_type env (ZIf_Then_Else p e1 e2) =
    infer_unify_types env [e1,e2]
infer_type env (ZSelect e v) =
    Type_Unknown "cannot infer type of E.v"
infer_type env (ZFSet es) =
    setof (infer_unify_types env es)
infer_type env (ZIntSet _ _) =
    setof Type_Int
infer_type env (ZBinding bs) =
    Type_Unknown "type_infer of bindings not implemented"
infer_type env (ZFree0 n) =
    Type_Free
infer_type env (ZFree1 n e) =
    Type_Free
infer_type env (ZFreeType _ _) =
    setof Type_Free
infer_type env e =
    Type_Unknown ("Cannot infer type of: " ++ show e)




type_zfunc1 :: ZFunc1 -> CLPSType -> CLPSType
type_zfunc1 ZDom     t = setof (dom_elem_type t)
type_zfunc1 ZRan     t = setof (ran_elem_type t)
type_zfunc1 ZSizeof  t = Type_Int
type_zfunc1 ZBigCup  t = setof (set_elem_type (set_elem_type t))
type_zfunc1 ZBigCap  t = setof (set_elem_type (set_elem_type t))
type_zfunc1 ZRev     t = seqof (seq_elem_type t)
type_zfunc1 ZHead    t = seq_elem_type t
type_zfunc1 ZLast    t = seq_elem_type t
type_zfunc1 ZTail    t = seqof (seq_elem_type t)
type_zfunc1 ZFront   t = seqof (seq_elem_type t)
type_zfunc1 ZSquash  t = seqof (seq_elem_type t)
type_zfunc1 ZDCat    t = seqof (seq_elem_type (seq_elem_type t))
type_zfunc1 ZSucc    t = Type_Int
type_zfunc1 ZNegate  t = Type_Int
type_zfunc1 ZMax     t = Type_Int
type_zfunc1 ZMin     t = Type_Int
type_zfunc1 ZInv     t = relof (ran_elem_type t) (dom_elem_type t)
type_zfunc1 ZStar    t = relof t2 t2
    where t2 = unify_types [dom_elem_type t, ran_elem_type t]
type_zfunc1 ZClosure t = relof t2 t2
    where t2 = unify_types [dom_elem_type t, ran_elem_type t]
type_zfunc1 ZSum     t = Type_Int


type_zfunc2 :: ZFunc2 -> [CLPSType] -> CLPSType
type_zfunc2 ZUpto     [a,b] = setof Type_Int
type_zfunc2 ZPlus     [a,b] = Type_Int
type_zfunc2 ZMinus    [a,b] = Type_Int
type_zfunc2 ZTimes    [a,b] = Type_Int
type_zfunc2 ZDiv      [a,b] = Type_Int
type_zfunc2 ZMod      [a,b] = Type_Int
type_zfunc2 ZUnion    [a,b] = setof (set_elem_type (unify_types [a,b]))
type_zfunc2 ZInter    [a,b] = setof (set_elem_type (unify_types [a,b]))
type_zfunc2 ZSetMinus [a,b] = setof (set_elem_type (unify_types [a,b]))
type_zfunc2 ZComp     [a,b] = relof (dom_elem_type a) (ran_elem_type b)
type_zfunc2 ZCirc     [a,b] = relof (dom_elem_type b) (ran_elem_type a)
type_zfunc2 ZDRes     [a,b] = b  -- TODO: add unification
type_zfunc2 ZRRes     [a,b] = a  -- TODO: add unification
type_zfunc2 ZNDRes    [a,b] = b  -- TODO: add unification
type_zfunc2 ZNRRes    [a,b] = a  -- TODO: add unification
type_zfunc2 ZRelImg   [a,b] = setof (ran_elem_type a)
type_zfunc2 ZOPlus    [a,b] = unify_types [a,b]
type_zfunc2 ZCat      [a,b] = unify_types [a,b]
type_zfunc2 ZExtract  [a,b] = b
type_zfunc2 ZFilter   [a,b] = a -- TODO: add unification
type_zfunc2 ZFirst    [a,b] = a
type_zfunc2 ZSecond   [a,b] = b
