module Main
--
-- $Id: Eval_Test.hs,v 1.23 2005/03/26 13:12:55 marku Exp $
--
-- This module contains test cases for expression/predicate evaluation.
-- Just execute 'main' to run all tests.
--
where

import Eval
import Errors

-- We also import some lower level set construction functions,
-- so we can directly build finite sets.
-- Note that set_from_ordered_list builds result sets without any sorting
-- or duplicate-removal, whereas 'set' does sort and remove duplicates.
import FiniteSets(set,set_from_ordered_list)


-- This optionally shows the result of each successful test (verbose!).
-- Uncomment the non-empty definition if you want to see results.
show_result :: (Show a) => a -> String
show_result v = ""
-- show_result v = "      Result is: " ++ show v ++ "\n"


test :: (Show b, Eq b) => String -> (a -> ErrorOr b) -> a -> ErrorOr b -> IO ()
test name eval arg expected
  = let actual = eval arg in
    if actual == expected || (isUndef actual && isUndef expected)
    then putStr ("  passed test: " ++ name ++ "\n" ++ show_result actual)
    else putStr ("  FAILED TEST: " ++ name ++ "\n" ++
		 "      Expected: " ++ show expected ++ "\n" ++
		 "      But got:  " ++ show actual ++ "\n")


-- We test expressions and predicates in an environment which
-- has 'even' equal to {2,4,6,8,10}
-- and 'odd' equal to {1,3,5,7,9}
-- and 'five' equal to 5.
even10, odd10, five, x, y, z :: ZVar
even10 = make_zvar "even" []
odd10  = make_zvar "odd"  []
five = make_zvar "five" []
x = make_zvar "x" []
y = make_zvar "y" []
z = make_zvar "z" []

testenv = envPushLocals 
	    [(even10, even_upto_10),
	     (odd10, odd_upto_10),
	     (five, ZInt 5)]
	    dummy_eval_env

testexpr n = test n (\e -> evalexpr e testenv)
testpred n = test n (\p -> evalpred p testenv)


-- Auxiliary functions for building up test expressions/predicates.

upto :: ZInt -> ZInt -> ZExpr
upto lo hi = ZIntSet (Just lo) (Just hi)

lessthan :: ZExpr -> ZExpr -> ZPred
lessthan e1 e2 = ZMember (ZTuple [e1,e2]) (ZReln ZLessThan)


-- Some handy finite set expressions.
emptyset     = ZSetDisplay []
ten          = ZSetDisplay [ZInt i | i <- [1..10]]
hundred      = ZSetDisplay [ZInt i | i <- [1..100]]
double       = ZSetDisplay [ ZTuple [ZInt 5, ZInt 10],
			     ZTuple [ZInt 6, ZInt 12] ]
pfunc        = ZFuncSet{ domset= 4 `upto` 6,
			 ranset= nats,
			 is_function=True,
			 is_total=False,
			 is_onto=False,
			 is_one2one=False,
			 is_sequence=False,
			 is_non_empty=False,
			 is_finite=False }


-- and some infinite/large sets.
ints = ZIntSet Nothing Nothing
nats = ZIntSet (Just 0) Nothing
big  = ZIntSet (Just 0) (Just 10000)


-- These should evaluate to an 'Undef' error.
undef_term = ZCall emptyset (ZInt 2)
undef_pred = ZEqual undef_term undef_term


-- It is interesting to evaluate these set expression for timing purposes.
big_slow = ZSetComp [Choose x hundred,
		     Choose y hundred,
		     Check (ZEqual (ZVar x) (ZInt 3))]
		(Just (ZVar x))
big_fast = ZSetComp [Choose x hundred,
		     Check (ZEqual (ZVar x) (ZInt 3)),
		     Choose y hundred]
		(Just (ZVar x))



-- These finite sets are ZValues (the result of an evaluation)
upto_10      = ZFSet (set_from_ordered_list (map ZInt [1..10]))
even_upto_10 = ZFSet (set_from_ordered_list (map ZInt [2,4,6,8,10]))
odd_upto_10  = ZFSet (set_from_ordered_list (map ZInt [1,3,5,7,9]))
s1248        = ZFSet (set_from_ordered_list (map ZInt [1,2,4,8]))
s5           = ZFSet (set [ZInt 5])
empty_result = ZFSet (set [])



test_set_displays =
 do putStrLn "\n Testing set displays: {a,b,c,...}"
    testexpr
	"{1,2,4,8}"
	(ZSetDisplay [ZInt 1, ZInt 2, ZInt 4, ZInt 8])
	(Ok s1248)
    testexpr
	"{8,4,2,1}"
	(ZSetDisplay [ZInt 8, ZInt 4, ZInt 2, ZInt 1])
	(Ok s1248)
    testexpr
	"{1,2,1,8,4,1,8}"
	(ZSetDisplay [ZInt 1, ZInt 2, ZInt 1, ZInt 8,
		      ZInt 4, ZInt 1, ZInt 8])
	(Ok s1248)
    testexpr
	"{5,5,5,5,5,5,5,5,five}"
	(ZSetDisplay ([ZInt 5| i <- [1..8]] ++ [ZVar five]))
	(Ok . ZFSet . FiniteSets.set $ [ZInt 5])


test_set_comprehensions =
 do putStrLn "\n Testing finite set comprehensions"
    testexpr
	"{x:-2..3 @ x}"
	(ZSetComp [Choose x ((-2) `upto` 3)] (Just (ZVar x)))
	(Ok . ZFSet . FiniteSets.set
	  $ [ZInt (-2),ZInt (-1),ZInt 0,ZInt 1,ZInt 2,ZInt 3])
    testexpr
	"{x:2..4;y:5..6 @ (x,y)}"
	(ZSetComp [Choose x (2 `upto` 4), Choose y (5 `upto` 6)]
	    (Just (ZTuple [ZVar x, ZVar y])))
	(Ok . ZFSet . set
	    $ [ ZTuple [(ZInt 2), (ZInt 5)],
		ZTuple [(ZInt 2), (ZInt 6)],
		ZTuple [(ZInt 3), (ZInt 5)],
		ZTuple [(ZInt 3), (ZInt 6)],
		ZTuple [(ZInt 4), (ZInt 5)],
		ZTuple [(ZInt 4), (ZInt 6)] ])
    testexpr
	"{x:2..4;y:5..6 | true @ x}"
	(ZSetComp [Choose x (2 `upto` 4),
		   Choose y (5 `upto` 6),
		   Check ztrue]
	    (Just (ZVar x)))
	(Ok . ZFSet . set $ [ZInt 2, ZInt 3, ZInt 4])
    testexpr
	"{x:2..4;y:5..6 | false @ x}"
	(ZSetComp [Choose x (2 `upto` 4),
		   Choose y (5 `upto` 6),
		   Check zfalse]
	    (Just (ZVar x)))
	(Ok empty_result)
    testexpr
	"{x:2..4;y:5..6 | y=6 @ (x,y)}"
	(ZSetComp [Choose x (2 `upto` 4),
		   Choose y (5 `upto` 6),
		   Check (ZEqual (ZVar y) (ZInt 6))]
	    (Just (ZTuple [ZVar x,ZVar y])))
	(Ok . ZFSet . set
	    $ [ ZTuple [(ZInt 2), (ZInt 6)],
		ZTuple [(ZInt 3), (ZInt 6)],
		ZTuple [(ZInt 4), (ZInt 6)] ])


test_functions =
 do putStrLn "\n Testing function calls"
    testexpr
	"({(5,10),(6,12)} 5)"
	(ZCall double (ZInt 5))
	(Ok (ZInt 10))
    testexpr
	"({(5,10),(6,12)} 7)"
	(ZCall double (ZInt 7))
	(Undefined [])

test_relations =
 do putStrLn "\n Testing toolkit relations"
    -- subseteq
    testpred
	"2..5 subseteq 2..5"
	(ZMember (ZTuple [2 `upto` 5, 2 `upto` 5]) (ZReln ZSubsetEq))
	(Ok True)
    testpred
	"2..6 subseteq 2..5"
	(ZMember (ZTuple [2 `upto` 6, 2 `upto` 5]) (ZReln ZSubsetEq))
	(Ok False)
    testpred
	"1..5 subseteq 2..5"
	(ZMember (ZTuple [1 `upto` 5, 2 `upto` 5]) (ZReln ZSubsetEq))
	(Ok False)
    testpred
	"big subseteq nats"
	(ZMember (ZTuple [big, nats]) (ZReln ZSubsetEq))
	(Ok True)
    -- strict subset
    testpred
	"2..5 subset 2..5"
	(ZMember (ZTuple [2 `upto` 5, 2 `upto` 5]) (ZReln ZSubset))
	(Ok False)
    testpred
	"2..6 subset 2..5"
	(ZMember (ZTuple [2 `upto` 6, 2 `upto` 5]) (ZReln ZSubset))
	(Ok False)
    testpred
	"1..5 subset 2..5"
	(ZMember (ZTuple [1 `upto` 5, 2 `upto` 5]) (ZReln ZSubset))
	(Ok False)
    -- function types
    testpred
	"{(5,10),(6,12)} in {4,5,6} \\pfun nat"
	(ZMember double pfunc)
	(Ok True)
    testpred
	"{(5,10),(6,12)} in {4,5,6} \\fun nat"
	(ZMember double pfunc{is_total=True})
	(Ok False)
    testpred
	"{(5,10),(6,12)} in {4,5,6} \\pfinj nat"
	(ZMember double pfunc{is_one2one=True})
	(Ok True)
    testpred
	"{(5,10),(6,10)} in {4,5,6} \\pfinj nat"
	(ZMember
	   (ZSetDisplay [ ZTuple [ZInt 5, ZInt 10],
			  ZTuple [ZInt 6, ZInt 10] ])
	    pfunc{is_one2one=True})
	(Ok False)


test_boolean_operators =
 do putStrLn "\n Testing boolean operators"
    -- and
    testpred
	"true and true"
	(ZAnd ztrue ztrue)
	(Ok True)
    testpred
	"true and false"
	(ZAnd ztrue zfalse)
	(Ok False)
    testpred
	"false and true"
	(ZAnd zfalse ztrue)
	(Ok False)
    testpred
	"false and false"
	(ZAnd zfalse zfalse)
	(Ok False)
    testpred
	"true and Undef"
	(ZAnd ztrue undef_pred)
	(Undefined [])
    testpred
	"Undef and true"
	(ZAnd undef_pred ztrue)
	(Undefined [])
    testpred
	"false and Undef"
	(ZAnd zfalse undef_pred)
	(Ok False)
    testpred
	"Undef and false"
	(ZAnd undef_pred zfalse)
	(Ok False)
    -- or
    testpred
	"true or true"
	(ZOr ztrue ztrue)
	(Ok True)
    testpred
	"true or false"
	(ZOr ztrue zfalse)
	(Ok True)
    testpred
	"false or true"
	(ZOr zfalse ztrue)
	(Ok True)
    testpred
	"false or false"
	(ZOr zfalse zfalse)
	(Ok False)
    testpred
	"true or Undef"
	(ZOr ztrue undef_pred)
	(Ok True)
    testpred
	"Undef or true"
	(ZOr undef_pred ztrue)
	(Ok True)
    testpred
	"false or Undef"
	(ZOr zfalse undef_pred)
	(Undefined [])
    testpred
	"Undef or false"
	(ZOr undef_pred zfalse)
	(Undefined [])
    -- not
    testpred
	"not true"
	(ZNot ztrue)
	(Ok False)
    testpred
	"not false"
	(ZNot zfalse)
	(Ok True)
    testpred
	"not Undef"
	(ZNot undef_pred)
	(Undefined [])
    -- implies (just a few cases, because it is defined using or+not)
    testpred
	"false => Undef"
	(ZImplies zfalse undef_pred)
	(Ok True)
    testpred
	"true => false"
	(ZImplies ztrue zfalse)
	(Ok False)
    testpred
	"Undef => true"
	(ZImplies undef_pred ztrue)
	(Ok True)
    -- iff
    testpred
	"true <=> true"
	(ZIff ztrue ztrue)
	(Ok True)
    testpred
	"true <=> false"
	(ZIff ztrue zfalse)
	(Ok False)
    testpred
	"false <=> true"
	(ZIff zfalse ztrue)
	(Ok False)
    testpred
	"false <=> false"
	(ZIff zfalse zfalse)
	(Ok True)
    testpred
	"Undef <=> false"
	(ZIff undef_pred zfalse)
	(Undefined [])
    testpred
	"true <=> Undef"
	(ZIff ztrue undef_pred)
	(Undefined [])


-- Some handy predicates and sets.
x_eq_3     = ZEqual (ZVar x) (ZInt 3)
y_in_124   = ZMember (ZVar y) (ZSetDisplay [ZInt 1, ZInt 2, ZInt 4])
y_in_10_20 = ZMember (ZVar y) (10 `upto` 20)
x_in_yup   = ZMember (ZVar x) (ZCall (ZFunc2 ZUpto) (ZTuple [ZVar y,ZInt 10]))

test_quantifiers =
 do putStrLn "\n Testing quantifiers"
    testpred
	"(forall x:1..10 @ x=3)"
	(ZForall [Choose x (1 `upto` 10)] x_eq_3)
	(Ok False)
    testpred
	"(forall x:1..10 @ not x=3)"
	(ZForall [Choose x (1 `upto` 10)] (ZNot x_eq_3))
	(Ok False)
    testpred
	"(forall x:4..10 @ not x=3)"
	(ZForall [Choose x (4 `upto` 10)] (ZNot x_eq_3))
	(Ok True)
    testpred
	"(forall x:4..6 @ ({(5,10),(6,12)} x) in 10..12)"
	(ZForall [Choose x (4 `upto` 6)]
	   (ZMember (ZCall double (ZVar x)) (10 `upto` 12)))
	(Undefined [])
    testpred
	"(forall x:4..6; y:7..11 @ x in y..10)"
	(ZForall [Choose x (4 `upto` 6), Choose y (7 `upto` 11)] x_in_yup)
	(Ok False)
    testpred
	"(forall x:4..6; y:4..7 @ x in y..10)"
	(ZForall [Choose x (4 `upto` 6), Choose y (4 `upto` 7)] x_in_yup)
	(Ok False)
    testpred
	"(forall x:4..6; y:0..3 @ x in y..10)"
	(ZForall [Choose x (4 `upto` 6), Choose y (0 `upto` 3)] x_in_yup)
	(Ok True)
    -- exists
    testpred
	"(exists x:1..3 @ x=3)"
	(ZExists [Choose x (1 `upto` 10)]  x_eq_3)
	(Ok True)
    testpred
	"(exists x:(-10)..3 @ x=3)"
	(ZExists [Choose x ((-10) `upto` 3)]  x_eq_3)
	(Ok True)
    testpred
	"(exists x:1..10 @ not x=3)"
	(ZExists [Choose x (1 `upto` 10)]  (ZNot x_eq_3))
	(Ok True)
    testpred
	"(exists x:1..10 @ false)"
	(ZExists [Choose x (1 `upto` 10)]  zfalse)
	(Ok False)
    testpred
	"(exists x:4..10 @ ({(5,10),(6,12)} x) in 11..12)"
	(ZExists [Choose x (4 `upto` 10)]
	   (ZMember (ZCall double (ZVar x)) (11 `upto` 12)))
	(Ok True)
    testpred
	"(exists x:1..4; y:5..7 @ x in y..10)"
	(ZExists [Choose x (1 `upto` 4), Choose y (5 `upto` 7)] x_in_yup)
	(Ok False)
    testpred
	"(exists x:1..4; y:4..7 @ x in y..10)"
	(ZExists [Choose x (1 `upto` 4), Choose y (4 `upto` 7)] x_in_yup)
	(Ok True)


test_builtins =
 do putStrLn "\n Testing builtin functions/predicates"
    testexpr
	"2 + (3 * five)"
	(ZCall (ZFunc2 ZPlus)
	   (ZTuple [ZInt 2,
		     (ZCall (ZFunc2 ZTimes)
			(ZTuple [ZInt 3, ZVar five]))
		    ]))
	(Ok (ZInt 17))
    testexpr
	"# (0..10000)"
	(ZCall (ZFunc1 ZSizeof) big)
	(Ok (ZInt 10001))
    testexpr
	"# (4..3)"
	(ZCall (ZFunc1 ZSizeof) (4 `upto` 3))
	(Ok (ZInt 0))
    testexpr
	"# nats"
	(ZCall (ZFunc1 ZSizeof) nats)
	(Undefined [])
    testpred
	"0 in (0..10000)"
	(ZMember (ZInt 0) big)
	(Ok True)
    testpred
	"10000 in (0..10000)"
	(ZMember (ZInt 10000) big)
	(Ok True)
    testpred
	"-1 in (0..10000)"
	(ZMember (ZInt (-1)) big)
	(Ok False)
    testpred
	"10001 in (0..10000)"
	(ZMember (ZInt 10001) big)
	(Ok False)
    testpred
	"0 in nats"
	(ZMember (ZInt 5) nats)
	(Ok True)
    testpred
	"-1 in nats"
	(ZMember (ZInt (-1)) nats)
	(Ok False)
    testpred
	"-1 in ints"
	(ZMember (ZInt (-1)) ints)
	(Ok True)
    testpred
	"(4..3) = emptyset"
	(ZEqual (4 `upto` 3) emptyset)
	(Ok True)
    testpred
	"even union odd = 1..10"
	(ZEqual (ZCall (ZFunc2 ZUnion) (ZTuple [ZVar even10, ZVar odd10]))
		(1 `upto` 10))
	(Ok True)
    testpred
	"even inter odd = {}"
	(ZEqual (ZCall (ZFunc2 ZInter) (ZTuple [ZVar even10, ZVar odd10]))
		emptyset)
	(Ok True)
    testpred
	"even diff odd = even"
	(ZEqual (ZCall (ZFunc2 ZSetMinus) (ZTuple [ZVar even10, ZVar odd10]))
		(ZVar even10))
	(Ok True)
    testpred
	"even diff even = {}"
	(ZEqual (ZCall (ZFunc2 ZSetMinus) (ZTuple [ZVar even10, ZVar even10]))
		(ZSetDisplay []))
	(Ok True)
    testexpr
	"dom double"
	(ZCall (ZFunc1 ZDom) double)
	(Ok (ZFSet (set [ZInt 5, ZInt 6])))
    testexpr
	"ran double"
	(ZCall (ZFunc1 ZRan) double)
	(Ok (ZFSet (set [ZInt 10, ZInt 12])))


ft = make_zvar "FT" []
ftval = ZFreeType ft [ZBranch0 x,
		      ZBranch1 y (2 `upto` 5)]

-- yval == (\lambda z:2..5 @ y z)
yval =  ZSetComp [Choose z (2 `upto` 5)]
		 (Just (ZTuple [ZVar z, ZFree1 y (ZVar z)]))

-- lambdaf == (\lambda z:2..5 @ z+z)
lambdaf = ZSetComp [Choose z (2 `upto` 5)]
	   (Just (ZTuple [ZVar z,
			  ZCall (ZFunc2 ZPlus) (ZTuple [ZVar z,ZVar z])]))

-- lambdaf2 == (\lambda z:2..5 | z < 4 @ z+z)
lambdaf2 = ZSetComp [Choose z (2 `upto` 5),
		      Check (lessthan (ZVar z) (ZInt 4))]
	     (Just (ZTuple [ZVar z,
			    ZCall (ZFunc2 ZPlus) (ZTuple [ZVar z,ZVar z])]))

-- lambdaf3 == (\lambda x,z:2..5 @ x+z)
lambdaf3 = ZSetComp [Choose x (2 `upto` 5), Choose z (2 `upto` 5)]
	     (Just (ZTuple [ZTuple [ZVar x, ZVar z],
			    ZCall (ZFunc2 ZPlus) (ZTuple [ZVar x,ZVar z])]))

test_lambdas =
 do putStrLn "\n Testing lambda functions and application"
    testexpr
	"(\\lambda z:2..5 @ z+z) 5"
	(ZCall lambdaf (ZInt 5))
	(Ok (ZInt 10))
    testexpr
	"(\\lambda z:2..5 @ z+z) 6"
	(ZCall lambdaf (ZInt 6))
	(Undefined [])
    testexpr
	"(\\lambda z:2..5|z<4 @ z+z) 2"
	(ZCall lambdaf2 (ZInt 2))
	(Ok (ZInt 4))
    testexpr
	"(\\lambda z:2..5|z<4 @ z+z) 4"
	(ZCall lambdaf2 (ZInt 6))
	(Undefined [])
    testexpr
	"(\\lambda x,z:2..5 @ x+z) (2,3)"
	(ZCall lambdaf3 (ZTuple [ZInt 2,ZInt 3]))
	(Ok (ZInt 5))
    testexpr
	"(\\lambda x,z:2..5 @ x+z) (1,3)"
	(ZCall lambdaf3 (ZTuple [ZInt 1,ZInt 3]))
	(Undefined [])
    testexpr
	"(\\lambda x,z:2..5 @ x+z) (2,6)"
	(ZCall lambdaf3 (ZTuple [ZInt 2,ZInt 6]))
	(Undefined [])


test_freetypes =
 do putStrLn "\n Testing free types, with FT ::= x | y<<2..5>>"
    testexpr
	"y 1"
	(ZCall yval (ZInt 1))
	(Undefined [])
    testexpr
	"y 2"
	(ZCall yval (ZInt 2))
	(Ok (ZFree1 y (ZInt 2)))
    testpred
	"x in FT"
	(ZMember (ZFree0 x) ftval)
	(Ok True)
    testpred
	"z in FT"
	(ZMember (ZFree0 z) ftval)
	(Ok False)
    testpred
	"y in FT"
	(ZMember (ZFree0 y) ftval)
	(Ok False)
    testpred
	"y 2 in FT"
	(ZMember (ZCall yval (ZInt 2)) ftval)
	(Ok True)
    testpred
	"y 1 in FT"
	(ZMember (ZCall yval (ZInt 1)) ftval)
	(Undefined [])
    testpred
	"y 1 = x"
	(ZEqual (ZCall yval (ZInt 1)) (ZFree0 x))
	(Undefined [])
    testpred
	"y 2 = x"
	(ZEqual (ZCall yval (ZInt 2)) (ZFree0 x))
	(Ok False)
    testpred
	"x = x"
	(ZEqual (ZFree0 x) (ZFree0 x))
	(Ok True)
    -- TODO: test recursive free types!


main :: IO ()
main =
 do putStrLn "Testing evaluation functions."
    putStrLn "Note: even={2,4,6,8,10}, odd={1,3,5,7,9}, five=5"
    putStrLn ""
    test_set_displays
    test_set_comprehensions
    test_functions
    test_relations
    test_boolean_operators
    test_quantifiers
    test_builtins
    test_lambdas
    test_freetypes
