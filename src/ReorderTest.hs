module Main
--
-- $Id: ReorderTest.hs,v 1.1 2005/03/26 12:57:58 marku Exp $
--
-- This module contains test cases for the functions in Reorder.hs
-- Just execute 'main' to run all tests.
--
where

import AST
import Errors
import Parse
import Unfold
import Formatter
import Reorder

showexpr = zexpr_string (pinfo_extz 80)

-- This parses an expression
expr :: String -> ZExpr
expr es
  | notOk e = error (error_message e)
  | otherwise = fromOk e
  where
  e = parseZexpr es >>= unfoldexpr testenv :: ErrorOr ZExpr


test :: String -> ZExpr -> ZExpr -> IO ()
test name actual expected
  | actual == expected
    = putStrLn ("  passed test: " ++ name)
  | otherwise
    = putStrLn ("  FAILED TEST: " ++ name ++ "\n" ++
		"      Expected: " ++ showexpr expected ++ "\n" ++
		"      But got:  " ++ showexpr actual)

----------------------------------------------------------------------
-- Test Data
----------------------------------------------------------------------
x = make_zvar "x" []
x_1 = make_zvar "x" ["_1"]
x_2 = make_zvar "x" ["_2"]
x_3 = make_zvar "x" ["_3"]
y = make_zvar "y" []
z = make_zvar "z" []

-- a trick here: we push x=ZVar x so that when we read in
--  variable names, they evaluate to themselves, then we
--  can compare them with the results of the test. 
--  In other words, this just gives a convenient way of reading vars.
testenv = envPushLocals
	  [ (x,   ZVar x),
	    (x_1, ZVar x_1),
	    (x_2, ZVar x_2),
	    (y,   ZVar y),
	    (z,   ZVar z)]
	  dummy_eval_env

range_2_10  = ZIntSet (Just 2) (Just 10)
range_inf_9 = ZIntSet Nothing (Just 9)
range_3_inf = ZIntSet (Just 3) Nothing

lt8 = ZGenerator ZLessThan (ZInt 8)
leq8 = ZGenerator ZLessThanEq (ZInt 8)
gt4 = ZGenerator ZGreaterThan (ZInt 4)
geq4 = ZGenerator ZGreaterThanEq (ZInt 4)

main :: IO ()
main =
 do putStrLn "Testing range function..."
    test "range0"
             (range [])
	     (ZIntSet Nothing Nothing)
    test "range_2_10"
             (range [range_2_10])
	     range_2_10
    test "range_3_10"
             (range [range_2_10, range_3_inf])
	     (ZIntSet (Just 3) (Just 10))
    test "range_3_9"
             (range [range_inf_9, range_2_10, range_3_inf])
	     (ZIntSet (Just 3) (Just 9))
    test "range_5_7"
             (range [range_inf_9, lt8, gt4])
	     (ZIntSet (Just 5) (Just 7))
    test "range_4_8"
             (range [range_3_inf, geq4, leq8])
	     (ZIntSet (Just 4) (Just 8))





