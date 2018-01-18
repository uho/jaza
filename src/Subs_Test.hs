module Main
--
-- $Id: Subs_Test.hs,v 1.5 2003/12/09 20:52:56 marku Exp $
--
-- This module contains test cases for the substitution functions.
-- Just execute 'main' to run all tests.
--
where

import AST
import Errors
import Subs
import Parse
import Unfold
import Formatter

showexpr = zexpr_string (pinfo_extz 80)

-- This optionally shows the result of each successful test (verbose!).
-- Uncomment the non-empty definition if you want to see results.
show_result :: (Show a) => a -> String
--show_result v = ""
show_result v = "      Result is: " ++ show v ++ "\n"

test_free :: String -> String -> IO ()
test_free es vars
  | notOk e
    = putStrLn (error_message e ++ " in:\n" ++ es)
  | notOk vset
    = putStrLn (error_message vset ++ " in:\n" ++ vars)
  | actual == expected
    = putStrLn ("  passed test: free_vars (" ++ es ++ ") = " ++ vars)
  | otherwise
    = putStrLn ("  FAILED TEST: free_vars (" ++ es ++ ")\n" ++
	      "      Expected: " ++ show_varset expected ++ "\n" ++
	      "      But got:  " ++ show_varset actual)
  where
  e = parseZexpr es >>= unfoldexpr testenv :: ErrorOr ZExpr
  vset = parseZexpr vars >>= unfoldexpr testenv :: ErrorOr ZExpr
  actual = free_vars (fromOk e)
  expected = varset (setcontents (fromOk vset))

setcontents :: ZExpr -> [ZExpr]
setcontents (ZSetDisplay vs) = vs
setcontents (ZFSet []) = []

test_subs :: String -> Substitution -> String -> IO ()
test_subs es sub es2
  | notOk e
    = putStrLn (error_message e ++ " in:\n" ++ es)
  | notOk e2
    = putStrLn (error_message e2 ++ " in:\n" ++ es2)
  | actual == expected
    = putStrLn ("  passed test: substitute: " ++ es ++ "\n" ++
		"                     --->  " ++ es2)
  | otherwise
    = putStrLn ("  FAILED TEST: substitute (" ++ es ++ ")\n" ++
	      "      Expected: " ++ showexpr expected ++ "\n" ++
	      "      But got:  " ++ showexpr actual)
  where
  e = parseZexpr es >>= unfoldexpr testenv :: ErrorOr ZExpr
  e2 = parseZexpr es2 >>= unfoldexpr testenv :: ErrorOr ZExpr
  actual = substitute sub (free_vars (fromOk e)) (fromOk e)
  expected = fromOk e2


test_uniquify :: ZExpr -> ZExpr -> IO ()
test_uniquify e expected
  | actual == expected
    = putStrLn ("  passed test: uniquify: " ++ showexpr e ++ "\n" ++
		"                     --->  " ++ showexpr expected)
  | otherwise
    = putStrLn ("  FAILED TEST: uniquify:\n" ++
		"      Expected: " ++ showexpr expected ++ "\n" ++
		"      But got:  " ++ showexpr actual)
  where
  actual = uniquify (free_vars e `union_varset` varset_from_zvars[x,x_1]) e


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

-- (empty_uenv []) [x,x_1,x_2,y,z]

subsx = [(x, ZInt 7)]
subsy = [(y, ZInt 8)]
subsxyz = [(x, ZInt 7),
	   (y, ZInt 8),
	   (z, ZVar x)]

-- a free type
ftval = ZFreeType (make_zvar "FT" []) [ZBranch0 x,
		      ZBranch1 y (ZIntSet (Just 2) (Just 5))]


main :: IO ()
main =
 do putStrLn "Testing free_vars functions..."
    putStrLn ""
    test_free "x"                             "\\{ x \\}"
    test_free "(\\lambda x:y @ x)"            "\\{ y \\}"
    test_free "(\\lambda x:y @ x.z)"          "\\{ y \\}"
    test_free "(\\lambda x:x @ x)"            "\\{ x \\}"
    test_free "(\\lambda x:y @ (\\lambda z:x @ x z))"
					      "\\{y\\}"
    test_free "\\{x:x | x=y \\land x=x_2 @ (x,x_1,y,z)\\}"
					      "\\{ x, y, x_1, x_2, z \\}"
    -- Check that declaration order makes no difference.
    test_free "\\{ x:y; y:x | x=y @ (x,y,z) \\}" "\\{ x, y, z \\}"
    test_free "\\{ y:x; x:y | x=y @ (x,y,z) \\}" "\\{ x, y, z \\}"
    test_free "(\\LET x==z; y==z @ (x,y,z))"  "\\{ z \\}"
    test_free "(\\LET x==y; y==x @ (x,y,z))"  "\\{ x,y,z \\}"
    --
    putStrLn "Testing substitution functions..."
    test_subs "\\{y:x | x=y @ (x,y,z)\\}" subsx
	      "\\{y:7 | 7=y @ (7,y,z)\\}"
    test_subs "\\{x:x | x=y @ (x,y,z)\\}" subsx
	      "\\{x:7 | x=y @ (x,y,z)\\}"
    test_subs "\\{x  :x | x  =y @ (x  ,y,z)\\}" subsxyz
	      "\\{x_1:7 | x_1=8 @ (x_1,8,x)\\}"
    -- check field selection
    test_subs "(\\lambda x:x @ x.y)" subsx
	      "(\\lambda x:7 @ x.y)"
    test_subs "(\\lambda x:x @ x.y)" subsxyz
	      "(\\lambda x:7 @ x.y)"
    -- check that order of declarations does not matter.
    test_subs "\\{x  :y; y:x | x  =y @ (x,  y, z)\\}" subsxyz
	      "\\{x_1:8; y:7 | x_1=y @ (x_1,y, x)\\}"
    test_subs "\\{x  :y; x_1:x | x  =x_1 @ (x,   x_1, y, z)\\}" subsxyz
	      "\\{x_2:8; x_1:7 | x_2=x_1 @ (x_2, x_1, 8, x)\\}"
    test_subs "(\\LET x==y; y==x @ (x,y,z))" subsx
	      "(\\LET x==y; y==7 @ (x,y,z))"
    test_subs "(\\LET x  ==y; y==x @ (x  ,y,z))" subsxyz
	      "(\\LET x_1==8; y==7 @ (x_1,y,x))"

    putStrLn "Testing uniquify functions..."
    -- NOTE: x, x_1 are automatically in the avoid set.
    test_uniquify
      (ZSetComp [Choose x ZUniverse,
		 Check (ZEqual (ZVar x) (ZVar y))]
		(Just (ZTuple [ZVar x, ZVar y])))
      (ZSetComp [Choose x_2 ZUniverse,
		 Check (ZEqual (ZVar x_2) (ZVar y))]
		(Just(ZTuple [ZVar x_2, ZVar y])))
    test_uniquify
      (ZSetComp [Choose x ZUniverse,
		 Check (ZExists [Choose x_2 (ZVar x)]
				(ZEqual (ZVar x) (ZVar x_2)))
		]
		(Just (ZTuple [ZVar x, ZVar y])))
      (ZSetComp [Choose x_2 ZUniverse,
		 Check (ZExists [Choose x_3 (ZVar x_2)]
				(ZEqual (ZVar x_2) (ZVar x_3)))
		]
		(Just(ZTuple [ZVar x_2, ZVar y])))
    test_uniquify
      (ZSetComp [Choose x ZUniverse,
		 Check (ZExists [Choose x (ZVar x)]
				(ZEqual (ZVar x) (ZVar y)))
		]
		(Just (ZTuple [ZVar x, ZVar y])))
      (ZSetComp [Choose x_2 ZUniverse,
		 Check (ZExists [Choose x_3 (ZVar x_2)]
				(ZEqual (ZVar x_3) (ZVar y)))
		]
		(Just(ZTuple [ZVar x_2, ZVar y])))
    test_uniquify
      (ZSetComp [Evaluate x (ZVar y) ZUniverse,
		 Check (ZExists [Choose x (ZVar x)]
				(ZEqual (ZVar x) (ZVar y)))
		]
		(Just (ZTuple [ZVar x, ZVar y])))
      (ZSetComp [Evaluate x_2 (ZVar y) ZUniverse,
		 Check (ZExists [Choose x_3 (ZVar x_2)]
				(ZEqual (ZVar x_3) (ZVar y)))
		]
		(Just(ZTuple [ZVar x_2, ZVar y])))

