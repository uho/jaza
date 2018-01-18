module Main
-- This module tests the Unfold functions.
--
-- The tests are woefully inadequate, but that is okay, because
-- now that we have a parser, most of the functions are tested
-- via the top-level user interfaces:  Parse->Unfold->Eval->Display
--
-- Now this module is really only needed for obscure tests
-- that could not be (easily) entered via the parser.
where

import Unfold

main :: IO ()
main =
    do  test_unfold (unfoldexpr env1) e1 e1' "e1"
	test_unfold (unfoldexpr env1) e2 e2' "e2"
	test_unfold (unfoldexpr env1) e3 e3' "e3"


test_unfold :: (Eq b, Show a, Show b) => (a->b) -> a -> b -> String -> IO ()
test_unfold f start expected name
  | f start == expected
      = putStrLn ("  passed unfold test: " ++ name)
  | otherwise
      = do  putStrLn ("  FAILED unfold test: " ++ name)
	    putStrLn ("  Input:    " ++ show start)
	    putStrLn ("  Output:   " ++ show (f start))
	    putStrLn ("  Expected: " ++ show (f start))


----------------------------------------------------------------------
-- Test data
----------------------------------------------------------------------
-- NOTE: global defs must be fully unfolded.

a    = ("a",[])
bp   = ("b",["'"])
fred = ("fred",[])
mary = ("mary",[])
upto = ("\\upto",[])

gset = ("GSet",[])
nil  = ("nil",[])
cons = ("cons",[])
clist= ("CList",[])

clist_type = ZFreeType clist
	      [ZBranch0 nil,
	       ZBranch1 cons (ZCross [ZGivenSet gset,ZVar clist])]

gdefs = [ (gset,  ZGivenSet gset),
	  (fred,  ZInt 42),
	  (mary,  ZTuple [ZInt 3, ZInt 42]),
	  (clist, clist_type)
	]

env1 = empty_env gdefs


e1  = ZCall (ZInt 3) (ZVar fred)       -- not well-typed!
e1' = Ok (ZCall (ZInt 3) (ZInt 42))

e2  = ZTuple [ZVar fred, ZVar mary, ZVar fred]
e2' = Ok (ZTuple [ZInt 42, ZTuple [ZInt 3,ZInt 42],ZInt 42])

e3  = ZSetComp [Choose fred (ZCall (ZVar upto) (ZTuple [ZInt 2, ZVar fred])),
		Check       (ZEqual (ZVar fred) (ZInt 3)),
		Choose a    (ZVar gset),
		Choose bp   (ZVar clist)]
	 (Just (ZTuple [ZVar a, ZVar bp, ZVar fred,
			ZVar mary, ZVar upto, ZVar gset]))

e3' = Ok (ZSetComp
	  [Choose fred (ZIntSet (Just 2) (Just 42)),
	   Check (ZEqual (ZVar fred) (ZInt 3)),
	   Choose a    (ZGivenSet gset),
	   Choose bp   clist_type
	  ]
	  (Just (ZTuple [ZVar a,
			  ZVar bp,
			  ZVar fred,
			  ZTuple [ZInt 3,ZInt 42],
			  ZFunc2 ZUpto,
			  ZGivenSet gset])))


