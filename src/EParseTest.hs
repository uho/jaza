module EParseTest where

import Monad
-- import ParseLib
import EParseLib


-- This optionally shows the result of each successful test (verbose!).
-- Uncomment the non-empty definition if you want to see results.
show_result :: (Show a) => a -> String
-- show_result v = ""
show_result v = "      Result is: " ++ show v ++ "\n"


test :: (Show b, Eq b) => String -> (a -> b) -> a -> b -> IO ()
test name eval arg expected
  = let actual = eval arg in
    if actual == expected
    then putStr ("  passed test: " ++ name ++ "\n" ++ show_result actual)
    else putStr ("  FAILED TEST: " ++ name ++ "\n" ++
		 "      Expected: " ++ show expected ++ "\n" ++
		 "      But got:  " ++ show actual ++ "\n")


-- special case for applying Parser functions to strings.
testp :: (Show ast, Eq ast) => Parser ast -> String -> [(ast,String)] -> IO ()
testp eval arg result
  = test ("Parsing: " ++ arg) (papply eval) arg result


basic_tests =
  do testp natural "123"            [(123,"")]
     testp (string "where") "where" [("where","")]
     testp ident "a12"              [("a12","")]
     testp ident "12"               []
     testp natural ""               []

compound_tests =
  do testp (natural>>natural) "123  456  "            [(456,"")]
     testp (do{natural; return "nat"}
	    +++ do{i<-ident;junk;return i}) "xy "     [("xy","")]
     testp (do{natural; return "nat"}
	    +++ do{i<-ident;junk;return i}) "124 "    [("nat","")]

loop_tests =
  do testp (many1 integer) "-1 23 45 -51"         [([-1,23,45,-51],"")]

pa, pb :: Parser Int
pa = do symbol "a"
	return 1
     `mplus`
     do symbol "aa"
	return 2

pb = do {symbol "b";return 0}
     `mplus` do {symbol "b";return 1}

pc1 = do {a <- pa;
	  b <- pa;
	  c <- pb;
	  cut;
	  d <- pb;
	  return (a,b,c,d)}   `mplus`
      do {a <- many1(symbol "a");
	  b <- many1(symbol "b");
	  return (9,9,9,9)}

--pc2 = do {i<-integer; j<-integer; symbol ";"; return (i,j)} +++
--      errorRecovery (do {symbol ";"; return (0,0)})

cut_tests =
  do testp (pc1) "aaabb" [((1,2,0,0),""), ((1,2,0,1),"")]

main :: IO ()
main =
  do putStrLn "Doing Basic Tests"
     basic_tests
     putStrLn "Doing Compound Tests"
     compound_tests
     putStrLn "Doing Looping Tests"
     loop_tests
     putStrLn "Doing Cut Tests"
     cut_tests

