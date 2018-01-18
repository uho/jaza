module Main
where

import Parse
import Lexer
import Test_Strings


-- This optionally shows the result of each successful test (verbose!).
-- Uncomment the non-empty definition if you want to see results.
show_result :: (Show a) => a -> String
show_result v = ""
show_result v = "\t" ++ show v ++ "\n\n"


testparse :: String -> IO ()
testparse zp
  | isOk res  = putStr ("  passed test: " ++ zp ++ "\n" ++
			show_result (fromOk res))
  | otherwise = putStr ("  FAILED TEST: " ++ zp ++ "\n" ++
			error_message res ++ "\n")
  where res = parseZpara zp

-- Test strings are now in Test_Strings.hs

-- Try user defined in_fun

pfile :: String -> IO ()
pfile file
  = do  contents <- readFile file
	putStrLn "Starting parsing"
	let ast = parseZspec contents
	putStrLn "Finished parsing"
	if isOk ast
	  then do putStrLn "Successful parse returns tree:"
		  putStrLn (show (fromOk ast))
	  else do putStrLn (error_message ast)

tut1 = "/home/gregr/isurf/zspecs/z-eves_examples/tut1.zed"
bbook = "bbook.tex"
ai_orig = "ai_orig.zed"
ai_zeta = "ai_zeta.zed"
ai_zans = "ai_zans.zed"
test = "test.zed"

main :: IO ()
main
  = do  foldr1 (>>) (map testparse goodtests)
	putStrLn "\nThe following tests should all fail\n"
	foldr1 (>>) (map testparse failtests)

