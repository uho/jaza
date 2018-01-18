module Main
where

import AST
import Parse
import Pretty
import Formatter
import Test_Strings

-- This test function performs a parse on Z-text then pretty prints
-- and reparses again. The second parse tree
-- generated is tested against the first to ensure they are the same.
testpp :: String -> IO()
testpp s
  | notOk p1     = putStrLn ("ERROR parse 1: " ++ s ++ "\n"
			     ++ error_message p1 ++ "\n")
  | notOk p2     = putStrLn ("ERROR parse 2: " ++ error_message p2 ++ "\n"
			     ++ estr ++ "\n")
  | ast1 /= ast2 = putStrLn ("ERROR trees differ: " ++ s ++ "\n"
			     ++ show ast1 ++ "\n"
			     ++ estr ++ "\n"
			     ++ show ast2 ++ "\n")
  | otherwise    = do  putStrLn ("success: " ++ s ++ "\n")
		       putStr "    "
		       zpara_stdout pinfo ast1
  where
  pinfo = (prefix_lines "    " (pinfo_stdz 50))
  p1 = parseZspec s
  ast1 = head (fromOk p1)
  estr = zpara_string pinfo ast1
  p2 = parseZpara estr
  ast2 = head (fromOk p2)


main :: IO ()
main = foldl1 (>>) (map testpp goodtests)
