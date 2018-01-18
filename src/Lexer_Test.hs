module Main
where

import EParseLib
import Lexer

-- For the purposes of testing only, we define equality over Token.
instance Eq t => Eq (Token t) where
  (Token t1 l1 c1) == (Token t2 l2 c2) = t1==t2 && l1==l2 && c1==c2



-- This optionally shows the result of each successful test (verbose!).
-- Uncomment the non-empty definition if you want to see results.
show_result :: (Show a) => [a] -> String
-- show_result v = ""
show_result v = unlines (map (('\t':) . show) v) ++ "\n"


zlexfile :: String -> IO ()
zlexfile name
  = do  s <- readFile name
	let toks = zlex lexstate0 s
	putStrLn ("Tokens returned from file " ++ name ++ ":")
	putStr (unlines (map show toks))

testlex :: String -> [Token ZToken] -> IO ()
testlex string expected
  = let actual = zlex lexstate0 string
	name   = head(lines string)
	diffs  = [(a,e) | (a,e) <- zip actual expected, a /= e]
	fmtdiff (a,e) = "     Actual: " ++ show a ++ "\n" ++
			"   expected: " ++ show e ++ "\n"
    in
    if diffs == [] && length actual == length expected
    then putStr ("  passed test: " ++ name ++ "\n" ++ show_result actual)
    else putStr ("  FAILED TEST: " ++ name ++ "\n" ++
		 unlines (map fmtdiff (take 10 diffs)))



in1 = unlines
      ["A simple test of \\begin{zed} and \\end{zed} environments.",
       "\\begin{zed} \\t2 [A,B] \\end{zed}"
      ]

out1 :: [Token ZToken]
out1 = [mkToken L_BEGIN_ZED 2 0,
	mkToken L_OPENBRACKET 2 16,
	mkToken (L_WORD "A") 2 17,
	mkToken L_COMMA 2 18,
	mkToken (L_WORD "B") 2 19,
	mkToken L_CLOSEBRACKET 2 20,
	mkToken L_END_ZED 2 22]

in2 = "\\begin{zed} abc == 1+22**d\\_d \\end{zed}"
out2 :: [Token ZToken]
out2 = [mkToken (L_BEGIN_ZED)     1 0,
	mkToken (L_WORD "abc")    1 12,
	mkToken (L_EQUALS_EQUALS) 1 16,
	mkToken (L_NUMBER 1)      1 19,
	mkToken (L_IN_FUN 3 "+")  1 20,
	mkToken (L_NUMBER 22)     1 21,
	mkToken (L_WORD "**")     1 23,
	mkToken (L_WORD "d\\_d")  1 25,
	mkToken (L_END_ZED)       1 30]

in3 = unlines
      ["A standalone schema",
       "\\begin{schema}{fred}  ",
       "\t abc:\\nat_1 ",
       "\\where",
       "   abc \\in \\{ x:\\num | x\\bsup2\\esup < 10 @ x-1 \\} \\\\",
       "   abc \\geq 0% This is a comment",
       "\\end{schema}"
      ]
out3 :: [Token ZToken]
out3 = [mkToken (L_BEGIN_SCHEMA)     2  0,
	mkToken (L_OPENBRACE)     2 14,
	mkToken (L_WORD "fred")   2 15,
	mkToken (L_CLOSEBRACE)    2 19,
	mkToken (L_WORD "abc")    3  9,
	mkToken (L_COLON)         3 12,
	mkToken (L_WORD "\\nat_1")3 13,
	mkToken (L_WHERE)         4  0,
	mkToken (L_WORD "abc")    5  3,
	mkToken (L_IN)            5  7,
	mkToken (L_OPENSET)       5 11,
	mkToken (L_WORD "x")      5 14,
	mkToken (L_COLON)         5 15,
	mkToken (L_WORD "\\num")  5 16,
	mkToken (L_VERT)          5 21,
	mkToken (L_WORD "x")      5 23,
	mkToken (L_BSUP)          5 24,
	mkToken (L_NUMBER 2)      5 29,
	mkToken (L_ESUP)          5 30,
	mkToken (L_IN_REL "<")    5 36,
	mkToken (L_NUMBER 10)     5 38,
	mkToken (L_AT)            5 41,
	mkToken (L_WORD "x")      5 43,
	mkToken (L_HYPHEN)        5 44,   -- or should "-" be an infix?
	mkToken (L_NUMBER 1)      5 45,
	mkToken (L_CLOSESET)      5 47,
	mkToken (L_BACKSLASH_BACKSLASH) 5 50,
	mkToken (L_WORD "abc")    6  3,
	mkToken (L_IN_REL "\\geq")6  7,
	mkToken (L_NUMBER 0)      6 12,
	mkToken (L_END_SCHEMA)    7  0]

in4 = unlines
      ["A standalone schema, indented.",
       "  \\begin{schema}{frog}  ",
       "  x:T ",
       "  \\end{schema}"
      ]
out4 :: [Token ZToken]
out4 = [mkToken (L_BEGIN_SCHEMA)  2  2,
	mkToken (L_OPENBRACE)     2 16,
	mkToken (L_WORD "frog")   2 17,
	mkToken (L_CLOSEBRACE)    2 21,
	mkToken (L_WORD "x")      3  2,
	mkToken (L_COLON)         3  3,
	mkToken (L_WORD "T")      3  4,
	mkToken (L_END_SCHEMA)    4  2]

main :: IO ()
main =
 do testlex in1 out1
    testlex in2 out2
    testlex in3 out3
    testlex in4 out4

