module Main
-- This module is a filter that translates Jaza test files
-- (extension .jaza normally) into test files for the CLPS-B solver.
-- Output goes to standard
where

import AST
import Parse
import Unfold
import Errors
import Formatter
import List
import Char
import IO          -- Standard IO library, so we can catch IO errors etc.
import CLPSWrite

-- The internal state of the translator is a list of global defns.
type Translator = [(ZVar, ZExpr)]

prompt1 = ""
prompt2 = ""


-- These determine how most large output terms are displayed.
pinfo = pinfo_extz 75
output_zexpr = zexpr_stdout pinfo
output_zpred = zpred_stdout pinfo
output_zpara = zpara_stdout pinfo


uenv :: Translator -> Env
uenv defs =
    empty_env (defs ++ branches)
    where
    x = string_to_zvar "x"
    branches = concat [map mkbranch bs | (_,ZFreeType n bs) <- defs]
    mkbranch (ZBranch0 s) =
	(s, ZFree0 s)
    mkbranch (ZBranch1 s dom) =
	-- a function, expressed as a set comprehension
	(s, ZSetComp [Choose x dom] (Just (ZTuple[ZVar x, ZFree1 s (ZVar x)])))


-- process_paras spec newp.
--
--  This converts the parsed paragraphs into a list of defns.
--
process_paras :: Translator -> [ZPara] -> ErrorOr Translator
process_paras spec []
  = return spec
process_paras spec (p@(ZGivenSetDecl s) : ps)
  = do	let newp = (s, ZGivenSet s)
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (p@(ZSchemaDef name se) : ps)
  = do  gfs <- unfoldsexpr (uenv spec) se
	let newp = ( make_schema_name name,
		     ZESchema (ZSchema gfs) )
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (p@(ZAbbreviation n e) : ps)
  = do  ue <- unfoldexpr (uenv spec) e
	let newp = ( n, ue )
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (p@(ZFreeTypeDef n bs) : ps)
  = do  ue <- unfoldexpr (uenv spec) (ZFreeType n bs)
	let newp = ( n, ue )
	newspec <- adddefn newp spec
	process_paras newspec ps
process_paras spec (para : ps)
  = fail ("Not implemented yet: " ++ show para)

adddefn a b = return (a:b)


main :: IO ()
main
  = do  putStrLn "% CLPS-B tests translated from Jaza tests."
	putStrLn ""
	get_cmd []


-- Translates a given Z predicate.
checkpredicate :: String -> String -> Translator -> IO ()
checkpredicate testfunc s env
  | isOk result  = putStrLn (":- " ++ testfunc ++ "(" ++ term ++ ").")
  | otherwise    = putStrLn ("% " ++ error_message result)
  where
  result = do pred <- parseZpred s
	      upred <- unfoldpred (uenv env) pred
	      clps_pred emptyTypeEnv upred
	      -- evalpred (opt_pred (oenv anim) upred) (evalenv anim)
  term = show_clpsterm (fromOk result)


get_cmd :: Translator -> IO ()
get_cmd anim
  = do  -- TODO: this catch does not work with Hugs.  Find out why.
	s <- catch (getLineEdit prompt1) (\err -> return "quit")
	let (cmd,rest) = span (not . isSpace) (dropWhile isSpace s)
	get_cmd2 cmd rest anim


-- This handles reading any extra lines of input, until a complete
-- command has been read.  It counts opening and closing brackets
-- '([{ ... }])' and keeps reading lines until enough closing
-- brackets have been found.
-- Also, if cmd == a '\begin{...}' construct then reading continues
-- until a similar '\end{...}' is found.
-- It handles empty lines, comments and 'echo' lines itself, but
-- passes other commands to do_cmd.
get_cmd2 :: String -> String -> Translator -> IO ()
get_cmd2 "" ""    anim = get_cmd anim  -- empty command line
get_cmd2 "%" _    anim = get_cmd anim  -- a comment line
get_cmd2 "echo" s anim =               -- echoes the rest of the line
    do  putStrLn (":- format(" ++ show s ++ ", []),nl.")
	get_cmd anim
get_cmd2 cmd s anim
    | isPrefixOf "\\begin{" cmd
      = get_para (reverse endcmd)
	  [cmd ++ s]  -- don't drop spaces here, so that column
		      -- positions in error messages are more accurate.
	  anim
    | otherwise
      = get_cmd3 cmd
	  [reverse (dropWhile isSpace (reverse s))] -- take spaces off end.
	  (length (filter openbracket s) - length (filter closebracket s))
	  anim
    where
    endcmd = "\\end{" ++ takeWhile isAlpha (drop (length "\\begin{") cmd)
		      ++ "}"

-- This reads one paragraph of Z input (upto an \end{...} command).
get_para :: String -> [String] -> Translator -> IO ()
get_para revendcmd ("EOF":_) anim =
    return ()
get_para revendcmd sofar anim
    | revendcmd `isPrefixOf` (dropWhile isSpace (reverse (head sofar))) =
	do_cmd "begin" (unlines (reverse sofar)) anim
    | otherwise =
	do  {s <- getLineEdit prompt2;
	     get_para revendcmd (s:sofar) anim}

get_cmd3 :: String -> [String] -> Int -> Translator -> IO ()
-- 'sofar' is a list of the input lines for this command (in reverse order).
-- The Int argument is the number of unclosed brackets in 'sofar'.
get_cmd3 cmd sofar opened anim
    | opened <= 0
      = do_cmd cmd (dropWhile isSpace (concatMap ('\n':) (reverse sofar))) anim
    | otherwise
      = do  s <- getLineEdit prompt2
	    let opened2 = opened + length (filter openbracket s)
				 - length (filter closebracket s)
	    get_cmd3 cmd (s:sofar) opened2 anim

openbracket :: Char -> Bool
openbracket '(' = True
openbracket '[' = True
openbracket '{' = True
openbracket  _  = False

closebracket :: Char -> Bool
closebracket ')' = True
closebracket ']' = True
closebracket '}' = True
closebracket  _  = False



-- This processes each command.
--    Pre: The 'cmd' and 'args' strings must have no whitespace
--         at the start or end of the string.
do_cmd :: String -> String -> Translator -> IO ()
do_cmd cmd args anim
  | cmd == "quit" =
      return ()
  | cmd == "begin" && isOk paras =
      get_cmd (fromOk paras)
  | cmd == "begin" =
      do  putStrLn (error_message paras)
	  get_cmd anim
  | cmd == "checktrue" =
      do  checkpredicate "checktrue" args anim
	  get_cmd anim
  | cmd == "checkundef" =
      do  checkpredicate "checkundef" args anim
	  get_cmd anim
  | otherwise =
      do  putStrLn "Unknown/illegal command."
	  get_cmd anim
  where
  -- rd is used to read input values from user
  rd p = getLineEdit ("    Input " ++ p ++ " = ")
  paras = do  paras0 <- parseZpara args
	      process_paras anim paras0


putErrorMsg :: ErrorMsg -> IO ()
putErrorMsg m =
    do  sequence_ (map putMsgPart m)
	putStrLn ""

putMsgPart :: MsgPart -> IO ()
putMsgPart (MStr s)   = putStr s
putMsgPart (MNewLine) = putStrLn ""
putMsgPart (MExpr e)  = output_zexpr e
putMsgPart (MPred p)  = output_zpred p
putMsgPart (MVars vs) = putStr (show_zvars vs)


-- Strips leading and trailing whitespace
canonical :: String -> String
canonical = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- Left justifies a string
ljustify :: Int -> String -> String
ljustify n s = s ++ take (max 0 (n - length s)) (repeat ' ')

-- Formats a parse error.
fmtperr :: SyntaxError -> String
fmtperr (l,c,m)
  = "Error on line " ++ show l ++ ", column " ++ show c ++ ": " ++ m

-- Formats a command help message
fmtcmd :: String -> String -> String
fmtcmd cmd msg = "    " ++ ljustify 24 cmd ++ msg


getLineEdit :: String -> IO String
getLineEdit prompt =
    do  putStr prompt
	getLine
