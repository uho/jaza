module Main
-- This module defines a simple textual user interface
-- for the animator.  Call 'main' to start it up, then type 'help'.
where

import AST
import Errors
import Animate
import List
import Char
import Formatter
import IO          -- Standard IO library, so we can catch IO errors etc.

prompt1 = "JAZA> " -- prompt for each command
prompt2 = "      " -- a visible, but cut/pastable, prompt for multiline input

-- These determine how most large output terms are displayed.
pinfo = pinfo_extz 75
output_zexpr = zexpr_stdout pinfo
output_zpred = zpred_stdout pinfo
output_zpara = zpara_stdout pinfo


main :: IO ()
main
  = do  putStrLn "Welcome to Jaza, version 1.1.  June 2005"
	putStrLn "Copyright(C) 1999-2005 Mark Utting (marku@cs.waikato.ac.nz)."
	putStrLn "Jaza comes with ABSOLUTELY NO WARRANTY (see file COPYING)."
	putStrLn "This is free software, and you are welcome to redistribute"
	putStrLn "it under certain conditions (see file COPYING)."
	putStrLn ""
	putStrLn "Type `help' to see the available commands."
	putStrLn ""
	get_cmd animator0


get_cmd :: Animator -> IO ()
get_cmd anim
  = do  -- TODO: this catch does not work with Hugs.  Find out why.
	s <- catch (getLineEdit prompt1) (\err -> return "quit")
	get_cmd2 (dropWhile isSpace s) anim


-- This handles reading any extra lines of input, until a complete
-- command has been read.  It counts opening and closing brackets
-- '([{ ... }])' and keeps reading lines until enough closing
-- brackets have been found.
-- Also, if cmd == a '\begin{...}' construct then reading continues
-- until a similar '\end{...}' is found.
-- It handles empty lines, comments and 'echo' lines itself, but
-- passes other commands to do_cmd.
get_cmd2 :: String -> Animator -> IO ()
get_cmd2 ""       anim = get_cmd anim  -- empty command line
get_cmd2 ('%':_)  anim = get_cmd anim  -- a comment line
get_cmd2 ('e':'c':'h':'o':' ':rest) anim =
    done_cmd(anim, Done rest)   -- echoes the rest of the line
get_cmd2 (';':rest)  anim =
    get_cmd3 ";" [rest] openbrackets anim
    where
    openbrackets = length(filter openbracket rest)
		   - length(filter closebracket rest)
get_cmd2 cmd anim
    | isPrefixOf "\\begin{" cmd
      = get_para (reverse endcmd) [cmd] anim
    | otherwise
      = get_cmd3 word
	  [reverse (dropWhile isSpace (reverse rest))] -- take spaces off end.
	  (length(filter openbracket rest) - length(filter closebracket rest))
	  anim
    where
    (word,rest) = span isAlpha cmd
    endcmd = "\\end{" ++ takeWhile isAlpha (drop (length "\\begin{") cmd)
		      ++ "}"

-- This reads one paragraph of Z input (upto an \end{...} command).
get_para :: String -> [String] -> Animator -> IO ()
get_para revendcmd ("EOF":_) anim =
    return ()
get_para revendcmd sofar anim
    | revendcmd `isPrefixOf` (dropWhile isSpace (reverse (head sofar))) =
	done_cmd (pushpara (unlines (reverse sofar)) anim)
    | otherwise =
	do  {s <- getLineEdit prompt2;
	     get_para revendcmd (s:sofar) anim}

get_cmd3 :: String -> [String] -> Int -> Animator -> IO ()
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


help =
  ["Available commands:",
   fmtcmd "quit"                   "Exit the animator",
   fmtcmd "\\begin{..}..\\end{..}" "Enter a Z paragraph",
   fmtcmd "load filename"          "Load a Z specification from a file",
   fmtcmd "show"                   "Display a summary of whole spec.",
   fmtcmd "show N"                 "Display unfolded definition of N",
   fmtcmd "pop"                    "Delete last Z paragraph",
   fmtcmd "reset"                  "Reset the whole specification",
   fmtcmd "do S"                   "Execute schema expression S",
   fmtcmd "; S (or 'then S')"      "Compose schema S with the current state",
   fmtcmd "next (or 'n')"          "Show the next state of current schema",
   fmtcmd "curr"                   "Reshow the current state",
   fmtcmd "prev (or 'p')"          "Show the previous state",
   fmtcmd "state N"                "Show the N'th state",
   fmtcmd "undo"                   "Undo the current operation",
   fmtcmd "eval E"                 "Evaluate expression E",
   fmtcmd "evalp P"                "Evaluate predicate P",
   fmtcmd "why"      "Show the optimized code of the most recent evaluation",
   fmtcmd "checktrue P"     "Check that P is true, else give an error.",
   fmtcmd "checkundef P"    "Check that P is undefined, else give an error.",
   fmtcmd "echo msg..."            "Echo msg (the rest of the line)",
   fmtcmd "set"                    "Show current settings",
   fmtcmd "set setsize NNN"        "Set maximum set size to NNN",
   fmtcmd "set searchsize NNN"     "Set maximum search space to NNN",
   fmtcmd "writebztt machine file" "Write a state machine in BZTT syntax",
   fmtcmd "help"                   "Display this message",
   fmtcmd "% comment"              "(Ignored)"
  ]


-- This processes each command.
--    Pre: The 'cmd' and 'args' strings must have no whitespace
--         at the start or end of the string.
-- For convenience, the Hugs ":load" command is similar to "quit".
--  (I often forget to get out of the animator before doing a
--   ":load" command while developing the animator in Emacs).
do_cmd cmd args anim
  | cmd == "quit" =
      return ()
  | cmd == ":load" =
      do {putStrLn ("ERROR \"" ++ args
		    ++ "\" (Line 1): You did not quit JAZA."
		    ++ "\nDo the load again...");
	  return ()}
  | cmd == "help" && args =="" =
      do {putStr (unlines help); get_cmd anim}
  | cmd == "load" =
      catch
	  (do {putStrLn ("Loading '"++args++"' ...");
	       spec <- readFile args;
	       done_cmd (pushfile args spec anim)})
	  (\err ->
	      do {putStrLn (ioeGetErrorString err);
		  get_cmd anim})
  | cmd == "pop" && args == "" =
      done_cmd (poppara anim)
  | cmd == "reset" && args == "" =
      done_cmd (resetanimator anim)
  | cmd == "show" =
      done_cmd (anim, showinfo args)
  | cmd == "do" =
      do  let (anim2,ans) = execschema args anim
	  if isDone ans
	     then done_cmd(showstate 0 anim2)
	     else done_cmd(anim2,ans)
  | cmd == "then" || cmd == ";" =
      do {(anim2,ans) <- compose_schema rd args anim;
	  if isDone ans
	    then done_cmd (showstate 0 anim2)
	    else done_cmd (anim2,ans)}
  | cmd == "next" || cmd == "n" =
      done_cmd (showstate (currstate anim + 1) anim)
  | cmd == "curr" =
      done_cmd (showstate (currstate anim) anim)
  | cmd == "prev" || cmd == "p" =
      done_cmd (showstate (currstate anim - 1) anim)
  | cmd == "state" && all isDigit args =
      done_cmd (showstate (read args) anim)
  | cmd == "undo" && args == "" =
      done_cmd (popstate anim)
  | cmd == "why" && args == "" =
      done_cmd (anim, showcode anim)
  | cmd == "code" && args == "" =
      done_cmd (anim, Done "'code' has been renamed to 'why'.")
  | cmd == "eval" =
      done_cmd (evalexpression args anim)
  | cmd == "evalp" =
      done_cmd (evalpredicate args anim)
  | cmd == "checktrue" =
      do  let (anim2,ans) = evalpredicate args anim
	  checktrue ans args
	  get_cmd anim2
  | cmd == "checkundef" =
      do  let (anim2,ans) = evalpredicate args anim
	  checkundef ans args
	  get_cmd anim2
  | cmd == "set" =
      do_settings (words args) anim
  | cmd == "writebztt" =
      do  (anim2,ans) <- writebztt (words args) anim
	  done_cmd (anim2,ans)
  | otherwise =
      do  putStrLn "Unknown/illegal command."
	  get_cmd anim
  where
  -- rd is used to read input values from user
  rd p = getLineEdit ("    Input " ++ p ++ " = ")
  showinfo "" = showspec anim
  showinfo s = showunfolded args anim

-- This prompts for an entire Z paragraph on standard input.
-- First argument is the end command that terminates the paragraph
-- Second argument is the lines of input so far (in reverse order!).
do_paragraph :: String -> [String] -> Animator -> IO ()
do_paragraph endcmd cmds anim
  | isSuffixOf endcmd (head cmds)
    = done_cmd (pushpara (unlines (reverse cmds)) anim)
  | otherwise
    = do s <- getLineEdit prompt2
	 do_paragraph endcmd (canonical s : cmds) anim

do_settings :: [String] -> Animator -> IO ()
do_settings [] anim =
    do  let ss = ["\t" ++ k ++ "    \t" ++ show (get_setting k anim)
		  | k <- settings]
	putStrLn ("Current settings are:\n" ++ unlines ss)
	get_cmd anim
do_settings [key,val] anim
    | not (all isDigit val) =
	done_cmd (anim, errstr ("Illegal value in `set' command: " ++ val))
    | not (key `elem` settings) =
	done_cmd (anim, errstr ("Illegal command: set " ++ key))
    | otherwise =
	done_cmd (set_setting key (read val) anim)
do_settings _ anim =
    done_cmd (anim, errstr "Illegal set command")


done_cmd :: (Animator, Answer) -> IO ()
done_cmd (anim, Done s)       = do {putStrLn s; get_cmd anim}
done_cmd (anim, ErrorMsg m)   = do {putErrorMsg m; get_cmd anim}
done_cmd (anim, ErrorLocns es)= do {putStrLn (unlines (map fmtperr es));
				    get_cmd anim}
done_cmd (anim, Value v)      = do {output_zexpr v; get_cmd anim}
done_cmd (anim, Pred p)       = do {output_zpred p; get_cmd anim}
done_cmd (anim, BoolValue v)  = do {putStrLn (show v); get_cmd anim}
done_cmd (anim, Defn v)       = do {output_zpara v; get_cmd anim}
done_cmd (anim, SchemaCode name (ZSetComp gfs (Just (ZBinding bs))) depth) =
    do  -- output_zpara (ZSchemaDef (ZSPlain name) (ZSchema gfs))
	-- Here is a alternative to the above line, that numbers the lines.
	putStrLn ("\\begin{schema}{"++name++"}")
        mapM (putStrLn . fmtgfs) (zip [1..] gfs) 
	putStrLn "\\end{schema}"
	let hidden = genfilt_names gfs \\ (map fst bs)
	if hidden == []
	   then putStr ""
	   else putStrLn ("hiding: " ++ show_zvars hidden)
	if depth < length gfs
	  then putStrLn("The maximum number of true constraints was "
			++ show depth ++ ".")
	  else putStr ""
	get_cmd anim

fmtgfs :: (Int,ZGenFilt) -> String
fmtgfs (n,Check ZFalse{reason=(r:rs)}) = 
   show n ++ "  " ++ "false  \\because{"
	++ concat[zpred_string pinfo p ++ "; " | p<- r:rs]
	++ "}"
fmtgfs (n,gf) =
   show n ++ "  " ++ zgenfilt_string pinfo gf


checktrue, checkundef :: Answer -> String -> IO ()
checktrue (BoolValue True) pred = return ()  -- ignore successful results
checktrue ans pred = checkpred ans ("checktrue " ++ pred)

checkundef (ErrorMsg m) pred
    | isUndefMsg m = return ()  -- ignore successful results
checkundef ans pred = checkpred ans ("checkundef " ++ pred)

checkpred :: Answer -> String -> IO ()
-- this handles the common cases of checktrue and checkundef
checkpred (BoolValue b) cmd =
    putStrLn ("Error: " ++ show b ++ " returned from: " ++ cmd)
checkpred (ErrorMsg m) cmd =
    do  putStrLn ("Error in: " ++ cmd)
	putErrorMsg m
checkpred (ErrorLocns es) cmd =
    do  putStrLn ("Error in: " ++ cmd)
	putStr (unlines (map fmtperr es))
checkpred _ cmd =
    -- This should never happen.
    putStrLn ("Error: Unexpected animator answer from: " ++ cmd)


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
	hFlush stdout   -- needed with GHC.
	getLine
--    do  Just s <- readline prompt
--	if null s
--	   then return ()
--	   else addHistory s
--	return s
