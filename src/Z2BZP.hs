module Main
-- This module defines a simple translator from Z to BZP
-- (a Prolog-friendly format that is common to B and Z).
where

import AST
import Errors
import Animate
import List
import Char
import Formatter
import IO          -- Standard IO library, so we can catch IO errors etc.
import System

-- These determine how most large output terms are displayed.
pinfo = pinfo_extz 75
output_zexpr = zexpr_stdout pinfo
output_zpred = zpred_stdout pinfo
output_zpara = zpara_stdout pinfo


main :: IO ()
main
  = do  args <- getArgs
	if length args /= 2
	   then putStrLn usage 
	   else doFile (args!!0) (args!!1)

usage = "Usage: z2bzp <spec.zed> <Machine>\n" ++
	"Note: <spec.zed> must contain a schema called <Machine>,\n" ++
	"  which has 'state', 'init', and several operation fields."

-- this reads one .zed file and outputs a .bzp file
doFile :: String -> String -> IO ()
doFile zedfile machname =
    catch
      (do {putStrLn ("Loading '"++zedfile++"' ...");
	   spec <- readFile zedfile;
	   let {(anim1,ok1) = pushfile zedfile spec animator0};
	   checkResult ok1;
	   (anim2,ok2) <- writebztt [machname,machname++".bzp"] anim1;
	   checkResult ok2})
      (\err ->
           do {putStrLn (ioeGetErrorString err);
	       exitWith (ExitFailure 1)})

-- Eg. removeSuffix "test.zed"  gives "test"
removeSuffix =
    reverse . dropWhile (=='.') . dropWhile isAlphaNum . reverse 


checkResult :: Answer -> IO ()
checkResult (Done m) =
    putStrLn m
checkResult (ErrorMsg m) =
    do {putErrorMsg m; exitWith (ExitFailure 2)}
checkResult (ErrorLocns es) =
    do {putStrLn (unlines (map fmtperr es));
	exitWith (ExitFailure 3)}
checkResult (response) =
    do {putStrLn "Error: unknown response for Animate.hs";
	exitWith (ExitFailure 4)}


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


-- Formats a parse error.
fmtperr :: SyntaxError -> String
fmtperr (l,c,m)
  = "Error on line " ++ show l ++ ", column " ++ show c ++ ": " ++ m
