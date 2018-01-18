module Errors
--
-- $Id: Errors.hs,v 1.14 2002/04/12 22:49:10 marku Exp $
--
-- Exception Handling
--
-- The ErrorOr type is used as a wrapper for most of the evaluator results.
-- It provides a simple form of exception handling for evaluation errors.
-- Semantically, if an evaluation function returns one of the errors,
-- that is equivalent to returning bottom (meaning 'result is unknown,
-- uncomputable, too hard too compute, or erroneous').
-- Otherwise, it returns Ok(value).
--
-- In other words, the ErrorOr type is similar to the Maybe type in
-- the Haskell Prelude, but with more kinds of errors, and better messages.
--
where
import Monad
import AST

infixr 1 $?
infixr 1 ?$
infixr 1 ?$?
infixr 0 `orError`

data ErrorOr a
  = Ok a                    -- A correct result!
  | Fail
  | Undefined ErrorMsg      -- Undefined expression
  | TooBig BigInfo ErrorMsg -- too difficult, but recoverable
  | Impossible ErrorMsg     -- evaluation is impossible (eg. not implemented)
  | IllFormed ErrorMsg      -- input spec is incorrectly typed or ill-formed.
  | SyntaxErrors [SyntaxError] -- input spec had syntax errors
  deriving (Eq,Show)

type ErrorMsg = [MsgPart]

-- Error messages contain a list of these values, so that
-- the formatting of the message can be done by the displayer.
data MsgPart
    = MStr String
    | MNewLine
    | MExpr ZExpr
    | MPred ZPred
    | MVars [ZVar]
      deriving (Eq,Show)

data BigInfo
    = SearchError{estimated::SetSize,
		  currlimit::Integer,
		  currsearch::SearchSpace}
    | SetSizeError{estimated::SetSize,
		   currlimit::Integer}
      deriving (Eq, Ord)

data SetSize
    = Approx Integer   -- represents integers:  0..(huge-1)  (see SetSize.hs)
    | Huge             -- represents all larger integers, including infinity.
      deriving (Eq, Ord)

instance Show BigInfo where
    showsPrec d e@SearchError{} r =
	"search space is too big (~ " ++ show (estimated e) ++
	", but current limit=" ++ show (currlimit e) ++ ")\n\t" ++
	unwords (map fmtzvarsize (reverse (currsearch e))) ++
	r
	where
	fmtzvarsize (v,s) = show_zvar v ++ ":" ++ show s
    showsPrec d e@SetSizeError{} r =
	"set is too big to enumerate (~ " ++ show (estimated e) ++
	" but current limit=" ++ show (currlimit e) ++ ")" ++
	r

instance Show SetSize where
    showsPrec d (Approx n) r = show n ++ r
    showsPrec d Huge r = "huge" ++ r

-- Use this to tack on context information about where an error occurs.
error_context :: ErrorOr a -> ErrorMsg -> ErrorOr a
error_context (Ok a) m           = (Ok a)
error_context (Undefined ms) m   = Undefined (ms ++ m)
error_context (TooBig why ms) m  = TooBig why (ms ++ m)
error_context (Impossible ms) m  = Impossible (ms ++ m)
error_context (IllFormed ms) m   = IllFormed (ms ++ m)
error_context (SyntaxErrors s) m = SyntaxErrors s

-- This must be the same as ParseError in EParseLib.hs
type SyntaxError = (Int, Int, String)    -- (line,column,msg)

-- For many applications, it is convenient to use monad notation
-- to hide the error handling.  A limitation of this approach is that
-- the monad returns the first error that arises, regardless of the
-- kind of error.  For more sophisticated applications, it is sometimes
-- better/necessary to use the explicit error-combining combinators
-- defined later in this module.
--
instance Functor ErrorOr where
  fmap f (Ok v) = Ok (f v)
  fmap f err    = sameError err

instance Monad ErrorOr where
  return v = Ok v
  fail msg = Impossible [MStr msg]
  p >>= q  = if isOk p then q (fromOk p) else sameError p


isOk :: ErrorOr a -> Bool
isOk (Ok _) = True
isOk _      = False

notOk :: ErrorOr a -> Bool
notOk = not . isOk

fromOk :: ErrorOr a -> a
fromOk (Ok a) = a

isUndef (Undefined _) = True
isUndef _ = False


-- This converts all kinds of errors into a string.
-- Some applications might want more sophisticated formatting,
-- (so should do this translation themselves), but this is often
-- sufficient for simple output formats.
error_message :: ErrorOr t -> String
error_message (Undefined ms)
  = "Undefined result: " ++ concatMap format_msg ms
error_message (TooBig reason ms)
  = "Problem: " ++ show reason ++ " " ++ concatMap format_msg ms
error_message (Impossible ms)
  = "Problem: " ++ concatMap format_msg ms
error_message (IllFormed ms)
  = "Type Error: " ++ concatMap format_msg ms
error_message (SyntaxErrors errs)
  = tail (concat ["\nSyntax Error: " ++ format_syntax_error e | e <- errs])

format_msg :: MsgPart -> String
format_msg (MStr s)   = s
format_msg MNewLine   = "\n"
format_msg (MExpr e)  = show e
format_msg (MPred p)  = show p
format_msg (MVars vs) = show_zvars vs

-- TODO: put this into an Emacs-compatible format (with filename!)
format_syntax_error :: SyntaxError -> String
format_syntax_error (l,c,msg)
  = "Line " ++ show l ++ ", Column " ++ show c ++ ": " ++ msg


-- These are basically like $ (function application).
-- However, they pass errors through in a strict fashion,
-- from whatever side they have a ? on.
-- Eg. a $? b  returns (a b), but if b is an error, that error is returned.
--     a ?$ b  returns (a b), but if a is an error, that error is returned.

(?$?) :: ErrorOr (a -> b) -> ErrorOr a -> ErrorOr b
(?$?) (Ok f)        (Ok a)         = Ok (f a)
(?$?) (Ok f)        a              = sameError a
(?$?) f             a              = mergeErrors f a

($?) :: (a -> b) -> ErrorOr a -> ErrorOr b
($?) f (Ok arg) = Ok (f arg)
($?) f err      = sameError err

(?$) :: ErrorOr (a -> b) -> a -> ErrorOr b
(?$) (Ok f) arg = Ok (f arg)
(?$) err    _   = sameError err


-- This merges two errors, giving priority to certain errors.
-- Pre: first argument must be an error (second one need not be).
-- Post: always return a non-Ok error value.
mergeErrors :: ErrorOr a -> ErrorOr b -> ErrorOr c
mergeErrors (Undefined a) (Undefined b) =
    Undefined (a ++ [MNewLine,MStr "and: "] ++ b)
mergeErrors (SyntaxErrors a) (SyntaxErrors b) = SyntaxErrors (a++b)
mergeErrors (SyntaxErrors e) _                = SyntaxErrors e
mergeErrors _                (SyntaxErrors e) = SyntaxErrors e
mergeErrors (IllFormed s)    _                = IllFormed s
mergeErrors _                (IllFormed s)    = IllFormed s
mergeErrors (Impossible m)   _                = Impossible m
mergeErrors _                (Impossible m)   = Impossible m
mergeErrors (TooBig a ma) (TooBig b mb)
    | a <= b = TooBig a ma
    | a > b  = TooBig b mb
mergeErrors err1             err2             = sameError err1


-- This is only necessary because the typechecker thinks that
-- the default cases above have type ErrorOr a -> ErrorOr a,
-- but we actually want ErrorOr a -> ErrorOr b.
-- This definition must be the identity on all cases except Ok.
sameError :: ErrorOr a -> ErrorOr b
sameError (Undefined m)   = Undefined m
sameError (TooBig w m)    = TooBig w m
sameError (Impossible m)  = Impossible m
sameError (IllFormed m)   = IllFormed m
sameError (SyntaxErrors e)= SyntaxErrors e


-- This is used as an infix operator:   Ok mainresult `orError` err
-- The usual behaviour is to return Ok mainresult,
-- but if err is some kind of error, it is returned instead.
orError :: ErrorOr a -> ErrorOr b -> ErrorOr a
orError a (Ok _) = a
orError _ err    = sameError err

-- Some convenient functions for raising errors.
-- undef :: ZExpr -> ErrorOr a
-- Pre: e should be the function call, or expression, that is undefined.
undef e = Undefined [MExpr e]

searcherror :: SetSize -> Integer -> SearchSpace -> ErrorMsg -> ErrorOr ()
searcherror s limit ss msg =
    TooBig SearchError{estimated=s, currlimit=limit, currsearch=ss} msg

setsizeerror :: SetSize -> Integer -> ErrorMsg -> ErrorOr ()
setsizeerror s limit msg =
    TooBig SetSizeError{estimated=s,currlimit=limit} msg

asserterror msg = Impossible [MStr ("Internal evaluator error: " ++ msg)]

-- These functions raise an error when a given boolean test fails.
typecheck :: Bool -> String -> ErrorOr ()
typecheck True  _   = Ok ()
typecheck False msg = IllFormed [MStr "Type Error: ", MStr msg]

misccheck :: Bool -> String -> ErrorOr ()
misccheck True  _   = Ok ()
misccheck False msg = IllFormed [MStr msg]

-- Use this when checking internal consistency conditions.
assertcheck :: Bool -> String -> ErrorOr ()
assertcheck True  msg = Ok ()
assertcheck False msg = asserterror msg



multiply_search_space :: ZVar -> Int -> Env -> ErrorOr Env
multiply_search_space v n env =
    -- Pre: 0 <= n
    do  let newsize = fromIntegral n * search_space env
	if newsize > max_search_space env
	   then searcherror (Approx newsize)
		    (max_search_space env)
		    ((v,n) : search_vars env) []
	   else Ok ()
	return env{ search_space = newsize,
		    search_vars = (v,n):search_vars env }

