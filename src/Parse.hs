module Parse
  (-- For convenience, we export some error handling functions
   -- (from module Errors) that are needed to interpret parser results.
   ErrorOr(..),
   isOk,  notOk, fromOk, error_message,
   -- These are the top-level parsers, of type String -> ErrorOr ast
   parseZspec,   -- a whole spec
   parseZpara,   -- one paragraph only
   parseZsexpr,  -- a single schema expression (no \begin..\end needed)
   parseZexpr,   -- a single expression (no \begin..\end needed)
   parseZpred,   -- a single predicate (no \begin..\end needed)
   parseZident,  -- a single identifier (perhaps decorated)
   -- This lower-level paragraph-parsing function is for testing only
   pzp
  )
-- This Z parser is based closely upon the LL(infinity) Z grammar
-- in the paper: "A Concrete Z Grammar", PRG-TR-22-95,
-- by Peter T. Breuer and Jonathan P. Bowen, and the (more informal)
-- grammar in the appendix of "The Z Reference Manual" (Edition 2),
-- by J. M. Spivey, 1992 Prentice Hall.
--
-- It is reasonably complete, except that generics are not handled
-- and global definitions and let definitions cannot (yet) define
-- operators.
--
-- Note: paragraphs are flattened as much as possible.
--       In other words, a given set declaration, [A,B,C] is expanded
--       out into three separate given set declarations.  Similarly,
--       abbreviations (a==...), free type definitions etc. are all
--       expanded out into separate paragraphs.  This makes the
--       abstract syntax trees simpler (each paragraph generally
--       defines just one name).
--       However, axdef and gendef paragraphs are not expanded,
--       even when they define multiple names, because we assume that
--       the names and associated predicates are grouped together for
--       some semantic reason.  E.g. It is good style for all the
--       constraints on a declared constant to be given in the axdef
--       paragraph where the constant is declared.
where

import EParseLib
import Lexer
import AST
import Monad
import Errors


-- This shows you the whole result (all parses and all errors)
-- It is for debugging and testing only.
pzp :: String -> ParseResult ZToken ZSpec
pzp = epapply zparagraph . zlex lexstate0


check_parse :: ParseResult ZToken ast -> ErrorOr ast
check_parse ParseResult{parses=[], besterror=err}
  = SyntaxErrors [mkParseError err]
check_parse ParseResult{parses=[(t,[],[])]}
  = Ok t
check_parse ParseResult{parses=[(t,errs,[])]}
  = SyntaxErrors errs
check_parse ParseResult{parses=[(t,[],toks)], besterror=err}
  = SyntaxErrors [mkParseError (toks,"valid syntax upto here"),
		  mkParseError err]
check_parse ParseResult{}
  = SyntaxErrors [(0,0,"ambiguous parse!")]


parseZspec :: String -> ErrorOr ZSpec
parseZspec = check_parse . epapply zspec . zlex lexstate0

parseZpara :: String -> ErrorOr ZSpec
parseZpara = check_parse . epapply zparagraph . zlex lexstate0

parseZsexpr :: String -> ErrorOr ZSExpr
parseZsexpr = check_parse . epapply zschema_exp . zlexz 0 lexstate0

parseZexpr :: String -> ErrorOr ZExpr
parseZexpr = check_parse . epapply zexpression . zlexz 0 lexstate0

parseZpred :: String -> ErrorOr ZPred
parseZpred = check_parse . epapply zpredicate . zlexz 0 lexstate0

parseZident :: String -> ErrorOr ZVar
parseZident = check_parse . epapply zident . zlexz 0 lexstate0



zspec :: EParser ZToken ZSpec
zspec
  = do  ps <- many zparagraph
	return (concat ps)

zparagraph :: EParser ZToken [ZPara]
zparagraph
  = zunboxed_para +++
    zaxiomatic_box +++
    zschema_box +++
    zmachine_box   -- an extension for defining state machines.

zunboxed_para :: EParser ZToken [ZPara]
zunboxed_para
  = do  tok L_BEGIN_ZED
	cut
	s <- zitem `sepby1` many1 zsep
	optnls
	tok L_END_ZED
	return (concat s)

zitem :: EParser ZToken [ZPara]
zitem = zitem_givensets +++
	zitem_sdef +++
	zitem_abbrev +++
	zitem_freetype +++
	zitem_pred

zitem_givensets
  = do  tok L_OPENBRACKET
	gs <- zident `sepby1` comma
	tok L_CLOSEBRACKET
	return (map ZGivenSetDecl gs)

zitem_sdef :: EParser ZToken [ZPara]
zitem_sdef
  = do  name <- zschema_name
	optnls
	tok L_DEFS
	cut
	optnls
	se <- zschema_exp
	return [ZSchemaDef name se]

zitem_abbrev :: EParser ZToken [ZPara]
zitem_abbrev
  = do  zdef <- zdef_lhs
	optnls
	tok L_EQUALS_EQUALS
	cut
	optnls
	e <- zexpression
	return [ZAbbreviation zdef e]

zitem_freetype :: EParser ZToken [ZPara]
zitem_freetype
  = do  zdef <- zdef_lhs
	optnls
	tok L_COLON_COLON_EQUALS
	cut
	optnls
	b <- zbranch `sepby1` do {optnls; tok L_VERT; optnls}
	return [ZFreeTypeDef zdef b]


zitem_pred :: EParser ZToken [ZPara]
zitem_pred = do {p <- zpredicate; return [ZPredicate p]}

zdef_lhs :: EParser ZToken ZVar
zdef_lhs
  = do  var_name <- zword
	dec <- zdecoration
	return (make_zvar var_name dec)
-- TODO Pre_Gen_Decor Ident, Ident In_Gen_decor Ident and generic formals

zbranch :: EParser ZToken ZBranch
zbranch
  = do  {vn <- zvar_name;
	 tok L_LDATA;
	 e <- zexpression;
	 tok L_RDATA;
	 return (ZBranch1 vn e)} +++
    do  {i <- zident;
	 return (ZBranch0 i)}

zschema_exp :: EParser ZToken ZSExpr
zschema_exp
  = do  {tok L_FORALL;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 se <- zschema_exp;
	 return (ZSForall st se)} +++
    do  {tok L_EXISTS;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 se <- zschema_exp;
	 return (ZSExists st se)} +++
    do  {tok L_EXISTS_1;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 se <- zschema_exp;
	 return (ZSExists_1 st se)} +++
     zschema_exp_1


zschema_exp_1 :: EParser ZToken ZSExpr
zschema_exp_1
  = chainl1 zschema_exp_1a (do {optnls; tok L_PIPE; optnls; return (ZS2 ZSPipe)})

-- Note this differs from the Breuer/Bowen grammar because
--  \implies binds tighter than \iff and the precedence of
--  schema operators is respected as in zrm.

zschema_exp_1a :: EParser ZToken ZSExpr
zschema_exp_1a
  = chainl1 zschema_exp_1b (do {optnls; tok L_SEMI; optnls; return (ZS2 ZSSemi)})

zschema_exp_1b :: EParser ZToken ZSExpr
zschema_exp_1b
  = chainl1 zschema_exp_1c (do {optnls; tok L_PROJECT; optnls; return (ZS2 ZSProject)})

zschema_exp_1c :: EParser ZToken ZSExpr
zschema_exp_1c
  = chainl1 zschema_exp_1d (do {optnls; tok L_IFF; optnls; return (ZS2 ZSIff)})

zschema_exp_1d :: EParser ZToken ZSExpr
zschema_exp_1d
  = chainr1 zschema_exp_1e (do {optnls; tok L_IMPLIES; optnls; return (ZS2 ZSImplies)})

zschema_exp_1e :: EParser ZToken ZSExpr
zschema_exp_1e
  = chainl1 zschema_exp_1f (do {optnls; tok L_LOR; optnls; return (ZS2 ZSOr)})

zschema_exp_1f :: EParser ZToken ZSExpr
zschema_exp_1f
  = chainl1 zschema_exp_3 (do {optnls; tok L_LAND; optnls; return (ZS2 ZSAnd)})


zschema_exp_3 :: EParser ZToken ZSExpr
zschema_exp_3
  = do { se <- zschema_exp_u;
	 se2 <- opt se (do {hidel <- zit_hiding;
			   return (ZSHide se hidel)});
	 return se2 }

zit_hiding :: EParser ZToken [ZVar]
zit_hiding
  = do  {hidel <- many1 zhide;
	 return (concat hidel)}

zhide :: EParser ZToken [ZVar]
zhide
  = do  optnls
	tok L_HIDE
	optnls
	tok L_OPENPAREN
	dn <- zdecl_name `sepby1` comma
	tok L_CLOSEPAREN
	return dn

zschema_exp_u :: EParser ZToken ZSExpr
zschema_exp_u
  = do  {tok L_OPENBRACKET;
	 st <- zschema_text;
	 tok L_CLOSEBRACKET;
	 return (ZSchema st)} +++
    do  {tok L_LNOT;
	 se <- zschema_exp_u;
	 return (ZS1 ZSNot se)} +++
    do  {tok L_PRE;
	 se <- zschema_exp_u;
	 return (ZS1 ZSPre se)} +++
    do  {tok L_OPENPAREN;
	 se <- zschema_exp;
	 tok L_CLOSEPAREN;
	 return se} +++
    zschema_ref

zschema_ref :: EParser ZToken ZSExpr
zschema_ref
  = do  {zn <- zschema_name;
	 dec <- zdecoration;
	 reps <- opt [] zreplace;
	 return (ZSRef zn dec reps)}
-- TODO Gen_Actuals

zreplace :: EParser ZToken [ZReplace]
zreplace
  = do  {tok L_OPENBRACKET;
	 reps <- zrename_or_repl `sepby1` comma;
	 tok L_CLOSEBRACKET;
	 return reps}

zrename_or_repl :: EParser ZToken ZReplace
zrename_or_repl
  = do  {dn1 <- zdecl_name;
	 tok L_SLASH;
	 dn2 <- zdecl_name;
	 return (ZRename dn2 dn1)} +++
    do  {dn1 <- zdecl_name;
	 tok L_ASSIGN;
	 dn2 <- zexpression;
	 return (ZAssign dn1 dn2)}

zschema_name :: EParser ZToken ZSName
zschema_name
  = do  {tok L_DELTA; name <- zword; return (ZSDelta name)} +++
    do  {tok L_XI; name <- zword; return (ZSXi name)} +++
    do  {name <- zword; return (ZSPlain name)}


zschema_text :: EParser ZToken [ZGenFilt]
zschema_text
  = do  d <- zdeclaration
	p <- opt [] (do {optnls;
			 tok L_VERT;
			 optnls;
			 p <- zpredicate;
			 return [Check p]})
	return (concat d ++ p)

zdeclaration :: EParser ZToken [[ZGenFilt]]
zdeclaration = zbasic_decl `sepby1` do {optnls; tok L_SEMICOLON; optnls}

zsep :: EParser ZToken ZToken
zsep
  = tok L_BACKSLASH_BACKSLASH +++
    tok L_SEMICOLON +++
    tok L_ALSO

opt ::  a -> EParser ZToken a -> EParser ZToken a
opt def p = p +++ return def

optnls :: EParser ZToken [ZToken]
optnls = many (tok L_BACKSLASH_BACKSLASH)

comma = do {optnls; tok L_COMMA; optnls}

zaxiomatic_box :: EParser ZToken [ZPara]
zaxiomatic_box
  = do  tok L_BEGIN_AXDEF
	cut
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_AXDEF
	return [ZAxDef (concat decls ++ ax)]

zschema_box :: EParser ZToken [ZPara]
zschema_box
  = do  tok L_BEGIN_SCHEMA
	cut
	tok L_OPENBRACE
	name <- zschema_name
	tok L_CLOSEBRACE
	-- TODO: add generic formals
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_SCHEMA
	return [ZSchemaDef name (ZSchema (concat decls ++ ax))]

zmachine_box :: EParser ZToken [ZPara]
zmachine_box
  -- Eg: \begin{machine}{foo} State \init Init \ops Op1; Op2 \end{machine}
  -- Note: All names must be undecorated schema names.
  = do  tok L_BEGIN_MACHINE
	cut
	tok L_OPENBRACE
	name <- zword
	tok L_CLOSEBRACE
	-- TODO: add generic formals?
	state <- zword
	tok (L_WORD "\\machineInit")
	init <- zword
	tok (L_WORD "\\machineOps")
	ops <- zword `sepby1` zsep
	tok L_END_MACHINE
	return [ZMachineDef{machName=name,
			    machState=state,
			    machInit=init,
			    machOps=ops}]

zgeneric_box :: EParser ZToken [ZPara]
zgeneric_box
  = do  tok L_BEGIN_GENDEF
	cut
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_GENDEF
	return [ZGenDef (concat decls ++ ax)]
-- TODO Gen_Actuals

zdecl_part :: EParser ZToken [[ZGenFilt]]
zdecl_part = zbasic_decl `sepby1` many1 zsep

zaxiom_part :: EParser ZToken [ZGenFilt]
zaxiom_part
  = do  ps <- zpredicate `sepby1` many1 zsep
	return (map Check ps)

zbasic_decl :: EParser ZToken [ZGenFilt]
zbasic_decl
  = do  {ws <- zdecl_name `sepby1` comma;
	 optnls;
	 tok L_COLON;
	 optnls;
	 e <- zexpression;
	 return [Choose (make_zvar w d) e | (w,d) <- ws]} +++
    do  {sr <- zschema_ref;
	 return [Include sr]}

-- This differs slightly from the Breuer/Bowen grammar.
-- To avoid reparsing parenthesized expressions, we define
-- zexpression_0 so it only parses the special weakly binding
-- expressions, and does not call zexpression.
zexpression_0 :: EParser ZToken ZExpr
zexpression_0
  = do  {tok L_LAMBDA;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 e <- zexpression;
	 return (ZLambda st e)} +++
    do  {tok L_MU;
	 st <- zschema_text;
	 e <- opt Nothing (do {tok L_AT; exp <- zexpression; return (Just exp)});
	 return (ZMu st e)} +++
    do  {tok L_LET;
	 ldl <- zlet_def `sepby1` do {optnls; tok L_SEMICOLON; optnls};
	 optnls;
	 tok L_AT;
	 optnls;
	 e <- zexpression;
	 return (ZELet ldl e)}

zexpression :: EParser ZToken ZExpr
zexpression
  = do  {tok L_IF;
	 p <- zpredicate;
	 optnls;
	 tok L_THEN;
	 optnls;
	 e1 <- zexpression;
	 optnls;
	 tok L_ELSE;
	 optnls;
	 e2 <- zexpression;
	 return (ZIf_Then_Else p e1 e2)} +++
    zexpression_1

zexpression_1 :: EParser ZToken ZExpr
zexpression_1
  = chainr1 zexpression_1a (do {op <- zin_gen_decor;
				return (infixop((ZVar op)))})

zexpression_1a :: EParser ZToken ZExpr
zexpression_1a
  = do  {e <- (zexpression_2 1);
	 ce <- opt e (do {cel <- many1 (do {optnls;
					    tok L_CROSS;
					    optnls;
					    e2 <- zexpression_2 1;
					    return e2});
			  return (ZCross (e:cel))});
	 return (ce)}

zexpression_2 :: Int -> EParser ZToken ZExpr
zexpression_2 7 = zexpression_2a
zexpression_2 p
  = chainl1 (zexpression_2 (p+1)) (do {optnls;
				       op <- (zin_fun_decor p);
				       optnls;
				       return (infixop (ZVar op))})

infixop :: ZExpr -> ZExpr -> ZExpr -> ZExpr
infixop op a b = ZCall op (ZTuple [a,b])

zexpression_2a :: EParser ZToken ZExpr
zexpression_2a
  = do  {tok L_POWER;
	 e <- zexpression_4;
	 return (ZCall (ZVar (make_zvar "\\power" [])) e)} +++
    do  {op <- zpre_gen_decor;
	 e <- zexpression_4;
	 return (ZCall (ZVar op) e)} +++
    do  {tok L_HYPHEN;
	 dec <- zdecoration;
	 e <- zexpression_4;
	 return (ZCall (ZVar (make_zvar "\\negate" dec)) e)} +++
    do  {e4 <- zexpression_4;
	 -- We factor e4 out of the following 2 cases, to avoid reparsing it.
	 -- As Breuer/Bowen note, this is a source of inefficiency
	 -- in their parser.  e4 is often big, so reparsing it is bad.
	 do { tok L_LIMG;
	      e0 <- zexpression_0 +++ zexpression;
	      tok L_RIMG;
	      dec <- zdecoration;
	      let {op = make_zvar "\\relimg" dec};
	      return (ZCall (ZVar op) (ZTuple [e4,e0])) }
	    +++
	 do { -- this is zexpression_3 (function calls), done inline
	      es <- many zexpression_4;
	      return (foldl1 ZCall (e4:es)) }}

zexpression_4 :: EParser ZToken ZExpr
zexpression_4
 = do  {e <- zexpression_4a;
	e2 <- opt e (do {tok L_POINT;
			 v <- zvar_name;
			 return (ZSelect e v)} +++
		     do {op <- zpost_fun_decor;
			 return (ZCall (ZVar op) e)} +++
		     do {tok L_BSUP;
			 e2 <- zexpression;
			 tok L_ESUP;
			 let {op = make_zvar "iter" []};
			 -- iter is curried: 'R\bsup k \esep' means 'iter R k'
			 return (ZCall (ZCall (ZVar op) e2) e)});
	return e2 }

zexpressions :: EParser ZToken [ZExpr]
zexpressions
  = do  {e <- zexpression;
	 el <- many (do {comma;
			 e1 <- zexpression;
			 return e1});
	 return (e : el)}

zexpression_4a :: EParser ZToken ZExpr
zexpression_4a
  = do  {vn <- zvar_name; return (ZVar vn)} +++
-- TODO Gen_Actuals
    do  {i <- znumber; return (ZInt i)} +++
    do  {s <- zgivenval; return (ZGiven s)} +++
    do  {zset_exp} +++
    do  {tok L_LANGLE;
	 el <- opt [] zexpressions;
	 tok L_RANGLE;
	 return (ZSeqDisplay el)} +++
    zexpression_4b

zexpression_4b :: EParser ZToken ZExpr
zexpression_4b
  = do  {tok L_OPENPAREN;
	 -- Note: this *only* parses \lambda, \let and \mu
	 e <- zexpression_0;
	 tok L_CLOSEPAREN;
	 return e} +++
    do  { -- here we combine parsing of parenthesized expressions
	  -- and parsing of tuples, to avoid reparsing the first
	  -- expression in a tuple.  The Breuer/Bowen grammar does
	  -- does do this, so behaves exponentially on nested expressions
	 tok L_OPENPAREN;
	 es <- zexpressions;
	 tok L_CLOSEPAREN;
	 return (if length es == 1 then head es else ZTuple es)} +++
    do  {tok L_LBLOT;
	 bl <- opt [] (zlet_def `sepby1` do {optnls; tok L_COMMA; optnls});
	 tok L_RBLOT;
	 return (ZBinding bl)} +++
    do  {tok L_THETA;
	 sn <- zschema_name;
	 dec <- zdecoration;
	 reps <- opt [] zreplace;
	 return (ZTheta (ZSRef sn dec reps))} +++
    do  {sr <- zschema_ref;
	 return (ZESchema sr)}


zset_exp ::  EParser ZToken ZExpr
zset_exp
  = do  {tok L_OPENSET;
	 el <- opt [] zexpressions;
	 tok L_CLOSESET;
	 -- Note: Z is ambiguous here.
	 --   {S} can be parsed as a set display or a set comprehension.
	 --   Spivey (Edition 2) p.55 says if S is a schema reference,
	 --   this should be parsed as a set comprehension.
	 --   At this stage in parsing, we do not know which names are
	 --   schemas, so we leave it as a set display.
	 --   The Unfold module translates them to set comprehensions.
	 return (ZSetDisplay el) } +++
    do  {tok L_OPENSET;
	 st <- zschema_text;
	 e <- opt Nothing (do {optnls;
			       tok L_AT;
			       optnls;
			       exp <- zexpression;
			       return (Just exp)});
	 tok L_CLOSESET;
	 return (ZSetComp st e)}


zpredicate :: EParser ZToken ZPred
zpredicate
  = do  {tok L_FORALL;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZForall st p)} +++
    do  {tok L_EXISTS;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZExists st p)} +++
    do  {tok L_EXISTS_1;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZExists_1 st p)} +++
    do  {tok L_LET;
	 ldl <- zlet_def `sepby1` do {optnls; tok L_SEMICOLON; optnls};
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZPLet ldl p)} +++
    zpredicate_1

zpredicate_1 :: EParser ZToken ZPred
zpredicate_1
  = chainl1 zpredicate_1a (do {optnls; tok L_IFF; optnls; return ZIff})

-- Note this differs from the Breuer/Bowen grammar because
--  \implies binds tighter than \iff and the precedence of
--  predicate operators is respected as in zrm.

zpredicate_1a :: EParser ZToken ZPred
zpredicate_1a
  = chainr1 zpredicate_1b (do {optnls; tok L_IMPLIES; optnls; return ZImplies})

zpredicate_1b :: EParser ZToken ZPred
zpredicate_1b
  = chainl1 zpredicate_1c (do {optnls; tok L_LOR; optnls; return ZOr})

zpredicate_1c :: EParser ZToken ZPred
zpredicate_1c
  = chainl1 zpredicate_u (do {optnls; tok L_LAND; optnls; return ZAnd})

zpredicate_u :: EParser ZToken ZPred
zpredicate_u
    = do  {e1 <- zexpression;
	   es <- many1 (do {optnls;
			    r <- zrel;
			    optnls;
			    e2 <- zexpression;
			    return (r,e2)});
	   return (it_pred e1 es)} +++
--  Handles iterations, e.g. a=b=c or a \in b = c, by taking the conjunct
--   of each  iteration e.g. a=b \land b=c or a \in b \land b=c respectively.
--  Note: Single zexpressions are not allowed here by Spivey but are in
--   the Breuer/Bowen grammar (a mistake?).  We follow Spivey.
      do  {op <- zpre_rel_decor;
	   e <- zexpression;
	   return (ZMember e (ZVar op))} +++
      do  {tok L_PRE; sr <- zschema_ref; return (ZPre sr)} +++
      do  {tok L_TRUE; return ztrue} +++
      do  {tok L_FALSE; return zfalse} +++
      do  {tok L_LNOT;
	   p <- zpredicate;
	   return (ZNot p)} +++
      do  {tok L_OPENPAREN;
	   p <- zpredicate;
	   tok L_CLOSEPAREN;
	   return p;} +++
      do  {sr <- zschema_ref;
	   return (ZPSchema sr)}

it_pred :: ZExpr -> [(ZExpr -> ZExpr -> ZPred, ZExpr)] -> ZPred
it_pred e1 [(f,e2)]    = f e1 e2
it_pred e1 ((f,e2):fs) = f e1 e2 `ZAnd` it_pred e2 fs


zlet_def :: EParser ZToken (ZVar,ZExpr)
zlet_def
  = do  {vn <- zvar_name;
	 optnls;
	 tok L_EQUALS_EQUALS;
	 optnls;
	 e <- zexpression;
	 return (vn,e)}

zrel :: EParser ZToken (ZExpr -> ZExpr -> ZPred)
zrel
  = do  {tok L_EQUALS; return ZEqual} +++
    do  {tok L_IN; return ZMember} +++
    do  {tok L_NEQ; return (\e1 e2 -> (ZNot (ZEqual e1 e2)))} +++
    do  {tok L_NOTIN; return (\e1 e2 -> (ZNot (ZMember e1 e2)))} +++
    do  {ir <- zin_rel_decor; return (member_of_in_rel (ZVar ir))} +++
    do  {tok L_INREL; tok L_OPENBRACE; i <- zident;
	 tok L_CLOSEBRACE; return (member_of_in_rel (ZVar i))}
  where
  -- Translate (x R y) into (x,y) \in R.
  member_of_in_rel r e1 e2 = ZMember (ZTuple [e1,e2]) r

zvar_name :: EParser ZToken ZVar
zvar_name
  = do  {tok L_OPENPAREN; vn <- zop_name; tok L_CLOSEPAREN; return vn} +++
    zident

zdecl_name :: EParser ZToken ZVar
zdecl_name = zop_name +++ zident

zop_name :: EParser ZToken ZVar
zop_name =
  do  {tok L_UNDERSCORE;
       is <- zin_sym_decor;
       tok L_UNDERSCORE;
       return is} +++
  do  {ps <- zpre_sym_decor;
       tok L_UNDERSCORE;
       return ps} +++
  do  {tok L_UNDERSCORE;
       w <- zpost_fun;
       d <- zdecoration;
       return (make_zvar w d)} +++
  do  {tok L_UNDERSCORE;
       tok L_LIMG;
       tok L_UNDERSCORE;
       tok L_RIMG;
       dec <- zdecoration;
       return (make_zvar "\\relimg" dec)} +++
  do  {tok L_HYPHEN;
       dec <- zdecoration;
       return (make_zvar "\\negate" dec)}

zin_sym_decor :: EParser ZToken ZVar
zin_sym_decor
  = do  iop <- zin_fun_decor 0 +++ zin_gen_decor +++ zin_rel_decor
	return iop

zpre_sym_decor :: EParser ZToken ZVar
zpre_sym_decor = zpre_gen_decor +++ zpre_rel_decor

zident :: EParser ZToken ZVar
zident = do {w <- zword; d <- zdecoration; return (make_zvar w d)}


zdecoration :: EParser ZToken [ZDecor]
zdecoration = many zstroke

zstroke :: EParser ZToken ZDecor
zstroke
  = do  L_STROKE w <- sat isStroke
	return w
    where
    isStroke (L_STROKE _) = True
    isStroke _            = False

zword :: EParser ZToken String
zword =
  do L_WORD w <- sat isWord
     return w
  where
  isWord (L_WORD _) = True
  isWord _          = False

zpre_rel_decor :: EParser ZToken ZVar
zpre_rel_decor
  = do  {prs <- zpre_rel;
	 dec <- zdecoration;
	 return (make_zvar prs dec)}

zpre_rel :: EParser ZToken String
zpre_rel =
  do L_PRE_REL w <- sat isPre_Rel
     return w
  where
  isPre_Rel (L_PRE_REL _)  = True
  isPre_Rel _             = False

zin_rel_decor :: EParser ZToken ZVar
zin_rel_decor
  = do  {irs <- zin_rel;
	 dec <- zdecoration;
	 return (make_zvar irs dec)}

zin_rel :: EParser ZToken String
zin_rel =
  do  optnls
      L_IN_REL w <- sat isIn_Rel
      optnls
      return w
  where
  isIn_Rel (L_IN_REL _)  = True
  isIn_Rel _             = False

zpost_fun_decor :: EParser ZToken ZVar
zpost_fun_decor
  = do  {pfs <- zpost_fun;
	 dec <- zdecoration;
	 return (make_zvar pfs dec)}

zpost_fun :: EParser ZToken String
zpost_fun =
  do L_POST_FUN w <- sat isPost_Fun
     return w
  where
  isPost_Fun (L_POST_FUN _)  = True
  isPost_Fun _                = False

zin_gen_decor :: EParser ZToken ZVar
zin_gen_decor
  = do  {igs <- zin_gen;
	 dec <- zdecoration;
	 return (make_zvar igs dec)}

zin_gen :: EParser ZToken String
zin_gen =
  do  optnls
      L_IN_GEN w <- sat isIn_Gen
      optnls
      return w
  where
  isIn_Gen (L_IN_GEN _)  = True
  isIn_Gen _             = False

zpre_gen_decor :: EParser ZToken ZVar
zpre_gen_decor
  = do  {pgs <- zpre_gen;
	 dec <- zdecoration;
	 return (make_zvar pgs dec)}

zpre_gen :: EParser ZToken String
zpre_gen =
  do L_PRE_GEN w <- sat isPre_Gen
     return w
  where
  isPre_Gen (L_PRE_GEN _) = True
  isPre_Gen _             = False

zin_fun_decor :: Int -> EParser ZToken ZVar
zin_fun_decor p
  = do  {ifs <- zin_fun p;
	 dec <- zdecoration;
	 return (make_zvar ifs dec)}

zin_fun :: Int -> EParser ZToken String
zin_fun p =
  do {optnls;
      L_IN_FUN _ w <- sat (isIn_Fun p);
      optnls;
      return w} +++
  do {guard (p==3 || p==0);
      -- p==3 is when infix - appears within expressions: x - 2
      -- p==0 is when it appears in declarations:  _ - _ : Type
      optnls;
      tok L_HYPHEN;
      optnls;
      return ("-")}
  where
  isIn_Fun p2 (L_IN_FUN p _) = p == p2 || p2 == 0
  isIn_Fun p2 _              = False
-- calling this function with  an argument of zero will
-- match in_fun's with any precedence value i.e. 1-6

znumber :: EParser ZToken ZInt
znumber =
  do L_NUMBER i <- sat isNumber
     return i
  where
  isNumber (L_NUMBER _) = True
  isNumber _            = False

zgivenval :: EParser ZToken String
zgivenval =
  do L_GIVENVAL s <- sat isGivenVal
     return s
  where
  isGivenVal (L_GIVENVAL _) = True
  isGivenVal _              = False
