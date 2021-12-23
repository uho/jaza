module Formatter
(  -- Formatting options are stored in PrintInfo structure.
   PrintInfo,
   pinfo_stdz,  -- Standard Z style.  Should be parsable by module Parser.
   pinfo_extz,  -- Allow Z extensions (schema text is displayed in
		-- its optimized order, etc.)
   prefix_lines, -- modifies a PrintInfo structure so that every output
		 -- line (except the first) is prefixed by a given string.

   -- These are the user callable formatters, that return a string.
   -- They all have type:  PrintInfo -> term -> String
   zexpr_string,
   zpred_string,
   zsexpr_string,
   zpara_string,
   -- These are the same, but output directly to standard output.
   -- Also, they always add a trailing newline.
   -- They all have type:  PrintInfo -> term -> IO ()
   zexpr_stdout,
   zpred_stdout,
   zpara_stdout,

   zgenfilt_string
)
where

import Pretty
import AST
import Parse
import qualified FiniteSets

-- This can handle ZInt (which may be Int or Integer).
zint :: ZInt -> Doc
zint i = integer (fromIntegral i)


data PrintInfo
  = PrintInfo{linewidth::Int,
	      lineprefix::String,
	      reorder_stext::Bool,
	      preced::Prec}

pinfo_stdz, pinfo_extz :: Int -> PrintInfo
pinfo_stdz w = PrintInfo{linewidth = w,
			 lineprefix = "",
			 reorder_stext = True,
			 preced = None}

pinfo_extz w = (pinfo_stdz w){reorder_stext = False}

prefix_lines :: String -> PrintInfo -> PrintInfo
prefix_lines s pi = pi{lineprefix = s}


-- TODO: extend these to do 'lineprefix'?
zpara_string :: PrintInfo -> ZPara -> String
zpara_string pi t = render (print_para pi t)

zpred_string :: PrintInfo -> ZPred -> String
zpred_string pi t = render (print_pred pi t)

zexpr_string :: PrintInfo -> ZExpr -> String
zexpr_string pi t = render (print_expr pi t)

zsexpr_string :: PrintInfo -> ZSExpr -> String
zsexpr_string pi t = render (print_sexpr pi t)

zgenfilt_string :: PrintInfo -> ZGenFilt -> String
zgenfilt_string pi t = render (print_genfilt pi t)


-- Here is a renderer that prints directly onto standard output.
zterm_stdout :: PrintInfo -> (PrintInfo -> t -> Doc) -> t -> IO ()
zterm_stdout pi formatfunc t
  = fullRender
	PageMode
	(linewidth pi)
	1.0             -- ribbons per line (ie. fraction of line used?)
	(output_string (lineprefix pi))
	(putStrLn "")
	(formatfunc pi t)
  where
  output_string pre (Chr '\n') s = do {putStr ('\n':pre); s}
  output_string _   (Chr c)   s  = do {putStr [c]; s}
  output_string _   (Str s1)  s2 = do {putStr s1; s2}
--  output_string _   (PStr s1) s2 = do {putStr s1; s2}

zpara_stdout pi t = zterm_stdout pi print_para t
zpred_stdout pi t = zterm_stdout pi print_pred t
zexpr_stdout pi t = zterm_stdout pi print_expr t


-- This data type is used to represent the presedence of Z constructs.
-- The names used are representative of those in Breuer's/Bowen's
-- "A Concrete Z Grammar" and follow directly the gramar implemented
-- in Parse.hs
data Prec
  = Brac | None
  | SExpr | SExpr1 | SExpr1a | SExpr1b | SExpr1c
  | SExpr1d | SExpr1e | SExpr1f | SExpr3 | SExpru
  | Expr0
  | Pred | Pred1 | Pred1a | Pred1b | Pred1c | Predu
  | Expr | Expr1  | Expr1a
  | Op1 | Op2 | Op3 | Op4 | Op5 | Op6
  | Expr2a | Expr3 | Expr4
  | Exprs | Expr4ab
  | SRef  | Max
  deriving (Eq, Ord, Enum)

beg_unboxed = text "\\begin{zed}"
end_unboxed = text "\\end{zed}"

print_para :: PrintInfo -> ZPara -> Doc
print_para pi (ZGivenSetDecl gs)
  =  beg_unboxed $$ nest 4 (brackets (print_ident pi gs)) $$ end_unboxed
print_para pi (ZSchemaDef n (ZSchema st))
  | reorder_stext pi  = print_ebox pi name end st
  | otherwise         = name $$ nest 4 (print_stext pi{preced=None} st) $$ end
  where
  name = text "\\begin{schema}{" <> print_sname pi n <> text "}"
  end  = text "\\end{schema}"
print_para pi (ZSchemaDef n se)
  =  beg_unboxed
     $$  nest 4 (name <+> text "\\defs" <+> print_sexpr (reset_sexpr pi) se)
     $$  end_unboxed
  where
  name = print_sname pi n
print_para pi (ZAbbreviation v e)
  =  beg_unboxed
     $$ nest 4 (print_var pi v <+> text "==" <+> print_expr (reset_expr pi) e)
     $$ end_unboxed
print_para pi (ZFreeTypeDef v bl)
  =  beg_unboxed $$ nest 4 (print_ftype pi v bl) $$ end_unboxed
print_para pi (ZPredicate p)
  =  beg_unboxed $$ nest 4 (print_pred pi p) $$ end_unboxed
print_para pi (ZAxDef st) = print_ebox pi open end st
  where
  open = text "\\begin{axdef}"
  end  = text "\\end{axdef}"
-- TODO Can axdefs be reordered?
-- TODO Gendefs
print_para pi _  = text "Not Implemented (print_para)"


print_ebox :: PrintInfo -> Doc -> Doc -> [ZGenFilt] -> Doc
print_ebox pi open end st
  = open $$ vcat (sep_decls ++ opt_preds) $$ end
  where
  opt_preds = if null combined_preds
	      then []
	      else text "\\where":(map (nest 4) combined_preds)
  combined_preds    = sep_list (<+> text "\\\\") preds
  preds             = print_gensfilts pi (filter isCheck st)
  sep_decls         = map (nest 4) (sep_list (<+> text "\\\\") decls)
  decls             = print_gensfilts pi (filter (not .isCheck) st)
  isCheck (Check _) = True
  isCheck _         = False

reset_expr :: PrintInfo -> PrintInfo
reset_expr pi = pi{preced=Expr}

reset_pred :: PrintInfo -> PrintInfo
reset_pred pi = pi{preced=Pred}

reset_sexpr :: PrintInfo -> PrintInfo
reset_sexpr pi = pi{preced=SExpr}


-- The function plevel checks the precedence of the component Z and
-- parenthesizes it if necessary
plevel :: PrintInfo -> Prec -> Doc -> Doc
plevel pi currp doc
  |  preced pi <= currp  = doc
  |  otherwise         = parens doc


print_ident :: PrintInfo -> ZVar -> Doc
print_ident pi = text . show_zvar


print_var :: PrintInfo -> ZVar -> Doc
print_var pi v
  | null op   = print_ident pi v
  | otherwise = plevel pi Brac (print_opname pi (head op))
  where
  op = all_by_lstr v


print_opname :: PrintInfo -> OpInfo -> Doc
print_opname pi oi
  | (optype oi) == Infix     = uscr <> op <> uscr
  | (optype oi) == Prefix    = op <> uscr
  | (optype oi) == Postfix   = uscr <> op
  | (optype oi) == RelImg    = uscr <> text "\\limg" <> uscr <> text "\\rimg"
  | (optype oi) == Iteration = uscr <> text "\\bsup" <> uscr <> text "\\esup"
  | (optype oi) == PreRel    = op <> uscr
  | (optype oi) == Negation  = text "-"
  |  otherwise               = text "Not Implemented (print_opname)"
  where
  uscr = text "\\_"
  op   = print_ident pi (lstr oi)


print_declname :: PrintInfo -> ZVar -> Doc
print_declname pi v
  | null op   = print_ident pi v
  | otherwise = print_opname pi (head op)
  where
  op = all_by_lstr v


print_stext :: PrintInfo -> [ZGenFilt] -> Doc
print_stext pi st
  | reorder_stext pi =  fsep (sep_decls ++ opt_preds)
  | otherwise        =  sep (sep_list (<> text ";") unord_st)
  where
  unord_st          = print_gensfilts pi st
  opt_preds         = if null combined_preds
		      then []
		      else (text "|"):combined_preds
  combined_preds    = sep_list (<+> text "\\land") preds
  preds             = print_gensfilts pi (filter isCheck st)
  sep_decls         = (sep_list (<> text ";") decls)
  decls             = print_gensfilts pi (filter (not .isCheck) st)
  isCheck (Check _) = True
  isCheck _         = False

print_gensfilts :: PrintInfo -> [ZGenFilt] -> [Doc]
print_gensfilts pi l = map (print_genfilt pi) l

print_genfilt :: PrintInfo -> ZGenFilt -> Doc
print_genfilt pi (Include se)
  = print_sexpr (reset_sexpr pi) se
print_genfilt pi (Choose v e)
  = print_declname pi v <> text ":" <> print_expr (reset_expr pi) e
print_genfilt pi (Evaluate v e t)
  -- This is a Z extension that is introduced by module Optimize,
  -- so we make up some plausible syntax:   v==e:t
  = print_declname pi v <> text "==" <> pexpr <> text ":" <> ptype
  where
  pexpr = (print_expr (reset_expr pi) e)
  ptype = (print_expr (reset_expr pi) t)
print_genfilt pi (Check p)
  = print_pred (reset_pred pi) p


print_expr :: PrintInfo -> ZExpr -> Doc
print_expr pi (ZUniverse)   = text "ZUniverse"
print_expr pi (ZVar var)    = print_var pi var
print_expr pi (ZESchema se)
  = print_sexpr pi{preced=Expr4ab} se
print_expr pi (ZGiven gv)   = text (show gv)
print_expr pi (ZGivenSet gsn) = print_ident pi gsn
print_expr pi (ZInt i)      = text (show i)
print_expr pi e@(ZGenerator r v) =
  text "(_ " <> text(show r) <> text " " <> print_expr pi v <> text ")"
print_expr pi e@ZPowerSet{} = print_unaryop pi (pregen_op e) (baseset e)
print_expr pi e@ZFuncSet{}
  | is_sequence e &&
    domset e == ZIntSet (Just 1) Nothing &&
    not (null (fset_seq_op e))
    = print_unaryop pi (head (fset_seq_op e)) (ranset e)
  | not (is_sequence e) &&
    not (null (fset_op e))
    = print_binaryop pi (head (fset_op e)) (domset e) (ranset e)
  | otherwise
    = text ("Error: nonrepresentable function: " ++ show e ++ "  ")
print_expr pi (ZCross el)   = plevel pi Expr1a pcrossl
  where
  pcrossl = fsep (sep_list (<+> text "\\cross")
		  (map (print_expr pi{preced=Expr1a}) el))
print_expr pi (ZTuple el)
  = plevel pi Brac (fsep (comma_sep_exprs pi{preced=None} el))
-- always bracket
print_expr pi (ZCall e1 e2) =  print_zcall pi e1 e2
print_expr pi (ZSetDisplay el)
  =  text "\\{" <> fsep (comma_sep_exprs pi{preced=None} el) <>  text "\\}"
print_expr pi (ZSeqDisplay el)
  =  text "\\langle" <+> fsep (comma_sep_exprs pi{preced=None} el)
     <+>  text "\\rangle"
print_expr pi (ZSetComp st opte)
  =  text "\\{" <> print_stext pi{preced=None} st
     <+> print_optexpr (reset_expr pi) opte <> text "\\}"
print_expr pi (ZLambda st e)
  =  plevel pi Expr0 (text "\\lambda" <+> print_stext pi{preced=None} st
		      <+> text "@" <+> print_expr (reset_expr pi) e)
print_expr pi (ZMu st opte)
  =  plevel pi Expr0 (text "\\mu" <+> print_stext pi{preced=None} st
		      <+> print_optexpr pi{preced=Expr0} opte)
print_expr pi (ZELet ldl e)
  =  plevel pi Expr0 (fsep [text "\\LET", letdef,
			    text "@", print_expr pi{preced=Expr0} e])
  where
  letdef = fsep(sep_list (<> text ";") (map (print_letdef pi) ldl))
print_expr pi (ZIf_Then_Else p e1 e2)
  =  plevel pi Expr (fsep[(text "\\IF" <+> print_pred (reset_pred pi) p),
			  (text "\\THEN" <+> print_expr (reset_expr pi) e1),
			  (text "\\ELSE" <+> print_expr (reset_expr pi) e2)])
print_expr pi (ZSelect e v)
  =  plevel pi Expr4 (print_expr pi{preced=Expr4} e
		     <> text "." <> print_var pi v)
print_expr pi (ZTheta se)
  =  plevel pi Expr4ab (text "\\theta" <+> print_sexpr pi{preced=Expr4ab} se)
-- The remaining ones are mostly used for evaluation results
print_expr pi (ZReln r)     = print_var pi (lstr(reln_op r))
print_expr pi (ZFunc1 uo)   = print_var pi (lstr(unary_op uo))
print_expr pi (ZFunc2 bo)   = print_var pi (lstr(binary_op bo))
print_expr pi (ZStrange ZIter)     = text "iter"  -- TODO: display as R^n ?
print_expr pi (ZStrange ZDisjoint) = text "\\disjoint" -- TODO: format as a prefix relation?
print_expr pi (ZFSet s) = print_expr pi (ZSetDisplay (FiniteSets.set2list s))
print_expr pi (ZIntSet low high) = print_intset pi low high
print_expr pi (ZBinding lvl)
  =  text "\\lblot" <+> bc <+> text "\\rblot"
  where
  bc = fsep (sep_list (<> text ",") (map (print_bindmem pi) lvl))
print_expr pi (ZFree0 v) = print_var pi v
print_expr pi (ZFree1 v e) = print_expr pi (ZCall (ZVar v) e)
print_expr pi (ZFreeType v bl) = print_var pi v
print_expr pi _      = text "Not Implemented (print_expr)"


print_bindmem :: PrintInfo -> (ZVar, ZValue) -> Doc
print_bindmem pi (v,val)
  =  print_var pi v <> text "==" <> print_expr pi{preced=None} val

print_intset :: PrintInfo -> Maybe ZInt -> Maybe ZInt -> Doc
print_intset pi Nothing   Nothing   = text "\\num"
print_intset pi (Just 0)  Nothing   = text "\\nat"
print_intset pi (Just 1)  Nothing   = text "\\nat_1"
print_intset pi (Just lo) (Just hi)
  = plevel pi Op2 (fsep [zint lo,text "\\upto",zint hi])
print_intset pi Nothing (Just hi)
  = text "\\{x:\\num | x" <+> text "\\leq" <+> zint hi <> text "\\}"
print_intset pi (Just lo) Nothing
  = text "\\{x:\\num | x" <+> text "\\geq" <+> zint lo <> text "\\}"

print_letdef :: PrintInfo -> (ZVar,ZExpr) -> Doc
print_letdef pi (v,e) = fsep [(print_var pi v <+> text "=="), print_expr (reset_expr pi) e]


print_optexpr :: PrintInfo ->  (Maybe ZExpr) -> Doc
print_optexpr pi Nothing  = empty
print_optexpr pi (Just e) = text "@" <+> print_expr pi e


comma_sep_exprs :: PrintInfo -> [ZExpr] -> [Doc]
comma_sep_exprs pi el
  = sep_list (<> text ",") (map (print_expr (reset_expr pi)) el)


print_zcall :: PrintInfo -> ZExpr -> ZExpr -> Doc
print_zcall pi e@(ZVar v) args@(ZTuple[e1,e2])
  | null bop  = print_zcall1 pi e args
  | otherwise = print_binaryop pi (head bop) e1 e2
  where
  bop = bop_by_lstr v
print_zcall pi (ZVar v) e = print_unaryop pi (uop_by_lstr v) e
print_zcall pi (ZCall (ZReln r) e1) e2 = error "ZCall ZReln e1 e2 found!" --print_binaryop pi (reln_op r) e1 e2
print_zcall pi (ZFunc2 bo) (ZTuple[a,b]) = print_binaryop pi (binary_op bo) a b
print_zcall pi (ZFunc1 uo) e = print_unaryop pi (unary_op uo) e
print_zcall pi e1 e2 = print_zcall1 pi e1 e2

print_zcall1 pi e e1    -- Function Arg list
  = plevel pi Expr3 fcall
  where
  fcall = fcat [print_expr pi{preced=Expr3} e, space,
		print_expr (incr_prec pi) e1]  -- TODO: check this precedence!
  space = text "~"


print_unaryop :: PrintInfo -> OpInfo -> ZExpr -> Doc
print_unaryop pi oi e
  | (optype oi) == Postfix  = plevel pi oprec (fsep [pexpr, pop])
  | (optype oi) == Negation = text "-" <> pexpr
  | (optype oi) == Userdef  = plevel pi oprec (fcat [pop, text "~", pexpr])
  | otherwise               = plevel pi oprec (fsep [pop, pexpr])
  where
  pexpr = print_expr (update_prec pi oi) e
  pop   = print_ident pi (lstr oi)
  oprec = prec oi

print_binaryop :: PrintInfo -> OpInfo -> ZExpr -> ZExpr -> Doc
print_binaryop pi oi e1 e2
  | (optype oi) == Infix  = plevel pi oprec (fsep [lexpr, op, rexpr])
  | (optype oi) == RelImg = plevel pi oprec relimg
  | (optype oi) == Iteration = plevel pi oprec iter
  | (optype oi) == Userdef   = plevel pi oprec (fcat [op,space,lexpr,space,rexpr])
  | otherwise                = plevel pi oprec (fsep [op,lexpr,rexpr])
  where
  oprec   = prec oi
  lexpr   = print_expr (setl_prec pi oi) e1
  rexpr   = print_expr (setr_prec pi oi) e2
  unambe1 = print_expr (reset_expr pi) e1
  unambe2 = print_expr (reset_expr pi) e2
  op      = print_ident pi (lstr oi)
  relimg  = fsep [lexpr, text "\\limg", unambe2, text "\\rimg"]
  iter    = fsep [rexpr, text "\\bsup", unambe1, text "\\esup"]
  space   = text "~"


print_pred :: PrintInfo -> ZPred -> Doc
print_pred pi ZFalse{} = text "false"
print_pred pi ZTrue{}  = text "true"
print_pred pi (ZPre se)
  =  plevel pi Predu (text "\\pre" <+> print_sexpr pi{preced=Predu} se)
print_pred pi (ZAnd p1 p2)
  =  plevel pi Pred1c (fsep [lpred, text "\\land", rpred])
  where
  lpred = print_pred pi{preced=Pred1c} p1
  rpred = print_pred pi{preced=Predu} p2
print_pred pi (ZOr p1 p2)
  =  plevel pi Pred1b (fsep [lpred, text "\\lor", rpred])
  where
  lpred = print_pred pi{preced=Pred1b} p1
  rpred = print_pred pi{preced=Pred1c} p2
print_pred pi (ZImplies p1 p2)
  =  plevel pi Pred1a (fsep [lpred, text "\\implies", rpred])
  where
  lpred = print_pred pi{preced=Pred1b} p1
  rpred = print_pred pi{preced=Pred1a} p2
print_pred pi (ZIff p1 p2)
  =  plevel pi Pred1 (fsep [lpred, text "\\iff", rpred])
  where
  lpred = print_pred pi{preced=Pred1} p1
  rpred = print_pred pi{preced=Pred1a} p2
print_pred pi (ZNot (ZMember e1 e2))
  =  print_inrel pi (ZTuple [e1,e2]) (ZReln ZNotin)
-- special case for \notin
print_pred pi (ZNot (ZEqual e1 e2))
  =  print_inrel pi (ZTuple [e1,e2]) (ZReln ZNeq)
-- special case for \neq
print_pred pi (ZNot p)
  =  plevel pi Predu (text "\\lnot" <+> print_pred pi{preced=Predu} p)
print_pred pi (ZExists st p)
  =  plevel pi Pred (text "\\exists" <+> print_pquantify pi st p)
print_pred pi (ZExists_1 st p)
  =  plevel pi Pred (text "\\exists_1" <+> print_pquantify pi st p)
print_pred pi (ZForall st p)
  =  plevel pi Pred (text "\\forall" <+> print_pquantify pi st p)
print_pred pi (ZPLet ldl p)
  =  plevel pi Pred (fsep [text "\\LET",letdef,
			   text "@",print_pred pi{preced=Expr0} p])
  where
  letdef = fsep(sep_list (<> text ";") (map (print_letdef pi) ldl))
print_pred pi (ZEqual e1 e2)
  = plevel pi Predu (fsep [(expr e1 <+> text "="), expr e2])
  where
  expr e = print_expr pi{preced=Predu} e
print_pred pi (ZMember e1 e2)
  =  plevel pi Predu (print_inrel pi{preced=Predu} e1 e2)
print_pred pi (ZPSchema se)
  =  plevel pi Predu (print_sexpr pi{preced=Predu} se)
print_pred pi _      = text "Not Implemented (print_pred)"


print_inrel :: PrintInfo -> ZExpr -> ZExpr -> Doc
print_inrel pi (ZTuple [e1,e2]) (ZVar r)
  | (optype oi) == PreRel = fsep [rel, expr (ZTuple [e1,e2])]
  | otherwise             = fsep [expr e1, rel, expr e2] -- Infix
  where
  oi = reln_op_by_lstr r
  expr e = print_expr pi{preced=Predu} e
  rel = print_ident pi (lstr oi)
print_inrel pi (ZTuple el) (ZVar r) -- el > 2
  | (optype oi) == PreRel = fsep [rel, print_expr pi (ZTuple el)]
  | otherwise             = fsep [expr (ZTuple el), text "\\in", rel]
  where
  oi = reln_op_by_lstr r
  expr e = print_expr pi{preced=Predu} e
  rel = print_ident pi r
print_inrel pi (ZTuple el) (ZReln r)
  = fsep [expr e1, rel, expr e2]
  where
  expr e = print_expr pi{preced=Predu} e
  rel = print_ident pi (lstr(reln_op r))
  e1 = head el
  e2 = last el
print_inrel pi e (ZVar r) -- el > 2
  | (optype oi) == PreRel = fsep [rel, print_expr pi e]
  | otherwise             = fsep [expr e, text "\\in", rel]
  where
  oi = reln_op_by_lstr r
  expr e = print_expr pi{preced=Predu} e
  rel = print_ident pi r
print_inrel pi e1 e2 = fsep [expr e1, text "\\in", expr e2]
  where
  expr e = print_expr pi{preced=Predu} e


reln_op_by_lstr :: ZVar -> OpInfo
reln_op_by_lstr v
  = head ([op | op <- reln_op_list, (lstr op) == v]
	  ++ [OpReln{rop=error "rop of \\inrel",
		     lstr=make_zvar ("\\inrel{" ++ show_zvar v ++ "}") [],
		     optype=Infix,
		     prec=Predu,
		     assoc=N}])

print_pquantify :: PrintInfo -> [ZGenFilt] -> ZPred -> Doc
print_pquantify pi st p
  = fsep [print_stext newpi st, text "@", print_pred newpi p]
  where
  newpi = pi{preced=None}


print_sexpr :: PrintInfo -> ZSExpr -> Doc
print_sexpr pi (ZSchema st)
  =  brackets (print_stext pi{preced=SExpru} st)
print_sexpr pi (ZSRef sn dl rl)
  =  plevel pi SRef (print_sref pi{preced=SRef} sn dl rl)
print_sexpr pi (ZS1 uo se)  =  print_s1op pi (s1_op uo) se
print_sexpr pi (ZS2 bo se1 se2) = print_s2op pi (s2_op bo) se1 se2
print_sexpr pi (ZSHide se vl)
  =  plevel pi SExpr3 (sexpr <+> text "\\hide" <+> hide_labels)
  where
  hide_labels = parens (fsep (sep_list (<> text ",") (map (print_declname pi) vl)))
  sexpr =  print_sexpr pi{preced=SExpr3} se
print_sexpr pi (ZSExists st se)
  =  plevel pi SExpr (text "\\exists" <+> print_squantify pi st se)
print_sexpr pi (ZSExists_1 st se)
  =  plevel pi SExpr (text "\\exists_1" <+> print_squantify pi st se)
print_sexpr pi (ZSForall st se)
  =  plevel pi SExpr (text "\\forall" <+> print_squantify pi st se)
print_sexpr pi _      = text "Not Implemented (print_sexpr)"


print_squantify :: PrintInfo -> [ZGenFilt] -> ZSExpr -> Doc
print_squantify pi st se
  =  fsep [print_stext newpi st, text "@", print_sexpr newpi se]
  where
  newpi = pi{preced=SExpr}


sep_list :: (Doc -> Doc) -> [Doc] -> [Doc]
sep_list sep []           = []
sep_list sep (d:[])      = [d]
sep_list sep (d1:d2:rest) = (sep d1):(sep_list sep (d2:rest))


print_sref :: PrintInfo -> ZSName -> [ZDecor] -> [ZReplace] -> Doc
print_sref pi n dl rl
  =  print_sname pi n <> decs <+> repls
  where
  decs     = text (concat dl)
  repls    = if null repllist
	     then empty
	     else brackets (fsep repllist)
  repllist = sep_list (<> text ",") (map (print_replace pi) rl)


print_replace :: PrintInfo -> ZReplace -> Doc
print_replace pi (ZRename x y) = print_declname pi y <> text "/" <> print_declname pi x
print_replace pi (ZAssign x y) = print_declname pi x <> text ":=" <> print_expr pi y


print_sname :: PrintInfo -> ZSName -> Doc
print_sname pi (ZSPlain s) =  text s
print_sname pi (ZSDelta s) =  text "\\Delta" <+> text s
print_sname pi (ZSXi s)    =  text "\\Xi" <+> text s


print_s1op :: PrintInfo -> OpInfo -> ZSExpr-> Doc
print_s1op pi oi se = plevel pi oprec (op <+> rsexpr)
  where
  oprec = prec oi
  rsexpr = print_sexpr pi{preced=SExpru} se
  op = print_ident pi (lstr oi)


print_s2op :: PrintInfo -> OpInfo -> ZSExpr -> ZSExpr -> Doc
print_s2op pi oi se1 se2 = plevel pi oprec (fsep [lsexpr, op, rsexpr])
  where
  oprec = prec oi
  lsexpr = print_sexpr (setl_prec pi oi) se1
  rsexpr = print_sexpr (setr_prec pi oi) se2
  op = print_ident pi (lstr oi)
-- Note all are infix operators


print_ftype :: PrintInfo -> ZVar -> [ZBranch] -> Doc
print_ftype pi v bl
  = print_ident pi v <+> text "::=" <+> branches
  where
  branches = fsep (sep_list sep (map (print_branch pi) bl))
  sep = (<+> text "|")


print_branch :: PrintInfo -> ZBranch -> Doc
print_branch pi (ZBranch0 v) = print_ident pi v
print_branch pi (ZBranch1 v e)
  =  print_var pi v <> text "\\ldata" <+> print_expr pi{preced=None} e
     <+> text "\\rdata"


setl_prec :: PrintInfo -> OpInfo -> PrintInfo
setl_prec pi oi
  |  (assoc oi) == R = pi{preced=pplus1}    -- p+1
  |  (assoc oi) == N = pi{preced=pplus1}    -- p+1
  |  otherwise       = pi{preced=(prec oi)} -- p
  where
  pplus1 = head (tail (enumFrom (prec oi)))


setr_prec :: PrintInfo -> OpInfo -> PrintInfo
setr_prec pi oi
  |  (assoc oi) == L = pi{preced=pplus1}    -- p+1
  |  (assoc oi) == N = pi{preced=pplus1}    -- p+1
  |  otherwise       = pi{preced=(prec oi)} -- p
  where
  pplus1 = head (tail (enumFrom (prec oi)))


incr_prec :: PrintInfo -> PrintInfo
incr_prec pi = pi{preced=pplus1}
  where
  pplus1 = head (tail (enumFrom (preced pi)))

update_prec :: PrintInfo -> OpInfo -> PrintInfo
update_prec pi oi  = pi{preced=(prec oi)}


-- cannot return empty list
uop_by_lstr :: ZVar -> OpInfo
uop_by_lstr v = head (uop ++ pgop ++ psop ++ dop)
  where
  uop = [uo | uo <- unary_op_list, (lstr uo) == v]
  pgop = [pgo | pgo <- pregen_op_list, (lstr pgo) == v]
  psop = [pso | pso <- preseq_op_list, (lstr pso) == v]
  dop = [OpUserDef{lstr=v, prec=Expr3, optype=Userdef}]


-- may return empty list if no matching operator found
bop_by_lstr :: ZVar -> [OpInfo]
bop_by_lstr v = bo ++ igop
  where
  bo = [bo | bo <- binary_op_list, (lstr bo) == v]
  igop = [igo | igo <- ingen_op_list, (lstr igo) == v]


-- These data types are used to store operator information
-- (There may be a cleaner way of doing some of this, because
--  there is some redundancy between the constructor and the optype etc.)
data OpInfo -- operator information object
  = OpReln{rop::ZReln,lstr::ZVar,prec::Prec,optype::OpType,assoc::Assoc}
  | OpUnary{uop::ZFunc1,lstr::ZVar,prec::Prec,optype::OpType}
  | OpBinary{bop::ZFunc2,lstr::ZVar,prec::Prec,optype::OpType,assoc::Assoc}
  | OpInGen{fset::ZExpr,lstr::ZVar,prec::Prec,optype::OpType,assoc::Assoc}
  | OpPreGen{pset::ZExpr,lstr::ZVar,prec::Prec,optype::OpType}
  | OpPreSeq{fset::ZExpr,lstr::ZVar,prec::Prec,optype::OpType}
  | OpSchema1{usop::ZS1,lstr::ZVar,prec::Prec}
  | OpSchema2{bsop::ZS2,lstr::ZVar,prec::Prec,assoc::Assoc}
  | OpUserDef{lstr::ZVar,prec::Prec,optype::OpType}

data Assoc -- operator associativity
  = L
  | R
  | N
  deriving (Eq)

data OpType -- operator layout
  = Postfix
  | Infix
  | Prefix
  | RelImg
  | Negation
  | Iteration
  | PreRel
  | Userdef
  deriving (Eq)


reln_op :: ZReln -> OpInfo
reln_op ro =
    head ([op | op <- reln_op_list, (rop op) == ro] 
    ++ [error ("reln_op " ++ show ro)])

reln_op_list =
    [OpReln{rop=ZLessThan,   lstr=("<",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZLessThanEq, lstr=("\\leq",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZGreaterThan,lstr=(">",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZGreaterThanEq, lstr=("\\geq",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZSubset, lstr=("\\subset",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZSubsetEq, lstr=("\\subseteq",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZPartition,lstr=("\\partition",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZPrefix, lstr=("\\prefix",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZSuffix, lstr=("\\suffix",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZInSeq,  lstr=("\\inseq",[]),
	    prec=Predu,optype=Infix, assoc=N},
     OpReln{rop=ZNeq,    lstr=("\\neq",[]),
	    prec=Predu,optype=Infix,assoc=N},
     OpReln{rop=ZNotin,  lstr=("\\notin",[]),
	    prec=Predu,optype=Infix, assoc=N},
     OpReln{rop=error "\\disjoint has no rop",
	    lstr=("\\disjoint",[]), prec=Predu,
	    optype=PreRel, assoc=N}
     ]


unary_op :: ZFunc1 -> OpInfo
unary_op uo =
    head ([op | op <- unary_op_list, (uop op) == uo]
	  ++ [error ("unary_op " ++ show uo)])

unary_op_list =
    [OpUnary{uop=ZDom,    lstr=("\\dom",[]),     prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZRan,    lstr=("\\ran",[]),     prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZSizeof, lstr=("\\#",[]),       prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZBigCup, lstr=("\\bigcup",[]),  prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZBigCap, lstr=("\\bigcap",[]),  prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZId,     lstr=("\\id",[]),      prec=Expr2a, optype=Prefix},
     OpUnary{uop=ZRev,    lstr=("rev",[]),       prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZHead,   lstr=("head",[]),      prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZLast,   lstr=("last",[]),      prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZTail,   lstr=("tail",[]),      prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZFront,  lstr=("front",[]),     prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZSquash, lstr=("squash",[]),    prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZDCat,   lstr=("\\dcat",[]),    prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZSucc,   lstr=("succ",[]),      prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZNegate, lstr=("\\negate",[]),  prec=Expr2a, optype=Negation},
     OpUnary{uop=ZMax,    lstr=("max",[]),       prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZMin,    lstr=("min",[]),       prec=Expr3,  optype=Prefix},
     OpUnary{uop=ZInv,    lstr=("\\inv",[]),     prec=Expr4,  optype=Postfix},
     OpUnary{uop=ZStar,   lstr=("\\star",[]),    prec=Expr4,  optype=Postfix},
     OpUnary{uop=ZClosure,lstr=("\\plus",[]),    prec=Expr4,  optype=Postfix},
     -- This is a Jaza extension.
     OpUnary{uop=ZSum,    lstr=("sum",[]),       prec=Expr3,  optype=Prefix}
    ]


binary_op :: ZFunc2 -> OpInfo
binary_op bo =
    head ([op | op <- binary_op_list, (bop op) == bo]
	  ++ [error ("binary_op " ++ show bo)])

binary_op_list =
    [OpBinary{bop=ZMapsto,lstr=("\\mapsto",[]),prec=Op1,assoc=L,optype=Infix},
  -- Integer operations
     OpBinary{bop=ZUpto, lstr=("\\upto",[]), prec=Op1, assoc=L, optype=Infix},
     OpBinary{bop=ZPlus, lstr=("+",[]),      prec=Op1, assoc=L, optype=Infix},
     OpBinary{bop=ZMinus,lstr=("-",[]),      prec=Op1, assoc=L, optype=Infix},
     OpBinary{bop=ZTimes,lstr=("*",[]),      prec=Op1, assoc=L, optype=Infix},
     OpBinary{bop=ZDiv,  lstr=("\\div",[]),  prec=Op1, assoc=L, optype=Infix},
     OpBinary{bop=ZMod,  lstr=("\\mod",[]),  prec=Op1, assoc=L, optype=Infix},
  -- Set operations
     OpBinary{bop=ZUnion,   lstr=("\\cup",[]),prec=Op1,assoc=L,optype=Infix},
     OpBinary{bop=ZInter,   lstr=("\\cap",[]),prec=Op1,assoc=L,optype=Infix},
     OpBinary{bop=ZSetMinus,lstr=("\\setminus",[]),prec=Op1,assoc=L,optype=Infix},
  -- Relation/Function operations
     OpBinary{bop=ZComp, lstr=("\\comp",[]), prec=Op1,assoc=L, optype=Infix},
     OpBinary{bop=ZCirc, lstr=("\\circ",[]), prec=Op1,assoc=L, optype=Infix},
     OpBinary{bop=ZOPlus, lstr=("\\oplus",[]),prec=Op1,assoc=L, optype=Infix},
     OpBinary{bop=ZDRes,  lstr=("\\dres",[]), prec=Op1,assoc=L, optype=Infix},
     OpBinary{bop=ZRRes,  lstr=("\\rres",[]), prec=Op1,assoc=L, optype=Infix},
     OpBinary{bop=ZNDRes, lstr=("\\ndres",[]),prec=Op1,assoc=L, optype=Infix},
     OpBinary{bop=ZNRRes, lstr=("\\nrres",[]),prec=Op1,assoc=L, optype=Infix},
     OpBinary{bop=ZRelImg,lstr=("\\relimg",[]),prec=Op1,assoc=L,optype=RelImg},
  -- Sequence operations
     OpBinary{bop=ZCat,    lstr=("\\cat",[]),  prec=Op1,assoc=L,optype=Infix},
     OpBinary{bop=ZExtract,lstr=("\\extract",[]),prec=Op1,assoc=L,optype=Infix},
     OpBinary{bop=ZFilter, lstr=("\\filter",[]),prec=Op1,assoc=L,optype=Infix}]


fset_op :: ZExpr -> [OpInfo]
fset_op igo = [igoi | igoi <- ingen_op_list, (fset igoi) == cond]
  where
  cond = igo{domset=badset,ranset=badset}

fset_seq_op :: ZExpr -> [OpInfo]
fset_seq_op igo = [psoi | psoi <- preseq_op_list, (fset psoi) == cond]
  where
  cond = igo{domset=badset,ranset=badset}

ingen_op_list =
    [OpInGen{lstr=("\\rel",[]),  prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_function=False}},
     OpInGen{lstr=("\\pfun",[]), prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc},
     OpInGen{lstr=("\\fun",[]),  prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_total=True}},
     OpInGen{lstr=("\\pinj",[]), prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_one2one=True}},
     OpInGen{lstr=("\\inj",[]),  prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_total=True,is_one2one=True}},
     OpInGen{lstr=("\\psurj",[]),prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_onto=True}},
     OpInGen{lstr=("\\surj",[]), prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_total=True,is_onto=True}},
     OpInGen{lstr=("\\bij",[]),  prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_total=True,is_one2one=True,is_onto=True}},
     OpInGen{lstr=("\\ffun",[]), prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_finite=True}},
     OpInGen{lstr=("\\finj",[]), prec=Op1, assoc=L, optype=Infix,
	    fset=zfunc{is_finite=True,is_one2one=True}}]


-- a placeholder.  The fset_op function below sets domset and ranset
--   to this so that we get an exact match with the desired kind of
--   function in ingen_op_list and pregen_op_list.
badset = ZInt 999111

zfunc = ZFuncSet{ domset=badset,
		  ranset=badset,
		  is_function=True,
		  is_total   =False,
		  is_onto    =False,
		  is_one2one =False,
		  is_sequence=False,
		  is_non_empty=False,
		  is_finite  =False}

zseq = zfunc{is_sequence=True,is_finite=True}


pregen_op :: ZExpr -> OpInfo
pregen_op pgop = head [pgoi | pgoi <- pregen_op_list, (pset pgoi) == cond]
  where
  cond = pgop{baseset=badset}

-- prefix generics minus `id`
pregen_op_list =
    [OpPreGen{lstr=("\\power",[]),   prec=Expr2a, optype=Prefix,
	    pset=zset},
     OpPreGen{lstr=("\\power_1",[]), prec=Expr2a, optype=Prefix,
	    pset=zset{is_non_empty=True}},
     OpPreGen{lstr=("\\finset",[]),  prec=Expr2a, optype=Prefix,
	    pset=zset{is_finite=True}},
     OpPreGen{lstr=("\\finset_1",[]),prec=Expr2a, optype=Prefix,
	    pset=zset{is_finite=True,is_non_empty=True}}]

zset = ZPowerSet{ baseset=badset,
		  is_non_empty=False,
		  is_finite  =False}


preseq_op_list =
    [OpPreSeq{lstr=("\\seq",[]),     prec=Expr2a, optype=Prefix,
	    fset=zseq},
     OpPreSeq{lstr=("\\seq_1",[]),   prec=Expr2a, optype=Prefix,
	    fset=zseq{is_non_empty=True}},
     OpPreSeq{lstr=("\\iseq",[]),    prec=Expr2a, optype=Prefix,
	    fset=zseq{is_one2one=True}},
     OpPreSeq{lstr=("\\bag",[]),     prec=Expr2a, optype=Prefix,
	    fset=zfunc{ranset=ZIntSet (Just 1) Nothing}}]  -- nat_1


s1_op :: ZS1 -> OpInfo
s1_op s1o = head [op | op <- s1_op_list, (usop op) == s1o]

s1_op_list =
    [OpSchema1{usop=ZSPre, lstr=("\\pre",[]),  prec=SExpru},
     OpSchema1{usop=ZSNot, lstr=("\\lnot",[]), prec=SExpru}]

s2_op :: ZS2 -> OpInfo
s2_op s2o = head [op | op <- s2_op_list, (bsop op) == s2o]

s2_op_list =
    [OpSchema2{bsop=ZSAnd,    lstr=("\\land",[]),   prec=SExpr1f, assoc=L},
     OpSchema2{bsop=ZSOr,     lstr=("\\lor",[]),    prec=SExpr1e, assoc=L},
     OpSchema2{bsop=ZSImplies,lstr=("\\implies",[]),prec=SExpr1d, assoc=R},
     OpSchema2{bsop=ZSIff,    lstr=("\\iff",[]),    prec=SExpr1c, assoc=L},
     OpSchema2{bsop=ZSProject,lstr=("\\project",[]),prec=SExpr1b, assoc=L},
     OpSchema2{bsop=ZSSemi,   lstr=("\\semi",[]),   prec=SExpr1a, assoc=L},
     OpSchema2{bsop=ZSPipe,   lstr=("\\pipe",[]),   prec=SExpr1, assoc=L}]

all_by_lstr :: ZVar -> [OpInfo]
all_by_lstr v = [op | op <- all_op_list, (lstr op) == v] 

all_op_list
  = binary_op_list ++
    s2_op_list ++
    s1_op_list ++
    preseq_op_list ++
    pregen_op_list ++
    ingen_op_list ++
    unary_op_list ++
    reln_op_list
