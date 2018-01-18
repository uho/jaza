module Test_Strings
where

import AST

----------------------------------------------------------------------
-- These strings are used for testing the parser and formatter.
----------------------------------------------------------------------
s1 = "\\begin{zed} [ROOM, TIME, TIME'] \\end{zed}"
s2 = "\\begin{schema}{State} r:42 \\end{schema}"
s3 = "\\begin{schema}{State} r:42 \\where true \\\\ true \\end{schema}"
s4 = "\\begin{schema}{State} r:42 \\where \\lnot true \\\\ false \\end{schema}"
s5 = "\\begin{schema}{State} r:42 \\where \\lnot true \\\\ 3 = 4 \\\\ 3 \\in 4 \\end{schema}"
s6 = "\\begin{schema}{State} r:42 \\where true \\land false \\land false \\end{schema}"
s7 = "\\begin{schema}{State} r:42 \\where true \\lor false \\land true \\land false \\end{schema}"
s8 = "\\begin{schema}{State} r:42 \\where a = b \\end{schema}"
s9 = "\\begin{zed} s \\defs \\forall s:T @ [x:T] \\end{zed}"
s10 = "\\begin{zed} s \\defs [x,y:T; u:U] \\end{zed}"
s11 = "\\begin{zed} s \\defs \\lnot \\lnot [x,y:T; u:U | true] \\end{zed}"
s12 = "\\begin{zed} s \\defs \\pre \\lnot [u:U | true] \\end{zed}"
s13 = "\\begin{schema}{\\Xi S} a:A \\where a=b \\end{schema}"
s14 = "\\begin{schema}{\\Xi S} a:A; \\Delta T \\where a=b \\end{schema}"
s15 = "\\begin{zed} s \\defs \\exists T @ [x:T] \\end{zed}"
s16 = "\\begin{zed} s \\defs T \\implies S \\end{zed}"
s17 = "\\begin{zed} s \\defs R \\pipe T \\implies S \\end{zed}"
s18 = "\\begin{zed} s \\defs R \\pipe T \\implies S \\semi U \\end{zed}"
s19 = "\\begin{zed} s \\defs R \\pipe T \\project S \\semi U \\end{zed}"
s20 = "\\begin{zed} s \\defs T \\land S \\lor U \\iff V \\end{zed}"
s21 = "\\begin{schema}{State} r:42 \\where a = b = c \\notin  d \\end{schema}"
s22 = "\\begin{schema}{State} r:42 \\where true \\implies true \\end{schema}"
s23 = "\\begin{schema}{State} r:42 \\where true \\implies true \\implies false \\end{schema}"
s24 = "\\begin{schema}{State} r:42 \\where true \\iff false \\iff true \\end{schema}"
s25 = "\\begin{schema}{State} r:42 \\where true \\iff false \\implies true \\end{schema}"
s26 = "\\begin{schema}{State} r:42 \\where true \\iff false \\implies b \\end{schema}"
s27 = "\\begin{schema}{State} r:42 \\where true \\iff false \\implies b \\neq c \\end{schema}"
s28 = "\\begin{zed} S \\defs [x,y:S; z:T ] \\hide (x,y) \\end{zed}"
s29 = "\\begin{zed} S \\defs [x,y:S; z:T ] \\hide (x,y) \\hide (z) \\end{zed}"
s30 = "\\begin{zed} s \\defs \\exists_1 T @ [x:T] \\end{zed}"
s31 = "\\begin{zed} abbreviation == abbreviated \\end{zed}"
s32 = "\\begin{zed} freetype ::= a | b | c' \\ldata x \\rdata \\end{zed}"
s33 = "\\begin{zed} true \\end{zed}"
s34 = "\\begin{schema}{State} r:42 \\where true \\land (false \\iff false) \\end{schema}"
s35 = "\\begin{zed} true \\land (false \\lor true) \\end{zed}"
s36 = "\\begin{zed} schemaname \\end{zed}"
s37 = "\\begin{zed} \\pre schemaname \\end{zed}"
s38 = "\\begin{zed} \\forall T @ true \\end{zed}"
s39 = "\\begin{zed} \\exists S' @ \\exists_1 T @ R \\end{zed}"
s40 = "\\begin{zed} \\LET S' == T @ R \\end{zed}"
s41 = "\\begin{zed} S \\defs [a?,b':T] \\end{zed}"
s42 = "\\begin{zed} a \\inrel{plus} b \\end{zed}"
s43 = "\\begin{zed} a \\inrel{plus'!} b \\end{zed}"
s44 = "\\begin{axdef} a : B \\cross C \\end{axdef}"
s45 = "\\begin{axdef} a,b : C \\cross D \\where true \\end{axdef}"
s46 = "\\begin{axdef} a : B \\cross C \\cross D \\end{axdef}"
s47 = "\\begin{axdef} a : B \\end{axdef}"
s48 = "\\begin{axdef} a,b : C \\where a = \\IF true \\THEN a \\ELSE b \\end{axdef}"
s49 = "\\begin{axdef} a,b : C \\where a = a'? + b + c \\end{axdef}"
s50 = "\\begin{axdef} a,b : C \\where a = a + b \\cap c \\end{axdef}"
s51 = "\\begin{axdef} a,b : C \\where a = a \\cap b + c \\end{axdef}"
s52 = "\\begin{axdef} a,b : C \\where a = a \\setminus b \\upto e \\end{axdef}"
s53 = "\\begin{zed} s \\defs R \\hide (a,b) \\end{zed}"
s54 = "\\begin{axdef} a,b : C \\where a = a-b \\end{axdef}"
s55 = "\\begin{axdef} a,b : C \\where a = a + b \\end{axdef}"
s56 = "\\begin{axdef} a??,b!! : C \\where a?? = a?? \\filter b!! \\end{axdef}"
s57 = "\\begin{axdef} a : C \\where a = a \\setminus b \\end{axdef}"
s58 = "\\begin{axdef} S : \\power x \\end{axdef}"
s59 = "\\begin{axdef} A : \\finset_1 x \\\\ B : \\id x \\\\ C : \\seq x \\end{axdef}"
s60 = "\\begin{zed} s \\defs R \\project T \\end{zed}"
s61 = "\\begin{zed} s == -a  \\end{zed}"
s62 = "\\begin{zed} t == a b c \\end{zed}"
s63 = "\\begin{zed} t == a \\limg b \\rimg \\end{zed}"
s64 = "\\begin{zed} t == a \\limg \\lambda S @ b \\rimg \\end{zed}"
s65 = "\\begin{zed} t == a \\limg \\mu S \\rimg \\end{zed}"
s66 = "\\begin{zed} t == a \\limg \\mu S @ b \\rimg \\end{zed}"
s67 = "\\begin{zed} t' == a \\rel b  \\end{zed}"
s68 = "\\begin{zed} t? == a \\bij b \\psurj c ffun d \\end{zed}"
s69 = "\\begin{axdef} a : C \\end{axdef}"
s70 = "\\begin{axdef} a : C.x \\end{axdef}"
s71 = "\\begin{axdef} a : C \\inv \\end{axdef}"
s72 = "\\begin{zed} t == \\{1,2,3,4\\} \\end{zed}"
s73 = "\\begin{zed} t == \\{a,b,c,d\\} \\end{zed}"
s74 = "\\begin{zed} t == \\{x,y:a\\} \\end{zed}"
s75 = "\\begin{zed} t == \\{x,y:a | x = y \\} \\end{zed}"
s76 = "\\begin{zed} t == \\{x,y:a | x \\in y @ x\\} \\end{zed}"
s77 = "\\begin{zed} t == \\{x,y:a | x \\in y @ x\\} \\end{zed}"
s78 = "\\begin{zed} t == \\{\\} \\end{zed}"
s79 = "\\begin{zed} t == \\langle \\rangle \\end{zed}"
s80 = "\\begin{zed} t == \\langle a, 1, 2 \\rangle \\end{zed}"
s81 = "\\begin{zed} t == (x,y,z) \\end{zed}"
s82 = "\\begin{zed} t == \\{x,y:a | x \\in y @ (a,b)\\} \\end{zed}"
s83 = "\\begin{zed} t == \\{x,y:a @ (a,b)\\} \\end{zed}"
s84 = "\\begin{zed} t == \\{x:a | x \\in y @ (a,b)\\} \\end{zed}"
s85 = "\\begin{zed} t == \\lblot x==1, y==2 \\rblot \\end{zed}"
s86 = "\\begin{zed} t == \\lblot \\rblot \\end{zed}"
s87 = "\\begin{zed} \\theta S' = \\theta T \\end{zed}"
s88 = "\\begin{zed} t == (\\lambda S @ B ) \\end{zed}"
s89 = "\\begin{zed} t == (\\mu S' ) \\end{zed}"
s90 = "\\begin{zed} t == (\\LET S' == T @ R) \\end{zed}"
s91 = "\\begin{zed} S \\defs [\\_-\\_ : a \\fun b] \\end{zed}"
s92 = "\\begin{zed} t == -r \\end{zed}"
s93 = "\\begin{zed} t == (\\_\\rres\\_) \\end{zed}"
s94 = "\\begin{zed} T \\defs [\\disjoint\\_ : inRel] \\end{zed}"
s95 = "\\begin{zed} T \\defs [\\_\\inv : postfun] \\end{zed}"
s96 = "\\begin{zed} s == (\\_\\limg \\_ \\rimg') \\end{zed}"
s97 = "\\begin{zed} T \\defs [- : postfun] \\end{zed}"
s98 = "\\begin{zed} i == n \\bsup 10 \\esup \\end{zed}"
s99 = "\\begin{zed} \\disjoint (a,b,c) \\end{zed}"
s100 = "\\begin{zed} \\disjoint \\langle a \\rangle \\end{zed}"
s101 = "\\begin{zed} s == \\langle a \\rangle \\end{zed}"
s102 = "\\begin{zed} \\{1,2\\} \\subset \\{1,2,3\\}  \\end{zed}"
s103 = "\\begin{zed} S \\defs T [a/b',c:=15] \\end{zed}"
s104 = "\\begin{zed} T == \\theta S' [c?:=15,a/b'] \\end{zed}"
s105 = "\\begin{zed} \n InitBirthdayBook \\defs [BirthdayBook | birthday = \\emptyset] \n \\end{zed}"
s106 = "\\begin{zed} S \\defs [\\_-\\_ \\\\ \\\\ : \\\\\\\\ a \\fun b] \\end{zed}"
s107 = "\\begin{zed} S = \\{(a \\\\ \\mapsto \\\\ 1)\\} \\end{zed}"
s108 = "\\begin{zed} a \\\\ \\inrel{plus} b \\end{zed}"
s109 = "\\begin{zed} S == T \\\\ R==U \\end{zed}"
s110 = "\\begin{axdef} a:T \n \\where a<10 ;\\\\ a>2 \\end{axdef}"
s111 = "\\begin{zed} \\LET a == b \\\\ ; \\\\ \\\\ c == d @ a = c \\end{zed}"
s112 = "\\begin{zed} S \\defs [a:A \\\\ ; b:B]  \\end{zed}"
s113 = "\\begin{zed} C = \\{a:A \\\\ ;\\\\ b:B @ a\\} \\end{zed}"
s114 = "\\begin{axdef} a:A \\where a = (\\LET a==b \\\\ ; b==c @ d) \\end{axdef}"
s115 = "\\begin{zed} C = \\{a \\\\ : \\\\ A \\\\ ;\\\\ b: \\\\ B @ a\\} \\end{zed}"
s116 = "\\begin{zed} C = \\{1 \\\\ ,\\\\ 2 ,\\\\ 3 \\\\, 4 \\} \\end{zed}"
s117 = "\\begin{zed} [A \\\\,\\\\ B \\\\, C , \\\\ D ] \\end{zed}"
s118 = "\\begin{zed} S \\defs [x,y:S; z:T ] \\hide (x \\\\ , \\\\ y \\\\\\\\, z) \\end{zed}"
s119 = "\\begin{zed} S ::= a \\\\ | b' \\\\ \n | \\\\ c \\end{zed}"
s120 = "\\begin{zed} S \\defs [x,y:S; z:T \\\\ | \\\\ true ]  \\end{zed}"
s121 = "\\begin{zed} s \\defs \\exists s:T @ \\\\ [x:T] \\end{zed}"
s122 = "\\begin{zed} f = (\\lambda s:T \\\\ @ \\\\ (\\lambda t:T @ \\\\ 2 )) \\end{zed}"
s123 = "\\begin{zed} a = \\{ a:A \\\\ @ (a,\\\\b)\\} \\end{zed}"
s124 = "\\begin{zed} S == \\\\ T \\\\\n R\\\\==U \\end{zed}"
s125 = "\\begin{schema}{Remind}\n  \\Xi BirthdayBook \\\\\n  today?: DATE; cards!: \\power NAME\n\\where\n  cards! = \\{ n: known | birthday(n) =   today? \\}\\\\\n\\end{schema}"
s126 = "\\begin{schema}{Remind}\n  \\Xi BirthdayBook \n \\end{schema}"
s127 = "\\begin{zed} A \\defs S \\land T \\pipe U \\end{zed}"
s128 = "\\begin{zed} A \\defs S \\land (T \\lor U) \\end{zed}"
s129 = "\\begin{zed} A \\defs (\\exists S @ T) \\hide (a,b) \\end{zed}"
s130 = "\\begin{zed} x = \\IF \\pre S \\THEN 1 \\ELSE 0 \\end{zed}"
s131 = "\\begin{zed} true \\land false \\land true \\land false \\end{zed}"
s132 = "\\begin{zed} true \\land false \\land (true \\land false) \\end{zed}"
s133 = "\\begin{zed} \\LET a==2 ; b==3 @ true \\end{zed}"
s134 = "\\begin{zed} true \\land a=b=c \\end{zed}"
s135 = "\\begin{zed} true \\land a \\neq b \\neq c \\end{zed}"
s136 = "\\begin{zed} false \\land a < b \\leq c \\end{zed}"
s137 = "\\begin{zed} true \\implies a \\inrel{inrel} b \\inrel{inrel} c \\end{zed}"
s138 = "\\begin{zed} a \\subset b \\inrel{userinrel} c \\end{zed}"
s139 = "\\begin{zed} a \\notin b \\lor c \\end{zed}"
s140 = "\\begin{schema}{Sname}\n    a,b:T \\\\\n    c : \\nat\n\\where\n    true \\\\\n    false\n\\end{schema}"
s141 = "\\begin{axdef}\n    a,b:T\n\\where\n    a < b\n\\end{axdef}"
s142 = "\\begin{zed} (a,b) \\in c \\end{zed}"
s143 = "\\begin{zed} \\nat_1 \\setminus \\nat = \\{0\\} \\end{zed}"

goodtests = s1 : s2 : s3 : s4 : s5 : s6 : s7 : s8 : s9
 : s10 : s11 : s12 : s13 : s14 : s15 : s16 : s17 : s18 : s19
 : s20 : s21 : s22 : s23 : s24 : s25 : s26 : s27 : s28 : s29
 : s30 : s31 : s32 : s33 : s34 : s35 : s36 : s37 : s38 : s39
 : s40 : s41 : s42 : s43 : s44 : s45 : s46 : s47 : s48 : s49
 : s50 : s51 : s52 : s53 : s54 : s55 : s56 : s57 : s58 : s59
 : s60 : s61 : s62 : s63 : s64 : s65 : s66 : s67 : s68 : s69
 : s70 : s71 : s72 : s73 : s74 : s75 : s76 : s77 : s78 : s79
 : s80 : s81 : s82 : s83 : s84 : s85 : s86 : s87 : s88 : s89
 : s90 : s91 : s92 : s93 : s94 : s95 : s96 : s97 : s98 : s99
 : s100 : s101 : s102 : s103 : s104 : s105 : s106 : s107 : s108 : s109
 : s110 : s111 : s112 : s113 : s114 : s115 : s116 : s117 : s118 : s119
 : s120 : s121 : s122 : s123 : s124 : s125 : s126 : s127 : s128 : s129
 : s130 : s131 : s132 : s133 : s134 : s135 : s136 : s137 : s138 : s139
 : s140 : s141 : s142 : s143 : []


--
-- These strings should generate parse errors.
--
sf1 = "\\begin{zed} \\pre true \\end{zed}"
sf2 = "\\begin{zed} freetype ::= \\end{zed}"
sf3 = "\\begin{axdef} S : \\pfun x \\end{axdef}"
sf4 = "\\begin{axdef} S : \\inv x \\end{axdef}"
sf5 = "\\begin{zed} t == \\LET S == T @ R \\end{zed}"
sf6 = "\\begin{zed} s == _\\limg _ \\rimg' \\end{zed}"
sf7 = "\\begin{zed} S \\defs T [] \\end{zed}"
sf8 = "\\begin{zed} (\\lambda s:T \\\\ @ \\\\ (\\lambda t:T @ \\\\ 2 )) \\end{zed}"

failtests = sf1 : sf2 : sf3 : sf4 : []



----------------------------------------------------------------------
-- Here are some extra AST trees for testing the formatter (by hand).
----------------------------------------------------------------------

-- [x,y:S; z:T | true]
t1 = ZESchema (ZSchema [Check ztrue,Choose ("x",[]) (ZVar ("S",[])),Choose ("y",[]) (ZVar ("S",[])),Choose ("z",[]) (ZVar ("T",[]))] )
-- [x:S; R; z:T | true \land false]
t2 = ZESchema (ZSchema [Check ztrue,Choose ("x",[]) (ZVar ("S",[])),Include (ZSRef (ZSPlain "R") [] []),Check zfalse,Choose ("z",[]) (ZVar ("T",[]))] )

t3 = ZESchema (ZSchema [])
-- Try t1, t2 and t3 with pinfo0 and pinfo1
-- S''?
t4 = ZESchema (ZSRef (ZSPlain "S") ["'","'","?"] [])
-- S!' [x/y, x:=y']
t5 = ZESchema (ZSRef (ZSPlain "S") ["!","'"] [(ZRename ("y",[]) ("x",[])),(ZAssign ("x",[]) (ZVar ("y",["'"])))]  )
-- \Delta S [v!:=w, x:=y']
t6 = ZESchema (ZSRef (ZSDelta "S") [] [(ZAssign ("v",["!"]) (ZVar ("w",[]))),(ZAssign ("x",[]) (ZVar ("y",["'"])))]  )
-- \Xi S [x/y, g/f]
t7 = ZESchema (ZSRef (ZSXi "S") [] [(ZRename ("y",[]) ("x",[])),(ZRename ("f",[]) ("g",[]))]  )
-- \pre S
t8 = ZESchema (ZS1 ZSPre (ZSRef (ZSPlain "S") [] []))
-- \lnot R
t9 = ZESchema (ZS1 ZSNot (ZSRef (ZSPlain "R") [] []))
-- R \land S
t10 = ZESchema (ZS2 ZSAnd (ZSRef (ZSPlain "R") [] []) (ZSRef (ZSPlain "S") [] []))
-- R \pipe S
t11 = ZESchema (ZS2 ZSPipe (ZSRef (ZSPlain "R") [] []) (ZSRef (ZSPlain "S") [] []))
-- S \hide (a, b, c)
t12 = ZESchema (ZSHide (ZSRef (ZSPlain "S") [] []) [("a",[]),("b",[]),("c",[])])
-- See how a long hide list is formated
t13 = ZESchema (ZSHide (ZSRef (ZSPlain "S") [] []) [("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[]),("a",[]),("b",[]),("c",[])])
-- As Above
t14 = ZESchema (ZSHide (ZSRef (ZSPlain "S") [] []) [("quadratic",[]),("fragments",[]),("associativityholds",[]),("quadratic",[]),("fragments",[]),("associativityholds",[])])
-- \exists \Delta R @ S
t15 = ZESchema (ZSExists [Include (ZSRef (ZSDelta "R") [] [])] (ZSRef (ZSPlain "S") [] []))
-- \exists_1 \Delta R | true @ S
t16 = ZESchema (ZSExists_1 [Include (ZSRef (ZSDelta "R") [] []), Check ztrue] (ZSRef (ZSPlain "S") [] []))
-- 1
t17 = ZInt 1
-- 1 \cross 2 \cross 3 \cross 4 \cross 5
t18 = ZCross [ZInt 1, ZInt 2, ZInt 3, ZInt 4, ZInt 5]
-- (1, 2, 3, 4, 5)
t19 = ZTuple [ZInt 1, ZInt 2, ZInt 3, ZInt 4, ZInt 5]
-- f~x~y
t20 = ZCall (ZCall (ZVar ("f",[])) (ZVar ("x",[]))) (ZVar ("y",[]))
-- a+b
t21 = ZCall (ZVar ("+",[])) (ZTuple[ZVar ("a",[]), ZVar ("b",[])])
-- f \\limg a \\rimg
t22 = ZCall (ZVar ("\\relimg",[])) (ZTuple[ZVar ("f",[]), ZVar ("a",[])])
-- func a b c d
t23 = ZCall (ZCall (ZCall (ZCall (ZVar ("func",[])) (ZVar ("a",[]))) (ZVar ("b",[]))) (ZVar ("c",[]))) (ZVar ("d",[]))
-- func a b c
t24 = ZCall (ZCall (ZCall (ZVar ("func",[])) (ZVar ("a",[]))) (ZVar ("b",[]))) (ZVar ("c",[]))
-- f \inv
t25 = ZCall (ZVar ("\\inv",[])) (ZVar ("f",[]))
-- f~a
t26 = ZCall (ZVar ("f",[])) (ZVar ("a",[]))
-- \power x
t27 = ZCall (ZVar ("\\power",[])) (ZVar ("x",[]))
--  -x
t28 = ZCall (ZVar ("\\negate",[])) (ZVar ("x",[]))
-- f \\bsup 5 \\esup
t29 = ZCall (ZCall (ZVar ("iter",[])) (ZInt 5)) (ZVar ("f",[]))
-- \{1,2,3,4,5,6\}
t30 = ZSetDisplay [ZInt 1,ZInt 2,ZInt 3,ZInt 4,ZInt 5,ZInt 6]
-- \langle 1,2,3,4,5,6 \rangle
t31 = ZSeqDisplay [ZInt 1,ZInt 2,ZInt 3,ZInt 4,ZInt 5,ZInt 6]
-- \{ 1,2,3,4,5,6 \}
t32 = ZFSet [ZInt 1,ZInt 2,ZInt 3,ZInt 4,ZInt 5,ZInt 6]
-- \\{x,y:a | x \\in y @ (a,b)\\}
t33 = ZSetComp [Choose ("x",[]) (ZVar ("a",[])),Choose ("y",[]) (ZVar ("a",[])),Check (ZMember (ZVar ("x",[])) (ZVar ("y",[])))] (Just (ZTuple [ZVar ("a",[]),ZVar ("b",[])]))
-- \\{x,y:a | x = y \\}
t34 = ZSetComp [Choose ("x",[]) (ZVar ("a",[])),Choose ("y",[]) (ZVar ("a",[])),Check (ZEqual (ZVar ("x",[])) (ZVar ("y",[])))] Nothing
-- \\lambda S @ B
t35 = ZLambda [Include (ZSRef (ZSPlain "S") [] [])] (ZVar ("B",[]))
-- \\mu S'
t36 = ZMu [Include (ZSRef (ZSPlain "S") ["'"] [])] Nothing
-- \\mu S' @ T
t37 = ZMu [Include (ZSRef (ZSPlain "S") ["'"] [])] (Just (ZVar ("T",[])))
-- \\LET S' == T; R==U @ V
t38 = ZELet [(("S",["'"]),ZVar ("T",[])),(("R",[]),ZVar ("U",[]))] (ZVar ("V",[]))
-- \\IF true \\THEN a \\ELSE b
t39 = ZIf_Then_Else ztrue (ZVar ("a",[])) (ZVar ("b",[]))
-- (f x).a
t40 = ZSelect (ZTuple [ZCall (ZVar ("f",[])) (ZVar ("x",[]))]) ("a",[])
-- \\theta S'
t41 = ZTheta (ZSRef (ZSPlain "S") ["'"] [])
-- a < b    (a ZPred)
t42 = ZMember (ZTuple[ZVar ("a",[]), ZVar ("b",[])]) (ZReln ZLessThan)
-- a \\leq b    (a ZPred)
t43 = ZMember (ZTuple[ZVar ("a",[]), ZVar ("b",[])]) (ZReln ZLessThanEq)
-- f \\inv
t44 = ZCall (ZFunc1 ZInv) (ZVar ("f",[]))
-- \\power_1 x
t45 = ZCall (ZVar ("\\power_1",[])) (ZVar ("x",[]))
--  -x
t46 = ZCall (ZFunc1 ZNegate) (ZVar ("x",[]))
-- a+b
t47 = ZCall (ZFunc2 ZPlus)   (ZTuple[ZVar ("a",[]), ZVar ("b",[])])
-- f \\limg a \\rimg
t48 = ZCall (ZFunc2 ZRelImg) (ZTuple[ZVar ("f",[]), ZVar ("a",[])])
-- a-b
t49 = ZCall (ZFunc2 ZMinus)  (ZTuple[ZVar ("a",[]), ZVar ("b",[])])
-- \num
t50 = ZIntSet Nothing Nothing
-- -infinity \\upto 10
t51 = ZIntSet Nothing (Just 10)
-- 10 \\upto infinity
t52 = ZIntSet (Just 10) Nothing
-- 10 \\upto 13
t53 = ZIntSet (Just 10) (Just 13)
-- (a,b)
t54 = ZTuple[ZVar("a", []), ZVar("b", [])]
-- a+(b-c)
t55 = ZCall (ZVar ("+",[]))
	    (ZTuple[ZVar ("a",[]),
		     ZCall (ZVar ("-",[]))
			   (ZTuple[ZVar ("b",[]), ZVar ("c",[])])])
-- a+(b-c)  (unfolded)
t56 = ZCall (ZFunc2 ZPlus)
	    (ZTuple[ZVar ("a",[]),
		     ZCall (ZFunc2 ZMinus)
			   (ZTuple[ZVar ("b",[]), ZVar ("c",[])])])
-- a < a+(b-c)    (a ZPred)
t57 = ZMember (ZTuple[ZVar ("a",[]), t56]) (ZReln ZLessThan)
-- (f~a~b~c).x
t58 = ZSelect (ZCall (ZCall (ZCall (ZVar ("f",[])) (ZVar ("a",[]))) (ZVar ("b",[]))) (ZVar ("c",[]))) ("x",[])
-- f~(x+y)
t59 = ZCall (ZVar ("f",[])) (ZCall (ZVar ("+",[]))
				   (ZTuple[ZVar ("x",[]), ZVar ("y",[])]))
-- \\dom (a \\cup b)
t60 = ZCall (ZVar ("\\dom",[]))
	    (ZCall (ZVar ("\\cup",[])) (ZTuple[ZVar ("a",[]), ZVar ("b",[])]))
-- \power (x \cross y)
t61 = ZCall (ZVar ("\\power",[])) (ZCross [ZVar ("x",[]),ZVar ("y",[])])
-- a + (\\IF true \\THEN b \\ELSE c)
t62 = ZCall (ZVar ("+",[]))
	    (ZTuple[ZVar ("a",[]),
		     ZIf_Then_Else ztrue (ZVar ("b",[])) (ZVar ("c",[]))])
-- a + (\\IF true \\THEN (a,b) \\ELSE a+(b-c))
t63 = ZCall (ZVar ("+",[]))
	    (ZTuple[ZVar ("a",[]),
		     ZIf_Then_Else
			 ztrue
			 (ZTuple [ZVar("a", []), ZVar("b", [])])
			 t56])
-- (\\id \\{1,2\\}) 2 Interesting test case because it should not parse without parens.
t64 = ZCall (ZCall (ZVar ("\\id",[])) (ZSetDisplay [ZInt 1,ZInt 2])) (ZInt 2)
-- \\power \{1,2,3\}
t65 = ZPowerSet{baseset=ZSetDisplay [ZInt 1,ZInt 2,ZInt 3],is_non_empty=False,is_finite=False}
-- <
t66 = ZReln ZLessThan
-- \\langle a==10, b==11, c==a \\rangle
t67 = ZBinding [(("a",[]),ZInt 10), (("b",[]),ZInt 11), (("c",[]),ZVar ("a",[]))]
-- ZFree0
t68 = ZFree0 ("A", [])
-- ZFree1
t69 = ZFree1 ("B", []) (ZCross [ZVar ("C",[]), ZVar("D",[])])
-- T ::= A | B\\ldata C \\cross D \\rdata
t70 = ZFreeType ("T", []) [ZBranch0 ("A", []), ZBranch1 ("B", []) (ZCross [ZVar ("C",[]), ZVar("D",[])])]
-- S \\land T \\pipe U -- print_sexpr
t71 = ZS2 ZSPipe (ZS2 ZSAnd (ZSRef (ZSPlain "S") [] []) (ZSRef (ZSPlain "T") [] [])) (ZSRef (ZSPlain "U") [] [])
-- S \\land (T \\lor U) -- print_sexpr
t72 = ZS2 ZSAnd (ZSRef (ZSPlain "S") [] []) (ZS2 ZSOr (ZSRef (ZSPlain "T") [] []) (ZSRef (ZSPlain "U") [] []))
-- (\\exists S @ T) \\hide (a,b)
t73 = ZSHide (ZSExists [Include (ZSRef (ZSPlain "S") [] [])] (ZSRef (ZSPlain "T") [] [])) [("a",[]),("b",[])]
-- \\IF \\pre S \\THEN 1 \\ELSE 0
t74 = ZIf_Then_Else (ZPre (ZSRef (ZSPlain "S") [] [])) (ZInt 1) (ZInt 0)
-- true \\land false \\land true \\land false -- print_pred pinfo0 t75
t75 = ZAnd (ZAnd (ZAnd ztrue zfalse) ztrue) zfalse
-- true \\land false \\land (true \\land false) -- print_pred pinfo0 t76
t76 = ZAnd (ZAnd ztrue zfalse) (ZAnd ztrue zfalse)
-- \\LET a==2 ; b==3 @ true -- print_pred pinfo0 t77
t77 = ZPLet [(("a",[]),ZInt 2),(("b",[]),ZInt 3)] ztrue
-- true \\land a=b=c -- print_pred pinfo0 t78
t78 = ZAnd ztrue (ZAnd (ZEqual (ZVar ("a",[])) (ZVar ("b",[]))) (ZEqual (ZVar ("b",[])) (ZVar ("c",[]))))
-- a \\neq b \\neq c -- print_pred
t79 = ZAnd (ZNot (ZEqual (ZVar ("a",[])) (ZVar ("b",[])))) (ZNot (ZEqual (ZVar ("b",[])) (ZVar ("c",[]))))
-- a < b \leq c -- print_pred
t80 = ZAnd (ZMember (ZTuple [ZVar ("a",[]),ZVar ("b",[])]) (ZVar ("<",[])))
	   (ZMember (ZTuple [ZVar ("b",[]),ZVar ("c",[])]) (ZVar ("\\leq",[])))
-- true \\implies a \\inrel{inrel} b \\inrel{inrel} c -- print_pred
t81 = ZImplies ztrue
	       (ZAnd (ZMember (ZTuple [ZVar ("a",[]),ZVar ("b",[])])
			      (ZVar ("inrel",[])))
		     (ZMember (ZTuple [ZVar ("b",[]),ZVar ("c",[])])
			      (ZVar ("inrel",[]))))
-- a \\subset b \\inrel{userinrel} c -- print_pred
t82 = ZAnd (ZMember (ZTuple [ZVar ("a",[]),ZVar ("b",[])])
		    (ZVar ("\\subset",[])))
	   (ZMember (ZTuple [ZVar ("b",[]),ZVar ("c",[])])
		    (ZVar ("userinrel",[])))
-- a \notin b \lor c -- print_pred
t83 = ZOr (ZNot (ZMember (ZVar ("a",[])) (ZVar ("b",[])))) (ZPSchema (ZSRef (ZSPlain "c") [] []))
-- [ROOM] -- print_para
t84 = ZGivenSetDecl ("ROOM",[])
-- \begin{schema}{Sname}\n    a,b:T \\\n    c : \nat\n\where\n    true \\\n    false\n\end{schema}
t85 = ZSchemaDef (ZSPlain "Sname") (ZSchema [Choose ("a",[]) (ZVar ("T",[])),Choose ("b",[]) (ZVar ("T",[])),Choose ("c",[]) (ZVar ("\\nat",[])),Check ztrue,Check zfalse])
-- \\begin{zed} s == T \\cross W \\end{zed}
t86 = ZAbbreviation ("s",[]) (ZCross [ZVar ("T",[]),ZVar ("W",[])])
-- \\begin{zed} S ::= a | b | c \\end{zed}
t87 = ZFreeTypeDef ("S",[]) [ZBranch0 ("a",[]),ZBranch0 ("b",[]),ZBranch0 ("c",[])]
-- \\begin{zed} a \\notin b \\lor c \\end{zed}
t88 = ZPredicate (ZOr (ZNot (ZMember (ZVar ("a",[])) (ZVar ("b",[])))) (ZPSchema (ZSRef (ZSPlain "c") [] [])))
-- \\begin{axdef}\n    a,b:T\n\\where\n    a < b\n\\end{axdef}
t89 = ZAxDef [Choose ("a",[]) (ZVar ("T",[])),Choose ("b",[]) (ZVar ("T",[])),Check (ZMember (ZTuple [ZVar ("a",[]),ZVar ("b",[])]) (ZVar ("<",[])))]
-- \\begin{axdef}\n    a,b:T\n\\end{axdef}
t90 = ZAxDef [Choose ("a",[]) (ZVar ("T",[])),Choose ("b",[]) (ZVar ("T",[]))]
-- \\begin{schema}{State} r:42 \\where \\lnot true \\\\ 3 = 4 \\\\ 3 \\in 4 \\end{schema}
t91 = ZSchemaDef (ZSPlain "State") (ZSchema [Choose ("r",[]) (ZInt 42),Check (ZNot ztrue),Check (ZEqual (ZInt 3) (ZInt 4)),Check (ZMember (ZInt 3) (ZInt 4))])
