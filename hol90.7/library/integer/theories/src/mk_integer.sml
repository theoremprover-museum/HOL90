(*======================================================================*)
(* FILE		: mk_integer.sml					*)
(* DESCRIPTION  : defines the type of integer, the operations of	*)
(*                plus, minus, neg, and times, the predicates POS,	*)
(*                and NEG, and the relation below.  Develops much of	*)
(*                the basic algebraic, and some basic order theoretic	*)
(*                properties of the integers.				*)
(*									*)
(*									*)
(* AUTHOR	: E. L. Gunter						*)
(* DATE		: 89.3.23						*)
(*									*)
(* Modified     : 23 July 1989 to include more theorems. ELG		*)
(*									*)
(* TRANSLATED   : 91.26.12						*)
(*									*)
(*======================================================================*)

(* Copyright 1991 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

val _ = Lib.clean_directory ((!Globals.HOLdir)^"library/integer/theories/"^
			     (Globals.theory_file_type))

val _ = load_theory "elt_gp";
val _ = Library.load_library{lib = Sys_lib.group_lib, theory = "-"};

val _ = new_theory "integer";

val _ = Library.load_library{lib = Sys_lib.utils_lib,theory = "-"};
open ExtraGeneralFunctions;



local
    fun code file = (!HOLdir)^"library/integer/src/"^file
in
    val _ = compile (code "integer_tac.sig");
    val _ = compile (code "integer_tac.sml");
end;

open IntegerTactics;

(* Set the path to write the theory to. *)

local
    val path = (!HOLdir)^"library/integer/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;


(* Theorems needed from parent theories *)
val _ = add_theory_to_sml "arithmetic";

val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0"
val LESS_0 = theorem "prim_rec" "LESS_0"
val PAIR = theorem "pair" "PAIR"
val PAIR_EQ = theorem "pair" "PAIR_EQ";

val integer_TY_DEF =
    new_type_definition
     {name = "integer",
      pred = (--`\X.(?p. (p,0) = X) \/ (?n. (0,n) = X)`--),
      inhab_thm = prove((--`?X.(\X.(?p. (p,0) = X) \/ (?n. (0,n) = X))X`--),
			EXISTS_TAC (--`(0,0)`--) THEN BETA_TAC THEN
			DISJ1_TAC THEN EXISTS_TAC (--`0`--) THEN REFL_TAC)};

(*
val integer_TY_DEF =
  |- ?rep. TYPE_DEFINITION (\X. (?p. (p,0) = X) \/ (?n. (0,n) = X)) rep : thm
*)


val integer_ISO_DEF =
  define_new_type_bijections
    {name = "integer_ISO_DEF",
     ABS = "ABS_integer",
     REP = "REP_integer",
     tyax = integer_TY_DEF};

(*
val integer_ISO_DEF =
  |- (!a. ABS_integer (REP_integer a) = a) /\
     (!r. (\X. (?p. (p,0) = X) \/ (?n. (0,n) = X)) r =
          REP_integer (ABS_integer r) = r) : thm
*)


val thm1 = prove_rep_fn_one_one integer_ISO_DEF;
val thm2 = BETA_RULE (prove_rep_fn_onto integer_ISO_DEF);

(*
val thm1 = |- !a a'. (REP_integer a = REP_integer a') = a = a' : thm
val thm2 = 
  |- !r. (?p. (p,0) = r) \/ (?n. (0,n) = r) = (?a. r = REP_integer a) : thm
*)


val thm3 = prove
((--`!M.(?p. (p,0) = REP_integer M) \/ (?n. (0,n) = REP_integer M)`--),
 GEN_TAC THEN (PURE_REWRITE_TAC[thm2]) THEN
 (EXISTS_TAC (--`M:integer`--)) THEN
 REFL_TAC);

(*
val thm3 =
  |- !M. (?p. (p,0) = REP_integer M) \/ (?n. (0,n) = REP_integer M) : thm
*)


(*
 In defining the operations on the integers, we shall generally proceed by
 definining appropriate opperations on (==`:num#num`==) and then projecting
 on to the integers.
*)

val PROJ_DEF = new_definition("PROJ_DEF", 
(--`proj (p,n)= (n < p => (@N.REP_integer N = (p-n,0))
                        | (@N.REP_integer N = (0,n-p)))`--));

(*
val PROJ_DEF =
  |- !p n.
       proj (p,n) =
       ((n < p)
        => (@N. REP_integer N = (p - n,0))
        | (@N. REP_integer N = (0,n - p))) : thm
*)


(*
   What follows is a collection of lemmas useful for dealing with proj
*)

val thm4 = prove
((--`!M.(?p.M = proj(p,0)) \/ (?n.M = proj(0,n))`--),
 GEN_TAC THEN
 DISJ_CASES_TAC (SPEC (--`M:integer`--) thm3) THEN
 POP_ASSUM STRIP_ASSUME_TAC THEN
 REWRITE_TAC [PROJ_DEF,NOT_LESS_0,SUB_0,SYM (SPEC_ALL thm1)] THENL
 [DISJ1_TAC THEN EXISTS_TAC (--`p:num`--),
  DISJ2_TAC THEN EXISTS_TAC (--`n:num`--)] THEN
 FIRST_ASSUM SUBST1_TAC THENL [COND_CASES_TAC, ALL_TAC] THENL
 [ALL_TAC,
  REWRITE_TAC[REWRITE_RULE[SYM (REWRITE_RULE
                                 [(ASSUME (--`~(0 < p)`--))]
			         (SPEC (--`p:num`--) LESS_0_CASES))]
	                   (ASSUME (--`(p,0) = REP_integer M`--))],
  ALL_TAC] THEN
 CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
 EXISTS_TAC (--`M:integer`--) THEN REFL_TAC);

val PROJ_ONTO = store_thm("PROJ_ONTO",
(--`!M.?n.?p.M = proj(p,n)`--),
GEN_TAC THEN STRIP_ASSUME_TAC (SPEC (--`M:integer`--) thm4) THENL
[((EXISTS_TAC (--`0`--)) THEN (EXISTS_TAC (--`p:num`--)) THEN
  (ASM_REWRITE_TAC[])),
 ((EXISTS_TAC (--`n:num`--)) THEN (EXISTS_TAC (--`0`--)) THEN
  (ASM_REWRITE_TAC[]))]);

(*
val PROJ_ONTO = |- !M. ?n p. M = proj (p,n) : thm
*)

val thm5  = prove
((--`!p. REP_integer(@N.REP_integer N = (p,0))= (p,0)`--),
 GEN_TAC THEN CONV_TAC (SELECT_CONV THENC (ONCE_DEPTH_CONV SYM_CONV)) THEN
 PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL thm2)] THEN
 DISJ1_TAC THEN EXISTS_TAC (--`p:num`--) THEN REFL_TAC);

(*
val thm5 = |- !p. REP_integer (@N. REP_integer N = (p,0)) = (p,0) : thm
*)


val thm6  = prove
((--`!n. REP_integer(@N.REP_integer N = (0,n))= (0,n)`--),
 GEN_TAC THEN CONV_TAC (SELECT_CONV THENC (ONCE_DEPTH_CONV SYM_CONV)) THEN
 PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL thm2)] THEN
 DISJ2_TAC THEN EXISTS_TAC (--`n:num`--) THEN REFL_TAC);

(*
val thm6 = |- !n. REP_integer (@N. REP_integer N = (0,n)) = (0,n) : thm
*)


val PROJ_REP = store_thm ("PROJ_REP",
(--`!N.proj (REP_integer N) = N`--),
let
    val N = (--`N:integer`--)
    val p = (--`p:num`--)
    val posN = (--`(p,0) = REP_integer N`--)
    val negN = (--`(0,n) = REP_integer N`--)
    val p_is_0 = (--`p = 0`--)
in
GEN_TAC THEN
(PURE_ONCE_REWRITE_TAC [(SYM (SPEC_ALL PAIR))]) THEN
(PURE_ONCE_REWRITE_TAC [PROJ_DEF]) THEN
(STRIP_ASSUME_TAC (SPEC N thm3)) THENL
[((REWRITE_TAC[(SYM (ASSUME posN)),SUB_0]) THEN
  COND_CASES_TAC THENL
  [((REWRITE_TAC [(SYM (SPEC_ALL thm1)),thm5]) THEN (FIRST_ASSUM ACCEPT_TAC)),
   (((STRIP_ASSUME_TAC
      (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)(SPEC p LESS_0_CASES))) THEN
      RES_TAC) THEN
     (REWRITE_TAC [(SYM (SPEC_ALL thm1)),thm5]) THEN
     (REWRITE_TAC [(SYM (ASSUME posN)),(ASSUME p_is_0)]))]),
 ((REWRITE_TAC[(SYM (ASSUME negN)),SUB_0,NOT_LESS_0]) THEN
  (ASM_REWRITE_TAC [(SYM (SPEC_ALL thm1)),thm6]))]
end);

(*
val PROJ_REP = |- !N. proj (REP_integer N) = N :thm
*)


val REP_PROJ = store_thm("REP_PROJ",
(--`(!p.REP_integer(proj (p,0)) = (p,0)) /\
    (!n.REP_integer(proj (0,n)) = (0,n))`--),
let
    val p = (--`p:num`--)
in
(REWRITE_TAC [PROJ_DEF,SUB_0,NOT_LESS_0,thm6]) THEN
GEN_TAC THEN COND_CASES_TAC THEN (REWRITE_TAC []) THENL
[(ACCEPT_TAC (SPEC p thm5)),
 ((STRIP_ASSUME_TAC
   (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)(SPEC p LESS_0_CASES))) THEN
  RES_TAC THEN
  (ASM_REWRITE_TAC [thm5]))]
end);

(*
val REP_PROJ =
  |- (!p. REP_integer (proj (p,0)) = (p,0)) /\
     (!n. REP_integer (proj (0,n)) = (0,n)) :thm
*)


val LESS_EQ_IMP_LESS_EQ_ADD =
    prove ((--`!p n n'. (n <= p) ==> (n <= p + n')`--),
	   ((REPEAT STRIP_TAC) THEN
	    (DISJ_CASES_TAC
	     (PURE_ONCE_REWRITE_RULE
	      [LESS_OR_EQ]
	      (ASSUME (--`n <= p`--))) THENL
	     [((PURE_ONCE_REWRITE_TAC [LESS_OR_EQ]) THEN DISJ1_TAC THEN
	       (NEW_MATCH_ACCEPT_TAC
		(SPEC_ALL (UNDISCH (SPEC_ALL LESS_IMP_LESS_ADD))))),
	      ((PURE_ONCE_ASM_REWRITE_TAC []) THEN
	       NEW_MATCH_ACCEPT_TAC LESS_EQ_ADD)])));

local
    val p = (--`p:num`--) and n = (--`n:num`--) and n' = (--`n':num`--)
in
val SUB_ADD_ADD_SUB =
    prove ((--`!p n n'. (n <= p) ==> ((p - n) + n' = (p + n') - n)`--),
	   ((REPEAT STRIP_TAC) THEN
	    (NEW_SUBST1_TAC (SYM (UNDISCH
				  (SPECL
				   [(--`(p - n) + n'`--),n,(--`(p + n')`--)]
				   ADD_EQ_SUB)))) THENL
	    [((PURE_ONCE_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]) THEN
	      (NEW_SUBST1_TAC (SPECL [n',n] ADD_SYM)) THEN
	      (PURE_ONCE_REWRITE_TAC[SPEC_ALL ADD_ASSOC]) THEN
	      (NEW_SUBST1_TAC (UNDISCH (SPECL [p,n] SUB_ADD)))THEN
	      REFL_TAC),
	    NEW_MATCH_ACCEPT_TAC
	    (UNDISCH (SPEC_ALL LESS_EQ_IMP_LESS_EQ_ADD))]))
end;


local
    val p = (--`p:num`--) and n = (--`n:num`--)
    and p' = (--`p':num`--) and n' = (--`n':num`--)
in
val PROJ_EQ = store_thm("PROJ_EQ",
(--`!p n p' n'. (proj(p,n) = proj(p',n')) = (p + n' = p' + n)`--),
REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[PROJ_DEF] THEN
COND_CASES_TAC THEN COND_CASES_TAC THEN
PURE_ONCE_REWRITE_TAC [(SYM(SPEC_ALL thm1))] THEN
ASM_REWRITE_TAC[thm5,thm6,PAIR_EQ,(SYM_CONV (--`0 = m`--)),SUB_EQ_0] THENL

[(* Case: n < p and n' < p' *)

 (ASSUME_TAC (UNDISCH(SPECL [n,p]LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC (UNDISCH(SPECL [n',p']LESS_IMP_LESS_OR_EQ)) THEN
  NEW_SUBST1_TAC
    (SYM (UNDISCH (SPECL [(--`p - n`--),n',p'] ADD_EQ_SUB))) THEN
  NEW_SUBST1_TAC (UNDISCH (SPEC_ALL SUB_ADD_ADD_SUB)) THEN
  NEW_SUBST1_TAC (SYM_CONV (--`(p + n') - n = p'`--)) THEN
  NEW_SUBST1_TAC (SYM_CONV (--`p + n' = p' + n`--)) THEN
  NEW_MATCH_ACCEPT_TAC
    (SYM (UNDISCH (SPECL [p',n,(--`(p + n')`--)] ADD_EQ_SUB))) THEN
  NEW_MATCH_ACCEPT_TAC
    (UNDISCH (SPEC_ALL LESS_EQ_IMP_LESS_EQ_ADD))),

 (* Case:  n < p  and  ~(n' < p') *)

 (ASM_REWRITE_TAC [SYM(SPEC_ALL NOT_LESS)] THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE[NOT_LESS](ASSUME (--`~(n' < p')`--))) THEN
  STRIP_ASSUME_TAC (UNDISCH (SPECL [p,n] LESS_ADD_1)) THEN
  DISJ_CASES_TAC
    (PURE_ONCE_REWRITE_RULE [LESS_OR_EQ] (ASSUME (--`p' <= n'`--))) THENL
  [(* p' < n' *)
   (STRIP_ASSUME_TAC (UNDISCH (SPECL [n',p'] LESS_ADD_1)) THEN
    ASM_REWRITE_TAC[] THEN
    NEW_SUBST1_TAC
      (SPECL [(--`n + p'' + 1`--),p',(--`p''' + 1`--)] ADD_ASSOC) THEN
    NEW_SUBST1_TAC (SPECL [(--`n + p'' + 1`--),p'] ADD_SYM) THEN
    PURE_REWRITE_TAC [SYM (SPEC_ALL ADD_ASSOC)] THEN
    NEW_SUBST1_TAC (SPECL [p',n,(--`p'' + 1 + p''' + 1`--)] ADD_ASSOC) THEN
    REWRITE_TAC [ADD_INV_0_EQ,
		 SYM (SPEC_ALL ADD1),
		 ADD_CLAUSES,
		 CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) SUC_NOT]),
   (* p' = n' *)
   (ASM_REWRITE_TAC[] THEN
    NEW_SUBST1_TAC (SPECL [(--`n + p'' + 1`--),n'] ADD_SYM) THEN
    PURE_REWRITE_TAC [SYM (SPEC_ALL ADD_ASSOC)] THEN
    NEW_SUBST1_TAC (SPECL [n',n,(--`p'' + 1`--)] ADD_ASSOC) THEN
    REWRITE_TAC [ADD_INV_0_EQ,
		 SYM (SPEC_ALL ADD1),
		 ADD_CLAUSES,
		 CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) SUC_NOT])]),

 (* Case: n' < p' and  ~(n < p)  *)
 (ASM_REWRITE_TAC [SYM(SPEC_ALL NOT_LESS)] THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE[NOT_LESS](ASSUME (--`~(n < p)`--))) THEN
  STRIP_ASSUME_TAC (UNDISCH (SPECL [p',n'] LESS_ADD_1)) THEN
  DISJ_CASES_TAC
    (PURE_ONCE_REWRITE_RULE [LESS_OR_EQ] (ASSUME (--`p <= n`--))) THENL
  [(* p < n *)
   (STRIP_ASSUME_TAC (UNDISCH (SPECL [n,p] LESS_ADD_1)) THEN
    ASM_REWRITE_TAC[] THEN
    NEW_SUBST1_TAC
      (SPECL [(--`n' + p'' + 1`--),p,(--`p''' + 1`--)] ADD_ASSOC) THEN
    NEW_SUBST1_TAC (SPECL [(--`n' + p'' + 1`--),p] ADD_SYM) THEN
    PURE_REWRITE_TAC [SYM (SPEC_ALL ADD_ASSOC)] THEN
    NEW_SUBST1_TAC (SPECL [p,n',(--`p'' + 1 + p''' + 1`--)] ADD_ASSOC) THEN
    CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC [ADD_INV_0_EQ,
		 SYM (SPEC_ALL ADD1),
		 ADD_CLAUSES,
		 CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) SUC_NOT]),
     (* p' = n' *)
   (ASM_REWRITE_TAC[] THEN
    NEW_SUBST1_TAC (SPECL [(--`n' + p'' + 1`--),n] ADD_SYM) THEN
    PURE_REWRITE_TAC [SYM (SPEC_ALL ADD_ASSOC)] THEN
    NEW_SUBST1_TAC (SPECL [n,n',(--`p'' + 1`--)] ADD_ASSOC) THEN
    CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC [ADD_INV_0_EQ,
		 SYM (SPEC_ALL ADD1),
		 ADD_CLAUSES,
		 CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) SUC_NOT])]),

 (* Case: n < p and n' < p' *)
 (ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE[NOT_LESS](ASSUME (--`~(n < p)`--))) THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE[NOT_LESS](ASSUME (--`~(n' < p')`--))) THEN
  PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN
  NEW_SUBST1_TAC
    (SYM (UNDISCH (SPECL [(--`n - p`--),p',n'] ADD_EQ_SUB))) THEN
  NEW_SUBST1_TAC (UNDISCH (SPECL [n,p,p'] SUB_ADD_ADD_SUB)) THEN
  NEW_SUBST1_TAC (SYM_CONV (--`(n + p') - p = n'`--)) THEN
  NEW_MATCH_ACCEPT_TAC
    (SYM (UNDISCH (SPECL [n',p,(--`(n + p')`--)] ADD_EQ_SUB))) THEN
  NEW_MATCH_ACCEPT_TAC
    (UNDISCH (SPEC_ALL LESS_EQ_IMP_LESS_EQ_ADD)))])

end;

(*
val PROJ_EQ =
  |- !p n p' n'. (proj (p,n) = proj (p',n')) = p + n' = p' + n :thm
*)


(* The Natural Numbers can be embedded into the integers. *)

val INT_DEF = new_definition ("INT_DEF",(--`INT p=proj(p,0)`--));

(* val INT_DEF = |- !p. INT p = proj (p,0) : thm *)


val INT_ONE_ONE = store_thm ("INT_ONE_ONE",
(--`!m n.(INT m =INT n) = (m = n)`--),
REPEAT GEN_TAC THEN REWRITE_TAC[INT_DEF,PROJ_EQ,ADD_CLAUSES]);

(*
  Infix strength:
   plus == 500
   minus == 500
   times == 600
   div == 650
   mod == 650
   below == 450
*)

val PLUS_DEF =
new_infix_definition
("PLUS_DEF",
 (--`plus M N =  proj((FST(REP_integer M)) + (FST(REP_integer N)),
		      (SND(REP_integer M)) + (SND(REP_integer N)))`--),
 500);

(*
val PLUS_DEF =
  |- !M N.
       M plus N =
       proj
         (FST (REP_integer M) + FST (REP_integer N),
         SND (REP_integer M) + SND (REP_integer N)) :thm
*)


local
    val p = (--`p:num`--) and n = (--`n:num`--)
    and p' = (--`p':num`--) and n' = (--`n':num`--)
in
val PROJ_PLUS = store_thm("PROJ_PLUS",
(--`!p n p' n'. (proj(p,n)) plus (proj(p',n')) = proj(p + p',n + n')`--),
REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [PLUS_DEF] THEN
PURE_ONCE_REWRITE_TAC [PROJ_EQ] THEN
PURE_ONCE_REWRITE_TAC [PROJ_DEF] THEN
COND_CASES_TAC THEN COND_CASES_TAC THEN 
REWRITE_TAC [thm5,thm6,ADD_CLAUSES] THENL

[(* Case: (--`n < p`--) and (--`n' < p'--) *)

 (ASSUME_TAC (UNDISCH(SPECL [n,p] LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC (UNDISCH(SPECL [n',p'] LESS_IMP_LESS_OR_EQ)) THEN
  SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD_ADD_SUB)) THEN
  SUBST_MATCH_TAC (SPEC_ALL ADD_ASSOC) THEN
  (SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD)) THENL
   [ALL_TAC,
    MATCH_ACCEPT_TAC (UNDISCH (SPEC_ALL LESS_EQ_IMP_LESS_EQ_ADD))]) THEN
  SUBST_MATCH_TAC (SYM (SPEC_ALL ADD_ASSOC)) THEN
  SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD)) THEN REFL_TAC),

 (* Case: (--`n < p`--) and (--`~(n' < p')`--) *)

 (ASSUME_TAC (UNDISCH(SPECL [n,p] LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n' < p')`--))) THEN
  SUBST_MATCH_TAC (SPEC_ALL ADD_ASSOC) THEN
  SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD)) THEN
  SUBST_MATCH_TAC (SYM (SPEC_ALL ADD_ASSOC)) THEN
  NEW_SUBST1_TAC (SPECL [p',(--`n' - p'`--)] ADD_SYM) THEN
  SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD_ADD_SUB)) THEN
  SUBST_MATCH_TAC ADD_SUB THEN REFL_TAC),

 (* Case: (--`~(n < p)`--) and (--`n' < p'`--) *)

 (ASSUME_TAC (UNDISCH(SPECL [n',p']LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n < p)`--))) THEN
  NEW_SUBST1_TAC (SPECL [n,n'] ADD_SYM) THEN
  NEW_SUBST1_TAC (SPECL [(--`p + p'`--),(--`n - p`--)] ADD_SYM) THEN
  REPEAT (SUBST_MATCH_TAC (SPEC_ALL ADD_ASSOC)) THEN
  REPEAT (SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD))) THEN
  MATCH_ACCEPT_TAC ADD_SYM),

 (* Case: (--`~(n < p)`--) and (--`~(n' < p')`--) *)

 (ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n < p)`--))) THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n' < p')`--))) THEN
  SUBST_MATCH_TAC ADD_ASSOC THEN
  NEW_SUBST1_TAC (SPECL [(--`p + p'`--),(--`n - p`--)] ADD_SYM) THEN
  SUBST_MATCH_TAC ADD_ASSOC THEN
  SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD)) THEN
  SUBST_MATCH_TAC (SYM (SPEC_ALL ADD_ASSOC)) THEN
  NEW_SUBST1_TAC (SPECL [p', (--`n' - p'`--)] ADD_SYM) THEN
  SUBST_MATCH_TAC (UNDISCH (SPEC_ALL SUB_ADD)) THEN
  REFL_TAC)])
end;

(*
val PROJ_PLUS =
  |- !p n p' n'. proj (p,n) plus proj (p',n') = proj (p + p',n + n') :thm
*)


val NUM_ADD_IS_INT_ADD = store_thm ("NUM_ADD_IS_INT_ADD",
(--`!m n. (INT m) plus (INT n) = INT (m + n)`--),
REPEAT GEN_TAC THEN
REWRITE_TAC [INT_DEF,PLUS_DEF,ADD_CLAUSES,PROJ_EQ,REP_PROJ]);

(*
val NUM_ADD_IS_INT_ADD = |- !m n. INT m plus INT n = INT (m + n) :thm
*)


val ASSOC_PLUS = store_thm("ASSOC_PLUS",
(--`!M N P. M plus (N plus P) = (M plus N) plus P`--),
REPEAT GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC (--`M:integer`--) PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC (--`N:integer`--) PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC (--`P:integer`--) PROJ_ONTO) THEN
ASM_REWRITE_TAC [PROJ_PLUS,ADD_ASSOC]);

(*
val ASSOC_PLUS = |- !M N P. M plus N plus P = (M plus N) plus P :thm
*)


val COMM_PLUS = store_thm("COMM_PLUS",
(--`!M N. M plus N = N plus M`--),
REPEAT GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC (--`M:integer`--) PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC (--`N:integer`--) PROJ_ONTO) THEN
ASM_REWRITE_TAC [PROJ_PLUS,PROJ_EQ] THEN
NEW_SUBST1_TAC (SPECL [(--`n:num`--),(--`n':num`--)] ADD_SYM) THEN
NEW_SUBST1_TAC (SPECL [(--`p:num`--),(--`p':num`--)] ADD_SYM)THEN
REFL_TAC);

(*
val COMM_PLUS = |- !M N. M plus N = N plus M :thm
*)


val PROJ_ZERO = store_thm("PROJ_ZERO",
(--`!m. proj(m,m) = INT 0`--),
GEN_TAC THEN REWRITE_TAC[INT_DEF, PROJ_EQ, ADD_CLAUSES]);

(*
val PROJ_ZERO = |- !m. proj (m,m) = INT 0 :thm
*)


val PLUS_ID = store_thm("PLUS_ID",
(--`!M. (INT 0) plus M = M`--),
GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC (--`M:integer`--) PROJ_ONTO) THEN
ASM_REWRITE_TAC[INT_DEF, PROJ_PLUS, ADD_CLAUSES]);

(*
val PLUS_ID = |- !M. INT 0 plus M = M :thm
*)


val PLUS_INV = store_thm("PLUS_INV",
(--`!M.?N. N plus M = INT 0`--),
GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC (--`M:integer`--) PROJ_ONTO) THEN
EXISTS_TAC (--`proj(n,p)`--) THEN
ASM_REWRITE_TAC[INT_DEF,PROJ_PLUS,PROJ_EQ,ADD_CLAUSES] THEN
MATCH_ACCEPT_TAC ADD_SYM);

(*
val PLUS_INV = |- !M. ?N. N plus M = INT 0 :thm
*)


(*
 Now we have proven the pieces neccesary to show that the integers under
 addition form a group.  We shall formally prove this fact, and then
 instantiate the theory of groups in this particular case.
*)


val integer_as_GROUP = store_thm("integer_as_GROUP",
(--`GROUP((\N:integer.T), $plus)`--),
(PURE_ONCE_REWRITE_TAC[(definition "elt_gp" "GROUP_DEF")]) THEN
BETA_TAC THEN
REWRITE_TAC[(SYM (SPEC_ALL ASSOC_PLUS))] THEN
EXISTS_TAC (--`INT 0`--) THEN
REWRITE_TAC[PLUS_ID,PLUS_INV]);


(*
val integer_as_GROUP = |- GROUP ((\N. T),plus) :thm
*)


structure IntPlusGroup : GroupSig =
    struct
	val IsGroupThm = integer_as_GROUP
	val InstStructureName = "IntPlusGroupFun"
    end;

structure IntPlusGroupFun = GroupFunFunc(IntPlusGroup);

open IntPlusGroupFun;


val ID_EQ_0 = store_thm("ID_EQ_0",
(--`ID((\N:integer.T),^(--`$plus`--)) = INT 0`--),
PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
MP_IMP_TAC
 (SPEC
  (--`INT 0`--) 
  (return_GROUP_thm {elt_gp_thm_name = "UNIQUE_ID", rewrites = []})) THEN
DISJ1_TAC THEN
EXISTS_TAC (--`M:integer`--) THEN
ACCEPT_TAC (SPEC (--`M:integer`--) PLUS_ID));

(*
val ID_EQ_0 = |- ID ((\N. T),plus) = INT 0 :thm
*)


val neg_DEF = new_definition("neg_DEF",
(--`neg = INV((\N:integer.T),^(--`$plus`--))`--));

(*
val neg_DEF = |- neg = INV ((\N. T),plus) :thm
*)


val _ = include_GROUP_theory {thm_name_prefix = "PLUS",
			      rewrites = [ID_EQ_0,(SYM neg_DEF)]};

(*
 * val PLUS_GROUP_ASSOC =
 *   |- !x y z. (x plus y) plus z = x plus y plus z :thm
 * val PLUS_ID_LEMMA =
 *   |- (!x. INT 0 plus x = x) /\
 *    (!x. x plus INT 0 = x) /\
 *      (!x. ?y. y plus x = INT 0) :thm
 * val PLUS_LEFT_RIGHT_INV =
 *   |- !x y. (y plus x = INT 0) ==> (x plus y = INT 0) :thm
 * val PLUS_INV_LEMMA =
 *   |- !x. (neg x plus x = INT 0) /\ (x plus neg x = INT 0) :thm
 * val PLUS_LEFT_CANCELLATION =
 *   |- !x y z. (x plus y = x plus z) ==> (y = z) :thm
 * val PLUS_RIGHT_CANCELLATION =
 *   |- !x y z. (y plus x = z plus x) ==> (y = z) :thm
 * val PLUS_RIGHT_ONE_ONE_ONTO =
 *   |- !x y. ?z. (x plus z = y) /\ (!u. (x plus u = y) ==> (u = z)) :thm
 * val PLUS_LEFT_ONE_ONE_ONTO =
 *   |- !x y. ?z. (z plus x = y) /\ (!u. (u plus x = y) ==> (u = z)) :thm
 * val PLUS_UNIQUE_ID =
 *   |- !e. (?x. e plus x = x) \/ (?x. x plus e = x) ==> (e = INT 0) :thm
 * val PLUS_UNIQUE_INV = |- !x u. (u plus x = INT 0) ==> (u = neg x)
 *   :thm
 * val PLUS_INV_ID_LEMMA = |- neg (INT 0) = INT 0 :thm
 * val PLUS_INV_INV_LEMMA = |- !x. neg (neg x) = x :thm
 * val PLUS_DIST_INV_LEMMA =
 *   |- !x y. neg x plus neg y = neg (y plus x) :thm
 * val it = () :unit
 *****)


val PROJ_neg = store_thm("PROJ_neg",
(--`!p n. neg (proj(p,n)) = proj(n,p)`--),
REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
MATCH_MP_IMP_TAC PLUS_UNIQUE_INV THEN
PURE_ONCE_REWRITE_TAC [PROJ_PLUS] THEN
SUBST1_TAC (SPECL[(--`p:num`--),(--`n:num`--)] ADD_SYM) THEN
MATCH_ACCEPT_TAC PROJ_ZERO);

(*
val PROJ_neg = |- !p n. neg (proj (p,n)) = proj (n,p) : thm
*)


val MINUS_DEF = new_infix_definition ("MINUS_DEF",
 (--`minus M N = M plus (neg N)`--),500);

(*
val MINUS_DEF = |- !M N. M minus N = M plus neg N :thm
*)



(* The multiplicative structure of the integers *)

val TIMES_DEF = new_infix_definition("TIMES_DEF",
(--`times M N =
      proj(
	   (((FST(REP_integer M)) * (FST(REP_integer N))) +
	    ((SND(REP_integer M)) * (SND(REP_integer N)))),
	   (((FST(REP_integer M)) * (SND(REP_integer N))) +
	    ((SND(REP_integer M)) * (FST(REP_integer N)))) )`--),
600);

(*
 * val TIMES_DEF =
 *   |- !M N.
 *        M times N =
 *        proj
 *          (FST (REP_integer M) * FST (REP_integer N) +
 *           SND (REP_integer M) * SND (REP_integer N),
 *          FST (REP_integer M) * SND (REP_integer N) +
 *          SND (REP_integer M) * FST (REP_integer N)) :thm
 ***)


val LEFT_SUB_DISTRIB = prove ((--`!m n p. m * (n - p) = m * n - m * p`--),
REPEAT GEN_TAC THEN
PURE_ONCE_REWRITE_TAC [MULT_SYM] THEN
MATCH_ACCEPT_TAC RIGHT_SUB_DISTRIB);

(*
val LEFT_SUB_DISTRIB = |- !m n p. m * (n - p) = m * n - m * p :thm
*)

val LESS_EQ_ADD_DIFF = prove(--`!m n. m <= n ==> (?p. m + p = n)`--,
PURE_ONCE_REWRITE_TAC[ADD_SYM,LESS_OR_EQ] THEN
REPEAT STRIP_TAC THENL
[NEW_MATCH_ACCEPT_TAC(UNDISCH(SPEC_ALL LESS_ADD)),
 EXISTS_TAC (--`0`--) THEN
 ASM_REWRITE_TAC[ADD_CLAUSES]]);

(*
val LESS_EQ_ADD_DIFF = |- !m n. m <= n ==> (?p. m + p = n) :thm
*)


local
    val p = (--`p:num`--) and n = (--`n:num`--)
    and p' = (--`p':num`--) and n' = (--`n':num`--)
in
val CROSS_TERMS = prove 
((--`!n n' p p'.((n <= p) /\ (n' <= p')) ==>
		 n * p' + p * n' <= p * p' + n * n'`--),
REPEAT STRIP_TAC THEN
STRIP_ASSUME_TAC
  (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)
   (UNDISCH (SPECL [n,p] LESS_EQ_ADD_DIFF))) THEN
STRIP_ASSUME_TAC
  (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)
   (UNDISCH (SPECL [n',p'] LESS_EQ_ADD_DIFF))) THEN
ASM_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] THEN
NEW_SUBST1_TAC(SYM(SPECL[(--`n * n' + n * p'''`--),
			 (--`p'' * n' + p'' * p'''`--),
			 (--`n * n'`--)] ADD_ASSOC)) THEN
NEW_SUBST1_TAC(SPECL[(--`p'' * n' + p'' * p'''`--),(--`n * n'`--)]ADD_SYM) THEN
REWRITE_TAC[ADD_ASSOC,LESS_EQ_ADD])
end;

(*
val CROSS_TERMS =
  |- !n n' p p'.
       n <= p /\ n' <= p' ==> n * p' + p * n' <= p * p' + n * n'
*)


local
    val p = (--`p:num`--) and n = (--`n:num`--)
    and p' = (--`p':num`--) and n' = (--`n':num`--)
in
val PROJ_TIMES = store_thm("PROJ_TIMES",
(--`!p n p' n'. proj(p,n) times proj(p',n') =
	     proj((p * p') + (n * n'),(p * n') + (n * p'))`--),
REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [TIMES_DEF] THEN
PURE_ONCE_REWRITE_TAC [PROJ_EQ] THEN
PURE_ONCE_REWRITE_TAC [PROJ_DEF] THEN
COND_CASES_TAC THEN COND_CASES_TAC THEN 
REWRITE_TAC [thm5, thm6, ADD_CLAUSES,  MULT_CLAUSES] THEN
REWRITE_TAC [RIGHT_SUB_DISTRIB, LEFT_SUB_DISTRIB] THENL

[(* Case: (--`n < p`--) and (--`n' < p'--) *)

 (ASSUME_TAC (UNDISCH(SPECL [n,p] LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC (UNDISCH(SPECL [n',p'] LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [n',p',n]LESS_MONO_MULT))) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [n',p',p]LESS_MONO_MULT))) THEN
  SUBST_MATCH_TAC (UNDISCH(SPEC_ALL SUB_SUB)) THEN
  NEW_SUBST1_TAC
   (UNDISCH(SPECL [(--`p * p'`--),(--`p * n'`--),(--`n * n'`--)]
	          SUB_ADD_ADD_SUB)) THEN
  SUBST_MATCH_TAC (SYM(SPEC_ALL SUB_PLUS)) THEN
  MATCH_MP_IMP_TAC SUB_ADD THEN
  NEW_SUBST1_TAC (SPECL [(--`p * n'`--),(--`n * p'`--)] ADD_SYM) THEN
  MATCH_MP_IMP_TAC CROSS_TERMS THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC),

 (* Case: (--`n < p`--) and (--`~(n' < p')`--) *)

 (ASSUME_TAC (UNDISCH(SPECL [n,p] LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n' < p')`--))) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [p',n',n]LESS_MONO_MULT))) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [p',n',p]LESS_MONO_MULT))) THEN
  SUBST_MATCH_TAC (UNDISCH(SPEC_ALL SUB_SUB)) THEN
  SUBST_MATCH_TAC (UNDISCH(SPEC_ALL SUB_ADD_ADD_SUB)) THEN
  SUBST_MATCH_TAC (SYM(SPEC_ALL SUB_PLUS)) THEN
  NEW_MATCH_ACCEPT_TAC
   (SYM(UNDISCH(SPEC_ALL(PURE_ONCE_REWRITE_RULE[ADD_SYM]SUB_ADD)))) THEN
  NEW_SUBST1_TAC (SPECL [(--`p * p'`--),(--`n * n'`--)] ADD_SYM) THEN
  MATCH_MP_IMP_TAC CROSS_TERMS THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC),

 (* Case: (--`~(n < p)`--) and (--`n' < p'`--) *)

 (ASSUME_TAC (UNDISCH(SPECL [n',p'] LESS_IMP_LESS_OR_EQ)) THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n < p)`--))) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [n',p',p]LESS_MONO_MULT))) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [n',p',n]LESS_MONO_MULT))) THEN
  SUBST_MATCH_TAC (UNDISCH(SPEC_ALL SUB_SUB)) THEN
  SUBST_MATCH_TAC (UNDISCH(SPEC_ALL SUB_ADD_ADD_SUB)) THEN
  SUBST_MATCH_TAC (SYM(SPEC_ALL SUB_PLUS)) THEN
  NEW_SUBST1_TAC (SPECL [(--`n * n'`--),(--`p * p'`--)] ADD_SYM) THEN
  NEW_SUBST1_TAC (SPECL [(--`n * p'`--),(--`p * n'`--)] ADD_SYM) THEN
  NEW_MATCH_ACCEPT_TAC
   (SYM(UNDISCH(SPEC_ALL(PURE_ONCE_REWRITE_RULE[ADD_SYM]SUB_ADD)))) THEN
  NEW_SUBST1_TAC (SPECL [(--`p * n'`--),(--`n * p'`--)] ADD_SYM) THEN
  MATCH_MP_IMP_TAC CROSS_TERMS THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC),

 (* Case: (--`~(n < p)`--) and (--`~(n' < p')`--) *)

 (ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n < p)`--))) THEN
  ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE [NOT_LESS] (ASSUME(--`~(n' < p')`--))) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [p',n',p]LESS_MONO_MULT))) THEN
  ASSUME_TAC (PURE_ONCE_REWRITE_RULE [MULT_SYM]
	      (UNDISCH(SPECL [p',n',n]LESS_MONO_MULT))) THEN
  SUBST_MATCH_TAC (UNDISCH(SPEC_ALL SUB_SUB)) THEN
  NEW_SUBST1_TAC
   (UNDISCH(SPECL [(--`n * n'`--),(--`n * p'`--),(--`p * p'`--)]
	          SUB_ADD_ADD_SUB)) THEN
  SUBST_MATCH_TAC (SYM(SPEC_ALL SUB_PLUS)) THEN
  NEW_SUBST1_TAC (SPECL [(--`p * p'`--),(--`n * n'`--)] ADD_SYM) THEN
  NEW_SUBST1_TAC (SPECL [(--`n * p'`--),(--`p * n'`--)] ADD_SYM) THEN
  MATCH_MP_IMP_TAC SUB_ADD THEN
  MATCH_MP_IMP_TAC CROSS_TERMS THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)])
end;

(*
val PROJ_TIMES =
  |- !p n p' n'.
       proj (p,n) times proj (p',n') =
       proj (p * p' + n * n',p * n' + n * p') :thm
*)


val NUM_MULT_IS_INT_MULT = store_thm("NUM_MULT_IS_INT_MULT",
(--`!m n. (INT m) times (INT n) = INT (m * n)`--),
GEN_TAC THEN REWRITE_TAC[INT_DEF,PROJ_TIMES,ADD_CLAUSES,MULT_CLAUSES])

(*
val NUM_MULT_IS_INT_MULT = |- !m n. INT m times INT n = INT (m * n) :thm
*)


local
    val EQ_MONO_ADD_EQ1 = PURE_ONCE_REWRITE_RULE[ADD_SYM] EQ_MONO_ADD_EQ
    val M = (--`M:integer`--) and N = (--`N:integer`--)
    and P = (--`P:integer`--)
in
val ASSOC_TIMES = store_thm("ASSOC_TIMES",
(--`!M N P. M times (N times P) = (M times N) times P`--),
REPEAT GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC M PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC N PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC P PROJ_ONTO) THEN
ASM_REWRITE_TAC [PROJ_TIMES,PROJ_EQ,MULT_ASSOC,
		 LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] THEN
PURE_REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC),EQ_MONO_ADD_EQ1] THEN
NEW_SUBST1_TAC
  (SPECL [(--`(n * p') * p''`--),(--`(n * n') * n''`--)] ADD_SYM) THEN
PURE_REWRITE_TAC [SPEC_ALL ADD_ASSOC,EQ_MONO_ADD_EQ] THEN
NEW_SUBST1_TAC
  (SPECL [(--`(n * n') * p''`--),(--`(p * n') * n''`--)] ADD_SYM) THEN
PURE_REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC),EQ_MONO_ADD_EQ1] THEN
NEW_SUBST1_TAC
  (SPECL [(--`(p * n') * p''`--),(--`(n * n') * n''`--)] ADD_SYM) THEN
PURE_REWRITE_TAC [SPEC_ALL ADD_ASSOC,EQ_MONO_ADD_EQ] THEN
MATCH_ACCEPT_TAC ADD_SYM)
end;

(*
val ASSOC_TIMES = |- !M N P. M times N times P = (M times N) times P
*)


local
    val p = (--`p:num`--) and n = (--`n:num`--)
    and p' = (--`p':num`--) and n' = (--`n':num`--)
    and M = (--`M:integer`--) and N = (--`N:integer`--)
in
val COMM_TIMES = store_thm("COMM_TIMES",
(--`!M N. M times N = N times M`--),
REPEAT GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC M PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC N PROJ_ONTO) THEN
ASM_REWRITE_TAC [PROJ_TIMES] THEN
NEW_SUBST1_TAC (SPECL [n',n] MULT_SYM) THEN
NEW_SUBST1_TAC (SPECL [p',p] MULT_SYM) THEN
NEW_SUBST1_TAC (SPECL [n',p] MULT_SYM) THEN
NEW_SUBST1_TAC (SPECL [p',n] MULT_SYM) THEN
NEW_SUBST1_TAC (SPECL [(--`p * n'`--),(--`n * p'`--)] ADD_SYM) THEN
REFL_TAC)
end;

(*
val COMM_TIMES = |- !M N. M times N = N times M :thm
*)


val TIMES_IDENTITY = store_thm("TIMES_IDENTITY",
(--`!M. (M times (INT 1) = M) /\ ((INT 1) times M = M)`--),
GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC (--`M:integer`--) PROJ_ONTO) THEN
ASM_REWRITE_TAC[INT_DEF,TIMES_DEF,PROJ_EQ,REP_PROJ,PROJ_REP,
		ADD_CLAUSES,MULT_CLAUSES]);

(*
val TIMES_IDENTITY = |- !M. (M times INT 1 = M) /\ (INT 1 times M = M):thm
*)


local
    val EQ_MONO_ADD_EQ1 = PURE_ONCE_REWRITE_RULE[ADD_SYM] EQ_MONO_ADD_EQ
    val M = (--`M:integer`--) and N = (--`N:integer`--)
    and P = (--`P:integer`--)
in
val RIGHT_PLUS_DISTRIB = store_thm("RIGHT_PLUS_DISTRIB",
(--`!M N P. (M plus N) times P = (M times P) plus (N times P)`--),
REPEAT GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC M PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC N PROJ_ONTO) THEN
STRIP_ASSUME_TAC (SPEC P PROJ_ONTO)THEN
ASM_REWRITE_TAC[PROJ_PLUS,PROJ_TIMES,RIGHT_ADD_DISTRIB,PROJ_EQ] THEN
PURE_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),EQ_MONO_ADD_EQ1] THEN
PURE_REWRITE_TAC[ADD_ASSOC,EQ_MONO_ADD_EQ] THEN
NEW_SUBST1_TAC (SPECL [(--`p' * p''`--),(--`n * n''`--)] ADD_SYM) THEN
PURE_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),EQ_MONO_ADD_EQ1] THEN
MATCH_ACCEPT_TAC ADD_SYM)
end;

(*
val RIGHT_PLUS_DISTRIB =
  |- !M N P. (M plus N) times P = M times P plus N times P :thm
*)


val LEFT_PLUS_DISTRIB = store_thm("LEFT_PLUS_DISTRIB",
(--`!M N P. M times (N plus P) = (M times N) plus (M times P)`--),
REPEAT GEN_TAC THEN
PURE_ONCE_REWRITE_TAC[COMM_TIMES] THEN
MATCH_ACCEPT_TAC RIGHT_PLUS_DISTRIB);

(*
val LEFT_PLUS_DISTRIB =
  |- !M N P. M times (N plus P) = M times N plus M times P :thm
*)


val TIMES_ZERO = store_thm("TIMES_ZERO",
(--`!M. (M times (INT 0) = INT 0) /\ ((INT 0) times M = INT 0)`--),
GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC (--`M:integer`--) PROJ_ONTO) THEN
ASM_REWRITE_TAC[INT_DEF,TIMES_DEF,PROJ_EQ,REP_PROJ,ADD_CLAUSES,MULT_CLAUSES]);

(*
val TIMES_ZERO =
  |- !M. (M times INT 0 = INT 0) /\ (INT 0 times M = INT 0) :thm
*)


val TIMES_neg = store_thm("TIMES_neg",
(--`(!M N. M times (neg N) = neg(M times N)) /\
    (!M N. (neg M) times N = neg(M times N))`--),
ASM_CONJ1_TAC THENL
[GEN_TAC THEN
 MATCH_MP_IMP_TAC
   (SPEC_ALL (SPEC (--`M times N`--) PLUS_RIGHT_CANCELLATION)) THEN
 REWRITE_TAC[SYM (SPEC_ALL LEFT_PLUS_DISTRIB),
	     CONJUNCT1 (SPEC_ALL PLUS_INV_LEMMA),
	     CONJUNCT1 (SPEC_ALL TIMES_ZERO)],
 PURE_ONCE_REWRITE_TAC[COMM_TIMES] THEN ASM_REWRITE_TAC[]]);


(*
val TIMES_neg =
  |- (!M N. M times neg N = neg (M times N)) /\
     (!M N. neg M times N = neg (M times N)) :thm
*)


val neg_IS_TIMES_neg1 = store_thm("neg_IS_TIMES_neg1",
(--`!M. neg M = M times (neg(INT 1))`--),
STRIP_TAC THEN ASM_REWRITE_TAC [TIMES_neg,TIMES_IDENTITY]);

(*
val neg_IS_TIMES_neg1 = |- !M. neg M = M times neg (INT 1) :thm
*)


val neg_ONE_ONE = store_thm("neg_ONE_ONE",
(--`!x y. (neg x = neg y) = (x = y)`--),
REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
[PURE_ONCE_REWRITE_TAC[SYM(SPEC_ALL PLUS_INV_INV_LEMMA)],ALL_TAC] THEN
ASM_REWRITE_TAC[]);

(*
val neg_ONE_ONE = |- !x y. (neg x = neg y) = x = y : thm
*)

(* The order structure on the integers *)

val POS_DEF= new_definition
             ("POS_DEF",(--`!M. POS M = (?n:num.M=INT(SUC n))`--));

(*
val POS_DEF = |- !M. POS M = (?n. M = INT (SUC n)) :thm
*)

val NEG_DEF=new_definition ("NEG_DEF", (--`!M. NEG M = POS(neg M)`--));

(*
val NEG_DEF = |- !M. NEG M = POS (neg M) :thm
*)

val POS_INT = store_thm("POS_INT",(--`!n. POS(INT(SUC n))`--),
GEN_TAC THEN PURE_ONCE_REWRITE_TAC [POS_DEF] THEN
EXISTS_TAC (--`n:num`--) THEN REFL_TAC);

(*
val POS_INT = |- !n. POS (INT (SUC n)) : thm
*)


val NEG_neg_INT = store_thm("NEG_neg_INT",(--`!n. NEG(neg(INT(SUC n)))`--),
REWRITE_TAC[NEG_DEF,PLUS_INV_INV_LEMMA,POS_INT]);

(*
val NEG_neg_INT = |- !n. NEG (neg (INT (SUC n)))
*)


val POS_PLUS_POS_IS_POS = store_thm("POS_PLUS_POS_IS_POS",
(--`!M N. POS M /\ POS N ==> POS(M plus N)`--),
PURE_ONCE_REWRITE_TAC[POS_DEF] THEN
REPEAT STRIP_TAC THEN EXISTS_TAC (--`SUC (n + n')`--) THEN
ASM_REWRITE_TAC[NUM_ADD_IS_INT_ADD,ADD_CLAUSES]);

(*
val POS_PLUS_POS_IS_POS = |- !M N. POS M /\ POS N ==> POS (M plus N) : thm
*)


val NEG_PLUS_NEG_IS_NEG = store_thm("NEG_PLUS_NEG_IS_NEG",
(--`!M N. NEG M /\ NEG N ==> NEG(M plus N)`--),
PURE_REWRITE_TAC[NEG_DEF,SYM (SPEC_ALL PLUS_DIST_INV_LEMMA)] THEN
PURE_ONCE_REWRITE_TAC[COMM_PLUS] THEN
MATCH_ACCEPT_TAC POS_PLUS_POS_IS_POS);

(*
val NEG_PLUS_NEG_IS_NEG = |- !M N. NEG M /\ NEG N ==> NEG (M plus N) : thm
*)


val ZERO_NOT_POS = store_thm("ZERO_NOT_POS",
(--`~(POS(INT 0))`--),
PURE_ONCE_REWRITE_TAC[POS_DEF] THEN
CONV_TAC NOT_EXISTS_CONV THEN
REWRITE_TAC[INT_ONE_ONE,SUC_NOT]);

(*
val ZERO_NOT_POS = |- ~(POS (INT 0)) : thm
*)


val ZERO_NOT_NEG = store_thm("ZERO_NOT_NEG",
(--`~(NEG(INT 0))`--),
REWRITE_TAC[NEG_DEF,PLUS_INV_ID_LEMMA,ZERO_NOT_POS]);

(*
val ZERO_NOT_NEG = |- ~(NEG (INT 0)) : thm
*)


local
val M = (--`M:integer`--)
in
val TRICHOTOMY = store_thm("TRICHOTOMY",
(--`!M. (POS M \/ NEG M \/ (M = INT 0)) /\
        ~(POS M /\ NEG M) /\
        ~(POS M /\ (M = INT 0)) /\
        ~(NEG M /\ (M = INT 0))`--),
PURE_REWRITE_TAC [INT_DEF, POS_DEF, NEG_DEF] THEN
GEN_TAC THEN PURE_ONCE_REWRITE_TAC [PROJ_neg] THEN
ASM_CASES_TAC (--`M = proj(0,0)`--) THENL
[(ASM_REWRITE_TAC[PROJ_neg,PROJ_EQ,ADD_CLAUSES] THEN
  CONV_TAC NOT_EXISTS_CONV THEN ACCEPT_TAC SUC_NOT),
 (CONV_TAC (ONCE_DEPTH_CONV (ALPHA_CONV (--`m:num`--))) THEN
  REPEAT_TCL STRIP_THM_THEN
    (fn thm => STRIP_ASSUME_TAC (SYM (PURE_ONCE_REWRITE_RULE [PROJ_REP]
				      (AP_TERM (--`proj`--) thm))))
    (SPEC M thm3) THEN
  ASM_REWRITE_TAC[PROJ_neg,PROJ_EQ,ADD_CLAUSES,SUC_NOT] THEN
  POP_ASSUM (fn thm1 => (POP_ASSUM (fn thm2 =>
  let val thm3 = (PURE_ONCE_REWRITE_RULE [thm1] thm2)
      val {lhs,rhs} = (dest_eq o dest_neg o concl) thm3
      val p = rand lhs and z = rand rhs
      val not_zero_th = REWRITE_RULE [PAIR_EQ]
			(MP
			 (CONTRAPOS (DISCH_ALL (AP_TERM (--`proj`--)
				   (ASSUME (mk_eq{lhs = p, rhs = z})))))
			 thm3)
      val m = #lhs(dest_eq(rand(concl not_zero_th)))

  in
    ACCEPT_TAC
      (REWRITE_RULE[not_zero_th](SPEC m num_CASES))
  end))))])
end;

(*
val TRICHOTOMY =
  |- !M.
       (POS M \/ NEG M \/ (M = INT 0)) /\
       ~(POS M /\ NEG M) /\
       ~(POS M /\ (M = INT 0)) /\
       ~(NEG M /\ (M = INT 0)) : thm
*)

val POS_PLUS_NON_NEG_IS_POS = store_thm("POS_TIMES_NON_NEG_IS_POS",
(--`!M N. POS M /\ ~(NEG N) ==> POS(M plus N)`--),
REPEAT STRIP_TAC THEN
DISJ_CASES_TAC (CONJUNCT1 (REWRITE_RULE [ASSUME(--`~(NEG N)`--)]
			   (SPEC (--`N:integer`--) TRICHOTOMY))) THENL
[MATCH_MP_IMP_TAC POS_PLUS_POS_IS_POS THEN
 CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
 ASM_REWRITE_TAC [PLUS_ID_LEMMA]]);

(*
val POS_PLUS_NON_NEG_IS_POS = |- !M N. POS M /\ ~(NEG N) ==> POS (M plus N)
  : thm
*)


val NEG_PLUS_NON_POS_IS_NEG = store_thm("NEG_PLUS_NON_POS_IS_NEG",
(--`!M N. NEG M /\ ~(POS N) ==> NEG(M plus N)`--),
REPEAT STRIP_TAC THEN
DISJ_CASES_TAC (CONJUNCT1 (REWRITE_RULE [ASSUME(--`~(POS N)`--)]
			   (SPEC (--`N:integer`--) TRICHOTOMY))) THENL
[MATCH_MP_IMP_TAC NEG_PLUS_NEG_IS_NEG THEN
 CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
 ASM_REWRITE_TAC [PLUS_ID_LEMMA]]);

(*
val NEG_PLUS_NON_POS_IS_NEG = |- !M N. NEG M /\ ~(POS N) ==> NEG (M plus N)
  : thm
*)


val POS_TIMES_POS_IS_POS = store_thm("POS_TIMES_POS_IS_POS",
(--`!M N. POS M /\ POS N ==> POS (M times N)`--),
PURE_ONCE_REWRITE_TAC[POS_DEF] THEN REPEAT STRIP_TAC THEN
CONV_TAC (ONCE_DEPTH_CONV (ALPHA_CONV (--`m:num`--))) THEN
PURE_ASM_REWRITE_TAC[NUM_MULT_IS_INT_MULT,MULT,ADD_CLAUSES] THEN
EXISTS_TAC (--`(n * SUC n') + n'`--) THEN REFL_TAC);

(*
val POS_TIMES_POS_IS_POS = |- !M N. POS M /\ POS N ==> POS (M times N) : thm
*)


val POS_TIMES_NEG_IS_NEG = store_thm("POS_TIMES_NEG_IS_NEG",
(--`!M N. POS M /\ NEG N ==> NEG(M times N)`--),
REPEAT GEN_TAC THEN
PURE_REWRITE_TAC[NEG_DEF,SYM(SPEC_ALL (CONJUNCT1 TIMES_neg))] THEN
MATCH_ACCEPT_TAC POS_TIMES_POS_IS_POS);

(*
val POS_TIMES_NEG_IS_NEG = |- !M N. POS M /\ NEG N ==> NEG (M times N) : thm
*)

val NEG_TIMES_NEG_IS_POS = store_thm("NEG_TIMES_NEG_IS_POS",
(--`!M N. NEG M /\ NEG N ==>  POS (M times N)`--),
REPEAT GEN_TAC THEN
PURE_ONCE_REWRITE_TAC[NEG_DEF] THEN
ACCEPT_TAC (PURE_REWRITE_RULE[TIMES_neg, PLUS_INV_INV_LEMMA]
	    (SPECL [(--`neg M`--),(--`neg N`--)]POS_TIMES_POS_IS_POS)));


(*
val NEG_TIMES_NEG_IS_POS = |- !M N. NEG M /\ NEG N ==> POS (M times N) : thm
*)


val INT_INTEGRAL_DOMAIN = store_thm("INT_INTEGRAL_DOMAIN",
(--`!x y. (x times y = INT 0) ==> (x = INT 0) \/ (y = INT 0)`--),
(SIMPLE_INT_CASES_TAC THENL
 [GEN_TAC THEN DISCH_TAC, GEN_TAC THEN DISCH_TAC, REWRITE_TAC[]] THEN
 SIMPLE_INT_CASES_TAC THEN REWRITE_TAC[] THEN
 GEN_TAC THEN REPEAT DISCH_TAC) THENL
[CONTR_TAC(REWRITE_RULE[ASSUME(--`(x times y = INT 0)`--),
			UNDISCH_ALL(hd
                         (IMP_CANON(SPECL [(--`x:integer`--),(--`y:integer`--)]
				   POS_TIMES_POS_IS_POS)))]
	   (SPEC (--`x times y`--) TRICHOTOMY)),
 CONTR_TAC(REWRITE_RULE[ASSUME(--`(x times y = INT 0)`--),
			UNDISCH_ALL(hd
                         (IMP_CANON(SPECL [(--`x:integer`--),(--`y:integer`--)]
				   POS_TIMES_NEG_IS_NEG)))]
	   (SPEC (--`x times y`--) TRICHOTOMY)),
 CONTR_TAC(REWRITE_RULE[ASSUME(--`(x times y = INT 0)`--),
			PURE_ONCE_REWRITE_RULE[COMM_TIMES]
			(UNDISCH_ALL(hd
                         (IMP_CANON(SPECL [(--`y:integer`--),(--`x:integer`--)]
				   POS_TIMES_NEG_IS_NEG))))]
	   (SPEC (--`x times y`--) TRICHOTOMY)),
 CONTR_TAC(REWRITE_RULE[ASSUME(--`(x times y = INT 0)`--),
			UNDISCH_ALL(hd
                         (IMP_CANON(SPECL [(--`x:integer`--),(--`y:integer`--)]
				   NEG_TIMES_NEG_IS_POS)))]
	   (SPEC (--`x times y`--) TRICHOTOMY))]);

(*
val INT_INTEGRAL_DOMAIN =
  |- !x y. (x times y = INT 0) ==> (x = INT 0) \/ (y = INT 0) : thm
*)


val TIMES_LEFT_CANCELLATION = store_thm("TIMES_LEFT_CANCELLATION",
(--`!x y z. ~(x = INT 0) ==> (x times y = x times z) ==> (y = z)`--),
REPEAT STRIP_TAC THEN
MP_IMP_TAC (SPECL [(--`neg z`--),(--`y:integer`--),(--`z:integer`--)]
	    PLUS_RIGHT_CANCELLATION) THEN
PURE_ONCE_REWRITE_TAC [PLUS_INV_LEMMA] THEN
MATCH_MP_IMP_TAC
 (PURE_ONCE_REWRITE_RULE
  [REWRITE_RULE[](SYM(SPECL[(--`~t1`--),(--`t2:bool`--)] IMP_DISJ_THM))]
  (UNDISCH (SPECL [(--`x:integer`--),(--`y plus (neg z)`--)]
	    INT_INTEGRAL_DOMAIN))) THENL
 [FIRST_ASSUM ACCEPT_TAC,
  (MATCH_MP_IMP_TAC (SPEC (--`x times z`--) PLUS_RIGHT_CANCELLATION) THEN
   ASM_REWRITE_TAC [SYM (SPEC_ALL LEFT_PLUS_DISTRIB),PLUS_GROUP_ASSOC,
		    PLUS_INV_LEMMA,PLUS_ID_LEMMA])]);

(*
val TIMES_LEFT_CANCELLATION =
  |- !x y z. ~(x = INT 0) ==> (x times y = x times z) ==> (y = z)
*)


val TIMES_RIGHT_CANCELLATION = store_thm("TIMES_RIGHT_CANCELLATION",
(--`!x y z. ~(x = INT 0) ==> (y times x = z times x) ==> (y = z)`--),
PURE_ONCE_REWRITE_TAC [COMM_TIMES] THEN ACCEPT_TAC TIMES_LEFT_CANCELLATION);

(*
val TIMES_RIGHT_CANCELLATION =
  |- !x y z. ~(x = INT 0) ==> (y times x = z times x) ==> (y = z) : thm
*)


val NON_NEG_INT_IS_NUM = store_thm("NON_NEG_INT_IS_NUM",
(--`!N. ~NEG N = (?n. N = INT n)`--),
GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
[STRIP_ASSUME_TAC
 (REWRITE_RULE[ASSUME (--`~NEG N`--),POS_DEF]
              (CONJUNCT1(SPEC (--`N:integer`--) TRICHOTOMY))) THENL
 [EXISTS_TAC (--`SUC n`--), EXISTS_TAC (--`0`--)] THEN
 FIRST_ASSUM ACCEPT_TAC,
 POP_ASSUM STRIP_ASSUME_TAC THEN
 PURE_REWRITE_TAC[NEG_DEF,POS_DEF] THEN
 CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC THEN
 ASM_REWRITE_TAC[INT_DEF,PROJ_neg,PROJ_EQ,ADD_CLAUSES,SUC_NOT]]);

(*
val NON_NEG_INT_IS_NUM = |- !N. ~(NEG N) = (?n. N = INT n) : thm
*)


val NOT_NEG_INT = store_thm("NOT_NEG_INT",
(--`!n.~(NEG(INT n))`--),
GEN_TAC THEN PURE_ONCE_REWRITE_TAC [NON_NEG_INT_IS_NUM] THEN
EXISTS_TAC (--`n:num`--) THEN REFL_TAC);

(*
val NOT_NEG_INT = |- !n. ~(NEG (INT n)) : thm
*)


val NEG_IS_neg_INT = store_thm("NEG_IS_neg_INT",
(--`!N. NEG N = (?n. N = neg(INT(SUC n)))`--),
GEN_TAC THEN PURE_REWRITE_TAC[NEG_DEF,POS_DEF] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL
[POP_ASSUM (ASSUME_TAC o (PURE_ONCE_REWRITE_RULE[PLUS_INV_INV_LEMMA]) o
	    (AP_TERM (--`neg`--))), ALL_TAC] THEN
EXISTS_TAC (--`n:num`--) THEN
ASM_REWRITE_TAC[PLUS_INV_INV_LEMMA])

(*
val NEG_IS_neg_INT = |- !N. NEG N = (?n. N = neg (INT (SUC n))) : thm
*)


val NON_POS_INT_IS_neg_NUM = store_thm("NON_POS_INT_IS_neg_NUM",
(--`!N. ~(POS N) = (?n. N = neg(INT n))`--),
GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
[(STRIP_ASSUME_TAC
  (REWRITE_RULE[ASSUME (--`~POS N`--)]
   (CONJUNCT1(SPEC (--`N:integer`--) TRICHOTOMY))) THENL
  [STRIP_ASSUME_TAC
   (REWRITE_RULE[ASSUME (--`NEG N`--)]
    (SPEC (--`N:integer`--) NEG_IS_neg_INT)) THEN EXISTS_TAC (--`SUC n`--) THEN
   FIRST_ASSUM ACCEPT_TAC,
   EXISTS_TAC (--`0`--) THEN ASM_REWRITE_TAC[PLUS_INV_ID_LEMMA]]),
 (PURE_REWRITE_TAC[POS_DEF] THEN
  CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC THEN
  ASM_REWRITE_TAC[INT_DEF,PROJ_neg,PROJ_EQ,ADD_CLAUSES,SUC_NOT])]);

(*
val NON_POS_INT_IS_neg_NUM = |- !N. ~(POS N) = (?n. N = neg (INT n)) : thm
*)


val NOT_POS_neg_INT = store_thm("NOT_POS_neg_INT",
(--`!n. ~(POS (neg (INT n)))`--),
GEN_TAC THEN PURE_ONCE_REWRITE_TAC [NON_POS_INT_IS_neg_NUM] THEN
EXISTS_TAC (--`n:num`--) THEN REFL_TAC);

(*
val NOT_POS_neg_INT = |- !n. ~(POS (neg (INT n))) : thm
*)


val INT_CASES = store_thm("INT_CASES",
(--`!P. (!m. P(INT m)) /\ (!m. P(neg(INT m))) ==> (!M. P M)`--),
REPEAT STRIP_TAC THEN
DISJ_CASES_TAC
  (PURE_REWRITE_RULE [POS_DEF, NEG_IS_neg_INT]
     (CONJUNCT1 (SPEC (--`M:integer`--) TRICHOTOMY))) THEN
POP_ASSUM STRIP_ASSUME_TAC THEN
ASM_REWRITE_TAC []);

(*
val INT_CASES =
  |- !P. (!m. P (INT m)) /\ (!m. P (neg (INT m))) ==> (!M. P M) : thm
*)


val BELOW_DEF=new_infix_definition ("BELOW_DEF",
				    (--`below M N = POS(N minus M)`--),
				    450);

(*
BELOW_DEF = |- !M N. M below N = POS(N minus M)
*)


val POS_IS_ZERO_BELOW = store_thm("POS_IS_ZERO_BELOW",
(--`!N. POS N = (INT 0) below N`--),
GEN_TAC THEN REWRITE_TAC[BELOW_DEF,MINUS_DEF,
			 PLUS_INV_ID_LEMMA,PLUS_ID_LEMMA])

(*
val POS_IS_ZERO_BELOW = |- !N. POS N = INT 0 below N : thm
*)


val NEG_IS_BELOW_ZERO = store_thm("NEG_IS_BELOW_ZERO",
(--`!N. NEG N = N below (INT 0)`--),
GEN_TAC THEN REWRITE_TAC[NEG_DEF,BELOW_DEF,MINUS_DEF,
			 PLUS_INV_ID_LEMMA,PLUS_ID_LEMMA])

(*
val NEG_IS_BELOW_ZERO = |- !N. NEG N = N below INT 0 : thm
*)


val NUM_LESS_IS_INT_BELOW = store_thm("NUM_LESS_IS_INT_BELOW",
(--`!m n. m < n = (INT m) below (INT n)`--),
REPEAT GEN_TAC THEN
PURE_REWRITE_TAC
  [INT_DEF,BELOW_DEF,POS_DEF,MINUS_DEF,PROJ_neg,PROJ_PLUS,PROJ_EQ,
   ADD_CLAUSES] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL
[(STRIP_ASSUME_TAC
   (PURE_REWRITE_RULE[SYM(SPEC_ALL ADD1),ADD_CLAUSES]
    (UNDISCH(SPECL[(--`n:num`--),(--`m:num`--)]LESS_ADD_1))) THEN
  PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
  EXISTS_TAC (--`p:num`--) THEN
  FIRST_ASSUM ACCEPT_TAC),
(PURE_ONCE_ASM_REWRITE_TAC [] THEN
 PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL (CONJUNCT2 ADD))] THEN
 PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
 MATCH_ACCEPT_TAC LESS_ADD_SUC)]);

(*
val NUM_LESS_IS_INT_BELOW = |- !m n. m < n = INT m below INT n : thm
*)


val neg_REV_BELOW = store_thm("neg_REV_BELOW",
(--`!M N. (neg M) below (neg N) = N below M`--),
PURE_ONCE_REWRITE_TAC[BELOW_DEF] THEN
PURE_ONCE_REWRITE_TAC[MINUS_DEF] THEN
PURE_ONCE_REWRITE_TAC[PLUS_INV_INV_LEMMA] THEN
REWRITE_TAC[SPECL[(--`M:integer`--),(--`neg N`--)]COMM_PLUS]);

(*
val neg_REV_BELOW = |- !M N. neg M below neg N = N below M : thm
*)


val POS_MULT_PRES_BELOW = store_thm("POS_MULT_PRES_BELOW",
(--`!M N P. POS M ==> (N below P = (M times N) below (M times P))`--),
PURE_ONCE_REWRITE_TAC[POS_DEF] THEN
REPEAT STRIP_TAC THEN
SUBST1_TAC(ASSUME(--`M = INT (SUC n)`--)) THEN
PURE_REWRITE_TAC[BELOW_DEF, MINUS_DEF, POS_DEF,
		 SYM (SPEC_ALL LEFT_PLUS_DISTRIB),
		 SYM (SPEC_ALL (CONJUNCT1 TIMES_neg))] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL
[(SUBST1_TAC(ASSUME(--`P plus neg N = INT (SUC n')`--)) THEN
  REWRITE_TAC[NUM_MULT_IS_INT_MULT,MULT,ADD_CLAUSES] THEN
  EXISTS_TAC (--`(n * (SUC n')) + n'`--) THEN REFL_TAC),

 (PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL POS_DEF)] THEN
  (ASM_CASES_TAC (--`POS (P plus neg N)`--) THEN
   ASM_REWRITE_TAC[]) THEN 
  (let val not_gl = SPEC (--`n':num`--) POS_INT
   in ASSUME_TAC not_gl THEN UNDISCH_TAC (concl not_gl) end) THEN
  STRIP_ASSUME_TAC(PURE_ONCE_REWRITE_RULE[NON_POS_INT_IS_neg_NUM]
		   (ASSUME(--`~(POS (P plus neg N))`--))) THEN
  REWRITE_TAC
    [SYM(ASSUME(--`INT (SUC n) times (P plus neg N) = INT (SUC n')`--)),
     ASSUME(--`P plus neg N = neg (INT n'')`--),
     TIMES_neg, NUM_MULT_IS_INT_MULT] THEN
  PURE_REWRITE_TAC [SYM (SPEC_ALL NEG_DEF),NON_NEG_INT_IS_NUM] THEN
  EXISTS_TAC (--`SUC n * n''`--) THEN REFL_TAC)]);

(*
val POS_MULT_PRES_BELOW =
  |- !M N P. POS M ==> (N below P = M times N below M times P) : thm
*)


val NEG_MULT_REV_BELOW = store_thm("NEG_MULT_REV_BELOW",
(--`!M N P. NEG M ==> (N below P = (M times P) below (M times N))`--),
PURE_ONCE_REWRITE_TAC [NEG_DEF] THEN REPEAT STRIP_TAC THEN
SUBST1_TAC (SYM (SPEC (--`M:integer`--) PLUS_INV_INV_LEMMA)) THEN
PURE_ONCE_REWRITE_TAC [TIMES_neg] THEN
PURE_ONCE_REWRITE_TAC [neg_REV_BELOW] THEN 
NEW_MATCH_ACCEPT_TAC (UNDISCH (SPEC_ALL POS_MULT_PRES_BELOW)));

(*
val NEG_MULT_REV_BELOW =
  |- !M N P. NEG M ==> (N below P = M times P below M times N) : thm
*)


val ANTISYM = store_thm("ANTISYM",
(--`!M. ~(M below M)`--),
INT_CASES_TAC THENL
[GEN_TAC THEN
 REWRITE_TAC[SYM (SPEC_ALL NUM_LESS_IS_INT_BELOW),
	     theorem "prim_rec" "LESS_REFL"],
 ASM_REWRITE_TAC[neg_REV_BELOW]]);

(*
val ANTISYM = |- !M. ~(M below M) : thm
*)


val TRANSIT = store_thm("TRANSIT",
(--`!M N P. M below N /\ N below P ==> M below P`--),
PURE_REWRITE_TAC[BELOW_DEF,MINUS_DEF,POS_DEF,ADD1,
		 SYM (SPEC_ALL NUM_ADD_IS_INT_ADD)] THEN
REPEAT STRIP_TAC THEN
EXISTS_TAC (--`(n' + 1) + n`--) THEN
PURE_REWRITE_TAC[SYM (SPEC_ALL NUM_ADD_IS_INT_ADD),
		 SYM (ASSUME (--`P plus neg N = INT n' plus INT 1`--))] THEN
PURE_REWRITE_TAC[SYM (SPEC_ALL ASSOC_PLUS),
		 SYM (ASSUME (--`N plus neg M = INT n plus INT 1`--))] THEN
REWRITE_TAC[SPECL[(--`neg N`--),(--`N:integer`--),(--`neg M`--)]ASSOC_PLUS,
		  PLUS_INV_LEMMA,PLUS_ID_LEMMA]);

(*
val TRANSIT = |- !M N P. M below N /\ N below P ==> M below P : thm
*)


val COMPAR = store_thm("COMPAR",
(--`!M N. M below N \/ N below M \/ (M = N)`--),
REPEAT GEN_TAC THEN
PURE_REWRITE_TAC[BELOW_DEF] THEN
SUPPOSE_TAC (--`(M minus N) = neg(N minus M)`--) THENL
[SUPPOSE_TAC(--`(M = N) = (N minus M = INT 0)`--) THENL
 [ASM_REWRITE_TAC[SYM(SPEC_ALL NEG_DEF),TRICHOTOMY],
  EQ_TAC THEN REWRITE_TAC[MINUS_DEF] THENL
  [DISCH_TAC THEN ASM_REWRITE_TAC[PLUS_INV_LEMMA],
   ACCEPT_TAC
   (CONV_RULE (RAND_CONV SYM_CONV)
    (PURE_ONCE_REWRITE_RULE
       [PLUS_INV_INV_LEMMA]
       (SPECL [(--`neg M`--),(--`N:integer`--)] PLUS_UNIQUE_INV)))]],
 REWRITE_TAC[MINUS_DEF,SYM (SPEC_ALL PLUS_DIST_INV_LEMMA),
	     PLUS_INV_INV_LEMMA]]);

(*
val COMPAR = |- !M N. M below N \/ N below M \/ (M = N) : thm
*)


val DOUBLE_INF = store_thm("DOUBLE_INF",
(--`!M.(?N. N below M) /\ (?P. M below P)`--),
INT_CASES_TAC THENL
[(GEN_TAC THEN REWRITE_TAC[BELOW_DEF,MINUS_DEF] THEN CONJ_TAC THENL
  [(EXISTS_TAC(--`(neg(INT (SUC 0))) plus (INT n)`--) THEN
    PURE_REWRITE_TAC
      [SYM (SPEC_ALL PLUS_DIST_INV_LEMMA), PLUS_INV_INV_LEMMA,
       ASSOC_PLUS,PLUS_INV_LEMMA,PLUS_ID_LEMMA,POS_DEF] THEN
    EXISTS_TAC(--`0`--) THEN REFL_TAC),
  (EXISTS_TAC(--`(INT (SUC 0)) plus (INT n)`--) THEN
   PURE_REWRITE_TAC
     [SYM (SPEC_ALL ASSOC_PLUS), PLUS_INV_LEMMA,PLUS_ID_LEMMA,POS_DEF] THEN
   EXISTS_TAC(--`0`--) THEN REFL_TAC)]),
 (GEN_TAC THEN
  POP_ASSUM (STRIP_ASSUME_TAC o (SPEC (--`n:num`--))) THEN CONJ_TAC THENL
  [(PURE_ONCE_REWRITE_TAC
      [PURE_ONCE_REWRITE_RULE[PLUS_INV_INV_LEMMA]
       (SPECL[(--`neg M`--),(--`N:integer`--)] neg_REV_BELOW)] THEN
    EXISTS_TAC (--`neg P`--) THEN ASM_REWRITE_TAC[PLUS_INV_INV_LEMMA]),
   (PURE_ONCE_REWRITE_TAC
      [PURE_ONCE_REWRITE_RULE[PLUS_INV_INV_LEMMA]
       (SPECL[(--`M:integer`--),(--`neg N`--)] neg_REV_BELOW)] THEN
    EXISTS_TAC (--`neg N`--) THEN ASM_REWRITE_TAC[PLUS_INV_INV_LEMMA])])]);

(*
val DOUBLE_INF = |- !M. (?N. N below M) /\ (?P. M below P) : thm
*)


val PLUS_BELOW_TRANSL = store_thm("PLUS_BELOW_TRANSL",
(--`!M N P. M below N = (M plus P) below (N plus P)`--),
REPEAT GEN_TAC THEN 
PURE_REWRITE_TAC [BELOW_DEF, MINUS_DEF, POS_DEF,
		  SYM (SPEC_ALL PLUS_DIST_INV_LEMMA)] THEN
PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL ASSOC_PLUS)] THEN
NEW_SUBST1_TAC
    (SPECL [(--`P:integer`--),(--`neg P`--),(--`neg M`--)] ASSOC_PLUS) THEN
REWRITE_TAC [PLUS_INV_LEMMA,PLUS_ID_LEMMA]);

(*
val PLUS_BELOW_TRANSL = |- !M N P. M below N = M plus P below N plus P : thm
*)


(* Has become arithmetic.WOP 
val WELL_ORDER = save_thm("WELL_ORDER",
mk_thm([],(--`!S1. (?m. S1 m) ==> (?m. S1 m /\ (!n. n < m ==> ~S1 n))`--)));
*)


val DISCRETE = store_thm("DISCRETE",
(--`!IntSet.
    (?M. IntSet M) ==>
    ((?LB. !N. N below LB ==> ~IntSet N) ==>
     (?GLB. IntSet GLB /\ (!N. N below GLB ==> ~IntSet N))) /\
    ((?UB. !N. UB below N ==> ~IntSet N) ==>
     (?LUB. IntSet LUB /\ (!N. LUB below N ==> ~IntSet N)))`--),
REV_SUPPOSE_TAC (--`!IntSet. (?M. IntSet M) ==>
		      ((?LB.!N.((N below LB) ==> ~IntSet N)) ==> 
			  (?GLB. IntSet GLB /\ 
			   (!N.(N below GLB) ==> ~IntSet N)))`--) THENL
[(REPEAT STRIP_TAC THEN
  SUPPOSE_TAC (--`?n. IntSet (INT n plus LB)`--) THENL
  [(STRIP_ASSUME_TAC 
     (UNDISCH (BETA_RULE 
        (SPEC (--`\n.(IntSet((INT n) plus LB):bool)`--) WOP))) THEN
    EXISTS_TAC (--`INT n plus LB`--) THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    STRIP_ASSUME_TAC (SPECL[(--`N:integer`--),(--`LB:integer`--)]COMPAR) THENL
    [RES_TAC,
     (STRIP_ASSUME_TAC
        (REWRITE_RULE [BELOW_DEF,MINUS_DEF,POS_DEF]
         (ASSUME(--`LB below N`--))) THEN
      STRIP_ASSUME_TAC
        (REWRITE_RULE [SYM(SPEC_ALL ASSOC_PLUS),PLUS_INV_LEMMA,PLUS_ID_LEMMA]
         (BETA_RULE
	  (AP_TERM (--`\M. M plus LB`--)
	   (ASSUME(--`N plus neg LB = INT (SUC n')`--))))) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_IMP_TAC
        (ASSUME(--`!m. m < n ==> ~(IntSet (INT m plus LB))`--)) THEN
      ACCEPT_TAC(REWRITE_RULE [ASSUME(--`N = INT (SUC n') plus LB`--),
			       SYM(SPEC_ALL PLUS_BELOW_TRANSL),
			       SYM(SPEC_ALL NUM_LESS_IS_INT_BELOW)]
		 (ASSUME(--`N below INT n plus LB`--)))),
     (ASM_REWRITE_TAC[] THEN
      MP_IMP_TAC
      (PURE_REWRITE_RULE[PLUS_ID_LEMMA]
       (SPEC (--`0`--)
         (ASSUME(--`!m. m < n ==> ~(IntSet (INT m plus LB))`--)))) THEN
      PURE_REWRITE_TAC
        [NUM_LESS_IS_INT_BELOW,SYM(SPEC_ALL POS_IS_ZERO_BELOW)] THEN
      ACCEPT_TAC
        (REWRITE_RULE[ASSUME(--`N = (LB:integer)`--),BELOW_DEF,MINUS_DEF,
		      SYM(SPEC_ALL ASSOC_PLUS),PLUS_INV_LEMMA,PLUS_ID_LEMMA]
		      (ASSUME(--`N below INT n plus LB`--))))]),
  (STRIP_ASSUME_TAC
     (PURE_REWRITE_RULE[BELOW_DEF,MINUS_DEF,NON_POS_INT_IS_neg_NUM]
      (MP (REWRITE_RULE[]
	   (CONTRAPOS (SPEC (--`M:integer`--) 
		       (ASSUME(--`!N. N below LB ==> ~(IntSet N)`--)))))
       (ASSUME(--`(IntSet:integer -> bool) M`--)))) THEN
   EXISTS_TAC (--`n:num`--) THEN
   STRIP_ASSUME_TAC
     (PURE_REWRITE_RULE[SYM(SPEC_ALL ASSOC_PLUS),PLUS_INV_LEMMA,PLUS_ID_LEMMA]
      (BETA_RULE (AP_TERM (--`\X. X plus M`--)
		 (ASSUME(--`LB plus neg M = neg (INT n)`--))))) THEN
   ASM_REWRITE_TAC[ASSOC_PLUS,PLUS_INV_LEMMA,PLUS_ID_LEMMA])]),
 (GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
  [FIRST_ASSUM MATCH_MP_IMP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
   (UNDISCH_TAC (--`?M:integer. IntSet M`--) THEN
    POP_ASSUM (fn thm => STRIP_ASSUME_TAC
	       (BETA_RULE(SPEC (--`\X.((IntSet (neg X)):bool)`--) thm))) THEN
    REPEAT STRIP_TAC THEN
    (REV_SUPPOSE_TAC(--`?M. IntSet (neg M)`--) THENL
     [EXISTS_TAC (--`neg M`--) THEN ASM_REWRITE_TAC[PLUS_INV_INV_LEMMA],
      ASSUME_TAC
         (MP(ASSUME(--`(?M. IntSet (neg M)) ==>
		    (?LB. !N. N below LB ==> ~(IntSet (neg N))) ==>
			(?GLB.IntSet (neg GLB) /\
			 (!N. N below GLB ==> ~(IntSet (neg N))))`--))
	     (ASSUME(--`?M. IntSet (neg M)`--)))]) THEN
    (REV_SUPPOSE_TAC(--`?LB. !N. N below LB ==> ~(IntSet (neg N))`--) THENL
     [EXISTS_TAC(--`neg UB`--) THEN GEN_TAC THEN
      ACCEPT_TAC (PURE_ONCE_REWRITE_RULE [PLUS_INV_INV_LEMMA]
		  (PURE_ONCE_REWRITE_RULE [SYM(SPEC_ALL neg_REV_BELOW)]
		   (SPEC (--`neg N`--)
		    (ASSUME(--`!N. UB below N ==> ~(IntSet N)`--))))), 
      STRIP_ASSUME_TAC
         (MP(ASSUME (--`(?LB. !N. N below LB ==> ~(IntSet (neg N))) ==>
		     (?GLB. IntSet (neg GLB) /\
		      (!N. N below GLB ==> ~(IntSet (neg N))))`--))
	     (ASSUME(--`?LB. !N. N below LB ==> ~(IntSet (neg N))`--)))]) THEN
    EXISTS_TAC (--`neg GLB`--) THEN
    (CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC,
      GEN_TAC THEN
      PURE_ONCE_REWRITE_TAC
        [SYM(SPECL[(--`N:integer`--),(--`neg GLB`--)] neg_REV_BELOW)] THEN
      PURE_ONCE_REWRITE_TAC[PLUS_INV_INV_LEMMA] THEN
      ACCEPT_TAC(PURE_ONCE_REWRITE_RULE[PLUS_INV_INV_LEMMA]
		 (SPEC (--`neg N`--)
		  (ASSUME(--`!N. N below GLB ==>
			  ~(IntSet (neg N))`--))))]))])]);


(*
val DISCRETE =
  |- !IntSet.
       (?M. IntSet M) ==>
       ((?LB. !N. N below LB ==> ~(IntSet N)) ==>
        (?GLB. IntSet GLB /\ (!N. N below GLB ==> ~(IntSet N)))) /\
       ((?UB. !N. UB below N ==> ~(IntSet N)) ==>
        (?LUB. IntSet LUB /\ (!N. LUB below N ==> ~(IntSet N)))) : thm
*)

(* Added for Myra VanInwegen for her work on encoding SML *)

val abs_DEF = new_definition("abs_DEF",
			     (--`integer_abs N = (~(NEG N) => N | neg N)`--));

(*
val abs_DEF = |- !N. integer_abs N = ((~(NEG N)) => N | (neg N)) : thm
*)


val ABS_NOT_NEG = store_thm("ABS_NOT_NEG",
(--`!N. ~NEG (integer_abs N)`--),
GEN_TAC THEN PURE_ONCE_REWRITE_TAC[abs_DEF] THEN
(COND_CASES_TAC THENL
 [FIRST_ASSUM ACCEPT_TAC,
  POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE []))]) THEN
  REWRITE_TAC[NEG_DEF,PLUS_INV_INV_LEMMA,
	      REWRITE_RULE[ASSUME(--`NEG N`--)]
	                  (SPEC (--`N:integer`--) TRICHOTOMY)]);

(*
val ABS_NOT_NEG = |- !N. ~(NEG (integer_abs N)) : thm
*)


val ABS_ABS = save_thm ("ABS_ABS",
   GEN (--`N:integer`--)
       (REWRITE_RULE[ABS_NOT_NEG] (SPEC (--`integer_abs N`--) abs_DEF)));

(*
val ABS_ABS = |- !(N :integer). 
                 integer_abs (integer_abs N) = integer_abs N : thm
*)


val ABS_ZERO = save_thm("ABS_ZERO",
REWRITE_RULE[REWRITE_RULE[](SPEC(--`INT 0`--)TRICHOTOMY)]
	    (SPEC(--`INT 0`--)abs_DEF));

(*
val ABS_ZERO = |- integer_abs (INT 0) = INT 0 : thm
*)


val ABS_POS = store_thm("ABS_POS",
(--`!N. POS N ==> (integer_abs N = N)`--),
REPEAT STRIP_TAC THEN
REWRITE_TAC[abs_DEF,REWRITE_RULE[ASSUME(--`POS N`--)]
	                        (SPEC (--`N:integer`--) TRICHOTOMY)]);

(*
val ABS_POS = |- !N. POS N ==> (integer_abs N = N) : thm
*)

val ABS_NEG = store_thm("ABS_NEG",
(--`!N. NEG N ==> (integer_abs N = neg N)`--),
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[abs_DEF]);

(*
val ABS_NEG = |- !N. NEG N ==> (integer_abs N = neg N) : thm
*)

val ABS_TIMES_IS_ABS_TIMES_ABS = store_thm("ABS_TIMES_IS_ABS_TIMES_ABS",
(--`!M N. integer_abs (M times N) = (integer_abs M) times (integer_abs N)`--),
(SIMPLE_INT_CASES_TAC THENL
 [GEN_TAC THEN DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC (--`M:integer`--) ABS_POS)),
  GEN_TAC THEN DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC (--`M:integer`--) ABS_NEG)),
  REWRITE_TAC[TIMES_ZERO, ABS_ZERO]]) THEN
ASM_REWRITE_TAC[] THEN
(SIMPLE_INT_CASES_TAC THENL
 [GEN_TAC THEN DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC (--`N:integer`--) ABS_POS)),
  GEN_TAC THEN DISCH_TAC THEN
  ASSUME_TAC (UNDISCH (SPEC (--`N:integer`--) ABS_NEG)),
  REWRITE_TAC[TIMES_ZERO, ABS_ZERO]]) THEN
ASM_REWRITE_TAC[TIMES_neg,PLUS_INV_INV_LEMMA] THENL
[(MATCH_MP_IMP_TAC ABS_POS THEN
  MATCH_MP_IMP_TAC POS_TIMES_POS_IS_POS THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC),
 (MATCH_MP_IMP_TAC ABS_NEG THEN
  MATCH_MP_IMP_TAC POS_TIMES_NEG_IS_NEG THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC),
 (MATCH_MP_IMP_TAC ABS_NEG THEN
  MATCH_MP_IMP_TAC(PURE_ONCE_REWRITE_RULE[COMM_TIMES]POS_TIMES_NEG_IS_NEG)THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC),
 (MATCH_MP_IMP_TAC ABS_POS THEN
  MATCH_MP_IMP_TAC NEG_TIMES_NEG_IS_POS THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)]);

(*
val ABS_TIMES_IS_ABS_TIMES_ABS =
 |- !M N. integer_abs (M times N) = integer_abs M times integer_abs N : thm
*)


val ABS_SQUARE = store_thm("ABS_SQUARE",
(--`!N. integer_abs (N times N) = N times N`--),
(SIMPLE_INT_CASES_TAC THENL
 [ALL_TAC,ALL_TAC,REWRITE_TAC[ABS_ZERO,TIMES_ZERO]]) THEN
REPEAT STRIP_TAC THENL
[REWRITE_TAC[ABS_TIMES_IS_ABS_TIMES_ABS,
	     UNDISCH(SPEC(--`N:integer`--)ABS_POS)],
 REWRITE_TAC[ABS_TIMES_IS_ABS_TIMES_ABS,
	     UNDISCH(SPEC(--`N:integer`--)ABS_NEG),
	     TIMES_neg, PLUS_INV_INV_LEMMA]]);

(*
val ABS_SQUARE = |- !N. integer_abs (N times N) = N times N : thm
*)

local
val X = (--`X:integer`--)
val x = (--`x:num`--)
val D = (--`D:integer`--)
val d = (--`d:num`--)

val DIV_BODY =
(--`POS D
    => (POS X
	=> INT((@x.X = INT x) DIV (@d.D = INT d))
	 | neg((@x.X = neg(INT x)) MOD (@d.D = INT d) = 0
	       => INT((@x.X = neg(INT x)) DIV (@d.D = INT d))
		| INT(((@x.X = neg(INT x)) DIV (@d.D = INT d))) plus (INT 1)))
     | (POS X
	=> neg(((@x.X = INT x) MOD (@d.D = neg(INT d))) = 0
	       => INT((@x.X = INT x) DIV (@d.D = neg(INT d)))
	        | INT((@x.X = INT x) DIV (@d.D = neg(INT d))) plus (INT 1))
	 | INT((@x.X = neg(INT x)) DIV (@d.D = neg(INT d))))`--)

val DIV = list_mk_abs([X, D],DIV_BODY)
val MOD_BODY = (--`X plus (neg ((^(DIV_BODY) times D)))`--)
val MOD = list_mk_abs([X, D],MOD_BODY)
val xthm0 =
    prove((--`!X. POS X ==> ?x. X = INT x`--),
	  (PURE_ONCE_REWRITE_TAC[POS_DEF] THEN
	   REPEAT STRIP_TAC THEN EXISTS_TAC (--`SUC n`--) THEN
	   FIRST_ASSUM ACCEPT_TAC))
val xthm1 = CONV_RULE
             ((ONCE_DEPTH_CONV (ALPHA_CONV X)) THENC
	      (ONCE_DEPTH_CONV (ALPHA_CONV x)))
	     NON_POS_INT_IS_neg_NUM
val thm0 = SPEC_ALL (MP (SPEC (--`SUC d`--) DIVISION)
		     (SPEC (--`d:num`--) LESS_0))
val (thm1,thm2) =
    case CONJUNCTS
	   (PURE_REWRITE_RULE [SYM(SPEC_ALL INT_ONE_ONE),
			       NUM_LESS_IS_INT_BELOW,
			       SYM(SPEC_ALL NUM_ADD_IS_INT_ADD),
			       SYM(SPEC_ALL NUM_MULT_IS_INT_MULT)] thm0)
      of [thm1,thm2] => (PURE_ONCE_REWRITE_RULE[COMM_PLUS]thm1,thm2)
       | _ => raise HOL_ERR{message="Impossible",
			    origin_function = "mod_div_thm",
			    origin_structure = "integer"}

val prod_tm = rand(rhs(concl thm1))

val thm3 =
    PURE_REWRITE_RULE[PLUS_GROUP_ASSOC,PLUS_INV_LEMMA,PLUS_ID_LEMMA]
      (BETA_RULE(AP_TERM (--`\z. z plus (neg^(prod_tm))`--) thm1))

val thm4 = PURE_ONCE_REWRITE_RULE [COMM_PLUS]
             (PURE_REWRITE_RULE [PLUS_INV_INV_LEMMA,
				 SYM(SPEC_ALL PLUS_DIST_INV_LEMMA)]
	                        (AP_TERM (--`neg`--) thm3))
in
val mod_div_thm = prove
((--`?mod div. !D X. (~(D = INT 0)) ==>
	((X = ((div X D) times D) plus (mod X D)) /\
	 (POS D => ((~(NEG(mod X D))) /\ ((mod X D) below D))
	         | ((~(POS(mod X D))) /\ (D  below (mod X D)))))`--),
EXISTS_TAC MOD THEN EXISTS_TAC DIV THEN BETA_TAC THEN
GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
((DISJ_CASES_TAC (CONJUNCT1(REWRITE_RULE[ASSUME(--`~(D = INT 0)`--)]
                                        (SPEC D TRICHOTOMY))) THENL
  [(STRIP_ASSUME_TAC (UNDISCH (fst (EQ_IMP_RULE
				    (CONV_RULE (ONCE_DEPTH_CONV(ALPHA_CONV d)) 
				     (SPEC D POS_DEF))))) THEN
    (REV_SUPPOSE_TAC (--`(@d. D = INT d) = SUC d`--) THENL
     [(PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL INT_ONE_ONE)] THEN
       PURE_ONCE_REWRITE_TAC [SYM(ASSUME (--`D = INT (SUC d)`--))] THEN
       CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
       EXISTS_TAC (--`SUC d`--) THEN FIRST_ASSUM ACCEPT_TAC),
     (ASM_REWRITE_TAC[])])),
   (STRIP_ASSUME_TAC (UNDISCH (fst (EQ_IMP_RULE
				    (CONV_RULE (ONCE_DEPTH_CONV(ALPHA_CONV d)) 
				     (SPEC D NEG_IS_neg_INT))))) THEN
    (REV_SUPPOSE_TAC (--`(@d. D = neg(INT d)) = SUC d`--) THENL
     [(PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL INT_ONE_ONE)] THEN
       PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL neg_ONE_ONE)] THEN
       SUBST1_TAC(SYM(ASSUME (--`D = neg(INT (SUC d))`--))) THEN
       CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
       EXISTS_TAC (--`SUC d`--) THEN FIRST_ASSUM ACCEPT_TAC),
      (ASM_REWRITE_TAC[REWRITE_RULE
                        [ASSUME(--`NEG D`--)]
                        (CONJUNCT1(CONJUNCT2(SPEC D TRICHOTOMY)))])]))]) THEN
 (ASM_CASES_TAC (--`POS X`--) THENL
  [(STRIP_ASSUME_TAC (UNDISCH (SPEC X xthm0))  THEN
    (REV_SUPPOSE_TAC (--`(@x. X = INT x) = x`--) THENL
     [(PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL INT_ONE_ONE)] THEN
       SUBST1_TAC (SYM(ASSUME (--`X = INT x`--))) THEN
       CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
       EXISTS_TAC x THEN FIRST_ASSUM ACCEPT_TAC),
      (ASM_REWRITE_TAC[])])),
   (STRIP_ASSUME_TAC (UNDISCH (fst (EQ_IMP_RULE (SPEC X xthm1)))) THEN
    (REV_SUPPOSE_TAC (--`(@x. X = neg(INT x)) = x`--) THENL
     [(PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL INT_ONE_ONE)] THEN
       PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL neg_ONE_ONE)] THEN
       SUBST1_TAC(SYM(ASSUME (--`X = neg(INT x)`--))) THEN
       CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
       EXISTS_TAC (--`x:num`--) THEN FIRST_ASSUM ACCEPT_TAC),
      (ASM_REWRITE_TAC[PLUS_DIST_INV_LEMMA,
		       TIMES_neg,
		       PLUS_INV_INV_LEMMA])]))]) THEN
 (CONJ_TAC THENL
  [(PURE_ONCE_REWRITE_TAC [COMM_PLUS] THEN
    REWRITE_TAC[SYM (SPEC_ALL ASSOC_PLUS),PLUS_INV_LEMMA,PLUS_ID_LEMMA]),
   ALL_TAC])) THENL
[(REWRITE_TAC[thm3,thm2,NOT_NEG_INT]),
 (ASM_CASES_TAC (--`x MOD SUC d = 0`--) THENL
  [(ASM_REWRITE_TAC[thm4,PLUS_INV_ID_LEMMA,ZERO_NOT_NEG,LESS_0,
		    SYM(SPEC_ALL NUM_LESS_IS_INT_BELOW)]),
   (ASM_REWRITE_TAC[RIGHT_PLUS_DISTRIB,TIMES_IDENTITY,
		    SYM(SPEC_ALL PLUS_GROUP_ASSOC),thm4,
		    PURE_ONCE_REWRITE_RULE [PLUS_ID_LEMMA,
					    SYM(SPEC_ALL NEG_IS_BELOW_ZERO)]
		    (SYM(SPECL [X,(--`INT 0`--),D] PLUS_BELOW_TRANSL))] THEN
    PURE_ONCE_REWRITE_TAC[NEG_IS_BELOW_ZERO] THEN
    (CONJ_TAC THEN
     SUBST_MATCH_TAC(PURE_ONCE_REWRITE_RULE[COMM_PLUS]
		     (SPECL [(--`M:integer`--),(--`N:integer`--),
			      (--`INT (x MOD SUC d)`--)]
		       PLUS_BELOW_TRANSL))) THENL
    [(REWRITE_TAC[PLUS_ID_LEMMA,PLUS_INV_LEMMA,
		  SYM(SPEC_ALL PLUS_GROUP_ASSOC),
		  SYM(SPEC_ALL NUM_LESS_IS_INT_BELOW),
		  NOT_LESS,LESS_OR_EQ,CONJUNCT2 thm0]),
     (PURE_REWRITE_TAC[PLUS_ID_LEMMA,PLUS_INV_LEMMA,
		       SYM(SPEC_ALL NUM_LESS_IS_INT_BELOW)] THEN
      DISJ_CASES_TAC (SPEC (--`x MOD SUC d`--) LESS_0_CASES) THENL
      [POP_ASSUM (ASSUME_TAC o SYM) THEN RES_TAC,
       FIRST_ASSUM ACCEPT_TAC])])]),
 (ASM_CASES_TAC (--`x MOD SUC d = 0`--) THENL
  [(ASM_REWRITE_TAC[TIMES_neg,PLUS_INV_INV_LEMMA,PLUS_ID_LEMMA,thm3,
		    ZERO_NOT_POS,SYM(SPEC_ALL NEG_IS_BELOW_ZERO),NEG_neg_INT]),
   (ASM_REWRITE_TAC[TIMES_neg,RIGHT_PLUS_DISTRIB,TIMES_IDENTITY,
		    PLUS_INV_INV_LEMMA,PLUS_ID_LEMMA,
		    PURE_ONCE_REWRITE_RULE
		     [AP_TERM(--`neg`--)(SPEC_ALL COMM_PLUS)]
		     (SYM(SPEC_ALL PLUS_DIST_INV_LEMMA)),
		    SYM(SPEC_ALL PLUS_GROUP_ASSOC),thm3] THEN
    PURE_ONCE_REWRITE_TAC[POS_IS_ZERO_BELOW] THEN
    (CONJ_TAC THEN
     SUBST_MATCH_TAC(SPECL [(--`M:integer`--),(--`N:integer`--),
			    (--`INT (SUC d)`--)]
		           PLUS_BELOW_TRANSL)) THENL
    [(REWRITE_TAC[PLUS_ID_LEMMA,PLUS_INV_LEMMA,PLUS_GROUP_ASSOC,
		  SYM(SPEC_ALL NUM_LESS_IS_INT_BELOW),
		  NOT_LESS,LESS_OR_EQ,CONJUNCT2 thm0]),
     (PURE_REWRITE_TAC[PLUS_ID_LEMMA,PLUS_INV_LEMMA,PLUS_GROUP_ASSOC,
		       SYM(SPEC_ALL NUM_LESS_IS_INT_BELOW)] THEN
      DISJ_CASES_TAC (SPEC (--`x MOD SUC d`--) LESS_0_CASES) THENL
      [POP_ASSUM (ASSUME_TAC o SYM) THEN RES_TAC,
       FIRST_ASSUM ACCEPT_TAC])])]),
 (REWRITE_TAC[thm4,NOT_POS_neg_INT,neg_REV_BELOW,thm2])])
end;


val mod_div_DEF =
new_specification{name = "mod_div_DEF", sat_thm = mod_div_thm,
		  consts = [{const_name = "mod", fixity = Infix 650},
			    {const_name = "div", fixity = Infix 650}]};


val _ = export_theory ();


