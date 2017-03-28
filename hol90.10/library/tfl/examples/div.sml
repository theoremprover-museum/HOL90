(* An algorithm for division *)

new_theory"div";


(*---------------------------------------------------------------------------
 * Proof support
 *---------------------------------------------------------------------------*)
use"../utils.sml";
fun NTAC n tac = funpow n (curry (op THEN) tac) ALL_TAC;
local open RW
      val pss = RW.add_rws (RW.Implicit.implicit_simpls())
            [theorem"arithmetic" "ADD_CLAUSES",
             theorem"arithmetic" "MULT_CLAUSES",
             theorem "arithmetic" "LEFT_ADD_DISTRIB",
             theorem "arithmetic" "RIGHT_ADD_DISTRIB",
             theorem"arithmetic" "LESS_EQ_REFL",
             theorem"num" "NOT_SUC",
             theorem"arithmetic" "LESS_MONO_EQ",
             theorem"prim_rec" "LESS_REFL",
             theorem"prim_rec" "NOT_LESS_0",
             theorem"prim_rec" "LESS_0", 
             theorem"prim_rec" "LESS_SUC_REFL",
             theorem"prim_rec" "INV_SUC_EQ",
             theorem"arithmetic" "SUB_EQUAL_0",
             theorem"pair" "PAIR_EQ"]
      val RWTAC = REWRITE_TAC Fully (Simpls(pss,[]),Context([],ADD),
                                     Congs[],Solver std_solver)
in
val SIMPL = RWTAC THEN TRY(CHANGED_TAC BETA_TAC THEN RWTAC)
end;

val ARITH = EQT_ELIM o ARITH_CONV o Term;
val ARITH_TAC = CONV_TAC ARITH_CONV;
val LET_TAC = CONV_TAC (DEPTH_CONV let_CONV);


(*---------------------------------------------------------------------------
 * An (prim. rec.) algorithm for division in the natural numbers.
 *---------------------------------------------------------------------------*)
val div_def = 
Rfunction `inv_image ^pred FST`
   `(div(0,SUC x) = (0,0)) /\
    (div(SUC x, SUC y) = let (q,r) = div(x, SUC y)
                         in (r=y) => (SUC q, 0) 
                                   |  (q, SUC r))`;

val slash_def = 
Q.new_infix_definition
("slash_def", `$/ x y = FST(div(x,y))`,650);

val mod_def = Q.new_definition("mod_def", `mod x y = SND(div(x,y))`);

val induction = save_thm("div_induction", #induction div_def);
val eqns = save_thm("div_eqns", #rules div_def);

val div_results = Q.store_thm("div_results",
`!m d. ?q r. div(m, SUC d) = (q,r)`,
REPEAT GEN_TAC 
   THEN Q.EXISTS_TAC`FST(div(m, SUC d))` 
   THEN Q.EXISTS_TAC`SND(div(m, SUC d))`
   THEN SIMPL);


(*---------------------------------------------------------------------------
 * Fake higher-order rewriting.
 *---------------------------------------------------------------------------*)
val lem = BETA_RULE
(Q.ISPECL
  [`\hole:num#num. ((q,r)=hole) ==> (SUC x = (y*q +q) + r)`,
   `div(x,SUC y)`, `\q r. (r=y) => (SUC q,0) | (q,SUC r)`]
       PULL_LET2);;


val lem1 = BETA_RULE
(Q.ISPECL
  [`\hole:num#num. ((q,r)=hole) ==> r < SUC y`,
   `div(x,SUC y)`, `\q r. (r=y) => (SUC q,0) | (q,SUC r)`]
       PULL_LET2);;

(*---------------------------------------------------------------------------
 * Correctness of div.
 *---------------------------------------------------------------------------*)
val div_correct = Q.store_thm("div_correct",
`!a b q r. 0<b ==> ((q,r) = div(a,b)) ==> (a = b*q + r) /\ r<b`,
PROG_TAC{induction = induction, rules = eqns}
   THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(Term`x<x ==> F`)))
   THEN POP_ASSUM MP_TAC THEN SIMPL THEN TRY (CONV_TAC ARITH_CONV)
   THENL (map (fn th => PURE_RW_TAC[th]) [lem, lem1])
   THEN LET_INTRO_TAC THEN DISCH_TAC THEN RES_TAC THEN COND_CASES_TAC 
   THEN SIMPL THEN DISCH_THEN (K ALL_TAC)
   THEN ASM_RW_TAC[] THEN SIMPL
   THENL [ALL_TAC, NTAC 2 (POP_ASSUM MP_TAC)]
   THEN CONV_TAC ARITH_CONV);


(*---------------------------------------------------------------------------
 * Trade 0<b in correctness for a constructor formulation.
 *---------------------------------------------------------------------------*)
val pos_div_correct = save_thm("pos_div_correct",
 itlist Q.GEN [`a`,`b`]
   (RW_RULE[EQT_ELIM(ARITH_CONV(Term`0<SUC m`))]
     (Q.SPECL[`a`,`SUC b`] div_correct)));

(*---------------------------------------------------------------------------
 * Division by 1.
 *---------------------------------------------------------------------------*)
val div1_lem = Q.prove
`!a b. (b = SUC 0) ==> (div(a,b) = (a,0))`
(PROG_TAC{induction = induction, rules = eqns}
  THEN IMP_RES_TAC(ARITH`~(0 = SUC x)`)
  THEN RES_THEN SUBST1_TAC
  THEN LET_TAC THEN COND_CASES_TAC THEN SIMPL
  THEN NTAC 2 (POP_ASSUM MP_TAC) THEN CONV_TAC ARITH_CONV);

val div_one = save_thm("div_one",MATCH_MP (RW_RULE[]div1_lem) (Q.REFL`SUC 0`));
val div1    = save_thm("div1", RW_RULE[SYM(Q.num_CONV`1`)] div_one);
val slash_one = Q.store_thm("slash_one",
`!x. x/SUC 0 = x`,RW_TAC[slash_def,div_one]);
val slash1   = save_thm("slash1", RW_RULE[SYM(Q.num_CONV`1`)] slash_one);

val quotient0 = Q.store_thm("quotient0",
`!m d. m<SUC d ==> (div(m,SUC d) = (0,m))`,
PROG_TAC{induction = induction, rules = eqns}
  THEN IMP_RES_TAC(ARITH`SUC x < SUC 0 ==> F`)
  THEN IMP_RES_TAC(ARITH`SUC x < y ==> x < y`)
  THEN RES_THEN SUBST1_TAC
  THEN LET_TAC THEN COND_CASES_TAC THEN SIMPL
  THEN POP_ASSUM SUBST_ALL_TAC
  THEN IMP_RES_TAC(ARITH`~(x<x)`));

val slash_eq0 = Q.store_thm("slash_eq0",
`!m d. m<SUC d ==> (m/SUC d = 0) /\ (mod m (SUC d) = m)`,
RW_TAC[slash_def,mod_def,quotient0]);

val slash_eq0_numerator = Q.store_thm("slash_eq0_numerator",
`!m d. 0<d /\ (m/d = 0) ==> m<d`,
RW_TAC[slash_def] THEN REPEAT STRIP_TAC
 THEN IMP_RES_THEN (CHOOSE_THEN SUBST_ALL_TAC) 
    (Q.prove`!d. 0<d ==> ?d'. d = SUC d'`
         (GEN_CASES_TAC (theorem"arithmetic" "num_CASES") THEN SIMPL))
 THEN REPEAT_TCL CHOOSE_THEN (ASSUME_TAC o SYM) (Q.SPECL[`m`,`d'`]div_results)
 THEN IMP_RES_TAC div_correct THEN ASM_RW_TAC[]
 THEN Q.SUBGOAL_THEN`q=0`SUBST1_TAC
 THENL [RULE_ASSUM_TAC GSYM, SIMPL]
 THEN ASM_RW_TAC[]);

(* Generalizable? *)
val slash_numerator_pos = Q.store_thm("slash_numerator_pos",
`!d m. 0<d /\ 0<m/d ==> 0<m`,
RW_TAC[slash_def,Q.TAUT_CONV`x/\y==>z = x==>y==>z`]
THEN REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN(CHOOSE_THEN SUBST_ALL_TAC)
 (Q.prove`!d. 0<d ==> ?d'. d = SUC d'`
      (GEN_CASES_TAC (theorem"arithmetic" "num_CASES") THEN SIMPL)) 
THEN REPEAT_TCL CHOOSE_THEN (fn th => SUBST1_TAC th THEN ASSUME_TAC(SYM th))
                (Q.SPECL[`m`,`d'`]div_results)
THEN IMP_RES_TAC div_correct THEN ASM_RW_TAC[] THEN SIMPL THEN ARITH_TAC);

(*---------------------------------------------------------------------------
 * Miscellaneous lemmas
 *---------------------------------------------------------------------------*)
val lem = BETA_RULE
(Q.ISPECL
  [`\hole. hole = (1,0)`, `div(x,SUC (SUC y))`, 
   `\q r. (r=SUC y) => (SUC q,0) | (q,SUC r)`]
       PULL_LET2);;

val less_pos_mult = Q.prove
`!n m. n < SUC n * SUC m`(REPEAT INDUCT_TAC THEN SIMPL THEN ARITH_TAC);

val blat = Q.prove
`!p m n. (p = SUC p * m + n) ==> (m=0) /\ (n=p)`
(REPEAT GEN_TAC 
  THEN CONV_TAC CONTRAPOS_CONV THEN CONV_TAC NNF_CONV
  THEN STRIP_ASSUME_TAC (SPEC_ALL(theorem"arithmetic" "num_CASES"))
  THEN ASM_RW_TAC[]
  THENL [ SIMPL THEN CONV_TAC CONTRAPOS_CONV THEN SIMPL,
          MATCH_MP_TAC(ARITH`x<y ==> ~(x=y+z)`) 
          THEN MATCH_ACCEPT_TAC less_pos_mult]);

(*---------------------------------------------------------------------------
 * There must be a better proof. Probably one can reason just from the
 * correctness property.
 *---------------------------------------------------------------------------*)
val q1 = Q.prove
`!m d. (m=SUC d) ==> (div(m, SUC d) = (1,0))`
(PROG_TAC{induction = induction, rules = eqns}
 THEN IMP_RES_TAC(ARITH`~(0=SUC x)`)
 THENL
 [IMP_RES_THEN SUBST1_TAC (ARITH`(SUC x = SUC y) ==> (x=y)`) THEN RW_TAC[eqns]
   THEN LET_TAC THEN SIMPL THEN RW_TAC[Q.num_CONV`1`],
  RW_TAC[lem] THEN LET_INTRO_TAC THEN DISCH_TAC
   THEN IMP_RES_TAC pos_div_correct
   THEN COND_CASES_TAC
   THENL
    [ POP_ASSUM SUBST_ALL_TAC
      THEN Q.UNDISCH_TAC`SUC x = SUC (SUC y)` 
      THEN DISCH_THEN(SUBST_ALL_TAC o RW_RULE[ARITH`(SUC x = SUC y) = (x=y)`])
      THEN IMP_RES_TAC (ARITH`(x=y+x) ==> (y=0)`)
      THEN IMP_RES_TAC (MATCH_MP (Q.TAUT_CONV`(x=y) ==> (x ==> y)`)
                           (SPEC_ALL(theorem "arithmetic" "MULT_EQ_0")))
      THENL [IMP_RES_TAC(ARITH`~(SUC x = 0)`),
             ASM_RW_TAC[] THEN RW_TAC[Q.num_CONV`1`]],
     SIMPL THEN Q.UNDISCH_TAC`SUC x = SUC (SUC y)` 
     THEN DISCH_THEN (SUBST_ALL_TAC o RW_RULE[ARITH`(SUC x = SUC y) = (x=y)`])
     THEN IMP_RES_THEN SUBST_ALL_TAC blat
     THEN POP_ASSUM MP_TAC THEN RW_TAC[]]]);

val div_id = save_thm("div_id",MATCH_MP(RW_RULE[] q1) (Q.REFL`SUC d`));
val slash_mod_id = Q.store_thm("slash_mod_id",
`!x. (SUC x/SUC x = 1) /\ (mod (SUC x) (SUC x) = 0)`,
RW_TAC[slash_def,mod_def,div_id]);

val MULT_SYM = theorem"arithmetic" "MULT_SYM";
val num_CASES = theorem"arithmetic" "num_CASES";
val LESS_ADD = theorem"arithmetic" "LESS_ADD";
val TRICHOTOMY = theorem"arithmetic" "LESS_LESS_CASES";
val ADD_ASSOC = GSYM(theorem"arithmetic" "ADD_ASSOC");
val ADD_SYM = theorem"arithmetic" "ADD_SYM";

val thm = Q.prove
`(k*m = k*n + z) ==> ?d. z = k*d`
(DISCH_THEN (SUBST1_TAC o MATCH_MP (ARITH`(x = y+z) ==> (z = x-y)`))
 THEN Q.EXISTS_TAC`m-n`
 THEN RW_TAC[theorem"arithmetic" "LEFT_SUB_DISTRIB"]);

(*---------------------------------------------------------------------------
 * Could also use MULT_SUC_EQ ... for some unknown reason I thought I had to 
 * prove this myself.
 *---------------------------------------------------------------------------*)
val MULT11 = Q.prove`!k m n. (SUC k*m = SUC k*n) = (m=n)`
(REPEAT GEN_TAC 
  THEN SIMPL
  THEN STRIP_ASSUME_TAC(Q.SPECL[`m`,`n`] TRICHOTOMY)
  THENL [ ASM_RW_TAC[], ALL_TAC, ALL_TAC]
  THEN IMP_RES_THEN (CHOOSE_THEN (SUBST_ALL_TAC o SYM)) LESS_ADD
  THEN RW_TAC[theorem"arithmetic" "LEFT_SUB_DISTRIB"] THEN SIMPL
  THENL[ RW_TAC[ARITH`(x+y = (w+x)+v+y) = (0=w+v)`],
         RW_TAC[ARITH`((w+x)+v+y = x+y) = (0=w+v)`]]
  THEN IMP_RES_THEN MP_TAC (ARITH`m<p+m ==> ~(p=0)`)
  THEN ARITH_TAC);

val ADD11 = Q.prove`!a b x. ((a+x = b+x) = (a=b)) /\ ((x+a = x+b) = (a=b))`
(REPEAT GEN_TAC THEN ARITH_TAC);;

(*---------------------------------------------------------------------------
 * Numbers are fun! This is the crux lemma for the following 3 theorems.
 *---------------------------------------------------------------------------*)
val gag = Q.prove
`!r1 r2 d q1 q2.
    r1<d /\ r2<d ==> (d*q1 + r1 = d*q2 + r2) ==> (q1=q2) /\ (r1=r2)`
(GEN_TAC THEN GEN_TAC THEN GEN_CASES_TAC num_CASES THENL
 [ARITH_TAC,REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC
   THEN Q.SUBGOAL_THEN`r1:num = r2`(fn th => POP_ASSUM MP_TAC THEN RW_TAC[th])]
 THENL
 [POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC(Q.SPECL[`r1`,`r2`] TRICHOTOMY) 
   THEN ASM_RW_TAC[] THENL
   [MP_TAC(Q.SPECL[`r2`,`r1`]LESS_ADD),MP_TAC(Q.SPECL[`r1`,`r2`]LESS_ADD)]
   THEN ASM_RW_TAC[] THEN DISCH_THEN (CHOOSE_THEN (SUBST_ALL_TAC o SYM))
   THEN RW_TAC[GSYM ADD_ASSOC,ADD11] THENL[ALL_TAC,DISCH_THEN (MP_TAC o GSYM)]
   THEN DISCH_THEN(CHOOSE_THEN MP_TAC o MATCH_MP thm)
   THEN STRUCT_CASES_TAC(Q.SPEC`d`num_CASES) THEN SIMPL
   THEN DISCH_THEN SUBST_ALL_TAC 
   THENL [POP_ASSUM (K ALL_TAC), NTAC 2 (POP_ASSUM (K ALL_TAC))]
   THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
  RW_TAC[ADD11,MULT11]]);


(*---------------------------------------------------------------------------
 * This is the relationship between division and addition.
 *---------------------------------------------------------------------------*)
val div_plus_suc = Q.store_thm("div_plus_suc",
`!m d q r q1 r1. (div(m,SUC d) = (q,r)) 
                    ==> (div(m+SUC d,SUC d) = (q1,r1)) 
                      ==> (SUC q=q1) /\ (r=r1)`,
REPEAT GEN_TAC 
  THEN DISCH_THEN(STRIP_ASSUME_TAC o (MATCH_MP pos_div_correct o SYM))
  THEN DISCH_THEN(MP_TAC o (MATCH_MP pos_div_correct o SYM))
  THEN PURE_ASM_RW_TAC[]
  THEN Q.SUBGOAL_THEN`!d. (d*q+r)+d = SUC q*d + r` (fn th => RW_TAC[th])
  THENL
  [GEN_TAC THEN SIMPL THEN SUBST_TAC[Q.SPECL[`d'`,`q`]MULT_SYM]THEN ARITH_TAC,
   SUBST_TAC[Q.SPECL[`SUC q`,`SUC d`]MULT_SYM] THEN STRIP_TAC THEN 
   IMP_RES_TAC gag THEN ASM_RW_TAC[]]);


val slash_plus = Q.store_thm("slash_plus",
`!m d. (m+SUC d)/SUC d = SUC(m/SUC d)`,
RW_TAC[slash_def] 
  THEN REPEAT GEN_TAC THEN STRIP_ASSUME_TAC(Q.SPECL[`m+SUC d`,`d`] div_results)
  THEN STRIP_ASSUME_TAC (SPEC_ALL div_results) THEN IMP_RES_TAC div_plus_suc
  THEN ASM_RW_TAC[]);

val mod_plus = Q.store_thm("mod_plus",
`!m d. mod (m+SUC d) (SUC d) =  mod m (SUC d)`,
RW_TAC[mod_def] 
  THEN REPEAT GEN_TAC THEN STRIP_ASSUME_TAC(Q.SPECL[`m+SUC d`,`d`] div_results)
  THEN STRIP_ASSUME_TAC (SPEC_ALL div_results) THEN IMP_RES_TAC div_plus_suc
  THEN ASM_RW_TAC[]);


val quotient_less = Q.store_thm("quotient_less",
`!d n. 0<n /\ 0<d ==> n/SUC d < n`,
REPEAT GEN_TAC THEN RW_TAC[slash_def]
  THEN MP_TAC (Q.SPECL[`n`,`d`]div_results) 
  THEN DISCH_THEN (REPEAT_TCL CHOOSE_THEN(fn th => 
     SUBST1_TAC th THEN MP_TAC ((MATCH_MP pos_div_correct o SYM) th)))
  THEN RW_TAC[]
  THEN DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)
  THEN STRIP_ASSUME_TAC (Q.SPEC`q` num_CASES)
  THEN ASM_RW_TAC[] THEN SIMPL THEN ARITH_TAC);


html_theory"-";
export_theory();

