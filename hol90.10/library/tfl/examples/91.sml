(*---------------------------------------------------------------------------
 * McCarthy's 91 function.
 *---------------------------------------------------------------------------*)
new_theory"ninety_one";


val N1def = 
Rfunction  `measure \x. 101 - x`
           `ninety_one x = (x>100 => (x-10) | ninety_one (ninety_one (x+11)))`;


(*---------------------------------------------------------------------------
 * Beautify the rules and induction theorem.
 *---------------------------------------------------------------------------*)

val ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC ARITH_CONV;
fun arith_fact qtm = Q.prove qtm (CONV_TAC ARITH_CONV);
val USE_ARITH_FACT = IMP_RES_THEN (fn th => RW_TAC[th]) o arith_fact;

val lem0 = arith_fact`(~(x>100)) ==> (101-y < 101-x = x<y)`;
val eqns = ONCE_RW_RULE[lem0] (#rules N1def);
val induction = ONCE_RW_RULE[lem0] (#induction N1def);
val tc = ONCE_RW_CONV[lem0] (hd(#tcs N1def));


(*--------------------------------------------------------------------------- 
 * Prove termination. We need to use wellfounded induction, since 
 * application of recursion induction seems to get derailed by the 
 * destructor-style definition of the function.
 *---------------------------------------------------------------------------*)

val th = ISPEC (Term`measure \x. 101 - x`) 
               (theorem"WF" "WF_INDUCTION_THM");

val ind = CONV_RULE (tc_simplifier[])
                    (RW_RULE[theorem"WF" "WF_measure"] th);


(*---------------------------------------------------------------------------
 * This proof is rather involved, but the fact that it succeeds shows that,
 * sometimes, termination and partial correctness for nested functions 
 * do not depend on each other, contrary to feelings expressed in
 * the literature. Of course, the termination property for 91 is a
 * partial correctness statement, since it involves the constant "91", but
 * more importantly, it's a termination condition, and if we were forced to
 * put it in one or the other category, it would go in the termination box.
 * As one would expect, the induction hypothesis gets used twice in this
 * proof, once at "x+11" and once at "ninety_one((x+11)+11) - 11".
 *---------------------------------------------------------------------------*)

val ninety1_terminates = Q.store_thm("ninety1_terminates",
`!x. ~(x>100) ==> x < ninety_one(x+11)`,
PROGRAM_TAC{induction = ind, rules = eqns} 
 THEN IMP_RES_THEN (fn th => RULE_ASSUM_TAC(RW_RULE[th])) lem0 THENL
 [ CONV_TAC ARITH_CONV,
   Q.ASM_CASES_TAC`ninety_one((x+11)+11) -11 > 100` THENL
   [ SUBST_TAC[Q.INST[`x` |-> `ninety_one((x+11)+11)`] eqns] 
       THEN USE_ARITH_FACT`x-11 > 100 ==> x>100` 
       THEN Q.UNDISCH_TAC`x+11 < ninety_one((x+11)+11)` 
       THEN CONV_TAC ARITH_CONV,
     IMP_RES_TAC(arith_fact`v+11<z ==> v<z-11`) THEN RES_TAC 
      THEN IMP_RES_THEN SUBST_ALL_TAC (arith_fact`w+11<y ==> ((y-11)+11 = y)`)
      THEN IMP_RES_TAC (theorem"arithmetic" "LESS_TRANS")],
   ANTE_RES_THEN IMP_RES_TAC (arith_fact`x<x+11`) THEN RES_TAC]);

(*---------------------------------------------------------------------------
 Yet more junk

e (REC_INDUCT_TAC (#induction N1def));
e (RW_TAC[lem0]);
e (REPEAT STRIP_TAC);
e (Q.ASM_CASES_TAC`ninety_one(x+11) > 100`);
(*1*)
e (IMP_RES_TAC(EQT_ELIM(ARITH_CONV(Term`~(x>c) ==> y>c ==> x<y`))));

(*2*)
e (ONCE_RW_TAC[#rules N1def]);
e (COND_CASES_TAC);
(*2.1*)
e (CONV_TAC ARITH_CONV);
(*2.2*)
e (ASM_CRW_TAC[lem0]);


val th = RW_RULE[lem0] (#rules N1def);
val th1 = Q.SPEC`y-11` (GEN_ALL th);
val th2 = Q.SPEC`(x+11)+11` (GEN_ALL th1);
val th3 = RW_RULE[EQT_ELIM(ARITH_CONV(Term`(x+11)-11 = x`))] th2;

val th1 = Q.SPEC`x+22` (GEN_ALL th);
val th2 = Q.SPEC`(x+11)+11` (GEN_ALL th1);
val th3 = RW_RULE[EQT_ELIM(ARITH_CONV(Term`(x+11)-11 = x`))] th2;



g`!x. ~(x>100) ==> x < ninety_one(x+11)`;
e (REC_INDUCT_TAC ind);
e (ONCE_RW_TAC[Q.TAUT_CONV `A ==> B ==> C = B ==> A ==> C`]);
e (RW_TAC[lem0]);
e (REPEAT STRIP_TAC);
e (ONCE_RW_TAC[eqns]);
e (COND_CASES_TAC);
(*1*)
e (CONV_TAC ARITH_CONV);
(*2*)
e (COND_CASES_TAC);
(*2.1*)
val LESS_MONO_ADD_INV = theorem"arithmetic" "LESS_MONO_ADD_INV";
e (MATCH_MP_TAC LESS_MONO_ADD_INV);
e (Q.EXISTS_TAC	`11`);
e (MATCH_MP_TAC (theorem"arithmetic" "LESS_TRANS"));
e (Q.EXISTS_TAC `ninety_one ((x + 11) + 11)`);
e (ASM_RW_TAC[]);

(*2.2*)
e(ANTE_RES_THEN IMP_RES_TAC (arith_fact`x<x+11`) THEN RES_TAC);
*---------------------------------------------------------------------------*)


val N1induct = RW_RULE[ninety1_terminates] induction;

val N1eqns = RW_RULE[ninety1_terminates] eqns;


(*----------------------------------------------------------------------------
 * Prove a property of 91. Induction not needed. Not used in correctness proof.
 *---------------------------------------------------------------------------*)

fun UNROLL1_TAC qtm = 
    SUBST1_TAC (Q.INST[`x` |-> qtm] N1eqns) THEN CONV_TAC REDUCE_CONV;

val climb90 = Q.store_thm("climb90",
`!n. 90<=n/\n<=100 ==> (ninety_one(n) = ninety_one(n+1))`,
RW_TAC[definition"arithmetic" "LESS_OR_EQ"] THEN GEN_TAC THEN
 SUBST1_TAC(SYM_CONV(Term`90=n`)) THEN REPEAT STRIP_TAC THEN ASM_RW_TAC[] 
 THENL
   [ UNROLL1_TAC`n:num` THEN USE_ARITH_FACT`x<y ==> ~(x>y) /\ ~(x+1>y)` THEN
     UNROLL1_TAC`n+11`  THEN USE_ARITH_FACT`90<n ==> n+11>100` THEN
     SUBST1_TAC (arith_fact`(n+11)-10 = n+1`),

     UNROLL1_TAC`100` THEN UNROLL1_TAC`111`,
     UNROLL1_TAC`100` THEN UNROLL1_TAC`90` THEN UNROLL1_TAC`101`,
     UNROLL1_TAC`100` THEN UNROLL1_TAC`111`]
  THEN REFL_TAC);


Thm.counting_thms true;

(*---------------------------------------------------------------------------
 * A simple specification for 91. 
 *---------------------------------------------------------------------------*)
val ninety1_correct = Q.store_thm("ninety1_correct",
`!n. ninety_one n = (n>100 => n-10 | 91)`,
PROGRAM_TAC{induction = N1induct, rules = N1eqns} 
  THEN ASM_RW_TAC[]
  THEN POP_ASSUM MP_TAC
  THEN CONV_TAC ARITH_CONV);

let val {ABS,ASSUME,BETA_CONV,DISCH,INST_TYPE,MP,
            REFL,SUBST,drule,other,...} = thm_count()
in output(std_out,"theorems proved: "^
          Lib.int_to_string(ABS + ASSUME + BETA_CONV + DISCH + INST_TYPE + 
              MP + REFL + SUBST + drule + other)^".\n")
end;

html_theory"-";
