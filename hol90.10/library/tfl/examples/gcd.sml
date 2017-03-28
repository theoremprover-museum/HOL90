new_theory"gcd";

(*---------------------------------------------------------------------------
 * The definition of GCD.
 *---------------------------------------------------------------------------*)
val {induction,rules,...} = Rfunction `measure (prod_case $+)`
  `(gcd (0,y) = y) /\
   (gcd (SUC x, 0) = SUC x) /\
   (gcd (SUC x, SUC y) = ((y<=x) => gcd(x-y, SUC y) 
                                 |  gcd(SUC x, y-x)))`;


(*---------------------------------------------------------------------------
 * Termination has automatically been proved.
 *---------------------------------------------------------------------------*)
val gcd_eqns = save_thm("gcd_eqns", rules);
val gcd_induction = save_thm("gcd_induction", induction);


save_thm("calculation",Q.prove`gcd (24,9) = 3`
 (CONV_TAC (REPEATC(CHANGED_CONV
   (REDEPTH_CONV num_CONV THENC RW_CONV[gcd_eqns] THENC REDUCE_CONV)))));


val SUB_EQUAL_0 = theorem"arithmetic" "SUB_EQUAL_0";
val num_CASES = theorem"arithmetic" "num_CASES";
val LEQ_ANTISYM = theorem"arithmetic" "LESS_EQUAL_ANTISYM";

val gcd_commutes = Q.store_thm("gcd_commutes",
`!x y. gcd(x,y) = gcd(y,x)`,
PROGRAM_TAC{induction=gcd_induction, rules=gcd_eqns}
  THEN ASM_RW_TAC[] 
  THENL
  [ STRUCT_CASES_TAC(Q.SPEC`y` num_CASES) THEN RW_TAC[gcd_eqns],
    IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) LEQ_ANTISYM THEN REFL_TAC,
    IMP_RES_TAC (EQT_ELIM(ARITH_CONV(Term`~(y<=x) ==> ~(x<=y) ==> F`)))]);

html_theory"-";


