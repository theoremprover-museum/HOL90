Q.prove`!y.0<y ==> (SUC(PRE y) = y)`
(GEN_CASES_TAC num_CASES THEN SIMPL
 THENL [ARITH_TAC, RW_TAC[theorem"prim_rec" "PRE"]]);

