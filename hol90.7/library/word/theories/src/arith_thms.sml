(* ===================================================== *)
(* FILE: arith_thms.ml	    DATE: 8 Feb. 1994		 *)
(* AUTHOR: Wai WONG  	    	    			 *)
(* Description: Some arithmetic theorems used in more 	 *)
(*    than one file in the library.	    	 	 *)
(* TRANSLATED BY: Paul Curzon Aug 1994	    	 	 *)
(* ===================================================== *)

(*ba bb wa wb *)
(* LESS_EQ_SPLIT = |- !m n p. (m + n) <= p ==> n <= p /\ m <= p *)
val LESS_EQ_SPLIT = 
    let val asm_thm = ASSUME (--`(m + n) <= p`--)
    in
    GEN_ALL(DISCH_ALL
     (CONJ(MP(SPECL [(--`n:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
       	      (CONJ (SUBS [SPECL [(--`n:num`--),(--`m:num`--)] ADD_SYM]
                     (SPECL [(--`n:num`--),(--`m:num`--)] LESS_EQ_ADD))
                    asm_thm))
	  (MP (SPECL [(--`m:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
               (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm))))
    end;


val SUB_GREATER_EQ_ADD = prove(
    (--`!p n m. (p >= n) ==> (((p - n) >= m) = (p >= (m + n)))`--),
    REWRITE_TAC[
      SYM (SPEC (--`n:num`--) (SPEC (--`p-n`--) (SPEC (--`m:num`--) 
           (REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO_ADD_EQ))))]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM ( fn th  => ASSUME_TAC
      (MP (SPEC (--`n:num`--) (SPEC (--`p:num`--) SUB_ADD)) 
          (REWRITE_RULE[SPEC (--`n:num`--) (SPEC (--`p:num`--) GREATER_EQ)] th)))
    THEN SUBST_TAC[(SPEC_ALL ADD_SYM)] THEN ASM_REWRITE_TAC[]);

(*ba bb wa wb *)
(* ADD_LESS_EQ_SUB = |- !p n m. n <= p ==> ((n + m) <= p = m <= (p - n)) *)
val ADD_LESS_EQ_SUB = 
   GSYM (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);

(*wa *)
val ADD_LESS_EQ_TRANS = prove(
    (--`!m n p q. ((m + n) <= p) /\ (q <= n) ==> ((m + q) <= p)`--),
    INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[ADD]
      THENL[
      REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[CONJ_SYM]
      THEN MATCH_ACCEPT_TAC LESS_EQ_TRANS,
      GEN_TAC THEN INDUCT_TAC THENL[
        REWRITE_TAC[NOT_SUC_LESS_EQ_0],
        PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN REPEAT STRIP_TAC
        THEN RES_TAC]]);
(**)
val ADD_SUB_LEM = prove(
    (--`!m n p. p < n ==> ((m + n) - p = m + (n - p))`--),
    REPEAT INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_LESS_0,ADD_CLAUSES,LESS_MONO_EQ,SUB_0]
   THEN DISCH_TAC THEN REWRITE_TAC[SUB_MONO_EQ]
   THEN REWRITE_TAC[SUB,LESS_MONO_EQ]
    THEN IMP_RES_THEN (ASSUME_TAC o (PURE_ONCE_REWRITE_RULE[ADD_SYM])
        o (SPEC(--`m:num`--))) LESS_IMP_LESS_ADD
    THEN DISJ_CASES_THEN2 (fn t => ASSUME_TAC t THEN RES_TAC) (fn t => REWRITE_TAC[t])
        (REWRITE_RULE[DE_MORGAN_THM](SPECL[(--`p:num`--),(--`m + n`--)] LESS_ANTISYM))
    THEN RES_TAC THEN ASM_REWRITE_TAC[]);

(*ba wa wb *)
val LESS_EQ_0_EQ = prove(
    (--`!m. m <= 0 ==> (m = 0)`--),
    INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0]);

(*wb *)
val PRE_LESS_REFL = prove((--`!m . (0 < m) ==> (PRE m < m)`--),
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [LESS_REFL,LESS_0,PRE,LESS_SUC_REFL]);

(*ba bn *)
(* LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) *)
val LESS_DIV_EQ_ZERO = 
    GENL [(--`r:num`--),(--`n:num`--)] (DISCH_ALL (PURE_REWRITE_RULE[MULT,ADD]
    (SPEC (--`0`--)(UNDISCH_ALL (SPEC_ALL  DIV_MULT)))));

(*bn *)
(* MULT_DIV = |- !n q. 0 < n ==> ((q 'a n) DIV n = q) *)
val MULT_DIV = 
    GEN_ALL (PURE_REWRITE_RULE[ADD_0]
    (CONV_RULE RIGHT_IMP_FORALL_CONV (SPECL[(--`n:num`--),(--`0`--)] DIV_MULT)));

(* ba bn *)
val ADD_DIV_ADD_DIV = prove(
    (--`!n. 0 < n ==> !x r. ((((x * n) + r) DIV n) = x + (r DIV n))`--),
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN ASM_CASES_TAC (--`r < n`--) THENL[
      IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD_0]
      THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN (CHOOSE_TAC o (MATCH_MP (SPEC (--`r:num`--) DA)))
      THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
      THEN SUBST1_TAC (ASSUME (--`r = (q * n) + r'`--))
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB]
      THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT]);

(*bn *)
val NOT_MULT_LESS_0 = prove(
    (--`!m n. (0 < m) /\ (0 < n) ==> 0 < (m * n)`--),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,LESS_0]);

(*bn *)
val MOD_MULT_MOD = prove(
    (--`!m n. (0 < n) /\ (0 < m)  ==> !x. ((x MOD (n * m)) MOD n = x  MOD n)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NOT_MULT_LESS_0)) THEN GEN_TAC
    THEN POP_ASSUM (CHOOSE_TAC o (MATCH_MP (SPECL [(--`x:num`--),(--`m * n`--)]DA)))
    THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
    THEN SUBST1_TAC (ASSUME(--`x = (q * (n * m)) + r`--))
    THEN POP_ASSUM (SUBST1_TAC o (SPEC (--`q:num`--)) o (MATCH_MP MOD_MULT))
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN PURE_ONCE_REWRITE_TAC [GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN STRIP_ASSUME_TAC (ASSUME  (--`0 < n /\ 0 < m`--))
    THEN PURE_ONCE_REWRITE_TAC[UNDISCH_ALL(SPEC_ALL MOD_TIMES)]
    THEN REFL_TAC);

val MULT_RIGHT_1 = GEN_ALL (el 4 (CONJ_LIST 6 (SPEC_ALL MULT_CLAUSES)));

(*ba bn *)
(* |- !q. q DIV (SUC 0) = q *)
val DIV_ONE = 
    GEN_ALL (REWRITE_RULE[CONV_RULE (ONCE_DEPTH_CONV num_CONV) MULT_RIGHT_1]
    (MP (SPECL [(--`SUC 0`--), (--`q:num`--)] MULT_DIV) (SPEC (--`0`--) LESS_0)));

val Less_lemma = prove(
    (--`!m n. m < n ==> ?p. (n = m + p) /\ 0 < p`--),
    GEN_TAC THEN INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0],
      REWRITE_TAC[LESS_THM]
      THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
    	EXISTS_TAC (--`1`--) THEN CONV_TAC ((RAND_CONV o RAND_CONV)num_CONV)
    	THEN REWRITE_TAC[LESS_0,ADD1],
    	RES_TAC THEN EXISTS_TAC (--`SUC p`--)
    	THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_0]]]);

val Less_MULT_lemma = prove(
    (--`!r m p. 0 < p ==> (r < m) ==> (r < (p * m))`--),
    let val lem1 = MATCH_MP LESS_LESS_EQ_TRANS 
    	(CONJ (SPEC (--`m:num`--) LESS_SUC_REFL)
    	      (SPECL[(--`SUC m`--), (--`p * (SUC m)`--)] LESS_EQ_ADD))
   in
    GEN_TAC THEN REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN DISCH_TAC THEN REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)
    THEN PURE_ONCE_REWRITE_TAC[MULT]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THENL[
      ACCEPT_TAC lem1,
      ACCEPT_TAC (MATCH_MP LESS_TRANS (CONJ (ASSUME (--`r < m`--)) lem1))]
   end);

val Less_MULT_ADD_lemma = prove(
  (--`!m n r r'. 0 < m /\ 0 < n /\ r < m /\ r' < n ==> ((r' * m) + r) < (n * m)`--),
    REPEAT STRIP_TAC
    THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (--`r < m`--)))
    THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (--`r' < n`--)))
    THEN ASM_REWRITE_TAC[]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_ADD_EQ]
    THEN SUBST1_TAC (SYM (ASSUME(--`m = r + p`--)))
    THEN IMP_RES_TAC Less_MULT_lemma);

(*ba bn *)
val DIV_DIV_DIV_MULT = prove(
    (--`!m n. (0 < m) /\ (0 < n)  ==> !x. ((x DIV m) DIV n = x  DIV (m * n))`--),
    CONV_TAC (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN REPEAT STRIP_TAC
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC (--`x:num`--) (MATCH_MP DA (ASSUME (--`0 < m`--))))
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC (--`q:num`--) (MATCH_MP DA (ASSUME (--`0 < n`--))))
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN ASSUME_TAC (MATCH_MP NOT_MULT_LESS_0
    	(CONJ (ASSUME (--`0 < n`--)) (ASSUME (--`0 < m`--))))
    THEN CONV_TAC ((RAND_CONV o RAND_CONV) (REWR_CONV MULT_SYM))
    THEN CONV_TAC SYM_CONV THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN FIRST_ASSUM (fn t => REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV t])
    THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO
    THEN IMP_RES_TAC Less_MULT_ADD_lemma);
