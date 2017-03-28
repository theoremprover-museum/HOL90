(*===========================================================================*)
(* Definitions of the transcendental functions etc.                          *)
(*===========================================================================*)
(* use "useful.sml"; *)

load_theory "POWSER";

new_theory "TRANSC";

(*---------------------------------------------------------------------------*)
(* Some miscellaneous lemmas                                                 *)
(*---------------------------------------------------------------------------*)

val MULT_DIV_2 = PROVE
 ((--`!n. (2 * n) DIV 2 = n`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MP_TAC(SPECL [(--`2`--), (--`0`--)] DIV_MULT) THEN REDUCE_TAC THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_ACCEPT_TAC);

val EVEN_DIV2 = PROVE
 ((--`!n. ~(EVEN n) ==> ((SUC n) DIV 2 = SUC((n - 1) DIV 2))`--),
  GEN_TAC THEN REWRITE_TAC[EVEN_ODD, ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC) THEN
  REWRITE_TAC[SUC_SUB1] THEN REWRITE_TAC[ADD1, GSYM ADD_ASSOC] THEN
  SUBST1_TAC(EQT_ELIM(REDUCE_CONV (--`1 + 1 = 2 * 1`--))) THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB, MULT_DIV_2]);

map autoload_definitions ["REAL", "TOPOLOGY", "NETS","SEQ", "LIM", "POWSER"];

map autoload_theorems ["REAL", "TOPOLOGY", "NETS", "SEQ", "LIM", "POWSER"];

(*---------------------------------------------------------------------------*)
(* A conversion to differentiate expressions                                 *)
(*---------------------------------------------------------------------------*)

val basic_diffs = ref ([]:thm list);


(*---------------------------------------------------------------------------*)
(* DIFF_CONV "fn t => f[t]" =                                                *)
(*   |- !l1..ln x. conditions[x] ==> ((fn t => f[t]) diffl f'[x])(x)         *)
(* Where the li's are hypothetical derivatives for unknown sub-functions     *)
(*---------------------------------------------------------------------------*)

fun DIFF_CONV tm =
  let val xv = variant (frees tm) (--`x:real`--)
      val iths = map TAUT_CONV
             [(--`(a ==> c) /\ (b ==> d) ==> ((a /\ b) ==> (c /\ d))`--),
              (--`c /\ (b ==> d) ==> (b ==> (c /\ d))`--),
              (--`(a ==> c) /\ d ==> (a ==> (c /\ d))`--),
              (--`c /\ d ==> c /\ d`--)]
      val [DIFF_INV', DIFF_DIV'] =
        map (ONCE_REWRITE_RULE[TAUT_CONV (--`a /\ b ==> c = a ==> b ==> c`--)])
            [DIFF_INV, REWRITE_RULE[CONJ_ASSOC] DIFF_DIV]
      val comths = [DIFF_ADD, DIFF_MUL, DIFF_SUB,
        DIFF_DIV', DIFF_NEG, DIFF_INV']
      fun is_diffl tm =
        (funpow 3 rator tm = (--`$diffl`--) handle _ => false)
      fun make_assoc th =
        let val tm1 = (snd o strip_imp o snd o strip_forall o concl) th
            val tm2 = (rand o rator o rator) tm1 in
            if is_abs tm2 then
              (fst(strip_comb(body tm2)),th)
            else
              let val th1 = ETA_CONV (mk_abs((--`x:real`--),mk_comb(tm2,(--`x:real`--))))
                  val th2 = AP_TERM (--`$diffl`--) (SYM th1)
                  val th3 = ONCE_REWRITE_RULE[th2] th in
              (fst(strip_comb tm2),th3) end end
      val [cths, bths] = map (map make_assoc) [comths, !basic_diffs]
      fun ICONJ th1 th2 =
        let val [th1a, th2a] = map (SPEC xv) [th1, th2] in
        GEN xv (tryfind (C MATCH_MP (CONJ th1a th2a)) iths) end
      fun diff tm =
        let val (v,bod) = dest_abs tm in
            if not (free_in v bod) then
              GEN xv (SPECL [bod, xv] DIFF_CONST)
            else if bod = v then
              GEN xv (SPEC xv DIFF_X)
            else
              let val (opp,args) = strip_comb bod in
              (let val th1 = snd(assoc opp cths)
                   val nargs = map (curry mk_abs v) args
                   val dargs = map diff nargs
                   val th2 = end_itlist ICONJ dargs
                   val th3 = UNDISCH (SPEC xv th2) handle _ => SPEC xv th2
                   val th4 = MATCH_MP th1 th3
                   val th5 = DISCH_ALL th4 handle _ => th4
                   val th6 = Rewrite.GEN_REWRITE_RULE I Rewrite.empty_rewrites
                          [TAUT_CONV (--`a ==> b ==> c = a /\ b ==> c`--)] th5 
                          handle _ => th5
                   val th7 = CONV_RULE(REDEPTH_CONV BETA_CONV) th6 in
               GEN xv th7 end handle _ =>
               let val arg = hd args
                   val narg = mk_abs(v,arg)
                   val th1 = if opp = (--`$pow`--) 
                             then SPEC (last args) DIFF_POW
                             else snd(assoc opp bths)
                   val th2 = GEN xv (SPEC (mk_comb(narg,xv)) th1)
                   val th3 = diff narg
                   val th4 = SPEC xv (ICONJ th2 th3)
                   val th5 = MATCH_MP DIFF_CHAIN (UNDISCH th4 handle _ => th4)
                   val th6 = CONV_RULE(REDEPTH_CONV BETA_CONV) (DISCH_ALL th5) in
               GEN xv th6 end handle _ =>
               let val tm1 = mk_comb((--`$diffl`--),tm)
                   val var = variant (frees tm) (--`l:real`--)
                   val tm2 = mk_comb(tm1,var)
                   val tm3 = mk_comb(tm2,xv) in
               GEN xv (DISCH tm3 (ASSUME tm3)) end) end end
      val tha = diff tm
      val cjs = conjuncts(fst(dest_imp(snd(strip_forall(concl tha))))) handle _ => []
      val cj2 = filter is_diffl cjs
      val fvs = map (rand o rator) cj2
      val thb = itlist GEN fvs tha in
      CONV_RULE (ONCE_DEPTH_CONV(C ALPHA tm)) thb end;

(*---------------------------------------------------------------------------*)
(* The three functions we define by series are exp, sin, cos                 *)
(*---------------------------------------------------------------------------*)

val exp_ser = (--`\n. inv(&(FACT n))`--);

val sin_ser = (--`\n. EVEN n => &0 |
              ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n)`--);

val cos_ser = (--`\n. EVEN n =>
              ((--(&1)) pow (n DIV 2)) / &(FACT n) | &0`--);

val exp = new_definition("exp",
  (--`exp(x) = suminf(\n. (^exp_ser) n |*| (x pow n))`--));

val sin = new_definition("sin",
  (--`sin(x) = suminf(\n. (^sin_ser) n |*| (x pow n))`--));

val cos = new_definition("cos",
  (--`cos(x) = suminf(\n. (^cos_ser) n |*| (x pow n))`--));

(*---------------------------------------------------------------------------*)
(* Show the series for exp converges, using the ratio test                   *)
(*---------------------------------------------------------------------------*)

val EXP_CONVERGES = prove_thm("EXP_CONVERGES",
  (--`!x. (\n. (^exp_ser) n |*| (x pow n)) sums exp(x)`--),
  let fun fnz tm =
    (GSYM o MATCH_MP REAL_LT_IMP_NE o
     REWRITE_RULE[GSYM REAL_LT] o C SPEC FACT_LESS) tm in
  GEN_TAC THEN REWRITE_TAC[exp] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_RATIO THEN
  MP_TAC (SPEC (--`&1`--) REAL_DOWN) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`c:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`c:real`--) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC (--`c:real`--) REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC (--`abs(x)`--)) THEN
  DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THEN EXISTS_TAC (--`N:num`--) THEN
  X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[GREATER_EQ] THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ADD1, POW_ADD, ABS_MUL, REAL_MUL_ASSOC, POW_1] THEN
  GEN_REWR_TAC LAND_CONV  [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL_IMP THEN
  REWRITE_TAC[ABS_POS] THEN REWRITE_TAC[GSYM ADD1, FACT] THEN
  REWRITE_TAC[GSYM REAL_MUL, MATCH_MP REAL_INV_MUL (CONJ
   (REWRITE_RULE[GSYM REAL_INJ] (SPEC (--`n:num`--) NOT_SUC)) (fnz (--`n:num`--)))] THEN
  REWRITE_TAC[ABS_MUL, REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
  MP_TAC(SPEC (--`n:num`--) LESS_0) THEN REWRITE_TAC[GSYM REAL_LT] THEN
  DISCH_THEN(ASSUME_TAC o GSYM o MATCH_MP REAL_LT_IMP_NE) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LDIV THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM ABS_REFL, GSYM REAL_LE] ZERO_LESS_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&N |*| c`--) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
    REWRITE_TAC[REAL_LE] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    EXISTS_TAC (--`n:num`--) THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL]] end);

(*---------------------------------------------------------------------------*)
(* Show by the comparison test that sin and cos converge                     *)
(*---------------------------------------------------------------------------*)

val SIN_CONVERGES = prove_thm("SIN_CONVERGES",
  (--`!x. (\n. (^sin_ser) n |*| (x pow n)) sums sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[sin] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC (--`\n. (^exp_ser) n |*| (abs(x) pow n)`--) THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  EXISTS_TAC (--`0`--) THEN X_GEN_TAC (--`n:num`--) THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[ABS_MUL, POW_ABS] THENL
   [REWRITE_TAC[ABS_0, REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[ABS_POS],
    REWRITE_TAC[real_div, ABS_MUL, POW_M1, REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[ABS_REFL]] THEN
  MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, REAL_INV_POS] THEN
  REWRITE_TAC[REAL_LT, FACT_LESS]);

val COS_CONVERGES = prove_thm("COS_CONVERGES",
  (--`!x. (\n. (^cos_ser) n |*| (x pow n)) sums cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[cos] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC (--`\n. (^exp_ser) n |*| (abs(x) pow n)`--) THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  EXISTS_TAC (--`0`--) THEN X_GEN_TAC (--`n:num`--) THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[ABS_MUL, POW_ABS] THENL
   [REWRITE_TAC[real_div, ABS_MUL, POW_M1, REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[ABS_REFL],
    REWRITE_TAC[ABS_0, REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[ABS_POS]] THEN
  MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, REAL_INV_POS] THEN
  REWRITE_TAC[REAL_LT, FACT_LESS]);

(*---------------------------------------------------------------------------*)
(* Show what the formal derivatives of these series are                      *)
(*---------------------------------------------------------------------------*)

val EXP_FDIFF = prove_thm("EXP_FDIFF",
  (--`diffs ^exp_ser = ^exp_ser`--),
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV (--`n:num`--)) THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
  SUBGOAL_THEN (--`~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
    GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);

val SIN_FDIFF = prove_thm("SIN_FDIFF",
  (--`diffs ^sin_ser = ^cos_ser`--),
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV (--`n:num`--)) THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REWRITE_TAC[SUC_SUB1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
  SUBGOAL_THEN (--`~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);

val COS_FDIFF = prove_thm("COS_FDIFF",
  (--`diffs ^cos_ser = (\n. --((^sin_ser) n))`--),
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV (--`n:num`--)) THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO, REAL_NEG_0] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN BINOP_TAC THENL
   [POP_ASSUM(SUBST1_TAC o MATCH_MP EVEN_DIV2) THEN
    REWRITE_TAC[pow] THEN REWRITE_TAC[GSYM REAL_NEG_MINUS1],
    REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
    SUBGOAL_THEN (--`~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
     [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
      FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]]);

(*---------------------------------------------------------------------------*)
(* Now at last we can get the derivatives of exp, sin and cos                *)
(*---------------------------------------------------------------------------*)

val SIN_NEGLEMMA = prove_thm("SIN_NEGLEMMA",
  (--`!x. --(sin x) = suminf (\n. --((^sin_ser) n |*| (x pow n)))`--),
  GEN_TAC THEN MATCH_MP_TAC SUM_UNIQ THEN
  MP_TAC(MATCH_MP SER_NEG (SPEC (--`x:real`--) SIN_CONVERGES)) THEN
  BETA_TAC THEN DISCH_THEN ACCEPT_TAC);

val DIFF_EXP = prove_thm("DIFF_EXP",
  (--`!x. (exp diffl exp(x))(x)`--),
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS exp] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV)  [GSYM EXP_FDIFF] THEN
  CONV_TAC(LAND_CONV BETA_CONV) THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (--`abs(x) |+| &1`--) THEN
  REWRITE_TAC[EXP_FDIFF, MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`abs(x) |+| &1`--) THEN
  REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
  REWRITE_TAC[REAL_LT, num_CONV (--`1`--), LESS_0]);

val DIFF_SIN = prove_thm("DIFF_SIN",
  (--`!x. (sin diffl cos(x))(x)`--),
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS sin, cos] THEN
  ONCE_REWRITE_TAC[GSYM SIN_FDIFF] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (--`abs(x) |+| &1`--) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL SIN_CONVERGES)],
    REWRITE_TAC[SIN_FDIFF, MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)],
    REWRITE_TAC[SIN_FDIFF, COS_FDIFF] THEN BETA_TAC THEN
    MP_TAC(SPEC (--`abs(x) |+| &1`--) SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`abs(x) |+| &1`--) THEN
    REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT, num_CONV (--`1`--), LESS_0]]);

val DIFF_COS = prove_thm("DIFF_COS",
  (--`!x. (cos diffl --(sin(x)))(x)`--),
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS cos, SIN_NEGLEMMA] THEN
  ONCE_REWRITE_TAC[REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM(CONV_RULE(RAND_CONV BETA_CONV)
    (AP_THM COS_FDIFF (--`n:num`--)))] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (--`abs(x) |+| &1`--) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)],
    REWRITE_TAC[COS_FDIFF] THEN
    MP_TAC(SPEC (--`abs(x) |+| &1`--) SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    REWRITE_TAC[COS_FDIFF, DIFFS_NEG] THEN
    MP_TAC SIN_FDIFF THEN BETA_TAC THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
    MP_TAC(SPEC (--`abs(x) |+| &1`--) COS_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`abs(x) |+| &1`--) THEN
    REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT, num_CONV (--`1`--), LESS_0]]);

basic_diffs := !basic_diffs@[DIFF_EXP, DIFF_SIN, DIFF_COS];

(*---------------------------------------------------------------------------*)
(* Properties of the exponential function                                    *)
(*---------------------------------------------------------------------------*)

val EXP_0 = prove_thm("EXP_0",
  (--`exp(&0) = &1`--),
  REWRITE_TAC[exp] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC (--`1`--)) THEN
  REWRITE_TAC[num_CONV (--`1`--), sum] THEN
  REWRITE_TAC[ADD_CLAUSES, REAL_ADD_LID] THEN BETA_TAC THEN
  REWRITE_TAC[FACT, pow, REAL_MUL_RID, REAL_INV1] THEN
  REWRITE_TAC[SYM(num_CONV (--`1`--))] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[num_CONV (--`1`--), GSYM LESS_EQ] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES]);

val EXP_LE_X = prove_thm("EXP_LE_X",
  (--`!x. &0 |<=| x ==> (&1 |+| x) |<=| exp(x)`--),
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MP_TAC(SPECL [(--`\n. (^exp_ser) n |*| (x pow n)`--), (--`2`--)] SER_POS_LE) THEN
    REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
    REWRITE_TAC[GSYM exp] THEN BETA_TAC THEN
    W(C SUBGOAL_THEN (fn t =>REWRITE_TAC[t]) o
    funpow 2 (fst o dest_imp) o snd) THENL
     [GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_INV_POS THEN
        REWRITE_TAC[REAL_LT, FACT_LESS],
        MATCH_MP_TAC POW_POS THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_ASSUM ACCEPT_TAC],
      CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN REWRITE_TAC[sum] THEN
      BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES, FACT, pow, REAL_ADD_LID] THEN
      REWRITE_TAC[MULT_CLAUSES, REAL_INV1, REAL_MUL_LID, ADD_CLAUSES] THEN
      REWRITE_TAC[REAL_MUL_RID, SYM(num_CONV (--`1`--))]],
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXP_0, REAL_ADD_RID, REAL_LE_REFL]]);

val EXP_LT_1 = prove_thm("EXP_LT_1",
  (--`!x. &0 |<| x ==> &1 |<| exp(x)`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC (--`&1 |+| x`--) THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  MATCH_MP_TAC EXP_LE_X THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM ACCEPT_TAC);

val EXP_ADD_MUL = prove_thm("EXP_ADD_MUL",
  (--`!x y. exp(x |+| y) |*| exp(--x) = exp(y)`--),
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  SUBGOAL_THEN (--`exp(y) = (\x. exp(x |+| y) |*| exp(--x))(&0)`--) SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[REAL_ADD_LID, REAL_NEG_0] THEN
    REWRITE_TAC[EXP_0, REAL_MUL_RID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC (--`x:real`--) THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_0, REAL_MUL_RID, REAL_ADD_RID] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM]);

val EXP_NEG_MUL = prove_thm("EXP_NEG_MUL",
  (--`!x. exp(x) |*| exp(--x) = &1`--),
  GEN_TAC THEN MP_TAC(SPECL [(--`x:real`--), (--`&0`--)] EXP_ADD_MUL) THEN
  REWRITE_TAC[REAL_ADD_RID, EXP_0]);

val EXP_NEG_MUL2 = prove_thm("EXP_NEG_MUL2",
  (--`!x. exp(--x) |*| exp(x) = &1`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC EXP_NEG_MUL);

val EXP_NEG = prove_thm("EXP_NEG",
  (--`!x. exp(--x) = inv(exp(x))`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
  MATCH_ACCEPT_TAC EXP_NEG_MUL);

val EXP_ADD = prove_thm("EXP_ADD",
  (--`!x y. exp(x |+| y) = exp(x) |*| exp(y)`--),
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [(--`x:real`--), (--`y:real`--)] EXP_ADD_MUL) THEN
  DISCH_THEN(MP_TAC o C AP_THM (--`exp(x)`--) o AP_TERM (--`$|*|`--)) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] EXP_NEG_MUL, REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);

val EXP_POS_LE = prove_thm("EXP_POS_LE",
  (--`!x. &0 |<=| exp(x)`--),
  GEN_TAC THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [GSYM REAL_HALF_DOUBLE] THEN
  REWRITE_TAC[EXP_ADD] THEN MATCH_ACCEPT_TAC REAL_LE_SQUARE);

val EXP_NZ = prove_thm("EXP_NZ",
  (--`!x. ~(exp(x) = &0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`x:real`--) EXP_NEG_MUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC REAL_10);

val EXP_POS_LT = prove_thm("EXP_POS_LT",
  (--`!x. &0 |<| exp(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[EXP_POS_LE, EXP_NZ]);

val EXP_N = prove_thm("EXP_N",
  (--`!n x. exp(&n |*| x) = exp(x) pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, EXP_0, pow] THEN
  REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_ADD, EXP_ADD, REAL_RDISTRIB] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID]);

val EXP_SUB = prove_thm("EXP_SUB",
  (--`!x y. exp(x |-| y) = exp(x) / exp(y)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_sub, real_div, EXP_ADD, EXP_NEG]);

val EXP_MONO_IMP = prove_thm("EXP_MONO_IMP",
  (--`!x y. x |<| y ==> exp(x) |<| exp(y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
    MATCH_MP EXP_LT_1 o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  REWRITE_TAC[EXP_SUB] THEN
  SUBGOAL_THEN (--`&1 |<| exp(y) / exp(x) =
                 (&1 |*| exp(x)) |<| ((exp(y) / exp(x)) |*| exp(x))`--) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    MATCH_ACCEPT_TAC EXP_POS_LT,
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC, EXP_NEG_MUL2, GSYM EXP_NEG] THEN
    REWRITE_TAC[REAL_MUL_LID, REAL_MUL_RID]]);

val EXP_MONO_LT = prove_thm("EXP_MONO_LT",
  (--`!x y. exp(x) |<| exp(y) = x |<| y`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_LE_LT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    REWRITE_TAC[] THEN DISJ1_TAC THEN MATCH_MP_TAC EXP_MONO_IMP THEN
    POP_ASSUM ACCEPT_TAC,
    MATCH_ACCEPT_TAC EXP_MONO_IMP]);

val EXP_MONO_LE = prove_thm("EXP_MONO_LE",
  (--`!x y. exp(x) |<=| exp(y) = x |<=| y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[EXP_MONO_LT]);

val EXP_INJ = prove_thm("EXP_INJ",
  (--`!x y. (exp(x) = exp(y)) = (x = y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  REWRITE_TAC[EXP_MONO_LE]);

val EXP_TOTAL_LEMMA = prove_thm("EXP_TOTAL_LEMMA",
  (--`!y. &1 |<=| y ==> ?x. &0 |<=| x /\ x |<=| y |-| &1 /\ (exp(x) = y)`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IVT THEN
  ASM_REWRITE_TAC[EXP_0, REAL_LE_SUB_LADD, REAL_ADD_LID] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_LE]) THEN
    POP_ASSUM(MP_TAC o MATCH_MP EXP_LE_X) THEN REWRITE_TAC[REAL_SUB_ADD2],
    X_GEN_TAC (--`x:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`exp(x)`--) THEN
    MATCH_ACCEPT_TAC DIFF_EXP]);

val EXP_TOTAL = prove_thm("EXP_TOTAL",
  (--`!y. &0 |<| y ==> ?x. exp(x) = y`--),
  GEN_TAC THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPECL [(--`&1`--), (--`y:real`--)] REAL_LET_TOTAL) THENL
   [FIRST_ASSUM(X_CHOOSE_TAC (--`x:real`--) o MATCH_MP EXP_TOTAL_LEMMA) THEN
    EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
    MP_TAC(SPEC (--`y:real`--) REAL_INV_LT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(X_CHOOSE_TAC (--`x:real`--) o MATCH_MP EXP_TOTAL_LEMMA) THEN
    EXISTS_TAC (--`--x`--) THEN ASM_REWRITE_TAC[EXP_NEG] THEN
    MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Properties of the logarithmic function                                    *)
(*---------------------------------------------------------------------------*)

val ln = new_definition("ln",
  (--`ln x = @u. exp(u) = x`--));

val LN_EXP = prove_thm("LN_EXP",
  (--`!x. ln(exp x) = x`--),
  GEN_TAC THEN REWRITE_TAC[ln, EXP_INJ] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN MATCH_MP_TAC SELECT_AX THEN
  EXISTS_TAC (--`x:real`--) THEN REFL_TAC);

val EXP_LN = prove_thm("EXP_LN",
  (--`!x. (exp(ln x) = x) = &0 |<| x`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC EXP_POS_LT,
    DISCH_THEN(X_CHOOSE_THEN (--`y:real`--) MP_TAC o MATCH_MP EXP_TOTAL) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP_INJ, LN_EXP]]);

val LN_MUL = prove_thm("LN_MUL",
  (--`!x y. &0 |<| x /\ &0 |<| y ==> (ln(x |*| y) = ln(x) |+| ln(y))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM EXP_INJ] THEN
  REWRITE_TAC[EXP_ADD] THEN SUBGOAL_THEN (--`&0 |<| x |*| y`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[],
    EVERY_ASSUM(fn th => REWRITE_TAC[ONCE_REWRITE_RULE[GSYM EXP_LN] th])]);

val LN_INJ = prove_thm("LN_INJ",
  (--`!x y. &0 |<| x /\ &0 |<| y ==> ((ln(x) = ln(y)) = (x = y))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) 
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_INJ);

val LN_1 = prove_thm("LN_1",
  (--`ln(&1) = &0`--),
  ONCE_REWRITE_TAC[GSYM EXP_INJ] THEN
  REWRITE_TAC[EXP_0, EXP_LN, REAL_LT_01]);

val LN_INV = prove_thm("LN_INV",
  (--`!x. &0 |<| x ==> (ln(inv x) = --(ln x))`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  SUBGOAL_THEN (--`&0 |<| x /\ &0 |<| inv(x)`--) MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(fn th => REWRITE_TAC[GSYM(MATCH_MP LN_MUL th)]) THEN
    SUBGOAL_THEN (--`x |*| (inv x) = &1`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN
      POP_ASSUM(ACCEPT_TAC o MATCH_MP REAL_POS_NZ),
      REWRITE_TAC[LN_1]]]);

val LN_DIV = prove_thm("LN_DIV",
  (--`!x y. &0 |<| x /\ &0 |<| y ==> (ln(x / y) = ln(x) |-| ln(y))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`&0 |<| x /\ &0 |<| inv(y)`--) MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[real_div] THEN
    DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP LN_MUL th]) THEN
    REWRITE_TAC[MATCH_MP LN_INV (ASSUME (--`&0 |<| y`--))] THEN
    REWRITE_TAC[real_sub]]);

val LN_MONO_LT = prove_thm("LN_MONO_LT",
  (--`!x y. &0 |<| x /\ &0 |<| y ==> (ln(x) |<| ln(y) = x |<| y)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) 
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_MONO_LT);

val LN_MONO_LE = prove_thm("LN_MONO_LE",
  (--`!x y. &0 |<| x /\ &0 |<| y ==> (ln(x) |<=| ln(y) = x |<=| y)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) 
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_MONO_LE);

val LN_POW = prove_thm("LN_POW",
  (--`!n x. &0 |<| x ==> (ln(x pow n) = &n |*| ln(x))`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN (SUBST1_TAC o SYM) o MATCH_MP EXP_TOTAL) THEN
  REWRITE_TAC[GSYM EXP_N, LN_EXP]);

val LN_LT_X = prove_thm("LN_LT_X",
  (--`!x. &0 |<| x ==> ln(x) |<| x`--),
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`ln(x)`--) EXP_LE_X) THEN
  SUBGOAL_THEN (--`&0 |<=| ln(x)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC (--`x:real`--) EXP_LN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(&1 |+| ln(x)) |<=| ln(x)`--) MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--), ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`&0 |+| ln(x)`--) THEN
  REWRITE_TAC[REAL_LT_RADD, REAL_LT_01] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_LE_REFL]);

(*---------------------------------------------------------------------------*)
(* Some properties of roots (easier via logarithms)                          *)
(*---------------------------------------------------------------------------*)

val root = new_definition("root",
  (--`root(n) x = @u. (&0 |<| x ==> &0 |<| u) /\ (u pow n = x)`--));

val sqrt = new_definition("sqrt",
  (--`sqrt(x) = root(2) x`--));

val ROOT_LT_LEMMA = prove_thm("ROOT_LT_LEMMA",
  (--`!n x. &0 |<| x ==> (exp(ln(x) / &(SUC n)) pow (SUC n) = x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM EXP_N] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN (--`inv(&(SUC n)) |*| &(SUC n) = &1`--) SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ, NOT_SUC],
    ASM_REWRITE_TAC[REAL_MUL_RID, EXP_LN]]);

val ROOT_LN = prove_thm("ROOT_LN",
  (--`!n x. &0 |<| x ==> (root(SUC n) x = exp(ln(x) / &(SUC n)))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (--`y:real`--) THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    SUBGOAL_THEN (--`!z. &0 |<| y /\ &0 |<| exp(z)`--) MP_TAC THENL
     [ASM_REWRITE_TAC[EXP_POS_LT], ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN_ALL o SYM o MATCH_MP LN_INJ o SPEC_ALL) THEN
    DISCH_THEN(fn th => GEN_REWR_TAC I  [th]) THEN
    REWRITE_TAC[LN_EXP] THEN
    SUBGOAL_THEN (--`ln(y) |*| &(SUC n) = (ln(y pow(SUC n)) / &(SUC n)) |*| &(SUC n)`--)
    MP_TAC THENL
     [REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN (--`inv(&(SUC n)) |*| &(SUC n) = &1`--) SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ, NOT_SUC],
        REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC LN_POW THEN
        ASM_REWRITE_TAC[]],
      REWRITE_TAC[REAL_EQ_RMUL, REAL_INJ, NOT_SUC]],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXP_POS_LT] THEN
    MATCH_MP_TAC ROOT_LT_LEMMA THEN ASM_REWRITE_TAC[]]);

val ROOT_0 = prove_thm("ROOT_0",
  (--`!n. root(SUC n) (&0) = &0`--),
  GEN_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (--`y:real`--) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN EQ_TAC THENL
   [SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[pow] THENL
     [REWRITE_TAC[pow, REAL_MUL_RID],
      REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pow, REAL_MUL_LZERO]]);

val ROOT_POS_LT = prove_thm("ROOT_POS_LT",
  (--`!n x. &0 |<| x ==> &0 |<| root(SUC n) x`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ROOT_LN th]) THEN
  REWRITE_TAC[EXP_POS_LT]);

val ROOT_POS = prove_thm("ROOT_POS",
  (--`!n x. &0 |<=| x ==> &0 |<=| root(SUC n) x`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, ROOT_POS_LT] THEN
    POP_ASSUM ACCEPT_TAC,
    POP_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0, REAL_LE_REFL]]);

val ROOT_1 = prove_thm("ROOT_1",
  (--`!n. root(SUC n) (&1) = &1`--),
  GEN_TAC THEN REWRITE_TAC[MATCH_MP ROOT_LN REAL_LT_01] THEN
  REWRITE_TAC[LN_1, REAL_DIV_LZERO, EXP_0]);

val ROOT_POW_POS = prove_thm("ROOT_POW_POS",
  (--`!n x. &0 |<=| x ==> ((root(SUC n) x) pow (SUC n) = x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_ASSUM(fn th => REWRITE_TAC
     [MATCH_MP ROOT_LN th, MATCH_MP ROOT_LT_LEMMA th]),
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0] THEN
    MATCH_ACCEPT_TAC POW_0]);

val SQRT_0 = prove_thm("SQRT_0",
  (--`sqrt(&0) = &0`--),
  REWRITE_TAC[sqrt, num_CONV (--`2`--), ROOT_0]);

val SQRT_1 = prove_thm("SQRT_1",
  (--`sqrt(&1) = &1`--),
  REWRITE_TAC[sqrt, num_CONV (--`2`--), ROOT_1]);

val SQRT_POW2 = prove_thm("SQRT_POW2",
  (--`!x. (sqrt(x) pow 2 = x) = &0 |<=| x`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC REAL_LE_POW2,
    REWRITE_TAC[sqrt, num_CONV (--`2`--), ROOT_POW_POS]]);

val POW_ROOT_POS = prove_thm("POW_ROOT_POS",
  (--`!n x. &0 |<=| x ==> (root(SUC n)(x pow (SUC n)) = x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[root] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (--`y:real`--) THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME (--`&0 |<=| x`--))) THENL
     [DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
      FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_POS_LT th]) THEN
      DISCH_TAC THEN MATCH_MP_TAC POW_EQ THEN EXISTS_TAC (--`n:num`--) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
      REWRITE_TAC[POW_0, REAL_LT_REFL, POW_ZERO]],
    ASM_REWRITE_TAC[REAL_LT_LE] THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[POW_0]]);

val SQRT_EQ = prove_thm("SQRT_EQ",
  (--`!x y. (x pow 2 = y) /\ (&0 |<=| x) ==> (x = (sqrt(y)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`&0 |<=| y`--) ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[POW_2, REAL_LE_SQUARE],
    ALL_TAC] THEN
  MP_TAC(SPECL [(--`1`--), (--`y:real`--)] ROOT_POW_POS) THEN
  ASM_REWRITE_TAC[GSYM(num_CONV (--`2`--)), GSYM sqrt] THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [SYM th]) THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_SUB_0] THEN
  REWRITE_TAC[POW_2, GSYM REAL_DIFFSQ, REAL_ENTIRE] THEN
  REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (--`&0 |<=| sqrt(y)`--) ASSUME_TAC THENL
   [REWRITE_TAC[sqrt, num_CONV (--`2`--)] THEN MATCH_MP_TAC ROOT_POS THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`x = &0`--) SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a`--)] THEN
    PURE_REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC (--`sqrt(y) |+| x = &0`--) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`sqrt(y)`--) THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR],
    UNDISCH_TAC (--`&0 pow 2 = y`--) THEN REWRITE_TAC[POW_0, num_CONV (--`2`--)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SQRT_0]]);

(*---------------------------------------------------------------------------*)
(* Basic properties of the trig functions                                    *)
(*---------------------------------------------------------------------------*)

val SIN_0 = prove_thm("SIN_0",
  (--`sin(&0) = &0`--),
  REWRITE_TAC[sin] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC (--`0`--)) THEN REWRITE_TAC[ZERO_LESS_EQ] THEN
  BETA_TAC THEN
  REWRITE_TAC[sum] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC (--`n:num`--) THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  MP_TAC(SPEC (--`n:num`--) ODD_EXISTS) THEN ASM_REWRITE_TAC[ODD_EVEN] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO]);

val COS_0 = prove_thm("COS_0",
  (--`cos(&0) = &1`--),
  REWRITE_TAC[cos] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC (--`1`--)) THEN
  REWRITE_TAC[num_CONV (--`1`--), sum, ADD_CLAUSES] THEN BETA_TAC THEN
  REWRITE_TAC[EVEN, pow, FACT] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_MUL_RID] THEN
  SUBGOAL_THEN (--`0 DIV 2 = 0`--) SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC (--`0`--) THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES] THEN
    REWRITE_TAC[num_CONV (--`2`--), LESS_0],
    REWRITE_TAC[pow]] THEN
  SUBGOAL_THEN (--`&1 / &1 = &(SUC 0)`--) SUBST1_TAC THENL
   [REWRITE_TAC[SYM(num_CONV (--`1`--))] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    MATCH_ACCEPT_TAC REAL_10,
    DISCH_THEN MATCH_MP_TAC] THEN
  X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[GSYM LESS_EQ] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES]);

val SIN_CIRCLE = prove_thm("SIN_CIRCLE",
  (--`!x. (sin(x) pow 2) |+| (cos(x) pow 2) = &1`--),
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  SUBGOAL_THEN (--`&1 = (\x.(sin(x) pow 2) |+| (cos(x) pow 2))(&0)`--) SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0] THEN
    REWRITE_TAC[num_CONV (--`2`--), POW_0] THEN
    REWRITE_TAC[pow, POW_1] THEN REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC (--`x:real`--) THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_0] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC, REAL_MUL_RID] THEN
    AP_TERM_TAC THEN REWRITE_TAC[num_CONV (--`2`--), SUC_SUB1] THEN
    REWRITE_TAC[POW_1] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM]);

val SIN_BOUND = prove_thm("SIN_BOUND",
  (--`!x. abs(sin x) |<=| &1`--),
  GEN_TAC THEN GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a`--)] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o C CONJ(SPEC (--`cos(x)`--) REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LTE_ADD) THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`a |+| b |+| c = (a |+| c) |+| b`--)] THEN
  REWRITE_TAC[SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL]);

val SIN_BOUNDS = prove_thm("SIN_BOUNDS",
  (--`!x. --(&1) |<=| sin(x) /\ sin(x) |<=| &1`--),
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS, SIN_BOUND]);

val COS_BOUND = prove_thm("COS_BOUND",
  (--`!x. abs(cos x) |<=| &1`--),
  GEN_TAC THEN GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a`--)] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o CONJ(SPEC (--`sin(x)`--) REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD) THEN
  REWRITE_TAC[real_sub, REAL_ADD_ASSOC, SIN_CIRCLE,
    REAL_ADD_ASSOC, SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL]);

val COS_BOUNDS = prove_thm("COS_BOUNDS",
  (--`!x. --(&1) |<=| cos(x) /\ cos(x) |<=| &1`--),
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS, COS_BOUND]);

val SIN_COS_ADD = prove_thm("SIN_COS_ADD",
  (--`!x y. ((sin(x |+| y) |-| ((sin(x) |*| cos(y)) |+| (cos(x) |*| sin(y)))) pow 2) |+|
         ((cos(x |+| y) |-| ((cos(x) |*| cos(y)) |-| (sin(x) |*| sin(y)))) pow 2) = &0`--),
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o subst[((--`&0`--),(--`x:real`--))] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0] THEN
    REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LZERO, REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_SUB_RZERO, REAL_SUB_REFL] THEN
    REWRITE_TAC[num_CONV (--`2`--), POW_0, REAL_ADD_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO, GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN BINOP_TAC THENL
     [REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG, REAL_NEG_RMUL],
      REWRITE_TAC[GSYM REAL_NEG_RMUL, GSYM real_sub]]]);

val SIN_COS_NEG = prove_thm("SIN_COS_NEG",
  (--`!x. ((sin(--x) |+| (sin x)) pow 2) |+|
       ((cos(--x) |-| (cos x)) pow 2) = &0`--),
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o subst[((--`&0`--),(--`x:real`--))] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0, REAL_NEG_0] THEN
    REWRITE_TAC[REAL_ADD_LID, REAL_SUB_REFL] THEN
    REWRITE_TAC[num_CONV (--`2`--), POW_0, REAL_ADD_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_MUL_RID, real_sub, REAL_NEGNEG, GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_NEG_ADD, REAL_NEGNEG]]);

val SIN_ADD = prove_thm("SIN_ADD",
  (--`!x y. sin(x |+| y) = (sin(x) |*| cos(y)) |+| (cos(x) |*| sin(y))`--),
  REPEAT GEN_TAC THEN MP_TAC(SPECL [(--`x:real`--), (--`y:real`--)] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val COS_ADD = prove_thm("COS_ADD",
  (--`!x y. cos(x |+| y) = (cos(x) |*| cos(y)) |-| (sin(x) |*| sin(y))`--),
  REPEAT GEN_TAC THEN MP_TAC(SPECL [(--`x:real`--), (--`y:real`--)] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val SIN_NEG = prove_thm("SIN_NEG",
  (--`!x. sin(--x) = --(sin(x))`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_LNEG_UNIQ] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val COS_NEG = prove_thm("COS_NEG",
  (--`!x. cos(--x) = cos(x)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val SIN_DOUBLE = prove_thm("SIN_DOUBLE",
  (--`!x. sin(&2 |*| x) = &2 |*| sin(x) |*| cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, SIN_ADD] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);

val COS_DOUBLE = prove_thm("COS_DOUBLE",
  (--`!x. cos(&2 |*| x) = (cos(x) pow 2) |-| (sin(x) pow 2)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, COS_ADD, POW_2]);

(*---------------------------------------------------------------------------*)
(* Show that there's a least positive x with cos(x) = 0; hence define pi     *)
(*---------------------------------------------------------------------------*)

val SIN_PAIRED = prove_thm("SIN_PAIRED",
  (--`!x. (\n. (((--(&1)) pow n) / &(FACT((2 * n) + 1)))
         |*| (x pow ((2 * n) + 1))) sums (sin x)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM sin] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, EVEN_DOUBLE, REWRITE_RULE[ODD_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID, SUC_SUB1, MULT_DIV_2]);

val SIN_POS = prove_thm("SIN_POS",
  (--`!x. &0 |<| x /\ x |<| &2 ==> &0 |<| sin(x)`--),
  GEN_TAC THEN STRIP_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN
  REWRITE_TAC[SYM(MATCH_MP SUM_UNIQ (SPEC (--`x:real`--) SIN_PAIRED))] THEN
  REWRITE_TAC[SUM_2] THEN BETA_TAC THEN REWRITE_TAC[GSYM ADD1] THEN
  REWRITE_TAC[pow, GSYM REAL_NEG_MINUS1, POW_MINUS1] THEN
  REWRITE_TAC[real_div, GSYM REAL_NEG_LMUL, GSYM real_sub] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  W(C SUBGOAL_THEN SUBST1_TAC o curry mk_eq (--`&0`--) o curry mk_comb (--`sum(0,0)`--) o
  funpow 2 rand o snd) THENL [REWRITE_TAC[sum], ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC (--`n:num`--) THEN DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, MULT_CLAUSES] THEN
  REWRITE_TAC[num_CONV (--`2`--), ADD_CLAUSES, pow, FACT, GSYM REAL_MUL] THEN
  REWRITE_TAC[SYM(num_CONV (--`2`--))] THEN
  REWRITE_TAC[num_CONV (--`1`--), ADD_CLAUSES, pow, FACT, GSYM REAL_MUL] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN ONCE_REWRITE_TAC[GSYM pow] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC, MATCH_MP_TAC POW_POS_LT THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC, GSYM POW_2] THEN
  SUBGOAL_THEN (--`!n. &0 |<| &(SUC n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, LESS_0], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. &0 |<| &(FACT n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(SUC n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`a |*| b |*| c |*| d |*| e = (a |*| b |*| e) |*| (c |*| d)`--)] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC, MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  IMP_SUBST_TAC ((CONV_RULE(RAND_CONV SYM_CONV) o SPEC_ALL) REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[REAL_ENTIRE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
  REWRITE_TAC[POW_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC,
    MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT CONJ_TAC] THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [W(curry op THEN (MATCH_MP_TAC REAL_LT_TRANS) o EXISTS_TAC o
      curry mk_comb (--`&`--) o funpow 3 rand o snd) THEN
    REWRITE_TAC[REAL_LT, LESS_SUC_REFL], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`&2`--) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV num_CONV) THEN
  REWRITE_TAC[REAL_LE, LESS_EQ_MONO, ZERO_LESS_EQ]);

val COS_PAIRED = prove_thm("COS_PAIRED",
  (--`!x. (\n. (((--(&1)) pow n) / &(FACT(2 * n)))
         |*| (x pow (2 * n))) sums (cos x)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) COS_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM cos] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, EVEN_DOUBLE, REWRITE_RULE[ODD_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID, MULT_DIV_2]);

val COS_2 = prove_thm("COS_2",
  (--`cos(&2) |<| &0`--),
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MP_TAC(SPEC (--`&2`--) COS_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN BETA_TAC THEN
  DISCH_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC (--`sum(0,3) (\n. --((((--(&1)) pow n) / &(FACT(2 * n)))
                |*| (&2 pow (2 * n))))`--) THEN CONJ_TAC THENL
   [REWRITE_TAC[num_CONV (--`3`--), sum, SUM_2] THEN BETA_TAC THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, pow, FACT] THEN
    REWRITE_TAC[REAL_MUL_RID, POW_1, POW_2, GSYM REAL_NEG_RMUL] THEN
    IMP_SUBST_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_NEGNEG, REAL_10] THEN
    REDUCE_TAC THEN REWRITE_TAC[num_CONV (--`4`--), num_CONV (--`3`--), FACT, pow] THEN
    REWRITE_TAC[SYM(num_CONV (--`4`--)), SYM(num_CONV (--`3`--))] THEN
    REWRITE_TAC[num_CONV (--`2`--), num_CONV (--`1`--), FACT, pow] THEN
    REWRITE_TAC[SYM(num_CONV (--`1`--)), SYM(num_CONV (--`2`--))] THEN
    REWRITE_TAC[REAL_MUL] THEN REDUCE_TAC THEN
    REWRITE_TAC[real_div, REAL_NEG_LMUL, REAL_NEGNEG, REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, REAL_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_LT] THEN
    SUBGOAL_THEN (--`inv(&2) |*| &4 = &1 |+| &1`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC (--`&2`--) THEN
      REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC THEN
      REWRITE_TAC[REAL_ADD, REAL_MUL] THEN REDUCE_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN (--`&2 |*| inv(&2) = &1`--) SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC,
      REWRITE_TAC[REAL_MUL_LID, REAL_ADD_ASSOC] THEN
      REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LT_1 THEN REWRITE_TAC[REAL_LE, REAL_LT] THEN
      REDUCE_TAC], ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT_PAIR THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC (--`d:num`--) THEN BETA_TAC THEN
  REWRITE_TAC[POW_ADD, POW_MINUS1, REAL_MUL_RID] THEN
  REWRITE_TAC[num_CONV (--`3`--), pow] THEN REWRITE_TAC[SYM(num_CONV (--`3`--))] THEN
  REWRITE_TAC[POW_2, POW_1] THEN
  REWRITE_TAC[GSYM REAL_NEG_MINUS1, REAL_NEGNEG] THEN
  REWRITE_TAC[real_div, GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_NEGNEG] THEN
  REWRITE_TAC[GSYM real_sub, REAL_SUB_LT] THEN
  REWRITE_TAC[GSYM ADD1, ADD_CLAUSES, MULT_CLAUSES] THEN
  REWRITE_TAC[POW_ADD, REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[num_CONV (--`2`--), MULT_CLAUSES] THEN
    REWRITE_TAC[num_CONV (--`3`--), ADD_CLAUSES] THEN
    MATCH_MP_TAC POW_POS_LT THEN REWRITE_TAC[REAL_LT] THEN
    REDUCE_TAC] THEN
  REWRITE_TAC[num_CONV (--`2`--), ADD_CLAUSES, FACT] THEN
  REWRITE_TAC[SYM(num_CONV (--`2`--))] THEN
  REWRITE_TAC[num_CONV (--`1`--), ADD_CLAUSES, FACT] THEN
  REWRITE_TAC[SYM(num_CONV (--`1`--))] THEN
  SUBGOAL_THEN (--`!n. &0 |<| &(SUC n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, LESS_0], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. &0 |<| &(FACT n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(SUC n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`a |*| b |*| c |*| d = (a |*| b |*| d) |*| c`--)] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC[REAL_LT, FACT_LESS]] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  IMP_SUBST_TAC ((CONV_RULE(RAND_CONV SYM_CONV) o SPEC_ALL) REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
  REWRITE_TAC[POW_2, REAL_MUL, REAL_LE, REAL_LT] THEN REDUCE_TAC THEN
  REWRITE_TAC[num_CONV (--`4`--), num_CONV (--`3`--), MULT_CLAUSES, ADD_CLAUSES] THEN
  REWRITE_TAC[LESS_MONO_EQ] THEN
  REWRITE_TAC[num_CONV (--`2`--), ADD_CLAUSES, MULT_CLAUSES] THEN
  REWRITE_TAC[num_CONV (--`1`--), LESS_MONO_EQ, LESS_0]);

val COS_ISZERO = prove_thm("COS_ISZERO",
  (--`?!x. &0 |<=| x /\ x |<=| &2 /\ (cos x = &0)`--),
  REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN BETA_TAC THEN
  W(C SUBGOAL_THEN ASSUME_TAC o hd o conjuncts o snd) THENL
   [MATCH_MP_TAC IVT2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ACCEPT_TAC COS_2,
      REWRITE_TAC[COS_0, REAL_LE_01],
      X_GEN_TAC (--`x:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`--(sin x)`--) THEN
      REWRITE_TAC[DIFF_COS]],
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN
    GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a`--)] THEN
    PURE_REWRITE_TAC[NOT_IMP] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LT_TOTAL) THEN
    SUBGOAL_THEN (--`(!x. cos differentiable x) /\
                  (!x. cos contl x)`--) STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_TAC THENL
       [REWRITE_TAC[differentiable], MATCH_MP_TAC DIFF_CONT] THEN
      EXISTS_TAC (--`--(sin x)`--) THEN REWRITE_TAC[DIFF_COS], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [(--`cos`--), (--`x1:real`--), (--`x2:real`--)] ROLLE),
      MP_TAC(SPECL [(--`cos`--), (--`x2:real`--), (--`x1:real`--)] ROLLE)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o CONJ(SPEC (--`x:real`--) DIFF_COS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
    REWRITE_TAC[REAL_NEG_EQ0] THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x1:real`--) THEN
        ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x2:real`--) THEN
        ASM_REWRITE_TAC[]],
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x2:real`--) THEN
        ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x1:real`--) THEN
        ASM_REWRITE_TAC[]]]]);

val pi = new_definition("pi",
  (--`pi = &2 |*| @x. &0 |<=| x /\ x |<=| &2 /\ (cos x = &0)`--));

(*---------------------------------------------------------------------------*)
(* Periodicity and related properties of the trig functions                  *)
(*---------------------------------------------------------------------------*)

val PI2 = prove_thm("PI2",
  (--`pi / &2 = @x. &0 |<=| x /\ x |<=| &2 /\ (cos(x) = &0)`--),
  REWRITE_TAC[pi, real_div] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`(a |*| b) |*| c = (c |*| a) |*| b`--)] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ] THEN
  REDUCE_TAC THEN REWRITE_TAC[REAL_MUL_LID]);

val COS_PI2 = prove_thm("COS_PI2",
  (--`cos(pi / &2) = &0`--),
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val PI2_BOUNDS = prove_thm("PI2_BOUNDS",
  (--`&0 |<| (pi / &2) /\ (pi / &2) |<| &2`--),
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MP_TAC COS_0 THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM REAL_10],
    DISCH_TAC THEN MP_TAC COS_PI2 THEN FIRST_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_ACCEPT_TAC COS_2]);

val PI_POS = prove_thm("PI_POS",
  (--`&0 |<| pi`--),
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD THEN REWRITE_TAC[PI2_BOUNDS]);

val SIN_PI2 = prove_thm("SIN_PI2",
  (--`sin(pi / &2) = &1`--),
  MP_TAC(SPEC (--`pi / &2`--) SIN_CIRCLE) THEN
  REWRITE_TAC[COS_PI2, POW_2, REAL_MUL_LZERO, REAL_ADD_RID] THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [GSYM REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  REWRITE_TAC[GSYM REAL_DIFFSQ, REAL_ENTIRE] THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN(MP_TAC o AP_TERM (--`--`--)) THEN
  REWRITE_TAC[REAL_NEGNEG] THEN DISCH_TAC THEN
  MP_TAC REAL_LT_01 THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_GT THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MATCH_MP_TAC SIN_POS THEN
  REWRITE_TAC[PI2_BOUNDS]);

val COS_PI = prove_thm("COS_PI",
  (--`cos(pi) = --(&1)`--),
  MP_TAC(SPECL [(--`pi / &2`--), (--`pi / &2`--)] COS_ADD) THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO, REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_SUB_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC);

val SIN_PI = prove_thm("SIN_PI",
  (--`sin(pi) = &0`--),
  MP_TAC(SPECL [(--`pi / &2`--), (--`pi / &2`--)] SIN_ADD) THEN
  REWRITE_TAC[COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_ADD_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_DOUBLE] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC);

val SIN_COS = prove_thm("SIN_COS",
  (--`!x. sin(x) = cos((pi / &2) |-| x)`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, COS_ADD] THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LID] THEN
  REWRITE_TAC[SIN_NEG, REAL_NEGNEG]);

val COS_SIN = prove_thm("COS_SIN",
  (--`!x. cos(x) = sin((pi / &2) |-| x)`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, SIN_ADD] THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_ADD_RID] THEN
  REWRITE_TAC[COS_NEG]);

val SIN_PERIODIC_PI = prove_thm("SIN_PERIODIC_PI",
  (--`!x. sin(x |+| pi) = --(sin(x))`--),
  GEN_TAC THEN REWRITE_TAC[SIN_ADD, SIN_PI, COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO, REAL_ADD_RID, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);

val COS_PERIODIC_PI = prove_thm("COS_PERIODIC_PI",
  (--`!x. cos(x |+| pi) = --(cos(x))`--),
  GEN_TAC THEN REWRITE_TAC[COS_ADD, SIN_PI, COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO, REAL_SUB_RZERO, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);

val SIN_PERIODIC = prove_thm("SIN_PERIODIC",
  (--`!x. sin(x |+| (&2 |*| pi)) = sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
  REWRITE_TAC[SIN_PERIODIC_PI, REAL_NEGNEG]);

val COS_PERIODIC = prove_thm("COS_PERIODIC",
  (--`!x. cos(x |+| (&2 |*| pi)) = cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
  REWRITE_TAC[COS_PERIODIC_PI, REAL_NEGNEG]);

val COS_NPI = prove_thm("COS_NPI",
  (--`!n. cos(&n |*| pi) = --(&1) pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, COS_0, pow] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, COS_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[COS_PI] THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);

val SIN_NPI = prove_thm("SIN_NPI",
  (--`!n. sin(&n |*| pi) = &0`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, SIN_0, pow] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, SIN_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_ADD_RID] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO]);

val SIN_POS_PI2 = prove_thm("SIN_POS_PI2",
  (--`!x. &0 |<| x /\ x |<| pi / &2 ==> &0 |<| sin(x)`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIN_POS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC (--`pi / &2`--) THEN ASM_REWRITE_TAC[PI2_BOUNDS]);

val COS_POS_PI2 = prove_thm("COS_POS_PI2",
  (--`!x. &0 |<| x /\ x |<| pi / &2 ==> &0 |<| cos(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`cos`--), (--`&0`--), (--`x:real`--), (--`&0`--)] IVT2) THEN
  ASM_REWRITE_TAC[COS_0, REAL_LE_01, NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    X_GEN_TAC (--`z:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`--(sin z)`--) THEN
    REWRITE_TAC[DIFF_COS],
    DISCH_THEN(X_CHOOSE_TAC (--`z:real`--)) THEN
    MP_TAC(CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV COS_ISZERO)) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`z:real`--), (--`pi / &2`--)]) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`pi / &2`--) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC,
      ALL_TAC,
      ALL_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`x |<| pi / &2`--) THEN
      ASM_REWRITE_TAC[REAL_NOT_LT]] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[PI2_BOUNDS]]);

val COS_POS_PI = prove_thm("COS_POS_PI",
  (--`!x. --(pi / &2) |<| x /\ x |<| pi / &2 ==> &0 |<| cos(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (SPECL [(--`x:real`--), (--`&0`--)] REAL_LT_TOTAL) THENL
   [ASM_REWRITE_TAC[COS_0, REAL_LT_01],
    ONCE_REWRITE_TAC[GSYM COS_NEG] THEN MATCH_MP_TAC COS_POS_PI2 THEN
    ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG],
    MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[]]);

val SIN_POS_PI = prove_thm("SIN_POS_PI",
  (--`!x. &0 |<| x /\ x |<| pi ==> &0 |<| sin(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SIN_COS] THEN ONCE_REWRITE_TAC[GSYM COS_NEG] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  MATCH_MP_TAC COS_POS_PI THEN
  REWRITE_TAC[REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
  ASM_REWRITE_TAC[REAL_HALF_DOUBLE, REAL_ADD_LINV]);

val COS_POS_PI2_LE = prove_thm("COS_POS_PI2_LE",
  (--`!x. &0 |<=| x /\ x |<=| (pi / &2) ==> &0 |<=| cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[COS_PI2] THEN
  TRY(DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI2 THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SUBST1_TAC(SYM(ASSUME (--`&0 = x`--))) THEN
  REWRITE_TAC[COS_0, REAL_LT_01]);

val COS_POS_PI_LE = prove_thm("COS_POS_PI_LE",
  (--`!x. --(pi / &2) |<=| x /\ x |<=| (pi / &2) ==> &0 |<=| cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[COS_PI2] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[COS_NEG, COS_PI2, REAL_LT_01]]);

val SIN_POS_PI2_LE = prove_thm("SIN_POS_PI2_LE",
  (--`!x. &0 |<=| x /\ x |<=| (pi / &2) ==> &0 |<=| sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[SIN_PI2, REAL_LT_01] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC SIN_POS_PI2 THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SIN_0],
    MP_TAC PI2_BOUNDS THEN ASM_REWRITE_TAC[REAL_LT_REFL]]);

val SIN_POS_PI_LE = prove_thm("SIN_POS_PI_LE",
  (--`!x. &0 |<=| x /\ x |<=| pi ==> &0 |<=| sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[SIN_PI] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SIN_0]]);

val COS_TOTAL = prove_thm("COS_TOTAL",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==> ?!x. &0 |<=| x /\ x |<=| pi /\ (cos(x) = y)`--),
  GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC IVT2 THEN ASM_REWRITE_TAC[COS_0, COS_PI] THEN
    REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE PI_POS] THEN
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`--(sin x)`--) THEN
    REWRITE_TAC[DIFF_COS],
    MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LT_TOTAL) THENL
     [FIRST_ASSUM ACCEPT_TAC,
      MP_TAC(SPECL [(--`cos`--), (--`x1:real`--), (--`x2:real`--)] ROLLE),
      MP_TAC(SPECL [(--`cos`--), (--`x2:real`--), (--`x1:real`--)] ROLLE)]] THEN
  ASM_REWRITE_TAC[] THEN
  (W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2
                    (fst o dest_imp) o snd) THENL
    [CONJ_TAC THEN X_GEN_TAC (--`x:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
     TRY(MATCH_MP_TAC DIFF_CONT) THEN REWRITE_TAC[differentiable] THEN
     EXISTS_TAC (--`--(sin x)`--) THEN REWRITE_TAC[DIFF_COS], ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC (--`(cos diffl &0)(x)`--) THEN
  DISCH_THEN(MP_TAC o CONJ (SPEC (--`x:real`--) DIFF_COS)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
  REWRITE_TAC[REAL_NEG_EQ0] THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`x:real`--) SIN_POS_PI) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x1:real`--),
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x2:real`--),
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x2:real`--),
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x1:real`--)] THEN
  ASM_REWRITE_TAC[]);

val SIN_TOTAL = prove_thm("SIN_TOTAL",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==>
        ?!x.  --(pi / &2) |<=| x /\ x |<=| pi / &2 /\ (sin(x) = y)`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`!x. --(pi / &2) |<=| x /\ x |<=| pi / &2 /\ (sin(x) = y) =
    &0 |<=| (x |+| pi / &2) /\ (x |+| pi / &2) |<=| pi /\ (cos(x |+| pi / &2) = --y)`--)
  (fn th => REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[COS_ADD, SIN_PI2, COS_PI2] THEN
    REWRITE_TAC[REAL_MUL_RZERO, REAL_MUL_RZERO, REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_LZERO] THEN
    REWRITE_TAC[GSYM REAL_LE_SUB_RADD, GSYM REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_EQ_NEG] THEN AP_THM_TAC THEN
    REPEAT AP_TERM_TAC THEN
    GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [GSYM REAL_HALF_DOUBLE] THEN
    REWRITE_TAC[REAL_ADD_SUB], ALL_TAC] THEN
  MP_TAC(SPEC (--`--y`--) COS_TOTAL) THEN ASM_REWRITE_TAC[REAL_LE_NEG] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_LE_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC (--`x:real`--) o CONJUNCT1) THEN
    EXISTS_TAC (--`x |-| pi / &2`--) THEN ASM_REWRITE_TAC[REAL_SUB_ADD],
    POP_ASSUM(K ALL_TAC) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[REAL_EQ_RADD]]);

val COS_ZERO_LEMMA = prove_thm("COS_ZERO_LEMMA",
  (--`!x. &0 |<=| x /\ (cos(x) = &0) ==>
      ?n. ~EVEN n /\ (x = &n |*| (pi / &2))`--),
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC (--`x:real`--) (MATCH_MP REAL_ARCH_LEAST PI_POS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN (--`&0 |<=| x |-| &n |*| pi /\ (x |-| &n |*| pi) |<=| pi /\
                (cos(x |-| &n |*| pi) = &0)`--) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_LE_SUB_RADD] THEN
    REWRITE_TAC[real_sub, COS_ADD, SIN_NEG, COS_NEG, SIN_NPI, COS_NPI] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_NEG_RMUL, REAL_NEGNEG, REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN UNDISCH_TAC (--`x |<| &(SUC n) |*| pi`--) THEN
    REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID],
    MP_TAC(SPEC (--`&0`--) COS_TOTAL) THEN
    REWRITE_TAC[REAL_LE_01, REAL_NEG_LE0] THEN
    DISCH_THEN(MP_TAC o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`x |-| &n |*| pi`--), (--`pi / &2`--)] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MP_TAC PI2_BOUNDS THEN
      REWRITE_TAC[REAL_LT_HALF1, REAL_LT_HALF2] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD] THEN DISCH_TAC THEN
    EXISTS_TAC (--`SUC(2 * n)`--) THEN REWRITE_TAC[EVEN_ODD, ODD_DOUBLE] THEN
    REWRITE_TAC[ADD1, GSYM REAL_ADD, GSYM REAL_MUL] THEN
    REWRITE_TAC[REAL_RDISTRIB, REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC]);

val SIN_ZERO_LEMMA = prove_thm("SIN_ZERO_LEMMA",
  (--`!x. &0 |<=| x /\ (sin(x) = &0) ==>
        ?n. EVEN n /\ (x = &n |*| (pi / &2))`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`x |+| pi / &2`--) COS_ZERO_LEMMA) THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[PI2_BOUNDS],
      ASM_REWRITE_TAC[COS_ADD, COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
      MATCH_ACCEPT_TAC REAL_SUB_REFL],
    DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC (--`n:num`--) ODD_EXISTS) THEN ASM_REWRITE_TAC[ODD_EVEN] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST_ALL_TAC) THEN
  EXISTS_TAC (--`2 * m`--) THEN REWRITE_TAC[EVEN_DOUBLE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_EQ_SUB_LADD]) THEN
  FIRST_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_SUB]);

val COS_ZERO = prove_thm("COS_ZERO",
  (--`!x. (cos(x) = &0) = (?n. ~EVEN n /\ (x = &n |*| (pi / &2))) \/
                       (?n. ~EVEN n /\ (x = --(&n |*| (pi / &2))))`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [(--`&0`--), (--`x:real`--)] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[],
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[COS_NEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
      ASM_REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0]],
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC (--`n:num`--))) THEN
    ASM_REWRITE_TAC[COS_NEG] THEN MP_TAC(SPEC (--`n:num`--) ODD_EXISTS) THEN
    ASM_REWRITE_TAC[ODD_EVEN] THEN DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC) THEN
    REWRITE_TAC[ADD1] THEN SPEC_TAC((--`m:num`--),(--`m:num`--)) THEN INDUCT_TAC THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, REAL_MUL_LID, COS_PI2] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[GSYM REAL_ADD] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN REWRITE_TAC[COS_ADD] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE, REAL_HALF_DOUBLE] THEN
    ASM_REWRITE_TAC[COS_PI, SIN_PI, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO]]);

val SIN_ZERO = prove_thm("SIN_ZERO",
  (--`!x. (sin(x) = &0) = (?n. EVEN n /\ (x = &n |*| (pi / &2))) \/
                       (?n. EVEN n /\ (x = --(&n |*| (pi / &2))))`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [(--`&0`--), (--`x:real`--)] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC SIN_ZERO_LEMMA THEN ASM_REWRITE_TAC[],
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC SIN_ZERO_LEMMA THEN
      ASM_REWRITE_TAC[SIN_NEG, REAL_NEG_0, REAL_NEG_GE0]],
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC (--`n:num`--))) THEN
    ASM_REWRITE_TAC[SIN_NEG, REAL_NEG_EQ0] THEN
    MP_TAC(SPEC (--`n:num`--) EVEN_EXISTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC) THEN
    REWRITE_TAC[GSYM REAL_MUL] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      (--`(a |*| b) |*| c = b |*| (a |*| c)`--)] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE, REAL_HALF_DOUBLE, SIN_NPI]]);

(*---------------------------------------------------------------------------*)
(* Tangent                                                                   *)
(*---------------------------------------------------------------------------*)

val tan = new_definition("tan",
  (--`tan(x) = sin(x) / cos(x)`--));

val TAN_0 = prove_thm("TAN_0",
  (--`tan(&0) = &0`--),
  REWRITE_TAC[tan, SIN_0, REAL_DIV_LZERO]);

val TAN_PI = prove_thm("TAN_PI",
  (--`tan(pi) = &0`--),
  REWRITE_TAC[tan, SIN_PI, REAL_DIV_LZERO]);

val TAN_NPI = prove_thm("TAN_NPI",
  (--`!n. tan(&n |*| pi) = &0`--),
  GEN_TAC THEN REWRITE_TAC[tan, SIN_NPI, REAL_DIV_LZERO]);

val TAN_NEG = prove_thm("TAN_NEG",
  (--`!x. tan(--x) = --(tan x)`--),
  GEN_TAC THEN REWRITE_TAC[tan, SIN_NEG, COS_NEG] THEN
  REWRITE_TAC[real_div, REAL_NEG_LMUL]);

val TAN_PERIODIC = prove_thm("TAN_PERIODIC",
  (--`!x. tan(x |+| &2 |*| pi) = tan(x)`--),
  GEN_TAC THEN REWRITE_TAC[tan, SIN_PERIODIC, COS_PERIODIC]);

val TAN_ADD = prove_thm("TAN_ADD",
  (--`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x |+| y) = &0) ==>
           (tan(x |+| y) = (tan(x) |+| tan(y)) / (&1 |-| tan(x) |*| tan(y)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tan] THEN
  MP_TAC(SPECL [(--`cos(x) |*| cos(y)`--),
                (--`&1 |-| (sin(x) / cos(x)) |*| (sin(y) / cos(y))`--)]
         REAL_DIV_MUL2) THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$|*| (cos(x) |*| cos(y))`--)) THEN
    REWRITE_TAC[real_div, REAL_SUB_LDISTRIB, GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_RID, REAL_MUL_RZERO] THEN
    UNDISCH_TAC (--`~(cos(x |+| y) = &0)`--) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[COS_ADD] THEN AP_TERM_TAC,
    DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fn th => ONCE_REWRITE_TAC[th]) THEN BINOP_TAC THENL
     [REWRITE_TAC[real_div, REAL_LDISTRIB, GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[SIN_ADD] THEN BINOP_TAC THENL
       [ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
          (--`a |*| b |*| c |*| d = (d |*| a) |*| (c |*| b)`--)] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID],
        ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
          (--`a |*| b |*| c |*| d = (d |*| b) |*| (a |*| c)`--)] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID]],
      REWRITE_TAC[COS_ADD, REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
      AP_TERM_TAC THEN REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC]]] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`a |*| b |*| c |*| d |*| e |*| f = (f |*| b) |*| (d |*| a) |*| (c |*| e)`--)] THEN
  REPEAT(IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

val TAN_DOUBLE = prove_thm("TAN_DOUBLE",
  (--`!x. ~(cos(x) = &0) /\ ~(cos(&2 |*| x) = &0) ==>
            (tan(&2 |*| x) = (&2 |*| tan(x)) / (&1 |-| (tan(x) pow 2)))`--),
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [(--`x:real`--), (--`x:real`--)] TAN_ADD) THEN
  ASM_REWRITE_TAC[REAL_DOUBLE, POW_2]);

val TAN_POS_PI2 = prove_thm("TAN_POS_PI2",
  (--`!x. &0 |<| x /\ x |<| pi / &2 ==> &0 |<| tan(x)`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan, real_div] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI2,
    MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC COS_POS_PI2] THEN
  ASM_REWRITE_TAC[]);

val DIFF_TAN = prove_thm("DIFF_TAN",
  (--`!x. ~(cos(x) = &0) ==> (tan diffl inv(cos(x) pow 2))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(DIFF_CONV (--`\x. sin(x) / cos(x)`--)) THEN
  DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM tan, GSYM REAL_NEG_LMUL, REAL_NEGNEG, real_sub] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM POW_2, SIN_CIRCLE, GSYM REAL_INV_1OVER]);


val TAN_TOTAL_LEMMA = prove_thm("TAN_TOTAL_LEMMA",
  (--`!y. &0 |<| y ==> ?x. &0 |<| x /\ x |<| pi / &2 /\ y |<| tan(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`((\x. cos(x) / sin(x)) -> &0)(pi / &2)`--)
  MP_TAC THENL
   [SUBST1_TAC(SYM(SPEC (--`&1`--) REAL_DIV_LZERO)) THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC LIM_DIV THEN
    REWRITE_TAC[REAL_10] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    SUBST1_TAC(SYM COS_PI2) THEN SUBST1_TAC(SYM SIN_PI2) THEN
    REWRITE_TAC[GSYM CONTL_LIM] THEN CONJ_TAC THEN MATCH_MP_TAC DIFF_CONT THENL
     [EXISTS_TAC (--`--(sin(pi / &2))`--),
      EXISTS_TAC (--`cos(pi / &2)`--)] THEN
    REWRITE_TAC[DIFF_SIN, DIFF_COS], ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN DISCH_THEN(MP_TAC o SPEC (--`inv(y)`--)) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_POS th]) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [(--`d:real`--), (--`pi / &2`--)] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[PI2_BOUNDS] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`(pi / &2) |-| e`--) THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_sub, GSYM REAL_NOT_LE, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC (--`(pi / &2) |-| e`--)) THEN
  REWRITE_TAC[REAL_SUB_SUB, ABS_NEG] THEN
  SUBGOAL_THEN (--`abs(e) = e`--) (fn th => ASM_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  SUBGOAL_THEN (--`&0 |<| cos((pi / &2) |-| e) / sin((pi / &2) |-| e)`--)
  MP_TAC THENL
   [ONCE_REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC COS_POS_PI2,
      MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC SIN_POS_PI2] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE], ALL_TAC] THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC(MATCH_MP REAL_POS_NZ th)) THEN
  REWRITE_TAC[ABS_NZ, TAUT_CONV (--`a ==> b ==> c = a /\ b ==> c`--)] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_INV) THEN REWRITE_TAC[tan] THEN
  MATCH_MP_TAC (TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN BINOP_TAC THENL
   [MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  MP_TAC(ASSUME(--`&0 |<| cos((pi / &2) |-| e) / sin((pi / &2) |-| e)`--)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  REWRITE_TAC[GSYM ABS_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM, GSYM REAL_ENTIRE, GSYM real_div] THEN
    MATCH_MP_TAC REAL_POS_NZ THEN FIRST_ASSUM ACCEPT_TAC,
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS_PI2 THEN REWRITE_TAC[REAL_SUB_LT, GSYM real_div] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE]]);

val TAN_TOTAL_POS = prove_thm("TAN_TOTAL_POS",
  (--`!y. &0 |<=| y ==> ?x. &0 |<=| x /\ x |<| pi / &2 /\ (tan(x) = y)`--),
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP TAN_TOTAL_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [(--`tan`--), (--`&0`--), (--`x:real`--), (--`y:real`--)] IVT) THEN
    W(C SUBGOAL_THEN (fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) o
         funpow 2 (fst o dest_imp) o snd) THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN
      ASM_REWRITE_TAC[TAN_0] THEN X_GEN_TAC (--`z:real`--) THEN STRIP_TAC THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`inv(cos(z) pow 2)`--) THEN
      MATCH_MP_TAC DIFF_TAN THEN UNDISCH_TAC (--`&0 |<=| z`--) THEN
      REWRITE_TAC[REAL_LE_LT] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
        MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
        ASM_REWRITE_TAC[],
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[COS_0, REAL_10]],
      DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (--`z:real`--) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[]],
    POP_ASSUM(SUBST1_TAC o SYM) THEN EXISTS_TAC (--`&0`--) THEN
    REWRITE_TAC[TAN_0, REAL_LE_REFL, PI2_BOUNDS]]);

val TAN_TOTAL = prove_thm("TAN_TOTAL",
  (--`!y. ?!x. --(pi / &2) |<| x /\ x |<| (pi / &2) /\ (tan(x) = y)`--),
  GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [DISJ_CASES_TAC(SPEC (--`y:real`--) REAL_LE_NEGTOTAL) THEN
    POP_ASSUM(X_CHOOSE_TAC (--`x:real`--) o MATCH_MP TAN_TOTAL_POS) THENL
     [EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`&0`--) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0, PI2_BOUNDS],
      EXISTS_TAC (--`--x`--) THEN ASM_REWRITE_TAC[REAL_LT_NEG] THEN
      ASM_REWRITE_TAC[TAN_NEG, REAL_NEG_EQ, REAL_NEGNEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_LT_NEG] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[REAL_LE_NEGL]],
    MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LT_TOTAL) THENL
     [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM ACCEPT_TAC,
      ALL_TAC,
      POP_ASSUM MP_TAC THEN SPEC_TAC((--`x1:real`--),(--`z1:real`--)) THEN
      SPEC_TAC((--`x2:real`--),(--`z2:real`--)) THEN
      MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN DISCH_TAC THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN ONCE_REWRITE_TAC[CONJ_SYM]] THEN
    (STRIP_TAC THEN MP_TAC(SPECL [(--`tan`--), (--`x1:real`--), (--`x2:real`--)] ROLLE) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC CONTRAPOS_CONV THEN
     DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[NOT_IMP] THEN
     REPEAT CONJ_TAC THENL
      [X_GEN_TAC (--`x:real`--) THEN STRIP_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
       EXISTS_TAC (--`inv(cos(x) pow 2)`--) THEN MATCH_MP_TAC DIFF_TAN,
       X_GEN_TAC (--`x:real`--) THEN
       DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
       REWRITE_TAC[differentiable] THEN EXISTS_TAC (--`inv(cos(x) pow 2)`--) THEN
       MATCH_MP_TAC DIFF_TAN,
       REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(X_CHOOSE_THEN (--`x:real`--)
         (CONJUNCTS_THEN2 (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP
          REAL_LT_IMP_LE)) ASSUME_TAC)) THEN
       MP_TAC(SPEC (--`x:real`--) DIFF_TAN) THEN
       SUBGOAL_THEN (--`~(cos(x) = &0)`--) ASSUME_TAC THENL
        [ALL_TAC,
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o C CONJ (ASSUME (--`(tan diffl &0)(x)`--))) THEN
         DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN REWRITE_TAC[] THEN
         MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN
         ASM_REWRITE_TAC[]]] THEN
     (MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x1:real`--),
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x2:real`--)] THEN
     ASM_REWRITE_TAC[]))]);

(*---------------------------------------------------------------------------*)
(* Inverse trig functions                                                    *)
(*---------------------------------------------------------------------------*)

val asn = new_definition("asn",
  (--`asn(y) = @x. --(pi / &2) |<=| x /\ x |<=| pi / &2 /\ (sin x = y)`--));

val acs = new_definition("acs",
  (--`acs(y) = @x. &0 |<=| x /\ x |<=| pi /\ (cos x = y)`--));

val atn = new_definition("atn",
  (--`atn(y) = @x. --(pi / &2) |<| x /\ x |<| pi / &2 /\ (tan x = y)`--));

val ASN = prove_thm("ASN",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==>
     --(pi / &2) |<=| asn(y) /\ asn(y) |<=| pi / &2 /\ (sin(asn y) = y)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SIN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM asn]);

val ASN_SIN = prove_thm("ASN_SIN",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==> (sin(asn(y)) = y)`--),
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ASN th]));

val ASN_BOUNDS = prove_thm("ASN_BOUNDS",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==> --(pi / &2) |<=| asn(y) /\ asn(y) |<=| pi / &2`--),
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ASN th]));

val ASN_BOUNDS_LT = prove_thm("ASN_BOUNDS_LT",
  (--`!y. --(&1) |<| y /\ y |<| &1 ==> --(pi / &2) |<| asn(y) /\ asn(y) |<| pi / &2`--),
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`--(pi / &2) |<=| asn(y) /\ asn(y) |<=| pi / &2`--) ASSUME_TAC THENL
   [MATCH_MP_TAC ASN_BOUNDS THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[REAL_LT_LE]] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM (--`sin`--)) THEN
  REWRITE_TAC[SIN_NEG, SIN_PI2] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
  SUBGOAL_THEN (--`sin(asn y) = y`--) (fn th => ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ASN_SIN THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val SIN_ASN = prove_thm("SIN_ASN",
  (--`!x. --(pi / &2) |<=| x /\ x |<=| pi / &2 ==> (asn(sin(x)) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP SIN_TOTAL (SPEC (--`x:real`--) SIN_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ASN THEN
  MATCH_ACCEPT_TAC SIN_BOUNDS);

val ACS = prove_thm("ACS",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==>
     &0 |<=| acs(y) /\ acs(y) |<=| pi  /\ (cos(acs y) = y)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COS_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM acs]);

val ACS_COS = prove_thm("ACS_COS",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==> (cos(acs(y)) = y)`--),
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ACS th]));

val ACS_BOUNDS = prove_thm("ACS_BOUNDS",
  (--`!y. --(&1) |<=| y /\ y |<=| &1 ==> &0 |<=| acs(y) /\ acs(y) |<=| pi`--),
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ACS th]));

val ACS_BOUNDS_LT = prove_thm("ACS_BOUNDS_LT",
  (--`!y. --(&1) |<| y /\ y |<| &1 ==> &0 |<| acs(y) /\ acs(y) |<| pi`--),
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`&0 |<=| acs(y) /\ acs(y) |<=| pi`--) ASSUME_TAC THENL
   [MATCH_MP_TAC ACS_BOUNDS THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[REAL_LT_LE]] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM (--`cos`--)) THEN
  REWRITE_TAC[COS_0, COS_PI] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  SUBGOAL_THEN (--`cos(acs y) = y`--) (fn th => ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ACS_COS THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val COS_ACS = prove_thm("COS_ACS",
  (--`!x. &0 |<=| x /\ x |<=| pi ==> (acs(cos(x)) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP COS_TOTAL (SPEC (--`x:real`--) COS_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ACS THEN
  MATCH_ACCEPT_TAC COS_BOUNDS);

val ATN = prove_thm("ATN",
  (--`!y. --(pi / &2) |<| atn(y) /\ atn(y) |<| (pi / &2) /\ (tan(atn y) = y)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`y:real`--) TAN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM atn]);

val ATN_TAN = prove_thm("ATN_TAN",
  (--`!y. tan(atn y) = y`--),
  REWRITE_TAC[ATN]);

val ATN_BOUNDS = prove_thm("ATN_BOUNDS",
  (--`!y. --(pi / &2) |<| atn(y) /\ atn(y) |<| (pi / &2)`--),
  REWRITE_TAC[ATN]);

val TAN_ATN = prove_thm("TAN_ATN",
  (--`!x. --(pi / &2) |<| x /\ x |<| (pi / &2) ==> (atn(tan(x)) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC (--`tan(x)`--) TAN_TOTAL) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[ATN]);

(*---------------------------------------------------------------------------*)
(* A few additional results about the trig functions                         *)
(*---------------------------------------------------------------------------*)

val TAN_SEC = prove_thm("TAN_SEC",
  (--`!x. ~(cos(x) = &0) ==> (&1 |+| (tan(x) pow 2) = inv(cos x) pow 2)`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM
   (MATCH_MP REAL_DIV_REFL (SPEC (--`2`--) (MATCH_MP POW_NZ th)))]) THEN
  REWRITE_TAC[real_div, POW_MUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_INV th]) THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB, SIN_CIRCLE, REAL_MUL_LID]);

val SIN_COS_SQ = prove_thm("SIN_COS_SQ",
  (--`!x. &0 |<=| x /\ x |<=| pi ==> (sin(x) = sqrt(&1 |-| (cos(x) pow 2)))`--),
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_EQ THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD, SIN_CIRCLE] THEN
  MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REWRITE_TAC[]);

val COS_SIN_SQ = prove_thm("COS_SIN_SQ",
  (--`!x. --(pi / &2) |<=| x /\ x |<=| (pi / &2) ==>
             (cos(x) = sqrt(&1 |-| (sin(x) pow 2)))`--),
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_EQ THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[SIN_CIRCLE] THEN
  MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REWRITE_TAC[]);

val COS_ATN_NZ = prove_thm("COS_ATN_NZ",
  (--`!x. ~(cos(atn(x)) = &0)`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
  MATCH_MP_TAC COS_POS_PI THEN MATCH_ACCEPT_TAC ATN_BOUNDS);

val COS_ASN_NZ = prove_thm("COS_ASN_NZ",
  (--`!x. --(&1) |<| x /\ x |<| &1 ==> ~(cos(asn(x)) = &0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY MATCH_MP_TAC [REAL_POS_NZ, COS_POS_PI, ASN_BOUNDS_LT] THEN
  POP_ASSUM ACCEPT_TAC);

val SIN_ACS_NZ = prove_thm("SIN_ACS_NZ",
  (--`!x. --(&1) |<| x /\ x |<| &1 ==> ~(sin(acs(x)) = &0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY MATCH_MP_TAC [REAL_POS_NZ, SIN_POS_PI, ACS_BOUNDS_LT] THEN
  POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Derivatives of the inverse functions, starting with natural log           *)
(*---------------------------------------------------------------------------*)

val DIFF_LN = prove_thm("DIFF_LN",
  (--`!x. &0 |<| x ==> (ln diffl (inv x))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(ln diffl (inv x))(exp(ln(x)))`--) MP_TAC THENL
   [MATCH_MP_TAC DIFF_INVERSE_OPEN,
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[EXP_LN]] THEN
  MAP_EVERY EXISTS_TAC [(--`ln(x) |-| &1`--), (--`ln(x) |+| &1`--)] THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_01, LN_EXP,
    MATCH_MP DIFF_CONT (SPEC_ALL DIFF_EXP)] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC (--`ln(x)`--) DIFF_EXP) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM EXP_LN]), MATCH_MP_TAC REAL_POS_NZ] THEN
  ASM_REWRITE_TAC[]);

val DIFF_ASN_LEMMA = prove_thm("DIFF_ASN_LEMMA",
  (--`!x. --(&1) |<| x /\ x |<| &1 ==> (asn diffl (inv(cos(asn x))))(x)`--),
  GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPEC (--`x:real`--) ASN_SIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => GEN_REWR_TAC RAND_CONV  [SYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_OPEN THEN REWRITE_TAC[DIFF_SIN] THEN
  MAP_EVERY EXISTS_TAC [(--`--(pi / &2)`--), (--`pi / &2`--)] THEN
  MP_TAC(SPEC (--`x:real`--) ASN_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_SIN)] THEN
    MATCH_MP_TAC SIN_ASN THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC COS_ASN_NZ THEN ASM_REWRITE_TAC[]]);

val DIFF_ASN = prove_thm("DIFF_ASN",
  (--`!x. --(&1) |<| x /\ x |<| &1 ==> (asn diffl (inv(sqrt(&1 |-| (x pow 2)))))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ASN_LEMMA) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN (--`cos(asn(x)) = sqrt(&1 |-| (sin(asn x) pow 2))`--) SUBST1_TAC THENL
   [MATCH_MP_TAC COS_SIN_SQ THEN MATCH_MP_TAC ASN_BOUNDS,
    SUBGOAL_THEN (--`sin(asn x) = x`--) SUBST1_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC ASN_SIN] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val DIFF_ACS_LEMMA = prove_thm("DIFF_ACS_LEMMA",
  (--`!x. --(&1) |<| x /\ x |<| &1 ==> (acs diffl inv(--(sin(acs x))))(x)`--),
  GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPEC (--`x:real`--) ACS_COS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => GEN_REWR_TAC RAND_CONV  [SYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_OPEN THEN REWRITE_TAC[DIFF_COS] THEN
  MAP_EVERY EXISTS_TAC [(--`&0`--), (--`pi`--)] THEN
  MP_TAC(SPEC (--`x:real`--) ACS_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_COS)] THEN
    MATCH_MP_TAC COS_ACS THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[REAL_NEG_EQ, REAL_NEG_0] THEN
    MATCH_MP_TAC SIN_ACS_NZ THEN ASM_REWRITE_TAC[]]);

val DIFF_ACS = prove_thm("DIFF_ACS",
  (--`!x. --(&1) |<| x /\ x |<|  &1 ==> (acs diffl --(inv(sqrt(&1 |-| (x pow 2)))))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ACS_LEMMA) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN (--`sin(acs(x)) = sqrt(&1 |-| (cos(acs x) pow 2))`--) SUBST1_TAC THENL
   [MATCH_MP_TAC SIN_COS_SQ THEN MATCH_MP_TAC ACS_BOUNDS,
    SUBGOAL_THEN (--`cos(acs x) = x`--) SUBST1_TAC THENL
     [MATCH_MP_TAC ACS_COS,
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_NEG_INV THEN
      MATCH_MP_TAC REAL_POS_NZ THEN REWRITE_TAC[sqrt, num_CONV (--`2`--)] THEN
      MATCH_MP_TAC ROOT_POS_LT THEN
      REWRITE_TAC[REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
      REWRITE_TAC[SYM(num_CONV (--`2`--)), POW_2] THEN
      GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
      DISJ_CASES_TAC (SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THENL
       [ALL_TAC, GEN_REWR_TAC LAND_CONV  [GSYM REAL_NEG_MUL2]] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC [GSYM REAL_LT_NEG] THEN
      ASM_REWRITE_TAC[REAL_NEGNEG]]] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val DIFF_ATN = prove_thm("DIFF_ATN",
  (--`!x. (atn diffl (inv(&1 |+| (x pow 2))))(x)`--),
  GEN_TAC THEN
  SUBGOAL_THEN (--`(atn diffl (inv(&1 |+| (x pow 2))))(tan(atn x))`--) MP_TAC THENL
   [MATCH_MP_TAC DIFF_INVERSE_OPEN, REWRITE_TAC[ATN_TAN]] THEN
  MAP_EVERY EXISTS_TAC [(--`--(pi / &2)`--), (--`pi / &2`--)] THEN
  REWRITE_TAC[ATN_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC (--`x:real`--) THEN DISCH_TAC THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP TAN_ATN th]) THEN
    MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC (--`inv(cos(x) pow 2)`--) THEN
    MATCH_MP_TAC DIFF_TAN THEN
    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
    ASM_REWRITE_TAC[],
    MP_TAC(SPEC (--`atn(x)`--) DIFF_TAN) THEN REWRITE_TAC[COS_ATN_NZ] THEN
    REWRITE_TAC[MATCH_MP POW_INV (SPEC (--`x:real`--) COS_ATN_NZ)] THEN
    REWRITE_TAC[GSYM(MATCH_MP TAN_SEC (SPEC (--`x:real`--) COS_ATN_NZ))] THEN
    REWRITE_TAC[ATN_TAN],
    MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`&1`--) THEN
    REWRITE_TAC[REAL_LT_01, REAL_LE_ADDR, POW_2, REAL_LE_SQUARE]]);

export_theory();
