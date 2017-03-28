(*===========================================================================*)
(* Easy (relatively) n=4 case of FLT                                         *)
(*===========================================================================*)

load_library_in_place reduce_lib;
open Psyntax;

map add_theory_to_sml ["num", "prim_rec","arithmetic"];

Thm.counting_thms true; Thm.reset_thm_count();

new_theory "FERMAT";

(*---------------------------------------------------------------------------*)
(* Useful tactics.                                                           *)
(*---------------------------------------------------------------------------*)

fun PURE_GEN_REWRITE_TAC F thlist =
    Rewrite.GEN_REWRITE_TAC F Rewrite.empty_rewrites thlist;


fun W f x = f x x;
val TAUT_CONV =
  let fun bval w t = (type_of t = (==`:bool`==)) andalso 
                     (can (find_term is_var) t) andalso 
                     (free_in t w)
  in
  C (curry prove)
    (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
      (C (curry op THEN) (REWRITE_TAC[]) o BOOL_CASES_TAC o hd 
                    o sort free_in
                    o W(find_terms o bval) o snd))
  end;


val LAND_CONV = RATOR_CONV o RAND_CONV;

fun ANTE_RES_THEN ttac th = FIRST_ASSUM(fn t => ttac (MATCH_MP t th));

fun IMP_RES_THEN ttac th = FIRST_ASSUM(fn t => ttac (MATCH_MP th t));

(* ********************************************************************
 * Fold in parsing for some routines - this makes them slicker 
 * for interactive use.
 ******************************************************************** *)

fun Q_ERR{func,mesg} = 
    HOL_ERR{origin_structure = "FLT4 proof",
            origin_function = func, message = mesg};

val ptm = Parse.term_parser;

(* constrain parsed term to have a given type *)
fun ptm_with_ty qtm ty = 
   let fun trail s = [QUOTE (s^"):"), ANTIQUOTE(ty_antiq ty), QUOTE""]
   in
   ptm (case (Lib.front_n_back qtm)
          of ([],QUOTE s) => trail ("("^s)
           | (QUOTE s::rst, QUOTE s') => (QUOTE ("("^s)::rst) @ trail s'
           | _ => raise Q_ERR{func="ptm_with_ty",mesg="badly formed quote"})
   end;

(* coerce parsed term to be boolean *)
fun btm q = ptm_with_ty q bool;

val QTAUT_CONV = TAUT_CONV o ptm;
fun Qstore_thm(s,q,t) = store_thm(s,btm q,t);
fun Qnew_definition(s,q) = new_definition(s,btm q);
fun Qnew_infix_definition(s,q,f) = new_infix_definition(s,btm q,f);
fun QSPEC qtm th = 
    Drule.SPEC (ptm_with_ty qtm 
                  (Term.type_of(#Bvar(Dsyntax.dest_forall(concl th)))))
            th;

val QSPECL = rev_itlist QSPEC;
fun QSPEC_TAC(q1,q2) = SPEC_TAC(ptm q1, ptm q2);
fun QEXISTS_TAC qtm (g as (_,w)) =
     let val {Bvar,Body} = Dsyntax.dest_exists w
     in  Tactic.EXISTS_TAC (ptm_with_ty qtm (Term.type_of Bvar)) g
     end;

fun QX_CHOOSE_THEN [QUOTE s] (ttac:thm_tactic) : thm_tactic = fn xth =>
   let val {Bvar,Body} = Dsyntax.dest_exists (Thm.concl xth)
       val y = Term.mk_var{Name=s,Ty=Term.type_of Bvar}
   in
   fn (asl,w) =>
      let val th = itlist Drule.ADD_ASSUM (Thm.hyp xth)
                          (Thm.ASSUME (Term.subst [Bvar |-> y] Body))
          val (gl,prf) = ttac th (asl,w) 
      in
      (gl, (Drule.CHOOSE (y,xth)) o prf)
      end
   end
   handle _ => raise Q_ERR{func = "QX_CHOOSE_THEN",mesg = ""};

val QX_CHOOSE_TAC = C QX_CHOOSE_THEN ASSUME_TAC;

val QUNDISCH_TAC = Tactic.UNDISCH_TAC o btm
val Qnum_CONV = Num_conv.num_CONV o ptm

val QSUBGOAL_THEN = Tactical.SUBGOAL_THEN o btm
val QASSUME = ASSUME o btm
fun QX_GEN_TAC [QUOTE s] : tactic = fn (asl,w) =>
   let val {Bvar,Body} = Dsyntax.dest_forall w 
       val x1 = Term.mk_var{Name = s, Ty = Term.type_of Bvar}
   in if (Bvar=x1)
      then ([(asl,Body)], fn [th] => Drule.GEN x1 th)
      else ([(asl,Term.subst [Bvar |-> x1] Body)],
            fn [th] => 
               let val th' = Drule.GEN x1 th
               in Drule.EQ_MP(Drule.GEN_ALPHA_CONV Bvar (Thm.concl th')) th'
               end)
   end
   handle _ => raise Q_ERR{func = "QX_GEN_TAC",mesg = ""};

val QAP_TERM = Drule.AP_TERM  o ptm
val QASM_CASES_TAC = Tactic.ASM_CASES_TAC o btm
fun QAC_CONV p q = AC_CONV p (ptm q);


(*---------------------------------------------------------------------------*)
(* Enough preparation. Let get's started!                                    *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* We want to use complete induction, so package it up.                      *)
(*---------------------------------------------------------------------------*)

val COMPLETE_INDUCTION = Qstore_thm("COMPLETE_INDUCTION",
  `!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n`,
  let val wopeta = CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) WOP
  in
  GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP wopeta) THEN BETA_TAC THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(QX_CHOOSE_TAC `n`) THEN
  QEXISTS_TAC `n` THEN ASM_REWRITE_TAC[]
  end);

val COMPLETE_INDUCT_TAC =
  W(MATCH_MP_TAC o CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) o
    C SPEC COMPLETE_INDUCTION o rand o snd);

(*---------------------------------------------------------------------------*)
(* General arithmetic lemmas.                                                *)
(*---------------------------------------------------------------------------*)

val MULT_EQ_1 = Qstore_thm("MULT_EQ_1",
  `!x y. (x * y = 1) = (x = 1) /\ (y = 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(QSPEC `x` num_CASES) THEN
  STRUCT_CASES_TAC(QSPEC `y` num_CASES) THEN
  REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, Qnum_CONV `1`,
              INV_SUC_EQ, SUC_NOT, ADD_EQ_0] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES]);


val MULT_FIX = Qstore_thm("MULT_FIX",
  `!x y. (x * y = x) = (x = 0) \/ (y = 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(QSPEC `x` num_CASES) THEN
  REWRITE_TAC[MULT_CLAUSES, NOT_SUC] THEN
  REWRITE_TAC[SYM(el 5 (CONJUNCTS (SPEC_ALL MULT_CLAUSES)))] THEN
  PURE_GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
          [SYM(el 4 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))] THEN
  MATCH_ACCEPT_TAC MULT_MONO_EQ);

val LESS_EQ_MULT = Qstore_thm("LESS_EQ_MULT",
  `!m n p q. m <= n /\ p <= q ==> (m * p) <= (n * q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LESS_EQ_EXISTS]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
    GSYM ADD_ASSOC, LESS_EQ_ADD]);

val LESS_MULT = Qstore_thm("LESS_MULT",
  `!m n p q. m < n /\ p < q ==> (m * p) < (n * q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN
   ((CHOOSE_THEN SUBST_ALL_TAC) o MATCH_MP LESS_ADD_1)) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[GSYM ADD1, MULT_CLAUSES, ADD_CLAUSES, GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM (el 4 (CONJUNCTS ADD_CLAUSES))] THEN
  MATCH_ACCEPT_TAC LESS_ADD_SUC);

val MULT_LCANCEL = Qstore_thm("MULT_LCANCEL",
  `!a b c. ~(a = 0) /\ (a * b = a * c) ==> (b = c)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(QSPEC `a` num_CASES) THEN
  REWRITE_TAC[NOT_SUC, MULT_MONO_EQ]);

val LESS_EQ_ANTISYM_EQ = Qstore_thm("LESS_EQ_ANTISYM_EQ",
  `!x y. x <= y /\ y <= x = (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[LESS_EQUAL_ANTISYM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LESS_EQ_REFL]);

(*---------------------------------------------------------------------------*)
(* Properties of the exponential function.                                   *)
(*---------------------------------------------------------------------------*)

val EXP_0 = Qstore_thm("EXP_0",
  `!n. 0 EXP (SUC n) = 0`,
  REWRITE_TAC[EXP, MULT_CLAUSES]);

val EXP_1 = Qstore_thm("EXP_1",
  `!n. 1 EXP n = 1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES, EXP]);

val EXP_2 = Qstore_thm("EXP_2",
  `!x. x EXP 2 = x * x`,
  REWRITE_TAC[Qnum_CONV `2`, Qnum_CONV `1`, EXP, 
              MULT_CLAUSES, ADD_CLAUSES]);

val MULT_EXP = Qstore_thm("MULT_EXP",
  `!n x y. (x * y) EXP n = (x EXP n) * (y EXP n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP, MULT_CLAUSES] THEN
  REPEAT GEN_TAC THEN CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val EXP_EQ_0 = Qstore_thm("EXP_EQ_0",
  `!x n. (x EXP n = 0) = (x = 0) /\ ~(n = 0)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [QSPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[EXP] THEN REDUCE_TAC THEN
    REWRITE_TAC[MULT_EQ_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[NOT_SUC] THEN
    FIRST_ASSUM(IMP_RES_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[],
    STRUCT_CASES_TAC(QSPEC `n` num_CASES) THEN
    REWRITE_TAC[EXP, NOT_SUC, MULT_EQ_0] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);

val EXP_EQ_1 = Qstore_thm("EXP_EQ_1",
  `!x n. (x EXP n = 1) = (x = 1) \/ (n = 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(QSPEC `n` num_CASES) THEN
  ASM_REWRITE_TAC[EXP, NOT_SUC, MULT_EQ_1] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[EXP_1]);

val EXP_MONO_LEMMA = Qstore_thm("EXP_MONO_LEMMA",
  `!n x y. x < y ==> (x EXP (SUC n)) < (y EXP (SUC n))`,
  INDUCT_TAC THEN REWRITE_TAC[EXP, MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM EXP] THEN ONCE_REWRITE_TAC[EXP] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_MULT THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);

val EXP_MONO_LT = Qstore_thm("EXP_MONO_LT",
  `!n x y. (x EXP (SUC n)) < (y EXP (SUC n)) = (x < y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[EXP_MONO_LEMMA] THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LESS, LESS_OR_EQ] THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN MATCH_MP_TAC EXP_MONO_LEMMA THEN ASM_REWRITE_TAC[]);

val EXP_MONO_LE = Qstore_thm("EXP_MONO_LE",
  `!x y n. (x EXP (SUC n)) <= (y EXP (SUC n)) = x <= y`,
  REWRITE_TAC[GSYM NOT_LESS, EXP_MONO_LT]);

val EXP_MONO_EQ = Qstore_thm("EXP_MONO_EQ",
  `!x y n. (x EXP (SUC n) = y EXP (SUC n)) = (x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LESS_EQ_ANTISYM_EQ] THEN
  REWRITE_TAC[EXP_MONO_LE]);

val EXP_EXP = Qstore_thm("EXP_EXP",
  `!x m n. (x EXP m) EXP n = x EXP (m * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EXP, MULT_CLAUSES, EXP_ADD]);

(*---------------------------------------------------------------------------*)
(* More ad-hoc arithmetic lemmas unlikely to be useful elsewhere.            *)
(*---------------------------------------------------------------------------*)

val DIFF_LEMMA = Qstore_thm("DIFF_LEMMA",
  `!a b. a < b ==> (a = 0) \/ (a + (b - a)) < (a + b)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(QSPEC `a` LESS_0_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  DISJ2_TAC THEN REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
  PURE_GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 ADD_CLAUSES)] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REPEAT(MATCH_MP_TAC LESS_MONO_ADD) THEN POP_ASSUM ACCEPT_TAC);

val NOT_EVEN_EQ_ODD = Qstore_thm("NOT_EVEN_EQ_ODD",
 `!m n. ~(2 * m = SUC(2 * n))`,
  REWRITE_TAC[TIMES2, GSYM NOT_ODD_EQ_EVEN]);

val CANCEL_TIMES2 = Qstore_thm("CANCEL_TIMES2",
  `!x y. (2 * x = 2 * y) = (x = y)`,
  REWRITE_TAC[Qnum_CONV `2`, MULT_MONO_EQ]);

val EVEN_SQUARE = Qstore_thm("EVEN_SQUARE",
  `!n. EVEN(n) ==> ?x. n EXP 2 = 4 * x`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(QX_CHOOSE_THEN `m` SUBST1_TAC) THEN
  QEXISTS_TAC `m * m` THEN REWRITE_TAC[EXP_2] THEN
  REWRITE_TAC[SYM(REDUCE_CONV (--`2 * 2`--))] THEN
  CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val ODD_SQUARE = Qstore_thm("ODD_SQUARE",
  `!n. ODD(n) ==> ?x. n EXP 2 = (4 * x) + 1`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(QX_CHOOSE_THEN `m` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[EXP_2, MULT_CLAUSES, ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD1, INV_SUC_EQ] THEN
  QEXISTS_TAC `m * m + m` THEN
  REWRITE_TAC(map Qnum_CONV [`4`, `3`, `2`, `1`]) THEN
  REWRITE_TAC[ADD_CLAUSES, MULT_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
  CONV_TAC(AC_CONV(ADD_ASSOC,ADD_SYM)));

val DIFF_SQUARE = Qstore_thm("DIFF_SQUARE",
  `!x y. (x EXP 2) - (y EXP 2) = (x + y) * (x - y)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(QSPECL [`x`, `y`] LESS_EQ_CASES) THENL
   [QSUBGOAL_THEN `x * x <= y * y` MP_TAC THENL
     [MATCH_MP_TAC LESS_EQ_MULT THEN ASM_REWRITE_TAC[],
      POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM SUB_EQ_0] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[EXP_2, MULT_CLAUSES]],
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LESS_EQ_EXISTS]) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
    REWRITE_TAC[EXP_2, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM ADD_ASSOC, ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
    AP_TERM_TAC THEN PURE_GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC MULT_SYM]);

val ADD_IMP_SUB = Qstore_thm("ADD_IMP_SUB",
  `!x y z. (x + y = z) ==> (x = z - y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ADD_SUB]);

val ADD_SUM_DIFF = Qstore_thm("ADD_SUM_DIFF",
  `!v w. v <= w ==> ((w + v) - (w - v) = 2 * v) /\
                    ((w + v) + (w - v) = 2 * w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
  REWRITE_TAC[TIMES2, GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB, GSYM ADD_ASSOC]);

val EXP_4 = Qstore_thm("EXP_4",
  `!n. n EXP 4 = (n EXP 2) EXP 2`,
  GEN_TAC THEN REWRITE_TAC[EXP_EXP] THEN
  REDUCE_TAC THEN REFL_TAC);

(*---------------------------------------------------------------------------*)
(* Elementary theory of divisibility                                         *)
(*---------------------------------------------------------------------------*)

val divides = Qnew_infix_definition("divides",
  `$divides a b = ?x. b = a * x`,  450);

val DIVIDES_0 = Qstore_thm("DIVIDES_0",
  `!x. x divides 0`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN
  QEXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES]);

val DIVIDES_ZERO = Qstore_thm("DIVIDES_ZERO",
  `!x. 0 divides x = (x = 0)`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES]);

val DIVIDES_1 = Qstore_thm("DIVIDES_1",
  `!x. 1 divides x`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN
  QEXISTS_TAC `x` THEN REWRITE_TAC[MULT_CLAUSES]);

val DIVIDES_ONE = Qstore_thm("DIVIDES_ONE",
  `!x. (x divides 1) = (x = 1)`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  REWRITE_TAC[MULT_EQ_1] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN QEXISTS_TAC `1` THEN REFL_TAC);

val DIVIDES_GE = Qstore_thm("DIVIDES_GE",
  `!a b. a divides b ==> (b = 0) \/ a <= b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_THEN `x` SUBST1_TAC) THEN
  STRUCT_CASES_TAC(QSPEC `x` num_CASES) THEN
  REWRITE_TAC[MULT_CLAUSES, LESS_EQ_ADD]);

val DIVIDES_REFL = Qstore_thm("DIVIDES_REFL",
  `!x. x divides x`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN
  QEXISTS_TAC `1` THEN REWRITE_TAC[MULT_CLAUSES]);

val DIVIDES_TRANS = Qstore_thm("DIVIDES_TRANS",
  `!a b c. a divides b /\ b divides c ==> a divides c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
  REPEAT(DISCH_THEN(CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  W(EXISTS_TAC o rand o lhs o snd o dest_exists o snd) THEN
  REFL_TAC);
	
val DIVIDES_ANTISYM = Qstore_thm("DIVIDES_ANTISYM",
  `!x y. x divides y /\ y divides x = (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CHOOSE_THEN SUBST1_TAC)) THEN
    DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
    CONV_TAC(LAND_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM MULT_ASSOC, MULT_FIX, MULT_EQ_1] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIVIDES_REFL]]);

val DIVIDES_ADD = Qstore_thm("DIVIDES_ADD",
  `!d a b. d divides a /\ d divides b ==> d divides (a + b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN (CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  W(EXISTS_TAC o rand o lhs o snd o dest_exists o snd) THEN
  REFL_TAC);

val DIVIDES_SUB = Qstore_thm("DIVIDES_SUB",
  `!d a b. d divides a /\ d divides b ==> d divides (a - b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN (CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[GSYM LEFT_SUB_DISTRIB] THEN
  W(EXISTS_TAC o rand o lhs o snd o dest_exists o snd) THEN
  REFL_TAC);

val DIVIDES_LMUL = Qstore_thm("DIVIDES_LMUL",
  `!d a x. d divides a ==> d divides (x * a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_THEN `p` SUBST1_TAC) THEN
  QEXISTS_TAC `x * p` THEN
  CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val DIVIDES_RMUL = Qstore_thm("DIVIDES_RMUL",
  `!d a x. d divides a ==> d divides (a * x)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_ACCEPT_TAC DIVIDES_LMUL);

val DIVIDES_ADD_REVR = Qstore_thm("DIVIDES_ADD_REVR",
  `!d a b. d divides a /\ d divides (a + b) ==> d divides b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(QSPECL [`b`, `a`] ADD_SUB)) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[]);

val DIVIDES_ADD_REVL = Qstore_thm("DIVIDES_ADD_REVL",
  `!d a b. d divides b /\ d divides (a + b) ==> d divides a`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC DIVIDES_ADD_REVR);

val DIVIDES_DIV = Qstore_thm("DIVIDES_DIV",
  `!n x. 0 < n /\ (x MOD n = 0) ==> n divides x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o QSPEC`x:num` o MATCH_MP DIVISION) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[divides] THEN QEXISTS_TAC `x DIV n` THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val DIVIDES_MUL_L = Qstore_thm("DIVIDES_MUL_L",
  `!a b c. a divides b ==> (c * a) divides (c * b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_THEN `x` SUBST1_TAC) THEN
  QEXISTS_TAC `x` THEN REWRITE_TAC[MULT_ASSOC]);

val DIVIDES_MUL_R = Qstore_thm("DIVIDES_MUL_R",
  `!a b c. a divides b ==> (a * c) divides (b * c)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_ACCEPT_TAC DIVIDES_MUL_L);

val DIVIDES_LMUL2 = Qstore_thm("DIVIDES_LMUL2",
  `!d a x. (x * d) divides a ==> d divides a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_THEN `y` SUBST1_TAC) THEN
  QEXISTS_TAC `x * y` THEN
  CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val DIVIDES_RMUL2 = Qstore_thm("DIVIDES_RMUL2",
  `!d a x. (d * x) divides a ==> d divides a`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_ACCEPT_TAC DIVIDES_LMUL2);

val DIVIDES_CMUL2 = Qstore_thm("DIVIDES_CMUL2",
  `!a b c. (c * a) divides (c * b) /\ ~(c = 0) ==> a divides b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (QX_CHOOSE_TAC `x`) ASSUME_TAC) THEN
  QEXISTS_TAC `x` THEN MATCH_MP_TAC MULT_LCANCEL THEN
  QEXISTS_TAC `c` THEN ASM_REWRITE_TAC[MULT_ASSOC]);

val DIVIDES_LE = Qstore_thm("DIVIDES_LE",
  `!m n. m divides n ==> m <= n \/ (n = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_THEN `x` SUBST1_TAC) THEN
  REWRITE_TAC[MULT_EQ_0] THEN
  STRUCT_CASES_TAC(QSPEC `x` num_CASES) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES, LESS_EQ_ADD]);

val DIVIDES_DIV_NOT = Qstore_thm("DIVIDES_DIV_NOT",
  `!n x q r. (x = (q * n) + r) /\ 0 < r /\ r < n ==> ~(n divides x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(QSPEC `n` DIVIDES_REFL) THEN
  DISCH_THEN(MP_TAC o QSPEC `q:num` o MATCH_MP DIVIDES_LMUL) THEN
  PURE_REWRITE_TAC[QTAUT_CONV `a ==> ~b = a /\ b ==> F`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_ADD_REVR) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM, NOT_LESS_EQUAL, GSYM LESS_EQ_0]);

val DIVIDES_MUL2 = Qstore_thm("DIVIDES_MUL2",
  `!a b c d. a divides b /\ c divides d ==> (a * c) divides (b * d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (QX_CHOOSE_TAC `x`) (QX_CHOOSE_TAC `y`)) THEN 
  QEXISTS_TAC `x * y` THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val DIVIDES_EXP = Qstore_thm("DIVIDES_EXP",
  `!x y n. x divides y ==> (x EXP n) divides (y EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_THEN `d` SUBST1_TAC) THEN
  QEXISTS_TAC `d EXP n` THEN MATCH_ACCEPT_TAC MULT_EXP);

val DIVIDES_EXP2 = Qstore_thm("DIVIDES_EXP2",
  `!n x y. ~(n = 0) /\ (x EXP n) divides y ==> x divides y`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP] THEN
  DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o QSPECL [`x`, `y`]) THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC(QSPEC `n` num_CASES) THENL
   [REWRITE_TAC[EXP, MULT_CLAUSES],
    DISCH_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC DIVIDES_LMUL2 THEN
    QEXISTS_TAC `x` THEN ASM_REWRITE_TAC[]]);

val DIVIDES_FACT = Qstore_thm("DIVIDES_FACT",
  `!m n. 0 < m /\ m <= n ==> m divides (FACT n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (QX_CHOOSE_THEN `d` SUBST1_TAC))
  THEN QSPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES, FACT] THENL
   [QSPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[FACT, DIVIDES_REFL, LESS_REFL] THEN
    DISCH_TAC THEN MATCH_MP_TAC DIVIDES_RMUL THEN
    MATCH_ACCEPT_TAC DIVIDES_REFL,
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    MATCH_ACCEPT_TAC DIVIDES_LMUL]);

val DIVIDES_2 = Qstore_thm("DIVIDES_2",
  `!n. 2 divides n = EVEN(n)`,
  REWRITE_TAC[divides, EVEN_EXISTS]);

val DIVIDES_REXP = Qstore_thm("DIVIDES_REXP",
  `!x y n. x divides y ==> x divides (y EXP (SUC n))`,
  REWRITE_TAC[EXP, DIVIDES_RMUL]);

(*---------------------------------------------------------------------------*)
(* The Bezout theorem is a bit ugly for N, it'd be easier for Z              *)
(*---------------------------------------------------------------------------*)

val IND_EUCLID = Qstore_thm("IND_EUCLID",
  `!P. (!a b. P a b = P b a) /\
       (!a. P a 0) /\
       (!a b. P a b ==> P a (a + b)) ==>
         !a b. P a b`,
  REPEAT STRIP_TAC THEN
  W(fn (asl,w)=>  QSUBGOAL_THEN `!n a b. (a + b = n) ==> ^w` MATCH_MP_TAC)
  THENL
   [ALL_TAC, QEXISTS_TAC `a + b` THEN REFL_TAC] THEN
  COMPLETE_INDUCT_TAC THEN
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (QSPECL [`a`, `b`] LESS_LESS_CASES) THENL
   [DISCH_THEN SUBST1_TAC THEN
    PURE_GEN_REWRITE_TAC RAND_CONV [GSYM ADD_0] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN 
    (* ambiguity in rewriting! hol88:ASM_REWRITE_TAC[] *)
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    ALL_TAC, ALL_TAC] THEN
  DISCH_THEN(fn th => SUBST1_TAC(SYM(MATCH_MP SUB_ADD
                                      (MATCH_MP LESS_IMP_LESS_OR_EQ th))) THEN
    DISJ_CASES_THEN MP_TAC (MATCH_MP DIFF_LEMMA th)) THENL
   [DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM (CONV_TAC o REWR_CONV) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    REWRITE_TAC[QASSUME `a + b = n`] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM(IMP_RES_THEN MATCH_MP_TAC),
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (QASSUME `a + b = n`)] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    FIRST_ASSUM (CONV_TAC o REWR_CONV) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM(IMP_RES_THEN MATCH_MP_TAC)] THEN
  REWRITE_TAC[]);

val BEZOUT_LEMMA = Qstore_thm("BEZOUT_LEMMA",
  `!a b. (?d x y. (d divides a /\ d divides b) /\
                  ((a * x = (b * y) + d) \/
                   (b * x = (a * y) + d)))
     ==> (?d x y. (d divides a /\ d divides (a + b)) /\
                  ((a * x = ((a + b) * y) + d) \/
                   ((a + b) * x = (a * y) + d)))`,
  REPEAT STRIP_TAC THEN QEXISTS_TAC `d` THENL
   [MAP_EVERY QEXISTS_TAC [`x + y`, `y`],
    MAP_EVERY QEXISTS_TAC [`x`, `x + y`]] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [MATCH_MP_TAC DIVIDES_ADD, ALL_TAC]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[ADD_ASSOC] THEN DISJ1_TAC THEN
  CONV_TAC(AC_CONV(ADD_ASSOC,ADD_SYM)));


val BEZOUT_ADD = Qstore_thm("BEZOUT_ADD",
  `!a b. ?d x y. (d divides a /\ d divides b) /\
                 ((a * x = (b * y) + d) \/
                  (b * x = (a * y) + d))`,
  W(fn (asl,w) =>
     MP_TAC(QSPEC `\(a:num) (b:num). ^(snd(strip_forall w))` IND_EUCLID)) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT
     (AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC) THEN
    PURE_GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [DISJ_SYM] THEN
    PURE_GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [CONJ_SYM] THEN REFL_TAC,
    GEN_TAC THEN MAP_EVERY QEXISTS_TAC [`a`, `1`, `0`] THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, DIVIDES_0, DIVIDES_REFL],
                MATCH_ACCEPT_TAC BEZOUT_LEMMA]);

val BEZOUT = Qstore_thm("BEZOUT",
  `!a b. ?d x y. (d divides a /\ d divides b) /\
                 (((a * x) - (b * y) = d) \/
                  ((b * x) - (a * y) = d))`,
  REPEAT GEN_TAC THEN REPEAT_TCL STRIP_THM_THEN ASSUME_TAC
   (QSPECL [`a`, `b`] BEZOUT_ADD) THEN
  REPEAT(W(EXISTS_TAC o fst o dest_exists o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB]);

(*---------------------------------------------------------------------------*)
(* Greatest common divisor.                                                  *)
(*---------------------------------------------------------------------------*)

val gcd = Qnew_definition("gcd",
  `gcd(a,b) = @d. (d divides a /\ d divides b) /\
                  (!e. e divides a /\ e divides b ==> e divides d)`);

val GCD = Qstore_thm("GCD",
  `!a b. (gcd(a,b) divides a /\ gcd(a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides gcd(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcd] THEN
  CONV_TAC SELECT_CONV THEN 
  MP_TAC(QSPECL [`a`, `b`] BEZOUT) THEN
  DISCH_THEN(EVERY_TCL (map QX_CHOOSE_THEN [`d`, `x`, `y`]) STRIP_ASSUME_TAC)
  THEN QEXISTS_TAC `d` THEN ASM_REWRITE_TAC[] THEN
  QX_GEN_TAC `e` THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);

val GCD_COMMON = Qstore_thm("GCD_COMMON",
  `!d a b. d divides a /\ d divides b = d divides gcd(a,b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[GCD] THEN
  DISCH_TAC THEN CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THEN
  QEXISTS_TAC `gcd(a,b)` THEN ASM_REWRITE_TAC[GCD]);

val GCD_UNIQUE = Qstore_thm("GCD_UNIQUE",
  `!d a b. (d divides a /\ d divides b) /\
           (!e. e divides a /\ e divides b ==> e divides d) =
           (d = gcd(a,b))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[GCD] THEN
  ONCE_REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_REWRITE_TAC[GSYM GCD_COMMON] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GCD]);

val DIVIDES_GCD = Qstore_thm("DIVIDES_GCD",
  `!a b d. d divides gcd(a,b) = d divides a /\ d divides b`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[GCD] THEN
  DISCH_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC DIVIDES_TRANS THEN QEXISTS_TAC `gcd(a,b)` THEN
  ASM_REWRITE_TAC[GCD]);

val GCD_SYM = Qstore_thm("GCD_SYM",
  `!a b. gcd(a,b) = gcd(b,a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcd] THEN
  AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC(QTAUT_CONV `(a = b) /\ (c = d) ==> (a /\ c = b /\ d)`) THEN
  CONJ_TAC THEN PURE_GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[CONJ_SYM]
  THEN REFL_TAC);

val GCD_ASSOC = Qstore_thm("GCD_ASSOC",
  `!a b c. gcd(a,gcd(b,c)) = gcd(gcd(a,b),c)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REWRITE_TAC[DIVIDES_GCD, CONJ_ASSOC, GCD] THEN
  CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THEN
  QEXISTS_TAC `gcd(b,c)` THEN ASM_REWRITE_TAC[GCD]);

val BEZOUT_GCD = Qstore_thm("BEZOUT_GCD",
  `!a b. ?x y. ((a * x) - (b * y) = gcd(a,b)) \/
               ((b * x) - (a * y) = gcd(a,b))`,
  REPEAT GEN_TAC THEN
  MP_TAC(QSPECL [`a`, `b`] BEZOUT) THEN
  DISCH_THEN(EVERY_TCL (map QX_CHOOSE_THEN [`d`, `x`, `y`])
    (CONJUNCTS_THEN ASSUME_TAC)) THEN
  QSUBGOAL_THEN `d divides gcd(a,b)` MP_TAC THENL
   [MATCH_MP_TAC(snd(Lib.front_n_back(CONJUNCTS(SPEC_ALL GCD)))) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN(QX_CHOOSE_THEN `k` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    MAP_EVERY QEXISTS_TAC [`x * k`, `y * k`] THEN
    ASM_REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB, MULT_ASSOC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[]]);

val GCD_LMUL = Qstore_thm("GCD_LMUL",
  `!a b c. gcd(c * a, c * b) = c * gcd(a,b)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC DIVIDES_MUL_L) THEN
  REWRITE_TAC[GCD] THEN REPEAT STRIP_TAC THEN
  REPEAT_TCL STRIP_THM_THEN (SUBST1_TAC o SYM)
   (QSPECL [`a`, `b`] BEZOUT_GCD) THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB, MULT_ASSOC] THEN
  MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN ASM_REWRITE_TAC[]);

val GCD_RMUL = Qstore_thm("GCD_RMUL",
  `!a b c. gcd(a * c, b * c) = c * gcd(a,b)`,
  REPEAT GEN_TAC THEN
  PURE_GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  MATCH_ACCEPT_TAC GCD_LMUL);

val GCD_BEZOUT = Qstore_thm("GCD_BEZOUT",
  `!a b d. (?x y. ((a * x) - (b * y) = d) \/ ((b * x) - (a * y) = d)) =
           gcd(a,b) divides d`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[GCD],
    DISCH_THEN(QX_CHOOSE_THEN `k` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    STRIP_ASSUME_TAC(QSPECL [`a`, `b`] BEZOUT_GCD) THEN
    MAP_EVERY QEXISTS_TAC [`x * k`, `y * k`] THEN
    ASM_REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB, MULT_ASSOC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[]]);

val GCD_BEZOUT_SUM = Qstore_thm("GCD_BEZOUT_SUM",
  `!a b d x y. ((a * x) + (b * y) = d) ==> gcd(a,b) divides d`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[GCD]);

val GCD_0 = Qstore_thm("GCD_0",
  `!a. gcd(0,a) = a`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REWRITE_TAC[DIVIDES_0, DIVIDES_REFL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);

val GCD_ZERO = Qstore_thm("GCD_ZERO",
  `!a b. (gcd(a,b) = 0) = (a = 0) /\ (b = 0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GCD_0] THEN
  MP_TAC(QSPECL [`a`, `b`] GCD) THEN
  ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);

val GCD_REFL = Qstore_thm("GCD_REFL",
  `!a. gcd(a,a) = a`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REWRITE_TAC[DIVIDES_REFL]);

val GCD_1 = Qstore_thm("GCD_1",
  `!a. gcd(1,a) = 1`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REWRITE_TAC[DIVIDES_1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);

val GCD_MULTIPLE = Qstore_thm("GCD_MULTIPLE",
  `!a b. gcd(b,a * b) = b`,
  REPEAT GEN_TAC THEN
  PURE_GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
       [SYM(el 3 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))] THEN
  REWRITE_TAC[GCD_RMUL, GCD_1] THEN
  REWRITE_TAC[MULT_CLAUSES]);

(*---------------------------------------------------------------------------*)
(* Coprimality                                                               *)
(*---------------------------------------------------------------------------*)

val coprime = Qnew_definition("coprime",
  `coprime(a,b) = !d. d divides a /\ d divides b ==> (d = 1)`);

val COPRIME = Qstore_thm("COPRIME",
  `!a b. coprime(a,b) = !d. d divides a /\ d divides b = (d = 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coprime] THEN
  REPEAT(EQ_TAC ORELSE STRIP_TAC) THEN ASM_REWRITE_TAC[DIVIDES_1] THENL
   [FIRST_ASSUM MATCH_MP_TAC,
    FIRST_ASSUM(CONV_TAC o REWR_CONV o GSYM) THEN CONJ_TAC] THEN
  ASM_REWRITE_TAC[]);

val COPRIME_GCD = Qstore_thm("COPRIME_GCD",
  `!a b. coprime(a,b) = (gcd(a,b) = 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coprime] THEN EQ_TAC THENL
   [DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GCD],
    DISCH_TAC THEN MP_TAC(QSPECL [`a`, `b`] GCD) THEN
    ASM_REWRITE_TAC[DIVIDES_ONE] THEN DISCH_THEN(fn th => REWRITE_TAC[th])]);

val COPRIME_SYM = Qstore_thm("COPRIME_SYM",
  `!a b. coprime(a,b) = coprime(b,a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COPRIME_GCD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC GCD_SYM);

val COPRIME_BEZOUT = Qstore_thm("COPRIME_BEZOUT",
  `!a b. coprime(a,b) = ?x y. ((a * x) - (b * y) = 1) \/
                              ((b * x) - (a * y) = 1)`,
  REWRITE_TAC[GCD_BEZOUT, DIVIDES_ONE, COPRIME_GCD]);

val COPRIME_DIVPROD = Qstore_thm("COPRIME_DIVPROD",
  `!d a b. d divides (a * b) /\ coprime(d,a) ==> d divides b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[COPRIME_BEZOUT] THEN
  DISCH_THEN(QX_CHOOSE_THEN `x` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `y` MP_TAC) THEN
  DISCH_THEN (DISJ_CASES_THEN (MP_TAC o QAP_TERM `$* b`)) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB, MULT_ASSOC] THEN
  MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVIDES_RMUL THEN
  ASM_REWRITE_TAC[DIVIDES_REFL]);

val COPRIME_1 = Qstore_thm("COPRIME_1",
  `!a. coprime(a,1)`,
  GEN_TAC THEN REWRITE_TAC[coprime, DIVIDES_ONE] THEN
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[th]));

val GCD_COPRIME = Qstore_thm("GCD_COPRIME",
  `!a b a' b'. ~(gcd(a,b) = 0) /\
               (a = a' * gcd(a,b)) /\
               (b = b' * gcd(a,b)) ==> coprime(a',b')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[coprime] THEN
  CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(QX_CHOOSE_TAC `d`) THEN
  POP_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (QX_CHOOSE_THEN `a''` SUBST1_TAC)
    (QX_CHOOSE_THEN `b''` SUBST1_TAC)) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MULT_ASSOC] THEN
  DISCH_TAC THEN MP_TAC(QSPECL [`a`, `b`] GCD) THEN
  DISCH_THEN(MP_TAC o QSPEC `gcd(a,b) * d` 
             o snd o Lib.front_n_back o CONJUNCTS) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[divides] THEN QEXISTS_TAC `a'':num` THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1),
    REWRITE_TAC[divides] THEN QEXISTS_TAC `b'':num` THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT2),
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    REWRITE_TAC[DE_MORGAN_THM, NOT_LESS_EQUAL] THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
    QUNDISCH_TAC `~(d = 1)` THEN
    STRUCT_CASES_TAC(QSPEC `d` num_CASES) THEN
    REWRITE_TAC[MULT_CLAUSES, SUC_NOT, Qnum_CONV `1`, INV_SUC_EQ] THENL
     [DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[GCD_0],
      DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
      ASM_REWRITE_TAC[MULT_EQ_0]]]);

val GCD_COPRIME_EXISTS = Qstore_thm("GCD_COPRIME_EXISTS",
  `!a b. ~(gcd(a,b) = 0) ==>
        ?a' b'. (a = a' * gcd(a,b)) /\
                (b = b' * gcd(a,b)) /\
                coprime(a',b')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(QSPECL [`a`,`b`] GCD) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (QX_CHOOSE_TAC `a'` o GSYM)
   (QX_CHOOSE_TAC `b'` o GSYM)) THEN
  MAP_EVERY QEXISTS_TAC [`a':num`, `b':num`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GCD_COPRIME THEN
  MAP_EVERY QEXISTS_TAC [`a`, `b`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]);

val COPRIME_0 = Qstore_thm("COPRIME_0",
  `!d. coprime(d,0) = (d = 1)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_1] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[coprime] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[DIVIDES_REFL, DIVIDES_0]);

val COPRIME_MUL = Qstore_thm("COPRIME_MUL",
  `!d a b. coprime(d,a) /\ coprime(d,b) ==> coprime(d,a * b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COPRIME_GCD] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o QAP_TERM `$* a`)) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN
   (fn th => PURE_GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM th]) THEN
  REWRITE_TAC[GSYM GCD_LMUL, GCD_ASSOC, GCD_MULTIPLE]);

val COPRIME_LMUL2 = Qstore_thm("COPRIME_LMUL2",
  `!d a b. coprime(d,a * b) ==> coprime(d,b)`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[coprime] THEN CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[NOT_IMP] THEN
  DISCH_THEN(QX_CHOOSE_THEN `k` STRIP_ASSUME_TAC) THEN
  QEXISTS_TAC `k` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIVIDES_LMUL THEN ASM_REWRITE_TAC[]);

val COPRIME_RMUL2 = Qstore_thm("COPRIME_RMUL2",
  `!d a b.  coprime(d,a * b) ==> coprime(d,a)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[COPRIME_LMUL2]);

val COPRIME_EXP = Qstore_thm("COPRIME_EXP",
  `!n a d. coprime(d,a) ==> coprime(d,a EXP n)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP, COPRIME_1] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC COPRIME_MUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);

val COPRIME_EXP_IMP = Qstore_thm("COPRIME_EXP_IMP",
  `!n a b. coprime(a,b) ==> coprime(a EXP n,b EXP n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC COPRIME_EXP THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  MATCH_MP_TAC COPRIME_EXP THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[]);

val BEZOUT_GCD_POW = Qstore_thm("BEZOUT_GCD_POW",
  `!n a b. ?x y. (((a EXP n) * x) - ((b EXP n) * y) = gcd(a,b) EXP n) \/
                 (((b EXP n) * x) - ((a EXP n) * y) = gcd(a,b) EXP n)`,
  REPEAT GEN_TAC THEN QASM_CASES_TAC `gcd(a,b) = 0` THENL
   [STRUCT_CASES_TAC(QSPEC `n` num_CASES) THEN
    ASM_REWRITE_TAC[EXP, MULT_CLAUSES] THENL
     [MAP_EVERY QEXISTS_TAC [`1`, `0`] THEN REWRITE_TAC[SUB_0],
      REPEAT(QEXISTS_TAC `0`) THEN REWRITE_TAC[MULT_CLAUSES, SUB_0]],
    MP_TAC(QSPECL [`a`, `b`] GCD) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(QX_CHOOSE_THEN `b'` ASSUME_TAC) THEN
    DISCH_THEN(QX_CHOOSE_THEN `a'` ASSUME_TAC) THEN
    MP_TAC(QSPECL [`a`, `b`, `a':num`, `b':num`] GCD_COPRIME) THEN
    RULE_ASSUM_TAC GSYM THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o QSPEC `n` o MATCH_MP COPRIME_EXP_IMP) THEN
    REWRITE_TAC[COPRIME_BEZOUT] THEN
    DISCH_THEN(QX_CHOOSE_THEN `x` (QX_CHOOSE_THEN `y` MP_TAC)) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
    DISCH_THEN (MP_TAC o QAP_TERM `$* (gcd(a,b) EXP n)`) THEN
    REWRITE_TAC[MULT_CLAUSES, LEFT_SUB_DISTRIB] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY QEXISTS_TAC [`x`, `y`] THEN
    REWRITE_TAC[MULT_ASSOC, GSYM MULT_EXP] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THEN
    ASM_REWRITE_TAC[]]);

val GCD_EXP = Qstore_thm("GCD_EXP",
  `!n a b. gcd(a EXP n,b EXP n) = gcd(a,b) EXP n`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIVIDES_EXP THEN REWRITE_TAC[GCD],
    MATCH_MP_TAC DIVIDES_EXP THEN REWRITE_TAC[GCD],
    QX_GEN_TAC `d` THEN STRIP_TAC THEN
    MP_TAC(QSPECL [`n`, `a`, `b`] BEZOUT_GCD_POW) THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (DISJ_CASES_THEN
     (SUBST1_TAC o SYM))) THEN
    MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN ASM_REWRITE_TAC[]]);

val COPRIME_EXP2 = Qstore_thm("COPRIME_EXP2",
  `!n a b. coprime(a EXP (SUC n),b EXP (SUC n)) = coprime(a,b)`,
  REWRITE_TAC[COPRIME_GCD, GCD_EXP] THEN
  INDUCT_TAC THEN ONCE_REWRITE_TAC[EXP] THENL
   [REWRITE_TAC[EXP, MULT_CLAUSES],
    ASM_REWRITE_TAC[MULT_EQ_1]]);

val DIVISION_DECOMP = Qstore_thm("DIVISION_DECOMP",
  `!a b c. a divides (b * c) ==>
     ?b' c'. (a = b' * c') /\ b' divides b /\ c' divides c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  QEXISTS_TAC `gcd(a,b)` THEN REWRITE_TAC[GCD] THEN
  MP_TAC(QSPECL [`a`, `b`] GCD_COPRIME_EXISTS) THEN
  QASM_CASES_TAC `gcd(a,b) = 0` THENL
  [ASM_REWRITE_TAC[] THEN QEXISTS_TAC `1` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GCD_ZERO]) THEN
   ASM_REWRITE_TAC[MULT_CLAUSES, DIVIDES_1],
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(QX_CHOOSE_THEN `a'` (QX_CHOOSE_THEN `b'`
      (STRIP_ASSUME_TAC o GSYM o ONCE_REWRITE_RULE[MULT_SYM]))) THEN
   QEXISTS_TAC `a':num` THEN ASM_REWRITE_TAC[] THEN
   QUNDISCH_TAC `a divides (b * c)` THEN
   FIRST_ASSUM(fn th => PURE_GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)[GSYM th])
   THEN 
   FIRST_ASSUM(fn th => PURE_GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o LAND_CONV)
                           [GSYM th]) THEN REWRITE_TAC[MULT_ASSOC] THEN
   DISCH_TAC THEN MATCH_MP_TAC COPRIME_DIVPROD THEN
   QEXISTS_TAC `b':num` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC DIVIDES_CMUL2 THEN QEXISTS_TAC `gcd(a,b)` THEN
   REWRITE_TAC[MULT_ASSOC] THEN CONJ_TAC THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC]);

val DIVIDES_REV = Qstore_thm("DIVIDES_REV",
  `!n a b. (a EXP n) divides (b EXP n) /\ ~(n = 0) ==> a divides b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QASM_CASES_TAC `gcd(a,b) = 0` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GCD_ZERO]) THEN
    ASM_REWRITE_TAC[DIVIDES_REFL], ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GCD_COPRIME_EXISTS) THEN
  DISCH_THEN(QX_CHOOSE_THEN `a'` (QX_CHOOSE_THEN `b'`
   (STRIP_ASSUME_TAC o GSYM))) THEN
  QUNDISCH_TAC `(a EXP n) divides (b EXP n)` THEN
  DISCH_THEN(QX_CHOOSE_THEN `k` MP_TAC o REWRITE_RULE[divides]) THEN
  FIRST_ASSUM(fn th => PURE_GEN_REWRITE_TAC (funpow 3 LAND_CONV)[GSYM th]) THEN
  FIRST_ASSUM(fn th => PURE_GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o
                                        LAND_CONV o LAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[QSPECL [`x`, `gcd(a,b)`] MULT_SYM] THEN
  REWRITE_TAC[MULT_EXP, GSYM MULT_ASSOC] THEN
  QSUBGOAL_THEN `~(gcd(a,b) EXP n = 0)` MP_TAC THENL
   [QUNDISCH_TAC `~(gcd(a,b) = 0)` THEN
    STRUCT_CASES_TAC(QSPEC `gcd(a,b)` num_CASES) THEN
    REWRITE_TAC[NOT_EXP_0],
    ONCE_REWRITE_TAC[QTAUT_CONV `a ==> b ==> c = a /\ b ==> c`]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MULT_LCANCEL) THEN
  DISCH_TAC THEN QSUBGOAL_THEN `coprime(a' EXP n,b' EXP n)` MP_TAC THENL
   [QUNDISCH_TAC `~(n = 0)` THEN
    STRUCT_CASES_TAC(QSPEC `n` num_CASES) THEN
    ASM_REWRITE_TAC[COPRIME_EXP2], ALL_TAC] THEN
  ASM_REWRITE_TAC[coprime] THEN
  DISCH_THEN(MP_TAC o QSPEC `a' EXP n`) THEN
  REWRITE_TAC[MATCH_MP DIVIDES_RMUL (SPEC_ALL DIVIDES_REFL), DIVIDES_REFL] THEN
  ASM_REWRITE_TAC[EXP_EQ_1] THEN DISCH_THEN SUBST_ALL_TAC THEN
  QUNDISCH_TAC `1 * gcd(a,b) = a` THEN REWRITE_TAC[MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GCD]);

val DIVIDES_MUL = Qstore_thm("DIVIDES_MUL",
  `!m n r. 
       m divides r /\ n divides r /\ coprime(m,n) 
       ==> (m * n) divides r`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  POP_ASSUM(QX_CHOOSE_THEN `d` SUBST1_TAC o REWRITE_RULE[divides])
  THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COPRIME_DIVPROD) THEN
  MATCH_ACCEPT_TAC DIVIDES_MUL_L);

(*---------------------------------------------------------------------------*)
(* Primality                                                                 *)
(*---------------------------------------------------------------------------*)

val prime = Qnew_definition("prime",
  `prime(p) = ~(p = 1) /\ !x. x divides p ==> (x = 1) \/ (x = p)`);

(*---------------------------------------------------------------------------*)
(* A few useful theorems about primes                                        *)
(*---------------------------------------------------------------------------*)

val PRIME_0 = Qstore_thm("PRIME_0",
  `~prime 0`,
  REWRITE_TAC[prime] THEN
  DISCH_THEN(MP_TAC o QSPEC `2` o CONJUNCT2) THEN
  REWRITE_TAC[DIVIDES_0] THEN REDUCE_TAC);

val PRIME_1 = Qstore_thm("PRIME_1",
  `~prime 1`,
  REWRITE_TAC[prime]);

val PRIME_2 = Qstore_thm("PRIME_2",
  `prime 2`,
  REWRITE_TAC[prime] THEN REDUCE_TAC THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REDUCE_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN
  REWRITE_TAC[Qnum_CONV `2`, Qnum_CONV `1`, LESS_THM, NOT_LESS_0] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[DIVIDES_ZERO] THEN
  REDUCE_TAC THEN REWRITE_TAC[]);

val PRIME_GE_2 = Qstore_thm("PRIME_GE_2",
  `!p. prime(p) ==> 2 <= p`,
  GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LESS_EQUAL] THEN
  REWRITE_TAC[Qnum_CONV `2`, Qnum_CONV `1`, 
              LESS_THM, NOT_LESS_0] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[SYM(Qnum_CONV `1`), PRIME_0, PRIME_1]);

val PRIME_FACTOR = Qstore_thm("PRIME_FACTOR",
  `!n. ~(n = 1) ==> ?p. prime(p) /\ p divides n`,
  COMPLETE_INDUCT_TAC THEN
  QX_GEN_TAC `n` THEN REPEAT STRIP_TAC THEN
  QASM_CASES_TAC `prime(n)` THENL
   [QEXISTS_TAC `n` THEN ASM_REWRITE_TAC[DIVIDES_REFL],
    QUNDISCH_TAC `~prime(n)` THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[prime]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
    DISCH_THEN(QX_CHOOSE_THEN `m` MP_TAC) THEN
    REWRITE_TAC[NOT_IMP, DE_MORGAN_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(DISJ_CASES_THEN MP_TAC o MATCH_MP DIVIDES_LE) THENL
     [ASM_REWRITE_TAC[LESS_OR_EQ] THEN
      DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(QX_CHOOSE_THEN `p` STRIP_ASSUME_TAC) THEN
      QEXISTS_TAC `p` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIVIDES_TRANS THEN QEXISTS_TAC `m` THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN SUBST1_TAC THEN QEXISTS_TAC `2` THEN
      REWRITE_TAC[PRIME_2, DIVIDES_0]]]);

val PRIME_FACTOR_LT = Qstore_thm("PRIME_FACTOR_LT",
  `!n m p. prime(p) /\ ~(n = 0) /\ (n = p * m) ==> m < n`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
  ASM_REWRITE_TAC[LESS_EQ_EXISTS] THEN
  DISCH_THEN(QX_CHOOSE_THEN `q` SUBST_ALL_TAC) THEN
  REWRITE_TAC[Qnum_CONV `2`, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
  REWRITE_TAC[ADD_EQ_0] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES]);

val EUCLID = Qstore_thm("EUCLID",
  `!n. ?p. prime(p) /\ p > n`,
  PURE_GEN_REWRITE_TAC I [QTAUT_CONV `x = ~~x`] THEN
  DISCH_THEN(QX_CHOOSE_THEN `n` MP_TAC o CONV_RULE NOT_FORALL_CONV) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  MP_TAC(QSPEC `SUC(FACT n)` PRIME_FACTOR) THEN
  REWRITE_TAC[Qnum_CONV `1`, INV_SUC_EQ, GSYM LESS_EQ_0, NOT_LESS_EQUAL,
    FACT_LESS] THEN DISCH_THEN(QX_CHOOSE_TAC `p`) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o QSPEC `p`) THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(QSPECL [`n`, `p`] LESS_CASES) THEN
  ASM_REWRITE_TAC[GREATER] THEN
  QSUBGOAL_THEN `p divides (FACT n)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIVIDES_FACT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_0] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    EVERY_ASSUM(UNDISCH_TAC o concl) THEN REWRITE_TAC[PRIME_0],
    QSUBGOAL_THEN `p = 1` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM DIVIDES_ONE] THEN MATCH_MP_TAC DIVIDES_ADD_REVR THEN
      QEXISTS_TAC `FACT n` THEN ASM_REWRITE_TAC[GSYM ADD1],
      FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[PRIME_1]]]);

val PRIME_COPRIME = Qstore_thm("PRIME_COPRIME",
  `!n p. prime(p) ==> (n = 1) \/ p divides n \/ coprime(p,n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[prime, COPRIME_GCD] THEN
  STRIP_ASSUME_TAC(QSPECL [`p`, `n`] GCD) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o QSPEC `gcd(p,n)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[]);

val COPRIME_PRIME = Qstore_thm("COPRIME_PRIME",
  `!p a b. coprime(a,b) ==> ~(prime(p) /\ p divides a /\ p divides b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coprime] THEN REPEAT STRIP_TAC THEN
  QSUBGOAL_THEN `p = 1` SUBST_ALL_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
    QUNDISCH_TAC `prime 1` THEN REWRITE_TAC[PRIME_1]]);

val COPRIME_PRIME_EQ = Qstore_thm("COPRIME_PRIME_EQ",
  `!a b. coprime(a,b) = !p. ~(prime(p) /\ p divides a /\ p divides b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP COPRIME_PRIME th]),
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[coprime] THEN
    CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(QX_CHOOSE_THEN `d` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(QX_CHOOSE_TAC `p` o MATCH_MP PRIME_FACTOR) THEN
    QEXISTS_TAC `p` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_TRANS THEN QEXISTS_TAC `d` THEN
    ASM_REWRITE_TAC[]]);

val PRIME_DIVPROD = Qstore_thm("PRIME_DIVPROD",
  `!p a b. prime(p) /\ p divides (a * b) 
           ==> p divides a \/ p divides b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o QSPEC `a` o MATCH_MP PRIME_COPRIME) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN QUNDISCH_TAC `p divides (a * b)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES],
    DISJ2_TAC THEN MATCH_MP_TAC COPRIME_DIVPROD THEN
    QEXISTS_TAC `a` THEN ASM_REWRITE_TAC[]]);

val PRIME_DIVEXP = Qstore_thm("PRIME_DIVEXP",
  `!n p x. prime(p) /\ p divides (x EXP n) ==> p divides x`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[EXP, DIVIDES_ONE] THENL
   [DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[DIVIDES_1],
    DISCH_THEN(fn th => ASSUME_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP PRIME_DIVPROD) THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);

val PRIME_DIVEXP_N = Qstore_thm("PRIME_DIVEXP_N",
  `!n p x. 
       prime(p) /\ p divides (x EXP n) ==> (p EXP n) divides (x EXP n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PRIME_DIVEXP) THEN
  MATCH_ACCEPT_TAC DIVIDES_EXP);

val PARITY_EXP = Qstore_thm("PARITY_EXP",
  `!n x. EVEN(x EXP (SUC n)) = EVEN(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DIVIDES_2] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN
    QEXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[PRIME_2],
    REWRITE_TAC[EXP] THEN MATCH_ACCEPT_TAC DIVIDES_RMUL]);

val COPRIME_SOS = Qstore_thm("COPRIME_SOS",
  `!x y. coprime(x,y) ==> coprime(x * y,(x EXP 2) + (y EXP 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COPRIME_PRIME_EQ] THEN
  CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[] THEN 
  DISCH_THEN(QX_CHOOSE_THEN `p` STRIP_ASSUME_TAC) THEN
  QEXISTS_TAC `p` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(QSPECL [`p`, `x`, `y`] PRIME_DIVPROD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRIME_DIVEXP THEN
  QEXISTS_TAC `2` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIVIDES_ADD_REVR THENL
   [QEXISTS_TAC `x EXP 2`,
    QEXISTS_TAC `y EXP 2` THEN ONCE_REWRITE_TAC[ADD_SYM]] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[Qnum_CONV `2`] THEN
  MATCH_MP_TAC DIVIDES_REXP THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* One property of coprimality is easier to prove via prime factors.         *)
(*---------------------------------------------------------------------------*)

val PRIME_DIVPROD_POW = Qstore_thm("PRIME_DIVPROD_POW",
  `!n p a b. prime(p) /\ coprime(a,b) /\ (p EXP n) divides (a * b)
                ==> (p EXP n) divides a \/ (p EXP n) divides b`,
  REPEAT STRIP_TAC THEN
  QASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[EXP, DIVIDES_1] THEN
  QSUBGOAL_THEN `p divides a \/ p divides b` DISJ_CASES_TAC THENL
   [MATCH_MP_TAC PRIME_DIVPROD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIVIDES_EXP2 THEN QEXISTS_TAC `n` 
    THEN ASM_REWRITE_TAC[],
    DISJ1_TAC THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COPRIME_SYM, MULT_SYM]),
    DISJ2_TAC] THEN
  MATCH_MP_TAC COPRIME_DIVPROD THENL
   [QEXISTS_TAC `b`, QEXISTS_TAC `a`] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  MATCH_MP_TAC COPRIME_EXP THEN
  FIRST_ASSUM(MP_TAC o QSPEC `p` o MATCH_MP COPRIME_PRIME) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THENL
   [FIRST_ASSUM(MP_TAC o QSPEC `b` o MATCH_MP PRIME_COPRIME),
    FIRST_ASSUM(MP_TAC o QSPEC `a` o MATCH_MP PRIME_COPRIME)] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[COPRIME_1]);

val COPRIME_POW = Qstore_thm("COPRIME_POW",
  `!n a b c. coprime(a,b) /\ (a * b = c EXP n) ==>
             ?r s. (a = r EXP n) /\ (b = s EXP n)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (W(curry QSPEC_TAC)) [`a:num`, `b:num`, `n:num`, `c:num`] THEN
  COMPLETE_INDUCT_TAC THEN QX_GEN_TAC `c` THEN
  DISCH_THEN(MP_TAC o CONV_RULE(REDEPTH_CONV RIGHT_IMP_FORALL_CONV)) THEN
  REWRITE_TAC[QTAUT_CONV `a ==> b ==> c = a /\ b ==> c`] THEN
  DISCH_TAC THEN QX_GEN_TAC `n` THEN
  REPEAT GEN_TAC THEN QASM_CASES_TAC `c = 1` THENL
   [ASM_REWRITE_TAC[EXP_1, MULT_EQ_1] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY QEXISTS_TAC [`1`, `1`] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES, EXP_1],
    STRIP_TAC] THEN
  QASM_CASES_TAC `c = 0` THENL
   [QUNDISCH_TAC `a * b = c EXP n` THEN
    STRUCT_CASES_TAC(QSPEC `n` num_CASES) THEN
    ASM_REWRITE_TAC[MULT_EQ_0, EXP, MULT_CLAUSES, MULT_EQ_1] THEN
    STRIP_TAC THEN QUNDISCH_TAC `coprime(a,b)` THEN
    ASM_REWRITE_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_0, COPRIME_0] THEN
    DISCH_TAC THENL
     [MAP_EVERY QEXISTS_TAC [`0`, `1`],
      MAP_EVERY QEXISTS_TAC [`1`, `0`]] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES, MULT_CLAUSES, EXP_1], ALL_TAC] THEN
  FIRST_ASSUM(QX_CHOOSE_THEN `p` MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  STRIP_TAC THEN
  QSUBGOAL_THEN `(p EXP n) divides a \/ (p EXP n) divides b` MP_TAC THENL
   [MATCH_MP_TAC PRIME_DIVPROD_POW THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIVIDES_EXP THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  QUNDISCH_TAC `p divides c` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_TAC `l`) THEN
  QSUBGOAL_THEN `~(p EXP n = 0)` ASSUME_TAC THENL
   [QUNDISCH_TAC `c = p * l` THEN
    REWRITE_TAC[GSYM LESS_EQ_0, NOT_LESS_EQUAL] THEN
    STRUCT_CASES_TAC(QSPEC `p` num_CASES) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES, NOT_SUC, ZERO_LESS_EXP], ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN(QX_CHOOSE_TAC `k`)) THENL
   [QSUBGOAL_THEN `?r s. (k = r EXP n) /\ (b = s EXP n)` STRIP_ASSUME_TAC 
    THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN QEXISTS_TAC `l`,
      MAP_EVERY QEXISTS_TAC [`p * r`, `s`] THEN
      ASM_REWRITE_TAC[MULT_EXP]] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PRIME_FACTOR_LT THEN QEXISTS_TAC `p` THEN
      ASM_REWRITE_TAC[],
      QUNDISCH_TAC `coprime(a,b)` THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
      ASM_REWRITE_TAC[COPRIME_LMUL2],
      MATCH_MP_TAC MULT_LCANCEL THEN QEXISTS_TAC `p EXP n` THEN
      QUNDISCH_TAC `a * b = c EXP n` THEN
      ASM_REWRITE_TAC[MULT_ASSOC, MULT_EXP]],
    QSUBGOAL_THEN `?r s. (a = r EXP n) /\ (k = s EXP n)` STRIP_ASSUME_TAC 
    THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN QEXISTS_TAC `l`,
      MAP_EVERY QEXISTS_TAC [`r`, `p * s`] THEN
      ASM_REWRITE_TAC[MULT_EXP]] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PRIME_FACTOR_LT THEN QEXISTS_TAC `p` THEN
      ASM_REWRITE_TAC[],
      QUNDISCH_TAC `coprime(a,b)` THEN ASM_REWRITE_TAC[COPRIME_LMUL2],
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      MATCH_MP_TAC MULT_LCANCEL THEN QEXISTS_TAC `p EXP n` THEN
      QUNDISCH_TAC `a * b = c EXP n` THEN
      ASM_REWRITE_TAC[MULT_ASSOC, MULT_EXP] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM))]]);

(*---------------------------------------------------------------------------*)
(* Classification of Pythagorean triples.                                    *)
(*---------------------------------------------------------------------------*)

val PYTHAG_EVEN_LEMMA1 = Qstore_thm("PYTHAG_EVEN_LEMMA1",
  `!u v w. ((u EXP 2) + (v EXP 2) = w EXP 2) ==> ~(ODD(u) /\ ODD(v))`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP ODD_SQUARE)) THEN
  ONCE_REWRITE_TAC[(EQT_ELIM o QAC_CONV(ADD_ASSOC,ADD_SYM))
   `(a + b) + (c + d) = (a + c) + (b + d)`] THEN
  DISJ_CASES_THEN MP_TAC (QSPEC `w` EVEN_OR_ODD) THENL
   [DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP EVEN_SQUARE),
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP ODD_SQUARE)] THEN
  REWRITE_TAC[SYM(REDUCE_CONV (--`2 * 2`--))] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB, GSYM TIMES2, GSYM MULT_ASSOC] THEN
  REWRITE_TAC[CANCEL_TIMES2, GSYM ADD1, GSYM NOT_EVEN_EQ_ODD,
    NOT_EVEN_EQ_ODD]);

val PYTHAG_EVEN_LEMMA2 = Qstore_thm("PYTHAG_EVEN_LEMMA2",
  `!u v. coprime(u,v) ==> ~(EVEN(u) /\ EVEN(v))`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[GSYM DIVIDES_2, divides] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GCD_LMUL, COPRIME_GCD, MULT_EQ_1] THEN
  REDUCE_TAC THEN REWRITE_TAC[]);

val PYTHAG_EVEN = Qstore_thm("PYTHAG_EVEN",
  `!u v w. ((u EXP 2) + (v EXP 2) = w EXP 2) /\ coprime(u,v)
        ==> (EVEN(u) /\ ODD(v) /\ ODD(w)) \/
            (ODD(u) /\ EVEN(v) /\ ODD(w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PYTHAG_EVEN_LEMMA1) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PYTHAG_EVEN_LEMMA2) THEN
  REPEAT GEN_TAC THEN MAP_EVERY (DISJ_CASES_TAC o C QSPEC EVEN_OR_ODD)
   [`u`, `v`, `w`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM EVEN_ODD, GSYM ODD_EVEN] THENL
   [DISJ1_TAC, DISJ2_TAC] THEN
  (QSUBGOAL_THEN `~EVEN(w EXP 2)` MP_TAC THENL
    [FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EVEN_ADD], ALL_TAC] THEN
   ASM_REWRITE_TAC[Qnum_CONV `2`, PARITY_EXP] THEN
   ASM_REWRITE_TAC[GSYM ODD_EVEN]));

val PYTHAG_COCLASSIFY = Qstore_thm("PYTHAG_COCLASSIFY",
  `!u v w. ((u EXP 2) + (v EXP 2) = w EXP 2) /\ coprime(u,v) /\
           (EVEN(u) /\ ODD(v) /\ ODD(w)) ==>
                ?p q. coprime(p,q) /\
                      (u = 2 * p * q) /\
                      (v = (p EXP 2) - (q EXP 2)) /\
                      (w = (p EXP 2) + (q EXP 2))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ADD_IMP_SUB) THEN
  REWRITE_TAC[DIFF_SQUARE] THEN RULE_ASSUM_TAC(REWRITE_RULE[ODD_EVEN]) THEN
  QSUBGOAL_THEN `coprime(v,w)` ASSUME_TAC THENL
   [REWRITE_TAC[coprime] THEN QX_GEN_TAC `d` THEN STRIP_TAC THEN
    QSUBGOAL_THEN `d divides u` ASSUME_TAC THENL
     [MATCH_MP_TAC DIVIDES_REV THEN QEXISTS_TAC `2` THEN
      REDUCE_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC DIVIDES_ADD_REVR THEN QEXISTS_TAC `v EXP 2` THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC DIVIDES_EXP THEN ASM_REWRITE_TAC[],
      QUNDISCH_TAC `coprime(u,v)` THEN REWRITE_TAC[coprime] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  QASM_CASES_TAC `u = 0` THENL
   [ASM_REWRITE_TAC[EXP_2, MULT_CLAUSES] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[MULT_EQ_0] o SYM) THEN
    REWRITE_TAC[ADD_EQ_0, SUB_EQ_0] THEN
    DISCH_THEN(DISJ_CASES_TAC) THENL
     [QUNDISCH_TAC `coprime(u,v)` THEN ASM_REWRITE_TAC[COPRIME_0] THEN
      REDUCE_TAC THEN REWRITE_TAC[],
      QUNDISCH_TAC `coprime(u,v)` THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
      ASM_REWRITE_TAC[COPRIME_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY QEXISTS_TAC [`1`, `0`] THEN
      REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, SUB_0] THEN
      QUNDISCH_TAC `(u EXP 2) + (1 EXP 2) = w EXP 2` THEN
      ASM_REWRITE_TAC[EXP_2, MULT_CLAUSES, ADD_CLAUSES] THEN
      DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[MULT_EQ_1] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COPRIME_1]], ALL_TAC] THEN
  QSUBGOAL_THEN `EVEN(w + v)` 
               (QX_CHOOSE_TAC `r` o REWRITE_RULE[EVEN_EXISTS])
  THENL [ASM_REWRITE_TAC[EVEN_ADD], ALL_TAC] THEN
  DISJ_CASES_TAC(QSPECL [`v`, `w`] LESS_EQ_CASES) THENL
   [ALL_TAC,
    FIRST_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[GSYM SUB_EQ_0] th]) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES, EXP_2, MULT_EQ_0]] THEN
  QSUBGOAL_THEN `EVEN(w - v)` (QX_CHOOSE_TAC `s` o REWRITE_RULE[EVEN_EXISTS])
  THENL
   [QUNDISCH_TAC `v <= w` THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
    DISCH_THEN(QX_CHOOSE_THEN `d` SUBST_ALL_TAC) THEN
    QUNDISCH_TAC `~EVEN(v + d)` THEN ASM_REWRITE_TAC[EVEN_ADD] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB], ALL_TAC] THEN
  FIRST_ASSUM(QX_CHOOSE_TAC `t` o REWRITE_RULE[EVEN_EXISTS]) THEN
  ASM_REWRITE_TAC[EXP_2] THEN ONCE_REWRITE_TAC[(EQT_ELIM o QAC_CONV
    (MULT_ASSOC,MULT_SYM)) `(a * b) * (c * d) = (a * c) * (b * d)`] THEN
  REWRITE_TAC[REDUCE_CONV (--`2 * 2`--), Qnum_CONV `4`, MULT_MONO_EQ] THEN
  QSUBGOAL_THEN `coprime(r,s)` ASSUME_TAC THENL
   [REWRITE_TAC[coprime] THEN QX_GEN_TAC `d` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (QX_CHOOSE_TAC `k`) (QX_CHOOSE_TAC `l`))
    THEN MAP_EVERY QUNDISCH_TAC [`w + v = 2 * r`, `w - v = 2 * s`] THEN
    ASM_REWRITE_TAC[QTAUT_CONV `a ==> b ==> c = a /\ b ==> c`] THEN
    DISCH_THEN
     (fn th => let val (t2,t1) = CONJ_PAIR th 
               in MP_TAC(MK_COMB(QAP_TERM `$+` t1, t2)) THEN
                  MP_TAC(MK_COMB(QAP_TERM `$-` t1, t2))
               end) THEN
    FIRST_ASSUM(fn th =>  REWRITE_TAC[MATCH_MP ADD_SUM_DIFF th]) THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB, GSYM LEFT_SUB_DISTRIB] THEN
    REWRITE_TAC[Qnum_CONV `2`, MULT_MONO_EQ] THEN
    REPEAT DISCH_TAC THEN QUNDISCH_TAC `coprime(v,w)` THEN
    ASM_REWRITE_TAC[coprime] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN
    MATCH_ACCEPT_TAC DIVIDES_REFL,
    MP_TAC(QASSUME `coprime(r,s)`) THEN
    REWRITE_TAC[QTAUT_CONV `a ==> b ==> c = a /\ b ==> c`] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM EXP_2] o GSYM) THEN
    DISCH_THEN(MP_TAC o MATCH_MP COPRIME_POW) THEN
    DISCH_THEN(QX_CHOOSE_THEN `p` (QX_CHOOSE_THEN `q`
      (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ADD_SUM_DIFF) THEN
    ASM_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB, GSYM LEFT_SUB_DISTRIB] THEN
    REWRITE_TAC[Qnum_CONV `2`, MULT_MONO_EQ] THEN
    REWRITE_TAC[SYM(Qnum_CONV `2`)] THEN
    DISCH_THEN(CONJUNCTS_THEN(ASSUME_TAC o SYM)) THEN
    MAP_EVERY QEXISTS_TAC [`p`, `q`] THEN
    ASM_REWRITE_TAC[GSYM DIFF_SQUARE, GSYM EXP_2] THEN
    QUNDISCH_TAC `(u EXP 2) + (v EXP 2) = w EXP 2` THEN
    DISCH_THEN(MP_TAC o MATCH_MP ADD_IMP_SUB) THEN
    REWRITE_TAC[DIFF_SQUARE] THEN ASM_REWRITE_TAC[EXP_2] THEN
    ONCE_REWRITE_TAC[(EQT_ELIM o QAC_CONV (MULT_ASSOC,MULT_SYM))
                      `(a * b) * (c * d) = (a * c) * (b * d)`] THEN
    REWRITE_TAC[REDUCE_CONV (--`2 * 2`--), Qnum_CONV `4`, MULT_MONO_EQ] THEN
    ONCE_REWRITE_TAC[(EQT_ELIM o QAC_CONV (MULT_ASSOC,MULT_SYM))
                      `(a * b) * (c * d) = (a * c) * (b * d)`] THEN
    REWRITE_TAC[GSYM EXP_2] THEN REWRITE_TAC[Qnum_CONV `2`] THEN
    REWRITE_TAC[EXP_MONO_EQ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    QUNDISCH_TAC `coprime(p EXP 2,q EXP 2)` THEN
    REWRITE_TAC[Qnum_CONV `2`, COPRIME_EXP2]]);

(*---------------------------------------------------------------------------*)
(* Now the main result                                                       *)
(*---------------------------------------------------------------------------*)

val FLT42_DOWN_LEMMA1 = Qstore_thm("FLT42_DOWN_LEMMA1",
  `!x y z. ~coprime(x,y) /\
           ((x EXP 4) + (y EXP 4) = z EXP 2) /\
           ~(x = 0) /\ ~(y = 0)
        ==> ?u v w. ~(u = 0) /\ ~(v = 0) /\
                    ((u EXP 4) + (v EXP 4) = w EXP 2) /\ w < z`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  QSUBGOAL_THEN `~(z EXP 2 = 0)` MP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP_EQ_0, ADD_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN REDUCE_TAC,
    REWRITE_TAC[EXP_EQ_0] THEN REDUCE_TAC THEN DISCH_TAC] THEN
  REWRITE_TAC[COPRIME_PRIME_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(QX_CHOOSE_THEN `p` STRIP_ASSUME_TAC) THEN
  QSUBGOAL_THEN `(p EXP 2) divides z` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_REV THEN QEXISTS_TAC `2` THEN REDUCE_TAC THEN
    REWRITE_TAC[GSYM EXP_4] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_EXP THEN ASM_REWRITE_TAC[],
    DISCH_THEN(QX_CHOOSE_TAC `w` o REWRITE_RULE[divides])] THEN
  QUNDISCH_TAC `p divides y` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_TAC `v`) THEN
  QUNDISCH_TAC `p divides x` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(QX_CHOOSE_TAC `u`) THEN
  MAP_EVERY QEXISTS_TAC [`u`, `v`, `w`] THEN
  QUNDISCH_TAC `(x EXP 4) + (y EXP 4) = z EXP 2` THEN
  ASM_REWRITE_TAC[MULT_EXP, GSYM EXP_4, GSYM LEFT_ADD_DISTRIB] THEN
  QSUBGOAL_THEN `~(p EXP 4 = 0)` MP_TAC THENL
   [REWRITE_TAC[EXP_EQ_0] THEN REDUCE_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    QUNDISCH_TAC `prime(0)` THEN REWRITE_TAC[PRIME_0],
    REWRITE_TAC[QTAUT_CONV `a ==> b ==> c = a /\ b ==> c`]] THEN
  DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP MULT_LCANCEL th]) THEN
  QUNDISCH_TAC `~(x = 0)` THEN
  ASM_REWRITE_TAC[MULT_EQ_0, DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QUNDISCH_TAC `~(y = 0)` THEN 
  ASM_REWRITE_TAC[MULT_EQ_0, DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN 
  PURE_GEN_REWRITE_TAC LAND_CONV
           [GSYM(el 3 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  QUNDISCH_TAC `~(z = 0)` THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(QSPEC `w` num_CASES) THENL
   [REWRITE_TAC[MULT_CLAUSES],
    DISCH_TAC THEN REWRITE_TAC[LESS_MULT_MONO]] THEN
  QUNDISCH_TAC `prime(p)` THEN
  STRUCT_CASES_TAC(QSPEC `p` num_CASES) THEN
  REWRITE_TAC[PRIME_0, EXP_2] THEN
  REWRITE_TAC[ADD_CLAUSES, MULT_CLAUSES, LESS_MONO_EQ, 
              Qnum_CONV `1`] THEN
  W(STRUCT_CASES_TAC o C SPEC num_CASES o hd o free_vars o snd) THEN
  REWRITE_TAC[SYM(Qnum_CONV `1`), PRIME_1, ADD_CLAUSES, LESS_0]);

val FLT42_DOWN_LEMMA2 = Qstore_thm("FLT42_DOWN_LEMMA2",
  `!x y z. ~(x = 0) /\ ~(y = 0) /\
           ((x EXP 4) + (y EXP 4) = z EXP 2) /\
           coprime(x EXP 2,y EXP 2) /\
           (EVEN(x EXP 2) /\ ODD(y EXP 2) /\ ODD(z))
        ==> ?u v w. ~(u = 0) /\ ~(v = 0) /\
                    ((u EXP 4) + (v EXP 4) = w EXP 2) /\ w < z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP_4] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PYTHAG_COCLASSIFY) THEN
  DISCH_THEN(QX_CHOOSE_THEN `p` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `q` STRIP_ASSUME_TAC) THEN
  QSUBGOAL_THEN `(q EXP 2) + (y EXP 2) = p EXP 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    MATCH_MP_TAC SUB_ADD THEN ONCE_REWRITE_TAC[GSYM NOT_LESS] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LESS_IMP_LESS_OR_EQ) THEN
    REWRITE_TAC[GSYM SUB_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
    ASM_REWRITE_TAC[ODD], ALL_TAC] THEN
  QSUBGOAL_THEN `coprime(q,y)` MP_TAC THENL
   [REWRITE_TAC[COPRIME_PRIME_EQ] THEN QX_GEN_TAC `r` THEN
    STRIP_TAC THEN MP_TAC(QASSUME `coprime(p,q)`) THEN
    REWRITE_TAC[COPRIME_PRIME_EQ] THEN
    DISCH_THEN(MP_TAC o QSPEC `r`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRIME_DIVEXP THEN QEXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fn th => PURE_GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC DIVIDES_ADD THEN
    REWRITE_TAC[Qnum_CONV `2`] THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_REXP THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC 
             o CONJ(QASSUME `(q EXP 2) + (y EXP 2) = p EXP 2`)) THEN
  QSUBGOAL_THEN `ODD(y)` ASSUME_TAC THENL
   [REWRITE_TAC[ODD_EVEN] THEN 
    ONCE_REWRITE_TAC[GSYM(QSPEC `1` PARITY_EXP)] THEN
    REWRITE_TAC[SYM(Qnum_CONV `2`), GSYM ODD_EVEN] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o el 4 o CONJUNCTS), ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PYTHAG_EVEN) THEN
  ASM_REWRITE_TAC[EVEN_ODD] THEN REWRITE_TAC[GSYM EVEN_ODD] THEN STRIP_TAC THEN
  MP_TAC(QSPECL [`q`, `y`, `p`] PYTHAG_COCLASSIFY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(QX_CHOOSE_THEN `a` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `b` STRIP_ASSUME_TAC) THEN
  MP_TAC(QASSUME `x EXP 2 = 2 * p * q`) THEN
  REWRITE_TAC[QASSUME `p = (a EXP 2) + (b EXP 2)`, 
              QASSUME `q = 2 * a * b`] THEN
  QSUBGOAL_THEN `EVEN(x)` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(QSPEC `1` PARITY_EXP)] THEN
    REWRITE_TAC[SYM(Qnum_CONV `2`), GSYM ODD_EVEN] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o el 3 o CONJUNCTS), ALL_TAC] THEN
  REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(QX_CHOOSE_THEN `x2` SUBST_ALL_TAC) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[EXP_2, GSYM MULT_ASSOC]) THEN
  ONCE_REWRITE_TAC[(EQT_ELIM o QAC_CONV (MULT_ASSOC,MULT_SYM))
    `m * n * p * q = (m * p) * n * q`] THEN REDUCE_TAC THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  DISCH_THEN(MP_TAC o CONJ(EQF_ELIM(REDUCE_CONV (--`4 = 0`--)))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MULT_LCANCEL) THEN
  REWRITE_TAC[GSYM EXP_2] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(MATCH_MP COPRIME_SOS (QASSUME `coprime(a,b)`)) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN DISCH_TAC THEN
  MP_TAC(QSPECL [`2`, `(a EXP 2) + (b EXP 2)`, `a * b`, `x2`]
    COPRIME_POW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(QX_CHOOSE_THEN `Z` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `W` STRIP_ASSUME_TAC) THEN
  MP_TAC(QSPECL [`2`, `a`, `b`, `W`] COPRIME_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(QX_CHOOSE_THEN `X` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `Y` (STRIP_ASSUME_TAC o GSYM)) THEN
  MAP_EVERY QEXISTS_TAC [`X`, `Y`, `Z`] THEN 
  ASM_REWRITE_TAC[] THEN
  QSUBGOAL_THEN `~(W = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN QUNDISCH_TAC `a * b = W EXP 2` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    QUNDISCH_TAC `q = 2 * (W EXP 2)` THEN
    ASM_REWRITE_TAC[EXP_2, MULT_CLAUSES] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    QUNDISCH_TAC `(2 * x2) EXP 2 = 2 * p * 0` THEN
    REWRITE_TAC[MULT_CLAUSES, EXP_EQ_0] THEN
    REDUCE_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  QSUBGOAL_THEN `~(X EXP 2 = 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    QUNDISCH_TAC `a * b = W EXP 2` THEN
    ASM_REWRITE_TAC[EXP_2, MULT_CLAUSES, MULT_EQ_0] THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[MULT_EQ_0],
    REWRITE_TAC[EXP_EQ_0] THEN REDUCE_TAC THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  QSUBGOAL_THEN `~(Y EXP 2 = 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    QUNDISCH_TAC `a * b = W EXP 2` THEN
    ASM_REWRITE_TAC[EXP_2, MULT_CLAUSES, MULT_EQ_0] THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[MULT_EQ_0],
    REWRITE_TAC[EXP_EQ_0] THEN REDUCE_TAC THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  QSUBGOAL_THEN `~((2 * (W EXP 2)) EXP 2 = 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[EXP_EQ_0, MULT_EQ_0] THEN REDUCE_TAC, ALL_TAC] THEN
  REWRITE_TAC[GSYM LESS_EQ_0, NOT_LESS_EQUAL] THEN DISCH_TAC THEN
  MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN QEXISTS_TAC `(Z EXP 2) EXP 2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM EXP_4] THEN
    STRUCT_CASES_TAC(QSPEC `Z` num_CASES) THEN
    REWRITE_TAC[EXP_4, EXP_2, MULT_CLAUSES, LESS_EQ_REFL] THEN
    REWRITE_TAC[ADD_CLAUSES, MULT_CLAUSES, LESS_EQ_MONO] THEN
    REWRITE_TAC[GSYM ADD_ASSOC, LESS_EQ_ADD],
    PURE_GEN_REWRITE_TAC LAND_CONV [GSYM ADD_0] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_REWRITE_TAC[LESS_MONO_ADD_EQ]]);

val FLT42 = Qstore_thm("FLT42",
  `!z y x. ((x EXP 4) + (y EXP 4) = z EXP 2) ==> (x = 0) \/ (y = 0)`,
  COMPLETE_INDUCT_TAC THEN QX_GEN_TAC `z` THEN
  CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[NOT_IMP] THEN
  CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[NOT_IMP, DE_MORGAN_THM] THEN
  DISCH_THEN(QX_CHOOSE_THEN `y` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `x` STRIP_ASSUME_TAC) THEN
  QASM_CASES_TAC `coprime(x,y)` THENL
   [MP_TAC(QSPECL [`x EXP 2`, `y EXP 2`, `z`] PYTHAG_EVEN) THEN
    ASM_REWRITE_TAC[GSYM EXP_4] THEN
    ASM_REWRITE_TAC[Qnum_CONV `2`, COPRIME_EXP2] THEN
    REWRITE_TAC[SYM(Qnum_CONV `2`)] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(QSPECL [`x`, `y`,`z`] FLT42_DOWN_LEMMA2) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[Qnum_CONV `2`, COPRIME_EXP2] THEN
      REWRITE_TAC[SYM(Qnum_CONV `2`)],
      MP_TAC(QSPECL [`y`, `x`,`z`] FLT42_DOWN_LEMMA2) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[Qnum_CONV `2`, COPRIME_EXP2] THEN
      REWRITE_TAC[SYM(Qnum_CONV `2`)] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM, ADD_SYM] THEN ASM_REWRITE_TAC[]],
  MP_TAC(QSPECL [`x`, `y`, `z`] FLT42_DOWN_LEMMA1) THEN
  ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(QX_CHOOSE_THEN `u` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `v` MP_TAC) THEN
  DISCH_THEN(QX_CHOOSE_THEN `w` STRIP_ASSUME_TAC) THEN
  QEXISTS_TAC `w` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY QEXISTS_TAC [`v`, `u`] THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* And now at last....                                                       *)
(*---------------------------------------------------------------------------*)

val FLT4 = Qstore_thm("FLT4",
  `!x y z. ((x EXP 4) + (y EXP 4) = z EXP 4) ==> (x = 0) \/ (y = 0)`,
  REPEAT GEN_TAC THEN SUBST1_TAC(QSPEC `z` EXP_4) THEN
  MATCH_ACCEPT_TAC FLT42);

close_theory();

let val {ABS,ASSUME,BETA_CONV,DISCH,INST_TYPE,MP,
         REFL,SUBST,drule,other,...} = Thm.thm_count()
in
   Lib.say("\nTotal inferences = "
            ^Lib.int_to_string(ABS + ASSUME + BETA_CONV + DISCH + INST_TYPE + 
                               MP + REFL + SUBST + drule + other)^"\n")
end;

