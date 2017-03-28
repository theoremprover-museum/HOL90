(* ==================================================================== *)
(* FILE		: mk_automata.sml					*)
(* DESCRIPTION  : Theory of infinite automata and mappings between them *)
(* AUTHOR       : Paul Loewenstein (paul.loewenstein@eng.sun.com)       *)
(* DATE		: 19 February 1993                                      *)
(* ==================================================================== *)

new_theory "automata";

new_parent "zip";
compile "../../src/zip.sig";
compile "../../src/zip.sml";

new_parent "koenig";
load_library {lib = unwind_lib, theory = "-"};
load_library {lib = taut_lib, theory = "-"};

open Zip_lib;
open Unwind;
open Taut;

(* Labelled State Automaton *)

val Trace = new_definition ("Trace",
 (--`Trace (Q:'a#'b->bool,N) e =
   ?s. Q (e 0,s 0) /\ (!t. N (e t,s t) (e (SUC t),s(SUC t)))`--));

(* Trace can describe any behaviour *)

val eq_fun_lemma = TAC_PROOF (([],
  (--`(!x:'a. f x = (g x:'b)) ==> (f = g)`--)),
 DISCH_TAC THEN
 CONV_TAC FUN_EQ_CONV THEN
 POP_ASSUM ACCEPT_TAC);

val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val INDUCTION = theorem "num" "INDUCTION";

val Naive_Lemma = TAC_PROOF (([],
  (--`!P. ?(Q:'a#(num->'a)->bool) N. P = Trace(Q,N)`--)),
 GEN_TAC THEN
 EXISTS_TAC (--`\(e:'a,s:num->'a). P s:bool`--) THEN
 EXISTS_TAC
  (--`\(e:'a,s:num->'a)(e':'a,s':num->'a).
       (e = s 0) /\ (!t. s' t = s (SUC t))`--) THEN
 CONV_TAC FUN_EQ_CONV THEN
 REWRITE_TAC[Trace] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 GEN_TAC THEN
 EQ_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  EXISTS_TAC (--`\t t'. f (t + t'):'a`--) THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES,ETA_AX]
 ,
  SUBGOAL_THEN (--`!t t'.f (t + t') =  (s t' t:'a)`--) ASSUME_TAC THENL
  [
   INDUCT_THEN INDUCTION ASSUME_TAC THENL
   [
    ASM_REWRITE_TAC[ADD_CLAUSES]
   ,
    POP_ASSUM (fn x => REWRITE_TAC [ADD_CLAUSES,
     GEN_ALL (REWRITE_RULE[ADD_CLAUSES] (SPEC (--`SUC t'`--) x))]) THEN
    ASM_REWRITE_TAC[]
   ]
  ,
   POP_ASSUM (ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES] o GEN_ALL o
    SPECL [(--`t:num`--),(--`0`--)]) THEN
   IMP_RES_TAC eq_fun_lemma THEN
   ASM_REWRITE_TAC[]
  ]
 ]);

(* Implementation pre-order *)

val Implements = new_infix_definition ("Implements",
 (--`Implements ((Q1:'a#'a1->bool),N1) ((Q2:'a#'a2->bool),N2) =
       (!e. Trace (Q1,N1) e ==> Trace (Q2,N2) e)`--), 2000);

(* Simulation pre-order *)

val Simulates = new_infix_definition ("Simulates",
 (--`Simulates (Q1,N1) (Q2,N2) =
      (?R.
        (!(e:'a) (s1:'a1). Q1(e,s1) ==> (?s2:'a2. Q2(e,s2) /\ R e s1 s2)) /\
        (!e e' s1 s1' s2.
          R e s1 s2 /\ N1(e,s1)(e',s1') ==>
          (?s2'. R e' s1' s2' /\ N2(e,s2)(e',s2'))))`--), 2000);

val BINDER_CONV = RAND_CONV o ABS_CONV;
val PRIM_REC_THM = theorem "prim_rec" "PRIM_REC_THM";

(* Simulation relation theorem *)

val Sim_imp_Imp = TAC_PROOF (([],
  (--`!(Q1:'a#'a1->bool) (Q2:'a#'a2->bool) N1 N2.
     (Q1,N1) Simulates (Q2,N2) ==>
     (!e. Trace (Q1,N1) e ==> Trace (Q2,N2) e) `--)),
 REWRITE_TAC [Simulates,Trace] THEN
 REPEAT STRIP_TAC THEN
 RES_THEN STRIP_ASSUME_TAC THEN
 ASSUM_LIST 
   (FIRST 
    o (mapfilter (ASSUME_TAC 
                  o GENL [(--`s2:'a2`--),(--`t:num`--)] 
                  o SPECL [(--`(e:num->'a) t`--),
                           (--`e (SUC t):'a`--),
                           (--`(s:num->'a1) t`--),
                           (--`s (SUC t):'a1`--),
                           (--`s2:'a2`--)]))) THEN
 POP_ASSUM
   (STRIP_ASSUME_TAC 
    o CONV_RULE 
        (BINDER_CONV (BINDER_CONV RIGHT_IMP_EXISTS_CONV THENC
                      X_SKOLEM_CONV (--`f2:num->'a2`--)) THENC
                      X_SKOLEM_CONV (--`f2:'a2->num->'a2`--))) THEN
 EXISTS_TAC (--`PRIM_REC (s2:'a2) (f2:'a2->num->'a2)`--) THEN
 CONJ_TAC THENL
 [
  ALL_TAC
 ,
  SUBGOAL_THEN
   (--`!t. R (e (SUC t):'a) 
             (s (SUC t):'a1)
             (PRIM_REC s2 f2(SUC t):'a2) /\
           N2(e t,PRIM_REC s2 f2 t)
             (e(SUC t),PRIM_REC s2 f2 (SUC t))`--)
   ASSUME_TAC THENL
  [
   INDUCT_THEN INDUCTION (STRIP_ASSUME_TAC o REWRITE_RULE[PRIM_REC_THM]) THEN
   UNDISCH_TAC
     (--`!t. N1((e t:'a),(s t:'a1))((e(SUC t):'a),(s(SUC t):'a1))`--) THENL
   [
    DISCH_THEN (ASSUME_TAC o SPEC (--`0`--))
   ,
    DISCH_THEN (ASSUME_TAC o SPEC (--`SUC t`--))
   ] THEN
   RES_TAC
  ,
   ASM_REWRITE_TAC[]
  ]
 ] THEN
 ASM_REWRITE_TAC[PRIM_REC_THM]);

(* Simulation relations are transitive *)

val Sim_Trans = TAC_PROOF (([],
  (--`!(Q1:'a#'a1->bool) N1 (Q2:'a#'a2->bool) N2 (Q3:'a#'a3->bool) N3.
       (Q1,N1) Simulates (Q2,N2) /\ (Q2,N2) Simulates (Q3,N3) ==>
      (Q1,N1) Simulates (Q3,N3)`--)),
 REWRITE_TAC [Simulates] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC
   (--`\(e:'a) (s1:'a1) (s3:'a3). ?s:'a2. R e s1 s /\ R' e s s3`--) THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  RES_TAC THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  RES_THEN STRIP_ASSUME_TAC THEN
  EXISTS_TAC (--`s2':'a3`--) THEN
  CONJ_TAC THENL
  [
   ALL_TAC
  ,
   EXISTS_TAC (--`s2:'a2`--) THEN
   CONJ_TAC
  ]
 ,
  RES_TAC THEN
  RES_TAC THEN
  EXISTS_TAC (--`s2''':'a3`--) THEN
  CONJ_TAC THENL
  [
   EXISTS_TAC (--`s2'':'a2`--) THEN
   CONJ_TAC
  ,
   ALL_TAC
  ]
 ] THEN
 FIRST_ASSUM ACCEPT_TAC);

(* Supplementary invariant *)

val Trace_Inv = new_definition ("Trace_Inv",
 (--`!(Q:('a#'b)->bool) P N e. Trace_Inv (Q,P,N) e =
   (?s. Q(e 0, s 0) /\
        (!t. P(e t, s t)) /\ (!t. N(e t, s t)(e(SUC t),s(SUC t))))`--));

(* Trace_Inv expressible as Trace *)

val Trace_Inv_Trace = TAC_PROOF (([],
  (--`!e (Q:('a#'b)->bool) P N.
      Trace_Inv (Q,P,N) e = Trace (Q,(\s s'. P s /\ N s s')) e`--)),
 REPEAT GEN_TAC THEN
 REWRITE_TAC[Trace_Inv,Trace] THEN
 BETA_TAC THEN
 CONV_TAC (ONCE_DEPTH_CONV FORALL_AND_CONV) THEN
 REFL_TAC);

(* Alternative expression of Trace_Inv *)

val Trace_Inv_Trace' = TAC_PROOF (([],
  (--`!e (Q:('a#'b)->bool) P N.
     Trace_Inv (Q,P,N) e = Trace (Q,(\s s'. P s /\ P s' /\ N s s')) e`--)),
 REPEAT GEN_TAC THEN
 REWRITE_TAC[Trace_Inv,Trace] THEN
 BETA_TAC THEN
 EQ_TAC THEN
 STRIP_TAC THEN
 EXISTS_TAC (--`s:num->'b`--) THEN
 ASM_REWRITE_TAC[]);

(* Introduction of invariant *)

val Trace_imp_Trace_Inv = TAC_PROOF (([], (--`!(Q:('a#'b)->bool) P N.
    (?P'.
      (!e s. Q(e,s) ==> P(e,s) /\ P'(e,s)) /\
      (!e s e' s'.
        N(e,s)(e',s') /\ P(e,s) /\ P'(e,s) ==> P(e',s') /\ P'(e',s'))) ==>
    (!e. Trace (Q,N) e ==> Trace_Inv (Q,P,N) e)`--)),
 REPEAT GEN_TAC THEN
 STRIP_TAC THEN
 REWRITE_TAC[Trace_Inv_Trace] THEN
 MATCH_MP_TAC (REWRITE_RULE[Simulates] Sim_imp_Imp) THEN
 EXISTS_TAC (--`\(e:'a) s1 s2. (s2 = (s1:'b)) /\ P (e,s1) /\ P' (e,s1)`--) THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  EXISTS_TAC (--`s1:'b`--)
 ,
  EXISTS_TAC (--`s1':'b`--)
 ] THEN
 RES_TAC THEN
 ASM_REWRITE_TAC[]);

val Trace_Inv_imp_Trace = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) P N e. Trace_Inv (Q,P,N) e ==> Trace (Q,N) e`--)),
 REWRITE_TAC[Trace_Inv,Trace] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`s:num->'b`--) THEN
 ASM_REWRITE_TAC[]);

(* |- !N P Q.
        (?P'.
          (!e s. Q (e,s) ==> P (e,s) /\ P' (e,s)) /\
          (!e s e' s'.
            N (e,s) (e',s') /\ P (e,s) /\ P' (e,s) ==>
            P (e',s') /\ P' (e',s'))) ==>
        (!e. Trace (Q,N) e = Trace_Inv (Q,P,N) e) *)

val Trace_eq_Trace_Inv' = GEN_ALL (DISCH_ALL (GEN_ALL (IMP_ANTISYM_RULE
 (SPEC_ALL (UNDISCH (SPEC_ALL Trace_imp_Trace_Inv)))
  (SPEC_ALL Trace_Inv_imp_Trace))));

(* |- !Q P N.
      (!e s. Q(e,s) ==> P(e,s)) /\
      (!e s e' s'. N(e,s)(e',s') /\ P(e,s) ==> P(e',s')) ==>
      (!e. Trace(Q,N)e = Trace_Inv(Q,P,N)e) *)

(* Proof differs *)
(* Original 
    val Trace_eq_Trace_Inv = 
           GEN_ALL (REWRITE_RULE[] 
                     (SPEC (--`\x:'a#'b.T`--)
                           (CONV_RULE LEFT_IMP_EXISTS_CONV 
                                      (SPEC_ALL Trace_eq_Trace_Inv'))));
*)
val Trace_eq_Trace_Inv = 
GENL [(--`(Q :'a # 'b -> bool)`--),
      (--`(P :'a # 'b -> bool)`--),
      (--`(N :'a # 'b -> 'a # 'b -> bool)`--) ]
     (REWRITE_RULE[] 
       (SPEC (--`\x:'a#'b.T`--)
           (CONV_RULE LEFT_IMP_EXISTS_CONV (SPEC_ALL Trace_eq_Trace_Inv'))));

(* Properties of Automata *)

val Deterministic = new_definition ("Deterministic",
 (--`Deterministic ((Q:('a#'b)->bool),(N:'a#'b->'a#'b->bool)) =
   (!e s s'. Q (e,s) /\ Q (e,s') ==> (s = s')) /\
   (!e s e' s' s''. N (e,s) (e',s') /\ N (e,s) (e',s'') ==> (s' = s''))`--));

(* Finite Prefix Behaviour *)

val Prefix_Trace = new_definition ("Prefix_Trace",
 (--`Prefix_Trace n (Q:'a#'b->bool,N) e =
   (?s. Q (e 0,s 0) /\ (!t. t < n ==> N (e t,s t) (e (SUC t),s (SUC t))))`--));

(* Prefix Limit Behaviour *)

val Limit_Trace = new_definition ("Limit_Trace",
 (--`Limit_Trace (G:('a#'b->bool)#('a#'b->'a#'b->bool)) e = (!n. Prefix_Trace n G e)`--));

(* Prefix Limit contains Infinite Behaviour *)

val Trace_imp_Limit = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e. Trace (Q,N) e ==> Limit_Trace (Q,N) e`--)),
 REWRITE_TAC[Limit_Trace,Prefix_Trace,Trace] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`s:num->'b`--) THEN
 ASM_REWRITE_TAC[]);

val LESS_EQ = theorem "arithmetic" "LESS_EQ";
val LESS_IMP_LESS_OR_EQ = theorem "arithmetic" "LESS_IMP_LESS_OR_EQ";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";

(* A deterministic automaton's prefix limit behaviour is contained in
   its infinite behaviour *)

val Deterministic_Limit_imp_Trace = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N.
    Deterministic (Q,N) ==>
    (!e. Limit_Trace (Q,N) e ==> Trace (Q,N) e)`--)),
 REWRITE_TAC[Deterministic,Limit_Trace,Prefix_Trace,Trace] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM
  (STRIP_ASSUME_TAC o CONV_RULE (X_SKOLEM_CONV (--`s:num->num->'b`--))) THEN
 EXISTS_TAC (--`\t:num. s t t:'b`--) THEN
 BETA_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE FORALL_AND_CONV) THEN
 CONJ_TAC THENL
 [
  ASM_REWRITE_TAC[]
 ,
  SUBGOAL_THEN
   (--`!t m n. (t <= m) /\ (t <= n) ==> (s m t = (s n t:'b))`--)
    ASSUME_TAC THENL
  [
   INDUCT_THEN INDUCTION ASSUME_TAC THENL
   [
    REPEAT STRIP_TAC THEN
    ANTE_RES_THEN ACCEPT_TAC
     (let val x = ASSUME (--`!n:num. Q((e 0:'a),(s n 0:'b))`--) in
      CONJ (SPEC (--`m:num`--) x) (SPEC (--`n:num`--) x) end)
   ,
    REWRITE_TAC[SYM (SPEC_ALL LESS_EQ)] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    POP_ASSUM (fn x => (POP_ASSUM (fn y =>
     ANTE_RES_THEN ASSUME_TAC (CONJ x y)))) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    RES_TAC
   ]
  ,
   GEN_TAC THEN
   POP_ASSUM (fn x => POP_ASSUM (fn y =>
    ASSUME_TAC (REWRITE_RULE[LESS_SUC_REFL]
     (SPECL [(--`SUC t`--),(--`t:num`--)] y)) THEN
    ASSUME_TAC (REWRITE_RULE[LESS_OR_EQ,LESS_SUC_REFL]
     (SPECL[(--`t:num`--),(--`t:num`--),(--`SUC t`--)] x)))) THEN
   ASM_REWRITE_TAC[]
  ]
 ]);

(* This theorem is trivial *)

val Deterministic_Limit_eq_Trace = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N.
    Deterministic (Q,N) ==>
    (!e. Trace (Q,N) e = Limit_Trace (Q,N) e)`--)),
 REPEAT STRIP_TAC THEN
 EQ_TAC THEN
 STRIP_TAC THENL
 [
  IMP_RES_TAC Trace_imp_Limit
 ,
  IMP_RES_TAC Deterministic_Limit_imp_Trace
 ]);

(* Simulation Relation on Prefix_Trace *)
(* Proved without axiom of choice by induction on length of prefix *)

val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val LESS_SUC = theorem "prim_rec" "LESS_SUC";
val num_CASES = theorem "arithmetic" "num_CASES";
val LESS_THM =  theorem "prim_rec" "LESS_THM";
val NOT_SUC = theorem "num" "NOT_SUC";
val LESS_0 = theorem "prim_rec" "LESS_0";
val INV_SUC_EQ  = theorem "prim_rec" "INV_SUC_EQ";
val LESS_REFL = theorem "prim_rec" "LESS_REFL";
val SUC_LESS = theorem "prim_rec" "SUC_LESS";
val SUC_ID = theorem "prim_rec" "SUC_ID";
val LESS_REFL = theorem "prim_rec" "LESS_REFL";
val LESS_MONO_EQ = theorem "arithmetic" "LESS_MONO_EQ";

val Prefix_Trace_imp_Prefix_Trace = TAC_PROOF (([],
   (--`!(Q1:'a#'a1->bool) (Q2:'a#'a2->bool) N1 N2.
      (?R.
        (!e s1. Q1(e,s1) ==> (?s2. Q2(e,s2) /\ R e s1 s2)) /\
        (!e e' s1 s1' s2.
          R e s1 s2 /\ N1(e,s1)(e',s1') ==>
          (?s2'. R e' s1' s2' /\ N2(e,s2)(e',s2')))) ==>
     (!e n. Prefix_Trace n (Q1,N1) e ==> Prefix_Trace n (Q2,N2) e)`--)),
 REPEAT GEN_TAC THEN
 STRIP_TAC THEN
 GEN_TAC THEN
 REWRITE_TAC [Prefix_Trace] THEN
 SUBGOAL_THEN (--`!n s1.
  Q1((e 0:'a),(s1 0:'a1)) /\
  (!t. t < n ==> N1(e t,s1 t)(e(SUC t),s1(SUC t))) ==>
  (?s2. Q2(e 0,(s2 0:'a2)) /\ (!t. t < n ==> N2(e t,s2 t)(e(SUC t),s2(SUC t))
   /\ R (e t) (s1 t) (s2 t)))`--) ASSUME_TAC THENL
 [
  INDUCT_THEN INDUCTION ASSUME_TAC THENL
  [
   REPEAT STRIP_TAC THEN
   RES_THEN STRIP_ASSUME_TAC THEN
   EXISTS_TAC (--`\t:num. s2:'a2`--) THEN
   ASM_REWRITE_TAC[NOT_LESS_0]
  ,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
    (--`!t. t < n ==> N1((e t:'a),(s1 t:'a1))(e (SUC t),s1(SUC t))`--)
    ASSUME_TAC THENL
   [
    REPEAT STRIP_TAC THEN
    IMP_RES_THEN (ANTE_RES_THEN ACCEPT_TAC) LESS_SUC
   ,
    RES_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`n:num`--) num_CASES) THEN
    POP_ASSUM SUBST_ALL_TAC THENL
    [
     RES_TAC THEN
     ANTE_RES_THEN ASSUME_TAC (SPEC (--`0`--) LESS_SUC_REFL) THEN
     RES_TAC THEN
     EXISTS_TAC (--`\t. (t = 0) => s2'' | s2'''''':'a2`--) THEN
     BETA_TAC THEN
     CONJ_TAC THENL
     [
      ASM_REWRITE_TAC[]
     ,
      GEN_TAC THEN
      DISCH_THEN (ASSUME_TAC o
       REWRITE_RULE[LESS_THM,NOT_LESS_0]) THEN
      ASM_REWRITE_TAC[NOT_SUC]
     ]
    ,
     ANTE_RES_THEN STRIP_ASSUME_TAC (SPEC (--`n':num`--) LESS_SUC_REFL) THEN
     ANTE_RES_THEN ASSUME_TAC (SPEC (--`SUC n':num`--) LESS_SUC_REFL) THEN
     RES_TAC THEN
     EXISTS_TAC
      (--`\t. (t < SUC n') => s2 t | (t = SUC n') => s2''''' | s2'''''''':'a2`--) THEN
     BETA_TAC THEN
     CONJ_TAC THENL
     [
      ASM_REWRITE_TAC[LESS_0]
     ,
      GEN_TAC THEN
      DISCH_THEN (STRIP_ASSUME_TAC o
       REWRITE_RULE[LESS_THM]) THENL
      [
       ASM_REWRITE_TAC[LESS_MONO_EQ,INV_SUC_EQ,LESS_REFL,
        REWRITE_RULE[LESS_REFL](SPECL [(--`n:num`--),(--`n:num`--)] SUC_LESS),SUC_ID]
      ,
       ASM_REWRITE_TAC[LESS_SUC_REFL,LESS_REFL]
      ,
       IMP_RES_THEN (fn x => ASSUME_TAC x THEN ANTE_RES_THEN ASSUME_TAC x)
         LESS_SUC THEN
       ASM_REWRITE_TAC[LESS_MONO_EQ]
      ]
     ]
    ]
   ]
  ]
 ,
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  EXISTS_TAC (--`s2:num->'a2`--) THEN
  REPEAT STRIP_TAC THENL
  [
   FIRST_ASSUM ACCEPT_TAC
  ,
   RES_TAC
  ]
 ]);


val Reachable = new_definition ("Reachable",
 (--`Reachable (Q,N) ((e':'a),(s':'b)) =
   (?n e s. (e n = e') /\ (s n = s') /\ Q(e 0,s 0) /\
     (!t. t < n ==> N (e t,s t) (e (SUC t),s (SUC t))))`--));

val Reachable_Lemma = TAC_PROOF (([],
 (--`!(Q:'a#'b->bool) N e s e' s'. Reachable (Q,N) (e,s) /\
      N (e,s) (e',s') ==> Reachable (Q,N) (e',s')`--)),
 REWRITE_TAC[Reachable] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`SUC n`--) THEN
 EXISTS_TAC (--`\t. t < SUC n => e'' t | e':'a`--) THEN
 EXISTS_TAC (--`\t. t < SUC n => s'' t | s':'b`--) THEN
 BETA_TAC THEN
 ASM_REWRITE_TAC[LESS_REFL,LESS_0,LESS_MONO_EQ] THEN
 REWRITE_TAC[LESS_THM] THEN
 REPEAT STRIP_TAC THENL
 [
  ASM_REWRITE_TAC[LESS_REFL]
 ,
  RES_TAC THEN
  ASM_REWRITE_TAC[]
 ]);

val Finite_State = new_definition ("Finite_State",
 (--`Finite_State ((Q:'a#'b->bool),N) = Finite (Reachable (Q,N))`--));

val Fin_Non_Det = new_definition ("Fin_Non_Det",
 (--`Fin_Non_Det (Q,N) =
 (!e:'a. Finite (\s:'b. (Q(e,s)))) /\
 (!(e:'a) (s:'b) (e':'a). Finite (\s':'b. N (e,s) (e',s')))`--));

val No_Dead = new_definition ("No_Dead",
 (--`No_Dead (Q,N) =
   (!(e:'a) (s:'b). Reachable (Q,N) (e,s) ==> 
    (?e' s'. N (e,s) (e',s')))`--));

val UNZIP = definition "zip" "UNZIP";
val SIMP_REC_THM = theorem "prim_rec" "SIMP_REC_THM";

val No_Dead_THM = TAC_PROOF (([],
  (--`No_Dead (Q,N) =
   (!(e':'a) (s':'b). Reachable (Q,N) (e',s') ==> 
    (?e s. (e 0 = e') /\ (s 0 = s') /\
      (!t. N (e t,s t)  (e (SUC t),s (SUC t)))))`--)),
 REWRITE_TAC[No_Dead] THEN
 EQ_TAC THENL
 [
  REPEAT STRIP_TAC THEN
  EXISTS_TAC (--`FST (UNZIP
   (SIMP_REC (e',s') (\x:'a#'b. @y. N x y)))`--) THEN
  EXISTS_TAC (--`SND (UNZIP
   (SIMP_REC (e',s') (\x:'a#'b. @y. N x y)))`--) THEN
  REWRITE_TAC[UNZIP] THEN
  BETA_TAC THEN
  REWRITE_TAC[SIMP_REC_THM] THEN
  SUBGOAL_THEN
   (--`!t. Reachable (Q,N) (SIMP_REC (e',s') (\x:'a#'b. @y. N x y) t) /\
           N (SIMP_REC (e',s') (\x. @y. N x y) t)
             ((\x. @y. N x y) (SIMP_REC (e',s') (\x. @y. N x y) t))`--)
    (fn x => REWRITE_TAC[x]) THEN
  INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THENL
  [
   ASM_REWRITE_TAC[SIMP_REC_THM] THEN
   BETA_TAC THEN
   POP_ASSUM_LIST (EVERY o map (ASSUME_TAC o CONV_RULE
    (ONCE_DEPTH_CONV (BINDER_CONV (ONCE_DEPTH_CONV (GEN_ALPHA_CONV (--`e'':'a`--) THENC
     (BINDER_CONV (GEN_ALPHA_CONV (--`s'':'b`--))))))))) THEN
   RES_TAC THEN
   POP_ASSUM (ACCEPT_TAC o SELECT_RULE o
    EXISTS (--`?y:'a#'b. N ((e':'a),(s':'b)) y`--,--`(e'':'a),(s'':'b)`--))
  ,
   REWRITE_TAC[SIMP_REC_THM] THEN
   BETA_TAC THEN
   IMP_RES_TAC (REWRITE_RULE[] (SPECL
     [--`Q:'a#'b->bool`--,--`N:'a#'b->'a#'b->bool`--,--`FST (x:'a#'b)`--,
      --`SND (x:'a#'b)`--,--`FST (x':'a#'b)`--,--`SND (x':'a#'b)`--]
     Reachable_Lemma)) THEN
   POP_ASSUM_LIST (EVERY o map (ASSUME_TAC o BETA_RULE)) THEN
   FIRST_ASSUM (IMP_RES_TAC o REWRITE_RULE[] o SPECL
     [--`FST (x:'a#'b)`--,--`SND (x:'a#'b)`--]) THEN
   FIRST_ASSUM (ASSUME_TAC o SELECT_RULE o
     EXISTS(--`?x:'a#'b.N (@y. N (SIMP_REC (e',s') (\x. @y. N x y) t) y) x`--,
       --`(e'''':'a),(s'''':'b)`--)) THEN
   ASM_REWRITE_TAC[]
  ]
 ,
  CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  EXISTS_TAC (--`e' (SUC 0):'a`--) THEN
  EXISTS_TAC (--`s' (SUC 0):'b`--) THEN
  ASM_REWRITE_TAC[]
 ]);
 
val Stuttering = new_definition ("Stuttering",
 (--`Stuttering (Q,N) =
   (!(e:'a) (s:'b). Reachable (Q,N) (e,s) ==> N (e,s) (e,s))`--));

val Stutter_No_Dead = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. Stuttering (Q,N) ==> No_Dead (Q,N)`--)),
 REWRITE_TAC[Stuttering,No_Dead] THEN
 REPEAT STRIP_TAC THEN
 RES_TAC THEN
 EXISTS_TAC (--`e:'a`--) THEN
 EXISTS_TAC (--`s:'b`--) THEN
 ASM_REWRITE_TAC[]);

(* Subset Construction *)

val Subset = new_definition ("Subset",
 (--`Subset ((Q:'a#'b->bool),(N:'a#'b->'a#'b->bool)) =
  ((\(e,x). (!s. x s = Q(e,s)) /\ (?s. x s)),
   (\(e,x) (e',x').
     (!s'. x' s' = (?s. x s /\ N (e,s) (e',s'))) /\ (?s'. x' s')))`--));

(* Subset Construction is Deterministic *)

val Deterministic_Subset = TAC_PROOF (([],
 (--`!(Q:'a#'b->bool) N. Deterministic (Subset (Q,N))`--)),
 REWRITE_TAC[Deterministic,Subset] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REPEAT STRIP_TAC THEN
 CONV_TAC FUN_EQ_CONV THEN
 ASM_REWRITE_TAC[]);

val Powerset = new_definition ("Powerset",
 (--`Powerset ((Q:'a#'b->bool),(N:'a#'b->'a#'b->bool)) =
  ((\(e,x). (!s. x s ==> Q(e,s)) /\ (?s. x s)),
   (\(e,x) (e',x').
     (!s'. x' s' ==> (?s. x s /\ N (e,s) (e',s'))) /\ (?s'. x' s')))`--));

val Subset_sim_Powerset = TAC_PROOF (
  ([],(--`!(Q:'a#'b->bool) N. Subset(Q,N) Simulates Powerset(Q,N)`--)),
 REWRITE_TAC[Subset,Powerset,Simulates] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REPEAT GEN_TAC THEN
 EXISTS_TAC (--`\(e:'a) s1 s2. (!s:'b. s2 s = (s1 s:bool))`--) THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  EXISTS_TAC (--`s1:'b->bool`--) THEN
  REPEAT STRIP_TAC THENL
  [
   RES_TAC
  ,
   EXISTS_TAC (--`s:'b`--) THEN
   FIRST_ASSUM ACCEPT_TAC
  ,
   REFL_TAC
  ]
 ,
  EXISTS_TAC (--`s1':'b->bool`--) THEN
  REPEAT STRIP_TAC THENL
  [
   REFL_TAC
  ,
   RES_TAC THEN
   RES_TAC THEN
   EXISTS_TAC (--`s:'b`--) THEN
   ASM_REWRITE_TAC[]
  ,
   EXISTS_TAC (--`s':'b`--) THEN
   FIRST_ASSUM ACCEPT_TAC
  ]
 ]);
 
val Prefix_imp_Prefix_Subset = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e n.
     Prefix_Trace n (Q,N) e ==> Prefix_Trace n (Subset (Q,N)) e`--)),
 GEN_TAC THEN
 GEN_TAC THEN
 REWRITE_TAC[Subset] THEN
 MATCH_MP_TAC Prefix_Trace_imp_Prefix_Trace THEN
 EXISTS_TAC (--`\(e:'a) (s:'b) x. x s:bool`--) THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  EXISTS_TAC (--`\s:'b.Q(e:'a,s):bool`--) THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THENL
  [
   REFL_TAC
  ,
   EXISTS_TAC (--`s1:'b`--) THEN
   FIRST_ASSUM ACCEPT_TAC
  ,
   FIRST_ASSUM ACCEPT_TAC
  ]
 ,
  EXISTS_TAC (--`\s':'b. ?s:'b. s2 s /\ N (e:'a,s) (e':'a,s')`--) THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THENL
  [
   EXISTS_TAC (--`s1:'b`--) THEN
   ASM_REWRITE_TAC[]
  ,
   REFL_TAC
  ,
   EXISTS_TAC (--`s1':'b`--) THEN
   EXISTS_TAC (--`s1:'b`--) THEN
   ASM_REWRITE_TAC[]
  ]
 ]);

val lemma1 = TAC_PROOF (([],
  (--`!a b c d. ((a /\ b) /\ c ==> d) ==> b ==> a ==> c ==> d`--)),
 REPEAT STRIP_TAC THEN
 RES_TAC);

val Prefix_Powerset_imp_Prefix = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e n.
     Prefix_Trace n (Powerset (Q,N)) e ==> Prefix_Trace n (Q,N) e`--)),
 GEN_TAC THEN
 GEN_TAC THEN
 GEN_TAC THEN
 REWRITE_TAC[Prefix_Trace,Powerset] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 SUBGOAL_THEN (--`!n x.
    ((!s. x 0 s ==> Q(e 0:'a,s)) /\ (?s. x 0 s)) /\
    (!t.
      t < n ==>
      (!s'. x(SUC t)s' ==> (?s. x t s /\ N(e t,s)(e(SUC t),s'))) /\
      (?s'. x(SUC t)s')) ==>
  (!s':'b. x n s' ==>
    (?s. (s n = s') /\ Q(e 0,s 0) /\ (!t. t < n ==>
      N(e t,s t)(e(SUC t),s(SUC t)))))`--) ASSUME_TAC THENL
 [
  INDUCT_THEN INDUCTION ASSUME_TAC THENL
  [
   REPEAT STRIP_TAC THEN
   EXISTS_TAC (--`\t:num. s':'b`--) THEN
   REWRITE_TAC[NOT_LESS_0] THEN
   RES_TAC
  ,
   POP_ASSUM (STRIP_ASSUME_TAC o
    CONV_RULE (ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) o
    GEN_ALL o MATCH_MP lemma1 o SPEC_ALL) THEN
   REPEAT STRIP_TAC THEN
   ANTE_RES_THEN (ASSUME_TAC o CONJUNCT1)
    (SPEC (--`n:num`--) LESS_SUC_REFL) THEN
   RES_TAC THEN
   SUBGOAL_THEN (--`!t.
         t < n ==>
         (!s':'b. x(SUC t)s' ==> (?s. x t s /\ N(e t:'a,s)(e(SUC t),s'))) /\
         (?s'. x(SUC t)s')`--) ASSUME_TAC THENL
   [
    GEN_TAC THEN
    DISCH_TAC THEN
    IMP_RES_THEN (ANTE_RES_THEN ACCEPT_TAC) LESS_SUC
   ,
    POP_ASSUM (ANTE_RES_THEN IMP_RES_TAC) THEN
    EXISTS_TAC (--`\t. t < SUC n => s''' t | s':'b`--) THEN
    BETA_TAC THEN
    REPEAT STRIP_TAC THENL
    [
     REWRITE_TAC[LESS_REFL]
    ,
     ASM_REWRITE_TAC[LESS_0]
    ,
     ASM_CASES_TAC (--`t < n`--) THENL
     [
      ASM_REWRITE_TAC[LESS_MONO_EQ] THEN
      RES_TAC
     ,
      POP_ASSUM (fn x => POP_ASSUM (ASSUME_TAC o REWRITE_RULE[x,LESS_THM])) THEN
      ASM_REWRITE_TAC[LESS_REFL,LESS_SUC_REFL]
     ]
    ]
   ]
  ]
 ,
  GEN_TAC THEN
  CONV_TAC LEFT_IMP_EXISTS_CONV THEN
  GEN_TAC THEN
  DISCH_THEN (fn x =>
   ANTE_RES_THEN STRIP_ASSUME_TAC x THEN STRIP_ASSUME_TAC x) THEN
  STRIP_ASSUME_TAC (SPEC (--`n:num`--) num_CASES) THEN
  POP_ASSUM SUBST_ALL_TAC THENL
  [
   EXISTS_TAC (--`\t:num.s':'b`--) THEN
   RES_TAC THEN
   ASM_REWRITE_TAC[NOT_LESS_0]
  ,
   ANTE_RES_THEN STRIP_ASSUME_TAC (SPEC (--`n':num`--) LESS_SUC_REFL) THEN
   POP_ASSUM (ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
   EXISTS_TAC (--`s'''':num->'b`--) THEN
   ASM_REWRITE_TAC[]
  ]
 ]);

(* This theorem is not really needed *)

val Prefix_Subset_imp_Prefix_Powerset = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e n.
     Prefix_Trace n (Subset (Q,N)) e ==>
     Prefix_Trace n (Powerset (Q,N)) e`--)),
 REWRITE_TAC[Prefix_Trace,Subset,Powerset] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`s:num->('b->bool)`--) THEN
 REPEAT STRIP_TAC THENL
 [
  RES_TAC
 ,
  EXISTS_TAC (--`s':'b`--) THEN
  FIRST_ASSUM ACCEPT_TAC
 ,
  RES_TAC THEN
  EXISTS_TAC (--`s''':'b`--) THEN
  ASM_REWRITE_TAC[]
 ,
  RES_TAC THEN
  EXISTS_TAC (--`s'':'b`--) THEN
  FIRST_ASSUM ACCEPT_TAC
 ]);

(* The following 5 theorems demonstrate a circular implication *)

val Limit_imp_Limit_Subset = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e. Limit_Trace (Q,N) e ==>
      Limit_Trace (Subset (Q,N)) e`--)),
 REWRITE_TAC[Limit_Trace] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
 IMP_RES_TAC Prefix_imp_Prefix_Subset);

(* |- !N Q e. Limit_Trace (Subset (Q,N)) e ==> Trace (Subset (Q,N)) e *)

val Limit_Subset_imp_Trace_Subset = GEN_ALL
 (REWRITE_RULE[Deterministic_Subset]
  (SPECL [(--`FST (Subset (Q:'a#'b->bool,N))`--),(--`SND (Subset (Q:'a#'b->bool,N))`--)]
    (INST_TYPE [{residue = ==`:'b->bool`==,redex = ==`:'b`==}] Deterministic_Limit_imp_Trace)));

(* Odd behaviour here - proof needed to be fixed. *)
(* Original 
 *  val Trace_Subset_imp_Trace_Powerset = TAC_PROOF (([],
 *        (--`!(Q:'a#'b->bool) N e. 
 *            Trace (Subset (Q,N)) e ==> Trace (Powerset (Q,N)) e`--)),
 *   REWRITE_TAC[Trace,Subset,Powerset] THEN
 *   CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 *   REPEAT STRIP_TAC THEN
 *   EXISTS_TAC (--`s:num->('b->bool)`--) THEN
 *   ASM_REWRITE_TAC[] THEN
 *   EXISTS_TAC (--`s':'b`--) THEN
 *   RES_TAC);
*)
(* Old proof, needed to be changed because of change in rewriting. (Fix 
 * of bug in SUB_QCONV underneath abstractions,  August 1993.)
 * val Trace_Subset_imp_Trace_Powerset = TAC_PROOF (([],
 *   (--`!(Q:'a#'b->bool) N e. 
 *       Trace (Subset (Q,N)) e ==> Trace (Powerset (Q,N)) e`--)),
 *  REWRITE_TAC[Trace,Subset,Powerset] THEN
 *  CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 *  REPEAT STRIP_TAC THEN
 *  EXISTS_TAC (--`s:num->('b->bool)`--) THEN
 *  ASM_REWRITE_TAC[] THEN
 *  CONJ_TAC 
 *  THENL [STRIP_TAC, EXISTS_TAC (--`s':'b`--)] THEN
 *  ASM_REWRITE_TAC[]);
 ***)

val Trace_Subset_imp_Trace_Powerset = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e. 
      Trace (Subset (Q,N)) e ==> Trace (Powerset (Q,N)) e`--)),
 REWRITE_TAC[Trace,Subset,Powerset] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`s:num->('b->bool)`--) THEN
 ASM_REWRITE_TAC[] THEN
 EXISTS_TAC (--`s':'b`--) THEN
 RES_TAC);

(* |- !N Q e. Trace (Powerset (Q,N)) e ==> Limit_Trace (Powerset (Q,N)) e *)

val Trace_Powerset_imp_Limit_Powerset = GEN_ALL
 (REWRITE_RULE[]
  (SPECL [(--`FST (Powerset (Q:'a#'b->bool,N))`--),
          (--`SND (Powerset (Q:'a#'b->bool,N))`--)]
    (INST_TYPE [{residue = ==`:'b->bool`==, redex = ==`:'b`==}] Trace_imp_Limit)));

val Limit_Powerset_imp_Limit = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e. Limit_Trace (Powerset (Q,N)) e ==> Limit_Trace (Q,N) e`--)),
 REWRITE_TAC[Limit_Trace] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
 IMP_RES_TAC Prefix_Powerset_imp_Prefix);

(* Powerset construction restricted to finite sets *)

val Finite_Powerset = new_definition ("Finite_Powerset",
 (--`Finite_Powerset ((Q:'a#'b->bool),(N:'a#'b->'a#'b->bool)) =
  ((\(e,x). (!s. x s ==> Q(e,s)) /\ (?s. x s) /\ Finite x),
   (\(e,x) (e',x').
   (!s'. x' s' ==> (?s. x s /\ N (e,s) (e',s'))) /\
   (?s'. x' s') /\ Finite x'))`--));

val Finite = definition "koenig" "Finite";
val Bounded = definition "koenig" "Bounded";
val PAIR = theorem "pair" "PAIR";
val Koenig_Original_Lemma = theorem "koenig" "Koenig_Original_Lemma";

val Trace_Finite_Powerset_eq_Trace = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N e. Trace (Finite_Powerset (Q,N)) e = Trace(Q,N) e`--)),
 REPEAT GEN_TAC THEN
 REWRITE_TAC[Trace,Finite_Powerset] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 EQ_TAC THEN
 STRIP_TAC THENL
 [
  SUBGOAL_THEN (--`!n. Finite ((\n (s':'b,n'). s n s' /\ (n' = n)) n) /\
   (?x. (\n (s',n'). s n s' /\ (n' = n)) n x) /\
   (!x'. (\n (s',n'). s n s' /\ (n' = n)) (SUC n) x' ==>
      (?x. (\n (s',n'). s n s' /\ (n' = n)) n x /\
        (\ (s',n') (s'',n''). N (e n':'a,s') (e n'',s'')) x x'))`--)
   ASSUME_TAC THENL
  [
   GEN_TAC THEN
   REPEAT CONJ_TAC THENL
   [
    REWRITE_TAC[Finite,Bounded] THEN
    PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
    BETA_TAC THEN
    CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
    STRIP_ASSUME_TAC (SPEC (--`n:num`--) num_CASES) THEN
    POP_ASSUM (fn x => SUBST_TAC[x]) THENL
    [
     STRIP_ASSUME_TAC
      (REWRITE_RULE[Finite,Bounded] (ASSUME (--`Finite(s 0:'b->bool)`--))) THEN
     EXISTS_TAC (--`b:num`--) THEN
     EXISTS_TAC (--`\n:num. f n:'b, 0`--)
    ,
     POP_ASSUM (STRIP_ASSUME_TAC o
      REWRITE_RULE[Finite,Bounded] o SPEC (--`n':num`--)) THEN
     EXISTS_TAC (--`b:num`--) THEN
     EXISTS_TAC (--`\n:num. f n:'b, SUC n'`--)
    ] THEN
    BETA_TAC THEN
    REPEAT STRIP_TAC THEN
    RES_TAC THEN
    EXISTS_TAC (--`n:num`--) THEN
    PURE_ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[]
   ,
    PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
    BETA_TAC THEN
    CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
    STRIP_ASSUME_TAC (SPEC (--`n:num`--) num_CASES) THEN
    POP_ASSUM (fn x => SUBST_TAC[x]) THENL
    [
     EXISTS_TAC (--`((s':'b),0)`--) THEN
     ASM_REWRITE_TAC[]
    ,
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`n':num`--)) THEN
     EXISTS_TAC (--`((s'':'b),SUC n')`--) THEN
     ASM_REWRITE_TAC[]
    ]
   ,
    PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
    BETA_TAC THEN
    CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
    REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC THEN
    EXISTS_TAC (--`((s'':'b),(n:num))`--) THEN
    ASM_REWRITE_TAC[]
   ]
  ,
   IMP_RES_TAC Koenig_Original_Lemma THEN
   POP_ASSUM (ASSUME_TAC o PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL PAIR)]) THEN
   POP_ASSUM (ASSUME_TAC o CONV_RULE (REDEPTH_CONV PAIRED_BETA_CONV) o BETA_RULE) THEN
   POP_ASSUM (ASSUME_TAC o REWRITE_RULE[]) THEN
   EXISTS_TAC (--`\t. FST ((a:num->'b#num) t)`--) THEN
   BETA_TAC THEN
   POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE(REDEPTH_CONV FORALL_AND_CONV)) THEN
   ANTE_RES_THEN ASSUME_TAC (SPEC (--`0`--)
    (ASSUME (--`!n. s n (FST ((a:num->'b#num) n))`--))) THEN
   UNDISCH_TAC   (--`!n.
      N ((e (SND ((a:num->'b#num) n)):'a),FST (a n))
        (e (SND (a (SUC n))),FST (a (SUC n)))`--) THEN
   ASM_REWRITE_TAC[]
  ]
 ,
  EXISTS_TAC (--`\(t:num) (x:'b). x = s t`--) THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THENL
  [
   ASM_REWRITE_TAC[]
  ,
   EXISTS_TAC (--`s 0:'b`--) THEN
   REFL_TAC
  ,
   REWRITE_TAC[Finite,Bounded] THEN
   EXISTS_TAC (--`SUC 0`--) THEN
   EXISTS_TAC (--`\n:num.s 0:'b`--) THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC (--`0`--) THEN
   ASM_REWRITE_TAC[LESS_SUC_REFL]
  ,
   EXISTS_TAC (--`(s:num->'b) t`--) THEN
   ASM_REWRITE_TAC[]
  ,
   EXISTS_TAC (--`s (SUC t):'b`--) THEN
   REFL_TAC
  ,
   REWRITE_TAC[Finite,Bounded] THEN
   EXISTS_TAC (--`SUC 0`--) THEN
   EXISTS_TAC (--`\n:num.s (SUC t):'b`--) THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC (--`0`--) THEN
   ASM_REWRITE_TAC[LESS_SUC_REFL]
  ]
 ]);

(* Simulation relation theorem derived from Finite_Powerset construction
  of specification automaton *)

(* This is a theorem even when (Q2,N2) is infinitely nondeterministic *)

(* It can work in prophecy variable situations even when specification
  is a non-safety property *)

(* |- !N2 N1 Q2 Q1.
        (?R.
          (!e s1.
            Q1 (e,s1) ==>
            (?s2.
              ((!s. s2 s ==> Q2 (e,s)) /\ (?s. s2 s) /\ Finite s2) /\
              R e s1 s2)) /\
          (!e e' s1 s1' s2.
            R e s1 s2 /\ N1 (e,s1) (e',s1') ==>
            (?s2'.
              R e' s1' s2' /\
              (!s'. s2' s' ==> (?s. s2 s /\ N2 (e,s) (e',s'))) /\
              (?s'. s2' s') /\
              Finite s2'))) ==>
        (!e. Trace (Q1,N1) e ==> Trace (Q2,N2) e) *)

(* Problem with GEN_ALL.
   Original proof.
*)
   val Sim_imp_Imp' = GEN_ALL
    (REWRITE_RULE[SYM (SPEC_ALL Finite_Powerset),
                  Trace_Finite_Powerset_eq_Trace]
     (CONV_RULE (REDEPTH_CONV PAIRED_BETA_CONV)
      (SPECL
       [(--`Q1:'a#'a1->bool`--),
        (--`(\(e:'a,x). (!s:'a2. x s ==> Q2(e,s))/\(?s. x s) /\ Finite x)`--),
        (--`N1:'a#'a1->'a#'a1->bool`--),
        (--`(\(e:'a,x) (e':'a,x').
            (!s':'a2. x' s' ==> (?s:'a2. x s /\ N2 (e,s) (e',s'))) /\
           (?s'. x' s') /\ Finite x')`--)]
       (INST_TYPE [{residue = ==`:'a2->bool`==, redex = ==`:'a2`==}] 
                  Sim_imp_Imp))));

(* val Sim_imp_Imp' = 
   GENL [(--`N2:'a#'a2->'a#'a2->bool`--),
         (--`N1:'a#'a1->'a#'a1->bool`--),
         (--`Q2 :'a # 'a2 -> bool`--),
         (--`Q1:'a#'a1->bool`--)]

    (REWRITE_RULE[SYM (SPEC_ALL Finite_Powerset),
                  Trace_Finite_Powerset_eq_Trace]
     (CONV_RULE (REDEPTH_CONV PAIRED_BETA_CONV)
      (SPECL
       [(--`Q1:'a#'a1->bool`--),
        (--`(\(e:'a,x). (!s:'a2. x s ==> Q2(e,s))/\(?s. x s) /\ Finite x)`--),
        (--`N1:'a#'a1->'a#'a1->bool`--),
        (--`(\(e:'a,x) (e':'a,x').
            (!s':'a2. x' s' ==> (?s:'a2. x s /\ N2 (e,s) (e',s'))) /\
           (?s'. x' s') /\ Finite x')`--)]
       (INST_TYPE [{residue = ==`:'a2->bool`==, redex = ==`:'a2`==}] 
                  Sim_imp_Imp))));
*)
val Infinite_Path = definition "koenig" "Infinite_Path";
val Zip = theorem "zip" "Zip";
val PRE = theorem "prim_rec" "PRE";
val PAIR_EQ = theorem "pair" "PAIR_EQ";

val Trace_Infinite_Path = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. Trace (Q,N) e =
     Infinite_Path (0,x) (\(t,s) (t',s'). (t' = SUC t) /\ ((t = 0) => Q (e 0,s') | N (e (PRE t),s) (e t,s')))`--)),
 REWRITE_TAC[Trace,Infinite_Path] THEN
 REPEAT GEN_TAC THEN
 CONV_TAC (ONCE_DEPTH_CONV (EXISTS_ZIP_CONV (--`t:num->num`--,--`s:num->'b`--))) THEN
 REWRITE_TAC[Zip,PAIR_EQ] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 EQ_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  EXISTS_TAC (--`\t. t:num`--) THEN
  EXISTS_TAC (--`\t. (t = 0) => x | s (PRE t):'b`--) THEN
  BETA_TAC THEN
  REWRITE_TAC[] THEN
  GEN_TAC THEN
  STRIP_ASSUME_TAC (SPEC (--`d:num`--) num_CASES) THEN
  ASM_REWRITE_TAC[PRE,NOT_SUC]
 ,
  EXISTS_TAC (--`\t. s (SUC t):'b`--) THEN
  BETA_TAC THEN
  SUBGOAL_THEN (--`!n:num. t n = n`--) ASSUME_TAC THENL
  [
   INDUCT_TAC THEN
   ASM_REWRITE_TAC[]
  ,
   CONJ_TAC THENL
   [
    POP_ASSUM (fn x => POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[x] o SPEC(--`0`--)))
   ,
    GEN_TAC THEN
    POP_ASSUM (fn x => POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[x,PRE,NOT_SUC] o SPEC(--`SUC t'`--)))
   ]
  ]
 ]);

val Unbounded_Path = definition "koenig" "Unbounded_Path";
val LESS_MONO_REV = theorem "arithmetic" "LESS_MONO_REV";
val LESS_MONO = theorem "prim_rec" "LESS_MONO";

val Limit_Unbounded = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. 
      Limit_Trace (Q,N) e =
      Unbounded_Path (0,x) (\(t,s) (t',s'). 
                               (t' = SUC t) /\ 
                               ((t = 0) 
                                => Q (e 0,s') 
                                 | N (e (PRE t),s) (e t,s')))`--)),
 REWRITE_TAC[Limit_Trace,Prefix_Trace,Unbounded_Path] THEN
 REPEAT GEN_TAC THEN
 CONV_TAC (ONCE_DEPTH_CONV (EXISTS_ZIP_CONV (--`t:num->num`--,--`s:num->'b`--))) THEN
 REWRITE_TAC[Zip,PAIR_EQ] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 EQ_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`PRE n`--)) THEN
  EXISTS_TAC (--`\t. t:num`--) THEN
  EXISTS_TAC (--`\t. (t = 0) => x | s (PRE t):'b`--) THEN
  BETA_TAC THEN
  REWRITE_TAC[] THEN
  GEN_TAC THEN
  RES_TAC THEN
  STRIP_ASSUME_TAC (SPEC (--`d:num`--) num_CASES) THEN
  POP_ASSUM SUBST1_TAC THENL
  [
   ASM_REWRITE_TAC[PRE,NOT_SUC]
  ,
   STRIP_ASSUME_TAC (SPEC (--`n:num`--) num_CASES) THEN
   POP_ASSUM SUBST_ALL_TAC THENL
   [
    REWRITE_TAC[NOT_LESS_0]
   ,
    FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[PRE]) THEN
    STRIP_TAC THEN
    IMP_RES_TAC LESS_MONO_REV THEN
    RES_TAC THEN
    ASM_REWRITE_TAC[NOT_SUC,PRE]
   ]
  ]
 ,
  POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`SUC n`--)) THEN
  EXISTS_TAC (--`\t. s (SUC t):'b`--) THEN
  BETA_TAC THEN
  CONJ_TAC THENL
  [
   ANTE_RES_THEN MP_TAC (SPEC (--`n:num`--) LESS_0) THEN
   ASM_REWRITE_TAC[] THEN
   STRIP_TAC
  ,
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LESS_MONO THEN
   RES_TAC THEN
   SUBGOAL_THEN (--`!m. m < SUC n ==> (t m = m)`--) ASSUME_TAC THENL
   [
   INDUCT_TAC THENL
    [
     ASM_REWRITE_TAC[]
    ,
     STRIP_TAC THEN
     IMP_RES_TAC SUC_LESS THEN
     RES_TAC THEN
     ASM_REWRITE_TAC[]
    ]
   ,
    RES_TAC THEN
    UNDISCH_TAC (--`(t (SUC t') = 0)
    => (Q ((e 0:'a),(s (SUC (SUC t')):'b)))
    | (N (e (PRE (t (SUC t'))),s (SUC t'))
        (e (t (SUC t')),s (SUC (SUC t')))):bool`--) THEN
    ASM_REWRITE_TAC[NOT_SUC,PRE]
   ]
  ]
 ]);

val Fin_Non_Det_lemma = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. Fin_Non_Det (Q,N) ==>
     (!e x. Finite ((\(t,s) (t',s'). (t' = SUC t) /\ ((t = 0) => Q (e 0,s') | N (e (PRE t),s) (e t,s'))) x))`--)),
 REWRITE_TAC[Fin_Non_Det,Finite,Bounded] THEN
 CONV_TAC (REDEPTH_CONV (PAIR_FORALL_CONV (--`t:num`--,--`s:'b`--))) THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THEN
 STRIP_ASSUME_TAC (SPEC (--`t:num`--) num_CASES) THEN
 POP_ASSUM SUBST_ALL_TAC THENL
 [
  POP_ASSUM_LIST (EVERY o map (STRIP_ASSUME_TAC o SPEC (--`e 0:'a`--))) THEN
  EXISTS_TAC (--`b:num`--) THEN
  EXISTS_TAC (--`\n:num. (SUC 0,(f n:'b))`--) THEN
  BETA_TAC THEN
  REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  EXISTS_TAC (--`n:num`--) THEN
  ASM_REWRITE_TAC[] 
 ,
  FIRST_ASSUM (STRIP_ASSUME_TAC o SPECL[--`(e:num->'a) n`--,--`s:'b`--,--`e (SUC n):'a`--]) THEN
  EXISTS_TAC (--`b:num`--) THEN
  EXISTS_TAC (--`\n':num. (SUC (SUC n),(f n':'b))`--) THEN
  BETA_TAC THEN
  REWRITE_TAC[PRE,NOT_SUC] THEN
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  EXISTS_TAC (--`n':num`--) THEN
  ASM_REWRITE_TAC[] 
 ]);

val Koenig_Digraph_Lemma = theorem "koenig" "Koenig_Digraph_Lemma";

val Fin_Non_Det_Powerset_Trace = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N.
         Fin_Non_Det (Q,N) ==>
         (!e. Trace (Powerset (Q,N)) e ==> Trace (Q,N) e)`--)),
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC Trace_Powerset_imp_Limit_Powerset THEN
 IMP_RES_TAC Limit_Powerset_imp_Limit THEN
 IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) Limit_Unbounded THEN
 IMP_RES_THEN (ASSUME_TAC o GEN (--`x:num#'b`--) o SPEC_ALL) Fin_Non_Det_lemma THEN
 IMP_RES_TAC Koenig_Digraph_Lemma THEN
 IMP_RES_TAC Trace_Infinite_Path);

val Fin_Sim_Powerset_imp_Imp = TAC_PROOF (([],
  (--`!(Q1:'a#'a1->bool) N1 (Q2:'a#'a2->bool) N2.
         Fin_Non_Det (Q2,N2) ==>
         (Q1,N1) Simulates (Powerset (Q2,N2)) ==>
         (!e. (Trace (Q1,N1)) e ==> Trace (Q2,N2) e)`--)),
 PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC Sim_imp_Imp THEN
 POP_ASSUM_LIST (EVERY o map (ASSUME_TAC o REWRITE_RULE[])) THEN
 REWRITE_TAC[] THEN
 IMP_RES_TAC Fin_Non_Det_Powerset_Trace); 

val Deterministic_lemma = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. Deterministic (Q,N) ==> (!e s s' n.
       (Q (e 0, s 0) /\ (!t. t < n ==> N (e t,s t) (e (SUC t),s (SUC t)))) /\
       (Q (e 0, s' 0) /\
       (!t. t < n ==> N (e t,s' t) (e (SUC t),s' (SUC t)))) ==>
       (!t. t < SUC n ==> (s t = s' t)))`--)),
 REWRITE_TAC[Deterministic] THEN
 REPEAT GEN_TAC THEN
 STRIP_TAC THEN
 GEN_TAC THEN
 GEN_TAC THEN
 GEN_TAC THEN
 INDUCT_TAC THENL
 [
  REWRITE_TAC[LESS_THM,NOT_LESS_0] THEN
  DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]
 ,
  PURE_ONCE_REWRITE_TAC[LESS_THM] THEN
  REWRITE_TAC [TAUT_PROVE
   (--`a \/ b ==> c = (a ==> c) /\ (b ==> c)`--)] THEN
  CONV_TAC (ONCE_DEPTH_CONV FORALL_AND_CONV) THEN
  REPEAT STRIP_TAC THENL
  [
   ASM_REWRITE_TAC[] THEN
   RES_TAC THEN
   ASSUM_LIST (EVERY o mapfilter
    (ASSUME_TAC o REWRITE_RULE[LESS_SUC_REFL] o SPEC (--`n:num`--))) THEN
   ASSUM_LIST (FIRST o mapfilter SUBST_ALL_TAC) THEN
   RES_TAC   
  ,
   RES_TAC
  ]
 ]);

val LESS_MONO = theorem "prim_rec" "LESS_MONO";
val LESS_CASES = theorem "arithmetic" "LESS_CASES"; 
val LESS_OR = theorem "arithmetic" "LESS_OR";
val LESS_EQ_ADD_SUB = theorem "arithmetic" "LESS_EQ_ADD_SUB";
val ADD_SYM = theorem "arithmetic" "ADD_SYM";
val ADD1 = theorem "arithmetic" "ADD1";
val LESS_SUC_NOT = theorem "arithmetic" "LESS_SUC_NOT";
val SUB_EQUAL_0 = theorem "arithmetic" "SUB_EQUAL_0";


val Complete_Deterministic = TAC_PROOF (([],
  (--`!(Q1:'a#'a1->bool) (Q2:'a#'a2->bool) N1 N2.
      No_Dead (Q1,N1) /\
      Deterministic (Q2,N2) ==>
      (!e. Trace (Q1,N1) e ==> Trace (Q2,N2) e) ==>
      ((Q1,N1) Simulates (Q2,N2))`--)),
 REWRITE_TAC[Trace,No_Dead_THM,Reachable,Simulates] THEN
 CONV_TAC (REDEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`\(e':'a) (s1':'a1) (s2':'a2).
  ?n e s1 s2. (e n = e') /\ (s1 n = s1') /\ (s2 n = s2') /\
  Q1 (e 0, s1 0) /\ Q2 (e 0, s2 0) /\
  (!t. N1 (e t, s1 t) (e (SUC t), s1 (SUC t)) /\
     N2 (e t, s2 t) (e (SUC t), s2 (SUC t)))`--) THEN
 BETA_TAC THEN
 CONJ_TAC THENL
 [
  REPEAT STRIP_TAC THEN
  ASSUM_LIST (FIRST o mapfilter (IMP_RES_TAC o REWRITE_RULE[NOT_LESS_0] o
   BETA_RULE o SPECL [--`e:'a`--,--`s1:'a1`--,--`0`--,
          --`\n:num.e:'a`--,--`\n:num.s1:'a1`--])) THEN
  UNDISCH_TAC (--`Q1 ((e:'a),(s1:'a1)):bool`--) THEN
  ASSUM_LIST (REWRITE_TAC o mapfilter SYM) THEN
  DISCH_TAC THEN 
  RES_TAC THEN
  EXISTS_TAC (--`s' 0:'a2`--) THEN
  CONJ_TAC THENL
  [
   FIRST_ASSUM ACCEPT_TAC
  ,
   EXISTS_TAC (--`0`--) THEN
   EXISTS_TAC (--`e'':num->'a`--) THEN  (* changed to get to run in v5 hol90 *)
   EXISTS_TAC (--`s:num->'a1`--) THEN
   EXISTS_TAC (--`s':num->'a2`--) THEN
   ASM_REWRITE_TAC[]
  ]
 ,
  REPEAT STRIP_TAC THEN
  ASSUM_LIST (FIRST o mapfilter (ASSUME_TAC o
   REWRITE_RULE[LESS_REFL,LESS_0] o
   BETA_RULE o SPECL [--`e':'a`--,--`s1':'a1`--,--`SUC n`--,
     --`\t:num.t < SUC n => e'' t | e':'a`--,
     --`\t:num.t < SUC n => s1'' t | s1':'a1`--])) THEN
  POP_ASSUM IMP_RES_TAC THEN
  FIRST_ASSUM (fn x => SUBGOAL_THEN (#ant(dest_imp (concl x)))
   (ANTE_RES_THEN STRIP_ASSUME_TAC)) THENL
  [
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[LESS_THM]) THENL
   [
    ASM_REWRITE_TAC[LESS_REFL]
   ,
    IMP_RES_TAC LESS_MONO THEN
    ASM_REWRITE_TAC[]
   ]
  ,
   ASSUM_LIST (FIRST o mapfilter (ASSUME_TAC o REWRITE_RULE[LESS_0] o
    BETA_RULE o SPECL
    [--`\t:num.t < SUC n => e'' t | e''' (t - SUC n):'a`--,
     --`\t:num.t < SUC n => s1'' t | s (t - SUC n):'a1`--])) THEN
   FIRST_ASSUM IMP_RES_TAC THEN
   FIRST_ASSUM (fn x => SUBGOAL_THEN (#ant(dest_imp (concl x)))
    ASSUME_TAC) THENL
   [
    GEN_TAC THEN
    STRIP_ASSUME_TAC (REWRITE_RULE[LESS_OR_EQ]
     (SPECL [--`t:num`--,--`n:num`--] LESS_CASES)) THENL
    [
     IMP_RES_TAC LESS_MONO THEN
     IMP_RES_TAC LESS_SUC THEN
     ASM_REWRITE_TAC[]
    ,
     IMP_RES_TAC LESS_OR THEN
     IMP_RES_TAC LESS_EQ_ADD_SUB THEN
     POP_ASSUM (ASSUME_TAC o
      REWRITE_RULE[PURE_ONCE_REWRITE_RULE[ADD_SYM] (SYM (SPEC_ALL ADD1))] o
      SPEC (--`1`--)) THEN
     IMP_RES_TAC LESS_SUC THEN
     IMP_RES_TAC LESS_SUC_NOT THEN
     ASM_REWRITE_TAC[]
    ,
     POP_ASSUM SUBST_ALL_TAC THEN
     ASM_REWRITE_TAC[SUB_EQUAL_0,LESS_SUC_REFL,LESS_REFL]
    ]
   ,
    FIRST_ASSUM (ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`s' (SUC n):'a2`--) THEN
    CONJ_TAC THENL
    [
     EXISTS_TAC (--`SUC n`--) THEN
     EXISTS_TAC (--`\t. (t < SUC n) => (e'' t) | (e''' (t - SUC n)):'a`--) THEN
     EXISTS_TAC (--`\t. (t < SUC n) => (s1'' t) | (s (t - SUC n)):'a1`--) THEN
     EXISTS_TAC (--`s':num->'a2`--) THEN
     BETA_TAC THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[LESS_REFL,SUB_EQUAL_0,LESS_0] THEN
     ASM_REWRITE_TAC[]
    ,
     FIRST_ASSUM (ASSUME_TAC o MATCH_MP Deterministic_lemma) THEN
     POP_ASSUM (ASSUME_TAC o SPECL [--`e'':num->'a`--,--`s2':num->'a2`-- ,
     --`s':num->'a2`--,--`n:num`--]) THEN
     FIRST_ASSUM (fn x => SUBGOAL_THEN (#ant(dest_imp (concl x)))
      ASSUME_TAC) THENL
     [
      REPEAT STRIP_TAC THENL
      [
       FIRST_ASSUM ACCEPT_TAC
      ,
       ASM_REWRITE_TAC[]
      ,
       FIRST_ASSUM ACCEPT_TAC
      ,
       UNDISCH_TAC (--`!t.
       N2 (((t < SUC n) => (e'' t) | (e''' (t - SUC n)):'a),(s' t:'a2))
        (((SUC t < SUC n) => (e'' (SUC t)) | (e''' (SUC t - SUC n))),
        s' (SUC t))`--) THEN
       DISCH_THEN (MP_TAC o (SPEC (--`t:num`--))) THEN
       IMP_RES_TAC LESS_SUC THEN
       IMP_RES_TAC LESS_MONO THEN
       ASM_REWRITE_TAC[]
      ]
     ,
      POP_ASSUM (ANTE_RES_THEN ASSUME_TAC) THEN
      POP_ASSUM
       (ASSUME_TAC o REWRITE_RULE[LESS_SUC_REFL] o SPEC (--`n:num`--)) THEN
      UNDISCH_TAC (--`!t.
       N2 (((t < SUC n) => (e'' t) | (e''' (t - SUC n)):'a),(s' t:'a2))
        (((SUC t < SUC n) => (e'' (SUC t)) | (e''' (SUC t - SUC n))),
        s' (SUC t))`--) THEN
      DISCH_THEN (MP_TAC o (SPEC (--`n:num`--))) THEN
      REWRITE_TAC [LESS_SUC_REFL,LESS_REFL] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[SUB_EQUAL_0]
     ]
    ]
   ]
  ]
 ]);

val Simulates_Subset_Powerset = TAC_PROOF (([],
  (--`!(Q1:'a#'a1->bool) N1 (Q2:'a#'a2->bool) N2.
         (Q1,N1) Simulates (Subset (Q2,N2)) ==>
         (Q1,N1) Simulates (Powerset (Q2,N2))`--)),
 REWRITE_TAC[Simulates,Subset,Powerset] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`R:'a->'a1->('a2->bool)->bool`--) THEN
 REPEAT STRIP_TAC THENL
 [
  RES_TAC THEN
  EXISTS_TAC (--`s2:'a2->bool`--) THEN
  REPEAT STRIP_TAC THENL
  [
   RES_TAC
  ,
   EXISTS_TAC (--`s:'a2`--) THEN
   FIRST_ASSUM ACCEPT_TAC
  ,
   FIRST_ASSUM ACCEPT_TAC
  ]
 ,
  RES_TAC THEN
  EXISTS_TAC (--`s2':'a2->bool`--) THEN
  REPEAT STRIP_TAC THENL
  [
   FIRST_ASSUM ACCEPT_TAC
  ,
   RES_TAC THEN
   EXISTS_TAC (--`s'''':'a2`--) THEN
   ASM_REWRITE_TAC[]
  ,
   EXISTS_TAC (--`s':'a2`--) THEN
   FIRST_ASSUM ACCEPT_TAC
  ]
 ]);

val Complete_No_Dead = TAC_PROOF (([],
  (--`!(Q1:'a#'a1->bool) N1 (Q2:'a#'a2->bool) N2.
         No_Dead (Q1,N1) /\ (!e. Trace (Q1,N1) e ==> Trace (Q2,N2) e) ==>
         (Q1,N1) Simulates (Powerset (Q2,N2))`--)),
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN (--`!e. Trace ((Q1:'a#'a1->bool),N1) e ==> Trace (Subset((Q2:'a#'a2->bool),N2)) e`--)
  (ASSUME_TAC o (CONV_RULE (BINDER_CONV (RAND_CONV (ONCE_DEPTH_CONV (PURE_ONCE_REWRITE_CONV [SYM (SPEC_ALL PAIR)])))))) THENL
 [
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  IMP_RES_TAC Trace_imp_Limit THEN
  IMP_RES_TAC Limit_imp_Limit_Subset THEN
  IMP_RES_TAC Limit_Subset_imp_Trace_Subset  
 ,
  SUBGOAL_THEN
   (--`Deterministic (FST(Subset((Q2:'a#'a2->bool),N2)),SND(Subset((Q2:'a#'a2->bool),N2)))`--) ASSUME_TAC THENL
  [
   REWRITE_TAC[Deterministic_Subset]
  ,
   IMP_RES_TAC Complete_Deterministic THEN
   POP_ASSUM (ASSUME_TAC o REWRITE_RULE[]) THEN
   IMP_RES_TAC Simulates_Subset_Powerset
  ]
 ]);

(* Alternative treatment of finite non-determinism not using intermediate results from koenig *)

val Finite_EQ = theorem "koenig" "Finite_EQ";
val LESS_IMP_LESS_ADD = theorem "arithmetic" "LESS_IMP_LESS_ADD";
val LESS_MONO_ADD = theorem "arithmetic" "LESS_MONO_ADD";
val LESS_EQ_ADD = theorem "arithmetic" "LESS_EQ_ADD";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val ADD_SUB = theorem "arithmetic" "ADD_SUB";
val INDUCTION = theorem "num" "INDUCTION";
val LESS_MONO_ADD_EQ = theorem "arithmetic" "LESS_MONO_ADD_EQ";
val SUB_ADD = theorem "arithmetic" "SUB_ADD";

val Subset_Simulates_Finite_Powerset = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. Fin_Non_Det (Q,N) ==>
         Subset (Q,N) Simulates Finite_Powerset (Q,N)`--)),
 REWRITE_TAC[Fin_Non_Det,Subset,Finite_Powerset,Simulates,Finite_EQ] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`\(e:'a) (s1:'b->bool) s2. Finite s1 /\ (s2 = s1)`--) THEN
 REWRITE_TAC[Finite_EQ] THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  EXISTS_TAC (--`s1:'b->bool`--) THEN
  REPEAT STRIP_TAC THENL
  [
   RES_TAC
  ,
   EXISTS_TAC (--`s:'b`--) THEN
   FIRST_ASSUM ACCEPT_TAC
  ,
   ASM_REWRITE_TAC[]
  ,
   ASM_REWRITE_TAC[]
  ,
   REFL_TAC
  ]
 ,
  EXISTS_TAC (--`s1':'b->bool`--) THEN
  REWRITE_TAC[TAUT_PROVE(--`a /\ b /\ c /\ a = a /\ b /\ c`--)] THEN
  REPEAT STRIP_TAC THENL
  [
   CONV_TAC (GEN_ALPHA_CONV (--`b':num`--)) THEN
   CONV_TAC (ONCE_DEPTH_CONV (GEN_ALPHA_CONV (--`f':num->'b`--))) THEN
   ASM_REWRITE_TAC[] THEN
   POP_ASSUM_LIST (EVERY o (map ASSUME_TAC o filter (not o mem (--`b:num`--) o free_vars o concl))) THEN
   SPEC_TAC (--`b:num`--,--`b:num`--) THEN
   INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THENL
   [
    EXISTS_TAC (--`0`--) THEN
    REWRITE_TAC[NOT_LESS_0]
   ,
    CONV_TAC (GEN_ALPHA_CONV (--`b''':num`--)) THEN
    CONV_TAC (ONCE_DEPTH_CONV (GEN_ALPHA_CONV (--`f''':num->'b`--))) THEN
    REWRITE_TAC[LESS_THM,TAUT_PROVE (--`(a \/ b) /\ c = (a /\ c) \/ (b /\ c)`--)] THEN
    CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN
    REWRITE_TAC[TAUT_PROVE (--`(a \/ b) /\ c = (a /\ c) \/ (b /\ c)`--)] THEN
    CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN
    CONV_TAC (REDEPTH_CONV (CHANGED_CONV (UNWIND_AUTO_CONV THENC PRUNE_CONV))) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o SPECL[--`e:'a`--,--`(f:num->'b) b`--,--`e':'a`--]) THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC (--`b'' + b'`--) THEN
    EXISTS_TAC (--`\n. (n < b'') => (f'' n) | (f' (n - b''):'b)`--) THEN
    BETA_TAC THEN
    GEN_TAC THEN
    EQ_TAC THEN
    REPEAT STRIP_TAC THENL
    [
     EXISTS_TAC (--`n:num`--) THEN
     IMP_RES_TAC LESS_IMP_LESS_ADD THEN
     ASM_REWRITE_TAC[]
    ,
     EXISTS_TAC (--`b'' + n`--) THEN
     CONJ_TAC THENL
     [
      IMP_RES_TAC LESS_MONO_ADD THEN
      PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN
      ASM_REWRITE_TAC[]
     ,
      REWRITE_TAC[REWRITE_RULE[SYM(SPEC_ALL NOT_LESS)] LESS_EQ_ADD] THEN
      PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN
      ASM_REWRITE_TAC [ADD_SUB]
     ]
    ,
     ASM_CASES_TAC (--`n < b''`--) THENL
     [
      DISJ1_TAC THEN
      EXISTS_TAC (--`n:num`--) THEN
      ASM_REWRITE_TAC[]
     ,
      DISJ2_TAC THEN
      EXISTS_TAC (--`n - b''`--) THEN
      IMP_RES_TAC NOT_LESS THEN
      SUBST_TAC[SYM (SPECL[--`n - b''`--,--`b':num`--,--`b'':num`-- ]LESS_MONO_ADD_EQ)] THEN
      IMP_RES_TAC SUB_ADD THEN
      ASM_REWRITE_TAC[] THEN
      PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN
      FIRST_ASSUM ACCEPT_TAC
     ]
    ]
   ]
  ,
   RES_TAC THEN
   EXISTS_TAC (--`s:'b`--) THEN
   ASM_REWRITE_TAC[]
  ,
   EXISTS_TAC (--`s':'b`--) THEN
   FIRST_ASSUM ACCEPT_TAC
  ]
 ]);

Fin_Sim_Powerset_imp_Imp = TAC_PROOF (([],
  (--`!(Q1:'a#'a1->bool) N1 (Q2:'a#'a2->bool) N2.
         Fin_Non_Det (Q2,N2) ==>
         (Q1,N1) Simulates (Powerset (Q2,N2)) ==>
         (!e. (Trace (Q1,N1)) e ==> Trace (Q2,N2) e)`--)),
 PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC Subset_Simulates_Finite_Powerset THEN
 POP_ASSUM (ASSUME_TAC o PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL PAIR)]) THEN
 IMP_RES_TAC Sim_imp_Imp THEN
 POP_ASSUM_LIST (EVERY o map (ASSUME_TAC o REWRITE_RULE[])) THEN
 REWRITE_TAC[] THEN
 IMP_RES_TAC Trace_Powerset_imp_Limit_Powerset THEN
 IMP_RES_TAC Limit_Powerset_imp_Limit THEN
 IMP_RES_TAC Limit_imp_Limit_Subset THEN
 IMP_RES_TAC Limit_Subset_imp_Trace_Subset THEN
 RES_TAC THEN
 IMP_RES_TAC Trace_Finite_Powerset_eq_Trace);

save_thm ("Naive_Lemma",Naive_Lemma);
save_thm ("Sim_imp_Imp",Sim_imp_Imp);
save_thm ("Sim_Trans",Sim_Trans);
save_thm ("Trace_Inv_Trace",Trace_Inv_Trace);
save_thm ("Trace_Inv_Trace'",Trace_Inv_Trace');
save_thm ("Trace_imp_Trace_Inv",Trace_imp_Trace_Inv);
save_thm ("Trace_Inv_imp_Trace",Trace_Inv_imp_Trace);
save_thm ("Trace_eq_Trace_Inv'",Trace_eq_Trace_Inv');
save_thm ("Trace_eq_Trace_Inv",Trace_eq_Trace_Inv);
save_thm ("Trace_imp_Limit",Trace_imp_Limit);
save_thm ("Deterministic_Limit_imp_Trace",Deterministic_Limit_imp_Trace);
save_thm ("Deterministic_Limit_eq_Trace",Deterministic_Limit_eq_Trace);
save_thm ("Prefix_Trace_imp_Prefix_Trace",Prefix_Trace_imp_Prefix_Trace);
save_thm ("Deterministic_Subset",Deterministic_Subset);
save_thm ("Prefix_imp_Prefix_Subset",Prefix_imp_Prefix_Subset);
save_thm ("Prefix_Powerset_imp_Prefix",Prefix_Powerset_imp_Prefix);
save_thm
 ("Prefix_Subset_imp_Prefix_Powerset",Prefix_Subset_imp_Prefix_Powerset);
save_thm ("Limit_imp_Limit_Subset",Limit_imp_Limit_Subset);
save_thm ("Limit_Subset_imp_Trace_Subset",Limit_Subset_imp_Trace_Subset);
save_thm ("Trace_Subset_imp_Trace_Powerset",Trace_Subset_imp_Trace_Powerset);
save_thm
 ("Trace_Powerset_imp_Limit_Powerset",Trace_Powerset_imp_Limit_Powerset);
save_thm ("Limit_Powerset_imp_Limit",Limit_Powerset_imp_Limit);
save_thm ("Trace_Finite_Powerset_eq_Trace",Trace_Finite_Powerset_eq_Trace);
save_thm ("Sim_imp_Imp'",Sim_imp_Imp');
save_thm ("No_Dead_THM",No_Dead_THM);
save_thm ("Stutter_No_Dead",Stutter_No_Dead);
save_thm ("Complete_Deterministic",Complete_Deterministic);
save_thm ("Simulates_Subset_Powerset",Simulates_Subset_Powerset);
save_thm ("Subset_sim_Powerset",Subset_sim_Powerset);
save_thm ("Trace_Infinite_Path",Trace_Infinite_Path);
save_thm ("Limit_Unbounded",Limit_Unbounded);
save_thm ("Fin_Non_Det_Powerset_Trace",Fin_Non_Det_Powerset_Trace);
save_thm ("Fin_Sim_Powerset_imp_Imp",Fin_Sim_Powerset_imp_Imp);
save_thm ("Complete_No_Dead",Complete_No_Dead);
save_thm ("Subset_Simulates_Finite_Powerset",Subset_Simulates_Finite_Powerset);

export_theory();
