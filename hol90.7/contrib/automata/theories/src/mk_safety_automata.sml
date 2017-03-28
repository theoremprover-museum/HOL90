(* ==================================================================== *)
(* FILE		: mk_safety_automata.sml				*)
(* DESCRIPTION  : Theory of infinite automata and safety properties     *)
(* AUTHOR       : Paul Loewenstein (paul.loewenstein@eng.sun.com)       *)
(* DATE		: 20 February 1993                                      *)
(* ==================================================================== *)

new_theory "safety_automata";

new_parent "automata";
new_parent "safe_live";

compile "../../src/zip.sig";
compile "../../src/zip.sml";
open Zip_lib;

Library.load_library_in_place taut_lib;

val Safety = definition "safe_live" "Safety";
val Safe = definition "safe_live" "Safe";
val Live = definition "safe_live" "Live";
val Prefix_OK = definition "safe_live" "Prefix_OK";
val Limit_Trace = definition "automata" "Limit_Trace";
val Prefix_Trace = definition "automata" "Prefix_Trace";
val LESS_0 = theorem "prim_rec" "LESS_0";
val LESS_SUC = theorem "prim_rec" "LESS_SUC";
val LESS_MONO = theorem "prim_rec" "LESS_MONO";

(* Limit automata express safety properties *)

val Safety_Limit = TAC_PROOF (([],
 (--`! (Q:'a#'b->bool) N. Safety (Limit_Trace (Q,N))`--)),
 REWRITE_TAC[Safety,Live,Safe,Limit_Trace,Prefix_Trace,Prefix_OK] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`SUC n`--)) THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
 EXISTS_TAC (--`s:num->'b`--) THEN
 REPEAT STRIP_TAC THENL
 [
  ANTE_RES_THEN (ASSUME_TAC o SYM) (SPEC_ALL LESS_0)
 ,
  IMP_RES_THEN (ANTE_RES_THEN (ASSUME_TAC o SYM)) LESS_SUC THEN
  IMP_RES_THEN (ANTE_RES_THEN (ASSUME_TAC o SYM)) LESS_MONO THEN
  RES_TAC
 ] THEN
 ASM_REWRITE_TAC[]);

(* Deterministic automata express safety properties *)

val Trace_imp_Limit = theorem "automata" "Trace_imp_Limit";
val Deterministic_Limit_imp_Trace =
 theorem "automata" "Deterministic_Limit_imp_Trace";

val Safety_Deterministic = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. Deterministic (Q,N) ==> (Safety (Trace (Q,N)))`--)),
 REPEAT STRIP_TAC THEN
 IMP_RES_THEN (ASSUME_TAC o EXT o GEN_ALL o
   MP (MATCH_MP IMP_ANTISYM_AX (SPEC_ALL Trace_imp_Limit)) o SPEC_ALL)
  Deterministic_Limit_imp_Trace THEN
 ASM_REWRITE_TAC[Safety_Limit]);

(* Deterministic automaton from a property *)

val Klarlund = new_definition ("Klarlund",
 (--`Klarlund (P:(num->'a)->bool) =
   ((\(e:'a,s:(num->'a)->bool,n). (!w. s w) /\ (n = 0)),
    (\(e,s:(num->'a)->bool,n) (e':'a,s',n').
     (n' = SUC n) /\ (!w. s' w = (s w /\ (w n = e))) /\ (?w. s w /\ P w)))`--));
val Deterministic = definition "automata" "Deterministic";
val PAIR_EQ = theorem "pair" "PAIR_EQ";

val Deterministic_Klarlund = TAC_PROOF (([],
 (--`!P:(num->'a)->bool. Deterministic (Klarlund P)`--)),
 REWRITE_TAC[Klarlund,Deterministic] THEN
 CONV_TAC (REDEPTH_CONV (PAIR_FORALL_CONV ((--`s:(num->'a)->bool`--),(--`n:num`--)))) THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REWRITE_TAC[PAIR_EQ] THEN
 REPEAT STRIP_TAC THEN
 (CONV_TAC FUN_EQ_CONV ORELSE ALL_TAC) THEN
 ASM_REWRITE_TAC[]);

val Trace = definition "automata" "Trace";
val Zip = theorem "zip" "Zip";
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val LESS_THM = theorem "prim_rec" "LESS_THM";

val Safe_Trace_Klarlund = TAC_PROOF (([],
  (--`!P:(num->'a)->bool. Safe P = Trace (Klarlund P)`--)),
 REWRITE_TAC[Klarlund] THEN
 GEN_TAC THEN
 CONV_TAC FUN_EQ_CONV THEN
 REWRITE_TAC[Safe,Prefix_OK,Klarlund,Trace] THEN
 GEN_TAC THEN
 CONV_TAC (ONCE_DEPTH_CONV
  (EXISTS_ZIP_CONV ((--`s:num->(num->'a)->bool`--),(--`n:num->num`--)))) THEN
 PURE_ONCE_REWRITE_TAC[Zip] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 EQ_TAC THENL
 [
  DISCH_THEN (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
  POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE FORALL_AND_CONV) THEN
  EXISTS_TAC (--`\(t:num) (v:num->'a). (!t'. t' < t ==> (v t' = f t'))`--) THEN
  EXISTS_TAC (--`\t:num.t`--) THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THENL
  [
   IMP_RES_TAC NOT_LESS_0
  ,
   REFL_TAC
  ,
   REFL_TAC
  ,
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
   [
    IMP_RES_TAC LESS_SUC THEN
    RES_TAC
   ,
    ANTE_RES_THEN ACCEPT_TAC (SPEC (--`t:num`--) LESS_SUC_REFL)
   ,
    IMP_RES_TAC LESS_THM THENL
    [
     ASM_REWRITE_TAC[]
    ,
     RES_TAC
    ]
   ]
  ,
   EXISTS_TAC (--`(v:num->num->'a) t`--) THEN
   ASM_REWRITE_TAC[]
  ]
 ,
  STRIP_TAC THEN
  POP_ASSUM
   (STRIP_ASSUME_TAC o CONV_RULE (REDEPTH_CONV FORALL_AND_CONV)) THEN
  POP_ASSUM
   (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
  SUBGOAL_THEN
   (--`!t:num. (!w:num->'a. s t w = (!t'. t' < t ==> (w t' = f t'))) /\
     (n t = t)`--) ASSUME_TAC THENL
  [
   INDUCT_TAC THENL
   [
    ASM_REWRITE_TAC[NOT_LESS_0]
   ,
    REPEAT STRIP_TAC THENL
    [
     ASM_REWRITE_TAC[] THEN
     EQ_TAC THEN
     REPEAT STRIP_TAC THENL
     [
      IMP_RES_TAC LESS_THM THENL
      [
       ASM_REWRITE_TAC[]
      ,
       RES_TAC
      ]
     ,
      IMP_RES_TAC LESS_SUC THEN
      RES_TAC
     ,
      ANTE_RES_THEN ACCEPT_TAC (SPEC (--`t:num`--) LESS_SUC_REFL)
     ]
    ,
     ASM_REWRITE_TAC[]
    ]
   ]
  ,
   CONV_TAC SKOLEM_CONV THEN
   EXISTS_TAC (--`w:num->num->'a`--) THEN
   POP_ASSUM (fn x => POP_ASSUM_LIST
    (EVERY o map (STRIP_ASSUME_TAC o REWRITE_RULE[x])))
  ]
 ]);

val Strongest_safety = theorem "safe_live" "Strongest_safety";
val Safe_Contains = theorem "safe_live" "Safe_Contains";

val Safety_Klarlund = TAC_PROOF (([],
  (--`!P:(num->'a)->bool. Safety P ==> (Trace (Klarlund P) = P)`--)),
 REWRITE_TAC[SYM (SPEC_ALL Safe_Trace_Klarlund)] THEN
 REPEAT STRIP_TAC THEN
 CONV_TAC FUN_EQ_CONV THEN
 GEN_TAC THEN
 EQ_TAC THEN
 STRIP_TAC THENL
 [
  IMP_RES_THEN (IMP_RES_TAC o REWRITE_RULE[] o SPEC (--`P:(num->'a)->bool`--))
   Strongest_safety
 ,
  IMP_RES_TAC Safe_Contains
 ]);

(* |- !P. Safety P = (?Q N. Deterministic(Q,N) /\ (P = Trace(Q,N))) *)

val Safety_eq_Deterministic = CONV_RULE
 (ONCE_DEPTH_CONV (PAIR_EXISTS_CONV
  ((--`Q:('a#((num->'a)->bool)#num->bool)`--),
  (--`N:('a#((num->'a)->bool)#num->('a#((num->'a)->bool)#num->bool))`--))))
 (TAC_PROOF (([],
   (--`!P. Safety P =
     (?A:('a#((num->'a)->bool)#num->bool)#
     ('a#((num->'a)->bool)#num->('a#((num->'a)->bool)#num->bool)).
      Deterministic A /\ (P = Trace A))`--)),
  GEN_TAC THEN
  EQ_TAC THEN
  STRIP_TAC THENL
  [
   EXISTS_TAC (--`Klarlund (P:(num->'a)->bool)`--) THEN
   IMP_RES_TAC Safety_Klarlund THEN
   ASM_REWRITE_TAC[Deterministic_Klarlund]
  ,
   POP_ASSUM (fn x => SUBST_TAC[x]) THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC ((--`A:('a#((num->'a)->bool)#num->bool)#
     ('a#((num->'a)->bool)#num->('a#((num->'a)->bool)#num->bool))`--),
    (--`A:('a#((num->'a)->bool)#num->bool)#
     ('a#((num->'a)->bool)#num->('a#((num->'a)->bool)#num->bool))`--)) THEN
   CONV_TAC (PAIR_FORALL_CONV ((--`Q:('a#((num->'a)->bool)#num->bool)`--),
  (--`N:('a#((num->'a)->bool)#num->('a#((num->'a)->bool)#num->bool))`--))) THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC Safety_Deterministic  
 ]));

val PRE = theorem "prim_rec" "PRE";
val SUB_0 = theorem "arithmetic" "SUB_0";
val SUB_MONO_EQ = theorem "arithmetic" "SUB_MONO_EQ";
val PRE_SUB = theorem "arithmetic" "PRE_SUB";
val SUB_EQUAL_0 = theorem "arithmetic" "SUB_EQUAL_0";
val NOT_SUC = theorem "num" "NOT_SUC";

val NOT_Forever_Countdown = TAC_PROOF (([],
  (--`!n. ~!t. n t = SUC (n (SUC t))`--)),
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN (--`!t. n (SUC t) = PRE (n t)`--) ASSUME_TAC THENL
 [
  GEN_TAC THEN
  POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
  ASM_REWRITE_TAC[PRE] 
 ,
  SUBGOAL_THEN (--`!t. n t = n 0 - t`--) (MP_TAC o SPEC (--`n 0:num`--)) THENL
  [
   POP_ASSUM_LIST (fn (a :: b) => ASSUME_TAC a) THEN
   INDUCT_TAC THENL
   [
    REWRITE_TAC[SUB_0]
   ,
    ASM_REWRITE_TAC[] THEN
    CONV_TAC (RATOR_CONV (ONCE_DEPTH_CONV
     (PURE_ONCE_REWRITE_CONV[SYM (SPEC_ALL SUB_MONO_EQ)]))) THEN
    REWRITE_TAC[PRE_SUB,PRE]      
   ]
  ,
   REWRITE_TAC[SUB_EQUAL_0] THEN
   PURE_ONCE_ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[NOT_SUC]
  ]  
 ]);
 
val Stuttering = definition "automata" "Stuttering";
val SUC_LESS = theorem "prim_rec" "SUC_LESS";
val LESS_ANTISYM = theorem "arithmetic" "LESS_ANTISYM";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val LESS_EQ_IMP_LESS_SUC = theorem "arithmetic" "LESS_EQ_IMP_LESS_SUC";
val LESS_LESS_SUC = theorem "arithmetic" "LESS_LESS_SUC";
val num_CASES = theorem "arithmetic" "num_CASES";
val SUB = definition "arithmetic" "SUB";
val LESS_IMP_LESS_OR_EQ = theorem "arithmetic" "LESS_IMP_LESS_OR_EQ";
val SUB_EQ_0 = theorem "arithmetic" "SUB_EQ_0";
val SIMP_REC_THM = theorem "prim_rec" "SIMP_REC_THM";

val Stutter_not_Safety = TAC_PROOF (([],
  (--`? (Q:bool#num->bool) N. Stuttering (Q,N) /\ ~Safety (Trace (Q,N))`--)),
 EXISTS_TAC (--`\((e:bool),(s:num)).T`--) THEN
 EXISTS_TAC (--`\((e:bool),(s:num)) ((e':bool),(s':num)).((e' = e) /\ (s' = s)) \/ (s = SUC s')`--) THEN
 REWRITE_TAC[Stuttering,Trace,Safety,Live,Safe,Prefix_OK] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REWRITE_TAC[] THEN
 CONV_TAC NOT_FORALL_CONV THEN
 EXISTS_TAC (--`SIMP_REC F ~`--) THEN
 REWRITE_TAC[IMP_DISJ_THM,DE_MORGAN_THM] THEN
 CONJ_TAC THENL
 [
  GEN_TAC THEN
  EXISTS_TAC (--`\t. t < n => ((SIMP_REC F ~) t) | ((SIMP_REC F ~) n)`--) THEN
  BETA_TAC THEN
  REWRITE_TAC[SYM (SPEC_ALL IMP_DISJ_THM)] THEN
  REPEAT STRIP_TAC THENL
  [
   ASM_REWRITE_TAC[]
  ,
   EXISTS_TAC (--`\t. n - t`--) THEN
   BETA_TAC THEN
   GEN_TAC THEN
   ASM_CASES_TAC (--`t < n`--) THENL
   [
    DISJ2_TAC THEN
    STRIP_ASSUME_TAC (SPEC (--`n:num`--) num_CASES) THEN
    POP_ASSUM SUBST_ALL_TAC THENL
    [
     IMP_RES_TAC NOT_LESS_0
    ,
     REWRITE_TAC[SUB_MONO_EQ] THEN
     ASM_CASES_TAC (--`n' < t`--) THENL
     [
      IMP_RES_TAC LESS_LESS_SUC
     ,
      ASM_REWRITE_TAC[SUB]
     ]
    ]
   ,
    DISJ1_TAC THEN
    IMP_RES_TAC NOT_LESS THEN
    IMP_RES_TAC LESS_EQ_IMP_LESS_SUC THEN
    ASM_CASES_TAC (--`SUC t < n`--) THENL
    [
     IMP_RES_TAC LESS_ANTISYM
    ,
     ASM_REWRITE_TAC[SUB] THEN
     IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
     IMP_RES_TAC SUB_EQ_0 THEN
     ASM_REWRITE_TAC[]
    ]
   ]
  ]
 ,
  REWRITE_TAC [SIMP_REC_THM,Taut.TAUT_PROVE (--`~(~a = a)`--),
               NOT_Forever_Countdown]
 ]);

val LESS_SUC_NOT = theorem "arithmetic" "LESS_SUC_NOT";

val Not_Limit_Safe_Trace = TAC_PROOF (([],
  (--`?(Q:'a#num->bool) N. ~(!e. Limit_Trace(Q,N) e ==> Safe(Trace(Q,N)) e)`--)),
 EXISTS_TAC (--`\((e:'a),(s:num)).T`--) THEN
 EXISTS_TAC (--`\((e:'a),s) ((e':'a),s'). s = SUC s'`--) THEN
 REWRITE_TAC[Limit_Trace,Trace,Safe,Prefix_OK,Prefix_Trace] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 CONV_TAC NOT_FORALL_CONV THEN
 EXISTS_TAC (--`e:num->'a`--) THEN
 PURE_ONCE_REWRITE_TAC[IMP_DISJ_THM] THEN
 REWRITE_TAC[DE_MORGAN_THM] THEN
 CONJ_TAC THENL
 [
  GEN_TAC THEN
  EXISTS_TAC (--`\t. n - t`--) THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THEN
  CONV_TAC (RATOR_CONV (RAND_CONV (PURE_ONCE_REWRITE_CONV[SYM (SPEC_ALL SUB_MONO_EQ)]))) THEN
  IMP_RES_TAC LESS_SUC_NOT THEN
  ASM_REWRITE_TAC[SUB]
 ,
  REWRITE_TAC[NOT_Forever_Countdown]
 ]);

val No_Dead_THM = theorem "automata" "No_Dead_THM";
val Reachable = definition "automata" "Reachable";
val LESS_0_CASES = theorem "arithmetic" "LESS_0_CASES";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";

val No_Dead_Limit_Safe = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. No_Dead (Q,N) ==>
        (!e. Limit_Trace (Q,N) e ==> Safe (Trace (Q,N)) e)`--)),
 REWRITE_TAC[No_Dead_THM,Limit_Trace,Prefix_Trace,Safe,Prefix_OK,Trace,Reachable] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`n:num`--)) THEN
 FIRST_ASSUM (IMP_RES_TAC o SPECL [--`(e:num->'a) n`--,--`(s:num->'b) n`--]) THEN
 POP_ASSUM (ASSUME_TAC o REWRITE_RULE[] o SPECL [--`n:num`--,--`s:num->'b`--]) THEN
 POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[] o SPEC (--`e:num->'a`--)) THEN
 EXISTS_TAC (--`\t. t < n => e t | e' (t - n):'a`--) THEN
 BETA_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  ASM_REWRITE_TAC[]
 ,
  EXISTS_TAC (--`\t. t < n => s t | s' (t - n):'b`--) THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THENL
  [
   STRIP_ASSUME_TAC (SPEC (--`n:num`--) LESS_0_CASES) THENL
   [
    POP_ASSUM (SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[SUB_EQUAL_0,NOT_LESS_0]
   ,
    ASM_REWRITE_TAC[]
   ]
  ,
   ASM_CASES_TAC (--`SUC t < n`--) THENL
   [
    IMP_RES_TAC SUC_LESS THEN
    RES_TAC THEN
    ASM_REWRITE_TAC[]
   ,
    IMP_RES_TAC NOT_LESS THEN
    IMP_RES_TAC LESS_OR_EQ THENL
    [
     IMP_RES_TAC (REWRITE_RULE[] (CONTRAPOS (SPEC_ALL LESS_SUC_NOT))) THEN
     ASM_REWRITE_TAC[SUB]
    ,
     POP_ASSUM SUBST_ALL_TAC THEN
     ANTE_RES_THEN  ASSUME_TAC (SPEC (--`t:num`--) LESS_SUC_REFL) THEN
     ASM_REWRITE_TAC[LESS_SUC_REFL,SUB_EQUAL_0]
    ]    
   ]
  ]
 ]);

val Trace_Powerset_imp_Limit_Powerset = theorem "automata" "Trace_Powerset_imp_Limit_Powerset";
val Limit_Powerset_imp_Limit = theorem "automata" "Limit_Powerset_imp_Limit";

val No_Dead_Safety_Powerset = TAC_PROOF (([],
  (--`!(Q:'a#'b->bool) N. Safety(Trace (Q,N)) ==> No_Dead(Q,N) ==>
         (!e. Trace(Powerset(Q,N)) e ==> Trace(Q,N)e)`--)),
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC Trace_Powerset_imp_Limit_Powerset THEN
 IMP_RES_TAC Limit_Powerset_imp_Limit THEN
 IMP_RES_TAC No_Dead_Limit_Safe THEN
 IMP_RES_TAC (REWRITE_RULE[] (SPECL [--`P:(num->'a)->bool`--,--`P:(num->'a)->bool`--] Strongest_safety)));

save_thm ("Safety_Limit",Safety_Limit);
save_thm ("Safety_Deterministic",Safety_Deterministic);
save_thm ("Deterministic_Klarlund",Deterministic_Klarlund);
save_thm ("Safe_Trace_Klarlund",Safe_Trace_Klarlund);
save_thm ("Safety_Klarlund",Safety_Klarlund);
save_thm ("Safety_eq_Deterministic",Safety_eq_Deterministic);
save_thm ("Stutter_not_Safety",Stutter_not_Safety);
save_thm ("No_Dead_Limit_Safe",No_Dead_Limit_Safe);
save_thm ("No_Dead_Safety_Powerset",No_Dead_Safety_Powerset);

export_theory();

