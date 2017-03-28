(* ==================================================================== *)
(* FILE		: mk_safe_live.sml					*)
(* DESCRIPTION  : Theory of safety and liveness properties              *)
(* AUTHOR       : Paul Loewenstein (paul.loewenstein@eng.sun.com)       *)
(* DATE		: 20 February 1993                                      *)
(* ==================================================================== *)

new_theory "safe_live";

(* Prefix of n has extension satisfying P *)

val Prefix_OK = new_definition ("Prefix_OK",
 (--`Prefix_OK n P w = (?v. (!t. t < n ==> (v t:'a = w t)) /\ P v)`--));

(* Extensible prefix limit of a property *)

val Safe = new_definition ("Safe",
 (--`Safe P (w:num->'a) = (!n. Prefix_OK n P w)`--));

(* It accepts everything that the original property accepts *)

val Safe_Contains = TAC_PROOF (([],
  (--`!P (w:num->'a). P w ==> Safe P w`--)),
 REWRITE_TAC[Safe,Prefix_OK] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`w:num->'a`--) THEN
 ASM_REWRITE_TAC[]);

(* Idempotent *)

val Safe_Idem = TAC_PROOF (([],
  (--`!P:(num->'a)->bool. Safe (Safe P) = Safe P`--)),
 GEN_TAC THEN
 CONV_TAC FUN_EQ_CONV THEN
 GEN_TAC THEN
 REPEAT GEN_TAC THEN
 EQ_TAC THENL
 [
  REWRITE_TAC[Safe,Prefix_OK] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
  POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
  EXISTS_TAC (--`v':num->'a`--) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  ASM_REWRITE_TAC[]
 ,
  REWRITE_TAC[Safe_Contains]
 ]);

(* Monotonic *)

val Safe_Mono = TAC_PROOF (([],
  (--`!P Q:(num->'a)->bool. (!w. P w ==> Q w) ==>
     (!w. Safe P w ==> Safe Q w)`--)),
 REWRITE_TAC[Safe,Prefix_OK] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
 EXISTS_TAC (--`v:num->'a`--) THEN
 RES_TAC THEN
 ASM_REWRITE_TAC[]);

val Live = new_definition ("Live",
 (--`Live P (w:num->'a) = Safe P w ==> P w`--));

(* It accepts everything that the original property accepts *)

val Live_Contains = TAC_PROOF (([],
  (--`!P (w:num->'a). P w ==> Live P w`--)),
 REWRITE_TAC[Live] THEN
 REPEAT STRIP_TAC THEN
 FIRST_ASSUM ACCEPT_TAC);

(* Reconstruct P from Safe P and Live P *)

val Safe_and_Live = TAC_PROOF (([],
  (--`!P (w:num->'a). Safe P w /\ Live P w = P w`--)),
 REPEAT GEN_TAC THEN
 EQ_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  IMP_RES_TAC Live THEN
  RES_TAC
 ,
  IMP_RES_TAC Safe_Contains
 ,
  IMP_RES_TAC Live_Contains
 ]);

val Safe_Live = TAC_PROOF (([],
  (--`!P (w:num->'a). Safe (Live P) w`--)),
 REWRITE_TAC[Safe,Prefix_OK,Live] THEN
 REPEAT GEN_TAC THEN
 ASM_CASES_TAC (--`?v:num->'a. (!t. t < n ==> (v t = w t)) /\ P v`--) THENL
 [
  POP_ASSUM STRIP_ASSUME_TAC THEN
  EXISTS_TAC (--`v:num->'a`--) THEN
  ASM_REWRITE_TAC[]
 ,
  EXISTS_TAC (--`w:num->'a`--) THEN
  REPEAT STRIP_TAC THENL
  [
   REFL_TAC
  ,
   POP_ASSUM (ANTE_RES_THEN CONTR_TAC o SPEC (--`n:num`--))
  ]
 ]);
 
(* Idempotent *)

val Live_Idem = TAC_PROOF (([],
  (--`!P:(num->'a)->bool. Live (Live P) = Live P`--)),
 GEN_TAC THEN
 CONV_TAC FUN_EQ_CONV THEN
 GEN_TAC THEN
 EQ_TAC THENL
 [
  REWRITE_TAC[Live,Safe_Live]
 ,
  REWRITE_TAC[Live_Contains]
 ]);

val Live_Safe = TAC_PROOF (([], (--`!P (w:num->'a). Live (Safe P) w`--)),
 REWRITE_TAC[Live,Safe_Idem]);

(* Live is NOT monotonic *)

(* Safety Property *)

val Safety = new_definition ("Safety",
 (--`Safety P = (!w:num->'a. Live P w)`--));

val Safety_Safe = TAC_PROOF (([], (--`!P:(num->'a)->bool. Safety (Safe P)`--)),
 REWRITE_TAC[Safety,Live_Safe]);

(* Liveness Property *)

val Liveness = new_definition ("Liveness",
 (--`Liveness P = (!w:num->'a. Safe P w)`--));

val Liveness_Live = TAC_PROOF (([],
  (--`!P:(num->'a)->bool. Liveness (Live P)`--)),
 REWRITE_TAC[Liveness,Safe_Live]);

(* Liveness and Safety imply universal acceptance *)

val Liveness_AND_Safety = TAC_PROOF (([],
  (--`!P:(num->'a)->bool. Liveness P /\ Safety P ==> (!w. P w)`--)),
 REWRITE_TAC[Liveness,Safety,Live] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM_LIST (EVERY o map (ASSUME_TAC o SPEC_ALL))
 THEN RES_TAC);

(* Safe P is the strongest safety property containing P *)
(* There is no corresponding theorem for Live and Liveness *)

val Strongest_safety = TAC_PROOF (([],
   (--`!P Q:(num->'a)->bool.
      Safety Q /\ (!w. P w ==> Q w) ==> (!w. Safe P w ==> Q w)`--)),
 REWRITE_TAC[Safety,Live] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC Safe_Mono THEN
 RES_TAC);

(* All properties can be decomposed into a liveness property and
   a safety property *)

val Safety_Liveness_Decompose = TAC_PROOF (([],
  (--`!P:(num->'a)->bool.
     ?Q R. Safety Q /\ Liveness R /\ (!w. P w = (Q w /\ R w))`--)),
 GEN_TAC THEN
 EXISTS_TAC (--`Safe P:(num->'a)->bool`--) THEN
 EXISTS_TAC (--`Live P:(num->'a)->bool`--) THEN
 REWRITE_TAC[Safety_Safe,Liveness_Live,Safe_and_Live]);

val LESS_REFL = theorem "prim_rec" "LESS_REFL";

val Exists_not_Safety = TAC_PROOF (([],
  (--`?P:(num->bool)->bool. ~Safety P`--)),
 EXISTS_TAC (--`\w. ?t:num. w t`--) THEN
 REWRITE_TAC[Safety,Live,Safe,Prefix_OK] THEN
 BETA_TAC THEN
 CONV_TAC NOT_FORALL_CONV THEN
 EXISTS_TAC (--`\t:num.F`--) THEN
 BETA_TAC THEN
 REWRITE_TAC[IMP_DISJ_THM,DE_MORGAN_THM] THEN
 GEN_TAC THEN
 EXISTS_TAC (--`\t. ~(t < n)`--) THEN
 BETA_TAC THEN
 PURE_ONCE_REWRITE_TAC[EXCLUDED_MIDDLE] THEN
 REWRITE_TAC[] THEN
 EXISTS_TAC (--`n:num`--) THEN
 REWRITE_TAC[LESS_REFL]);

save_thm ("Safe_Contains",Safe_Contains);
save_thm ("Safe_Idem",Safe_Idem);
save_thm ("Safe_Mono",Safe_Mono);
save_thm ("Live_Contains",Live_Contains);
save_thm ("Safe_and_Live",Safe_and_Live);
save_thm ("Safe_Live",Safe_Live);
save_thm ("Live_Idem",Live_Idem);
save_thm ("Live_Safe",Live_Safe);
save_thm ("Safety_Safe",Safety_Safe);
save_thm ("Liveness_Live",Liveness_Live);
save_thm ("Liveness_AND_Safety",Liveness_AND_Safety);
save_thm ("Strongest_safety",Strongest_safety);
save_thm ("Safety_Liveness_Decompose",Safety_Liveness_Decompose);
save_thm ("Exists_not_Safety",Exists_not_Safety);

export_theory();
