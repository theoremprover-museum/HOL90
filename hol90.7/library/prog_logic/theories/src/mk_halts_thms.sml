(* ************************************************************************* *)
(*                                                                           *)
(* FILE          : mk_halts_thms.sml                                         *)
(* DESCRIPTION   : Proof of theorems corresponding to the Hoare rules and    *)
(*                 axioms for TOTAL CORRECTNESS.                             *)
(*                                                                           *)
(* AUTHOR        : Mike Gordon, University of Cambridge                      *)
(* DATE          : March 1988                                                *)
(*                                                                           *)
(* TRANSLATOR    : Matthew Morley, University of Edinburgh                   *)
(* DATE          : Feb 1993                                                  *)
(*                                                                           *)
(* ************************************************************************* *)


new_theory "halts_thms";

load_library{lib=string_lib,theory="halts_thms"};

new_parent "hoare_thms";
new_parent "halts";

Add_to_sml.add_theorems_to_sml "halts";

Add_to_sml.add_theorems_to_sml "hoare_thms";

val HALTS = definition "halts" "HALTS";

val MK_SPEC = definition "semantics" "MK_SPEC";

val T_SPEC = new_definition
    ("T_SPEC",
     (--`T_SPEC(p,c,q) = MK_SPEC(p,c,q) /\ HALTS p c`--));


val SKIP_T_THM = save_thm("SKIP_T_THM",
 prove
  ((--`! p. T_SPEC(p,MK_SKIP,p)`--),
   REWRITE_TAC[T_SPEC,SKIP_THM,SKIP_HALTS]));


val ASSIGN_T_THM = save_thm("ASSIGN_T_THM",
 prove
  ((--`!p x f. T_SPEC((\s. p (BND x (f s) s)), MK_ASSIGN(x,f), p)`--),
   REWRITE_TAC[T_SPEC,ASSIGN_THM,ASSIGN_HALTS]));


val SEQ_T_THM = save_thm("SEQ_T_THM",
 prove
  ((--`!p q r c c'.
    T_SPEC(p,c,q) /\ T_SPEC(q,c',r) ==> T_SPEC(p,MK_SEQ(c,c'),r)`--),
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SEQ_THM
    THEN IMP_RES_TAC SEQ_HALTS));

val IF1_T_THM = save_thm("IF1_T_THM",
 prove
  ((--`!p q c b.
     T_SPEC((\s. p s /\ b s),c,q) /\ (!s. p s /\ ~(b s) ==> q s) ==>
     T_SPEC(p,MK_IF1(b,c),q)`--),
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC IF1_THM
    THEN IMP_RES_TAC IF1_HALTS));

val IF2_T_THM = save_thm("IF2_T_THM",
 prove
  ((--`!p q c c' b.
     T_SPEC((\s. p s /\ b s),c,q) /\ T_SPEC((\s. p s /\ ~(b s)),c',q) ==>
     T_SPEC(p,MK_IF2(b,c,c'),q)`--),
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC IF2_THM
    THEN IMP_RES_TAC IF2_HALTS));

val PRE_STRENGTH_T_THM = save_thm("PRE_STRENGTH_T_THM",
 prove
  ((--`!p p' q c.
     (!s. p' s ==> p s) /\ T_SPEC(p,c,q) ==> T_SPEC(p',c,q)`--),
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC PRE_STRENGTH_THM
    THEN IMP_RES_TAC PRE_STRENGTH_HALTS));

val POST_WEAK_T_THM = save_thm("POST_WEAK_T_THM",
 prove
  ((--`!p q q' c.
     T_SPEC(p,c,q)/\ (!s. q s ==> q' s)  ==> T_SPEC(p,c,q')`--),
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC POST_WEAK_THM
    THEN ASM_REWRITE_TAC[]));

val WHILE_T_LEMMA1 = 
 TAC_PROOF
  (([],
    (--`(!n. HALTS(\s. p s /\ b s /\ (s x = n))c) 
               ==> HALTS(\s. p s /\ b s)c`--)),
   REWRITE_TAC[HALTS] 
    THEN  BETA_TAC THEN REPEAT STRIP_TAC 
    THEN  FIRST_ASSUM 
           (fn th => 
             fn g => MATCH_MP_TAC(SPECL[(--`(s:string->num)x`--),
                                        (--`s:string->num`--)] th) g) 
    THEN  ASM_REWRITE_TAC []);

val WHILE_T_LEMMA2 =
 TAC_PROOF
  (([],
    (--`(!n. MK_SPEC((\s. p s /\ b s /\ (s x = n)),c,(\s. p s /\ (s x) < n)))
     ==>
     MK_SPEC((\s. p s /\ b s),c,p)`--)),
   REWRITE_TAC[MK_SPEC] 
    THEN  BETA_TAC THEN REPEAT STRIP_TAC 
    THEN  ASSUME_TAC (REFL (--`(s:string->num) x`--)) 
    THEN  RES_TAC);


local
      
    (* FORALL_AND_CONV :  "!x: t1 x /\ t2 x" -----> (!x.t1 x) /\ (!x.t2 x) *)

    fun FORALL_AND_CONV tm = 
        let val {Bvar,...} = dest_forall tm
            val (p,q) = CONJ_PAIR(SPEC Bvar (ASSUME tm))
            val imp1 = DISCH tm (CONJ (GEN Bvar p) (GEN Bvar q))
            val (P,Q) = CONJ_PAIR(ASSUME ((#conseq o dest_imp) (concl imp1)))
            val imp2 = DISCH_ALL (GEN Bvar (CONJ (SPEC Bvar P) 
                           (SPEC Bvar Q)))
        in
            IMP_ANTISYM_RULE imp1 imp2
        end
in
    val WHILE_T_THM = save_thm("WHILE_T_THM",
        prove
         ((--`!p c b.
           (!n. T_SPEC((\s. p s /\ b s /\ (s x = n)), c, 
                       (\s. p s /\ s x < n)))
            ==> 
            T_SPEC(p,MK_WHILE(b,c),(\s. p s /\ ~(b s)))`--),
          REWRITE_TAC[T_SPEC]
          THEN REPEAT STRIP_TAC
          THEN POP_ASSUM(fn th => 
                 STRIP_ASSUME_TAC(EQ_MP(FORALL_AND_CONV(concl th))th))
          THEN IMP_RES_TAC WHILE_T_LEMMA1
          THEN IMP_RES_TAC WHILE_HALTS
          THEN IMP_RES_TAC WHILE_T_LEMMA2
          THEN IMP_RES_TAC WHILE_THM))
end;

close_theory();

export_theory();

