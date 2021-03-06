(* -*- Emacs Mode: sml -*- *)

(*---------------------------------------------------------------------------*)
(*
   File:         mk_ensures.sml

   Description:  This file defines ENSURES and the theorems and corrollaries
                 described in [CM88].

   Author:       (c) Copyright by Flemming Andersen
   Date:         June 29, 1989
*)
(*---------------------------------------------------------------------------*)

use"aux_definitions.sml";

Globals.tilde_symbols := ("~*" :: !Globals.tilde_symbols);

val path = 
   (!Globals.HOLdir)^"library/unity/theories/"^Globals.theory_file_type^"/"
val _ = theory_path := path::(!theory_path);

if (current_theory() <> "unless") then
    load_theory"unless"
else
    ();

delete_theory (path^"ensures");
new_theory"ensures";

(*---------------------------------------------------------------------------*)
(* Load the definitions and theorems                                         *)
(*---------------------------------------------------------------------------*)
val list_Axiom = theorem"list""list_Axiom";
val /\* = definition"state_logic""/\\*";
val False = definition"state_logic""False";
val ~* = definition"state_logic""~*";
val \/* = definition"state_logic""\\/*";
val STABLE = definition"unless""STABLE";
val UNLESS = definition"unless""UNLESS";
val UNLESS_STMT = definition"unless""UNLESS_STMT";

val AND_ASSOC_lemma = theorem"state_logic""AND_ASSOC_lemma";
val AND_COMM_lemma = theorem"state_logic""AND_COMM_lemma";
val AND_COMPL_OR_lemma = theorem"state_logic""AND_COMPL_OR_lemma";
val AND_False_lemma = theorem"state_logic""AND_False_lemma";
val AND_OR_EQ_AND_COMM_OR_lemma = theorem"state_logic""AND_OR_EQ_AND_COMM_OR_lemma";
val AND_OR_EQ_lemma = theorem"state_logic""AND_OR_EQ_lemma";
val IMPLY_WEAK_lemma5 = theorem"state_logic""IMPLY_WEAK_lemma5";
val IMPLY_WEAK_lemma_b = theorem"state_logic""IMPLY_WEAK_lemma_b";
val OR_AND_COMM_lemma = theorem"state_logic""OR_AND_COMM_lemma";
val OR_ASSOC_lemma = theorem"state_logic""OR_ASSOC_lemma";
val OR_False_lemma = theorem"state_logic""OR_False_lemma";
val P_AND_Q_OR_Q_lemma = theorem"state_logic""P_AND_Q_OR_Q_lemma";
val UNLESS_STMT_thm0 = theorem"unless""UNLESS_STMT_thm0";
val UNLESS_STMT_thm2 = theorem"unless""UNLESS_STMT_thm2";
val UNLESS_STMT_thm3 = theorem"unless""UNLESS_STMT_thm3";
val UNLESS_cor4 = theorem"unless""UNLESS_cor4";
val UNLESS_cor7 = theorem"unless""UNLESS_cor7";
val UNLESS_thm1 = theorem"unless""UNLESS_thm1";
val UNLESS_thm3 = theorem"unless""UNLESS_thm3";
val UNLESS_thm4 = theorem"unless""UNLESS_thm4";
val UNLESS_thm7 = theorem"unless""UNLESS_thm7";

(*---------------------------------------------------------------------------*)
(* The definition of ENSURES is based on the definition:

      p ensures q in Pr = <p unless q in Pr /\ (?s in Pr: {p /\ ~q} s {q})>

  where p /\* q are state dependent first order logic predicates /\*
  s in the program Pr are conditionally enabled statements transforming
  a state into a new state. ENSURES then requires safety /\* the existance
  of at least one state transition statement s which makes q valid.
*)

val EXIST_TRANSITION = new_recursive_definition
    {name = "EXIST_TRANSITION",
     def  = (--`(EXIST_TRANSITION (p:'a->bool) q [] = F) /\
	        (EXIST_TRANSITION p q (CONS (st:'a->'a) Pr) =
	           (!s. (p s /\ ~q s) ==> q (st s)) \/
                   (EXIST_TRANSITION p q Pr))`--),
     fixity = Infix 425,
     rec_axiom = list_Axiom}

val ENSURES = new_infix_definition
  ("ENSURES",
   (--`ENSURES (p:'a->bool) q (Pr:('a->'a)list) =
      ((p UNLESS q) Pr) /\ ((p EXIST_TRANSITION q) Pr)`--),
   425);

(*-------------------------------------------------------------------------*)
(*
  Lemmas
*)
(*-------------------------------------------------------------------------*)

val ENSURES_lemma0 = TAC_PROOF
  (([],
   (--`!(p:'a->bool) q r st.
          ((!s. p s /\ ~q s ==> q (st s)) /\ (!s. q s ==> r s)) ==>
           (!s. p s /\ ~r s ==> r (st s))`--)),
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (CONTRAPOS (SPEC_ALL (ASSUME (--`!s:'a. q s ==> r s`--)))) THEN
    ASSUME_TAC (SPEC (--`(st:'a->'a) s`--) (ASSUME (--`!s:'a. q s ==> r s`--))) THEN
    RES_TAC THEN
    RES_TAC);

val ENSURES_lemma1 = TAC_PROOF
  (([],
   (--`!(p:'a->bool) p' q q'.
     (!s. p s /\ ~q s ==> p (st s) \/ q (st s)) ==>
      ((!s. p' s /\ ~q' s ==> p'(st s) \/ q'(st s)) ==>
       ((!s. p' s /\ ~q' s ==> q'(st s)) ==>
        (!s. p s /\ p' s /\ (~p s \/ ~q' s) /\ 
        (~p' s \/ ~q s) /\ (~q s \/ ~q' s) ==>
            p (st s) /\ q'(st s) \/ p'(st s) /\
            q (st s) \/ q (st s) /\ q'(st s))))`--)),
     REPEAT STRIP_TAC THENL
       [
        RES_TAC
       ,
        RES_TAC
       ,
        RES_TAC
       ,
        RES_TAC
       ,
        RES_TAC
       ,
        RES_TAC
       ,
        REWRITE_TAC [REWRITE_RULE
         [ASSUME (--`~(q:'a->bool)s`--),ASSUME (--`~(q':'a->bool)s`--),
          ASSUME (--`(p':'a->bool)s`--),ASSUME (--`(p:'a->bool)s`--)] (SPEC_ALL
          (ASSUME (--`!s:'a. p' s /\ ~q' s ==> q'(st s)`--)))] THEN
        STRIP_ASSUME_TAC (REWRITE_RULE
         [ASSUME (--`~(q:'a->bool)s`--),ASSUME (--`~(q':'a->bool)s`--),
          ASSUME (--`(p':'a->bool)s`--),ASSUME (--`(p:'a->bool)s`--)] (SPEC_ALL (ASSUME
            (--`!s:'a. p s /\ ~q s ==> p(st s) \/ q(st s)`--)))) THENL
         [
          ASM_REWRITE_TAC []
         ,
          ASM_REWRITE_TAC []
         ]
       ,
        REWRITE_TAC [REWRITE_RULE
         [ASSUME (--`~(q:'a->bool)s`--),ASSUME (--`~(q':'a->bool)s`--),
          ASSUME (--`(p':'a->bool)s`--),ASSUME (--`(p:'a->bool)s`--)] (SPEC_ALL
          (ASSUME (--`!s:'a. p' s /\ ~q' s ==> q'(st s)`--)))] THEN
        STRIP_ASSUME_TAC (REWRITE_RULE
         [ASSUME (--`~(q:'a->bool)s`--),ASSUME (--`~(q':'a->bool)s`--),
          ASSUME (--`(p':'a->bool)s`--),ASSUME (--`(p:'a->bool)s`--)] (SPEC_ALL (ASSUME
            (--`!s:'a. p s /\ ~q s ==> p(st s) \/ q(st s)`--)))) THENL
         [
          ASM_REWRITE_TAC []
         ,
          ASM_REWRITE_TAC []
         ]
       ]);

val ENSURES_lemma2 = TAC_PROOF
  (([],
   (--`!(p:'a->bool) q r st.
       (!s. p s /\ ~q s ==> q (st s)) ==>
         (!s. (p s \/ r s) /\ ~(q s \/ r s) ==> q (st s) \/ r (st s))`--)),
     REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC))),
                  (SYM (SPEC_ALL DISJ_ASSOC)),NOT_CLAUSES,DE_MORGAN_THM] THEN
     REPEAT STRIP_TAC THENL
      [
       RES_TAC THEN
       ASM_REWRITE_TAC []
      ,
       RES_TAC
     ]);

val ENSURES_lemma3 = TAC_PROOF
  (([],
   (--`!(p:'a->bool) q r Pr. (p ENSURES (q \/* r)) Pr ==>
              (((p /\* (~* q)) \/* (p /\* q)) ENSURES (q \/* r)) Pr`--)),
   REWRITE_TAC [AND_COMPL_OR_lemma]);

(*---------------------------------------------------------------------------*)
(*
  Theorems about EXIST_TRANSITION
*)
(*---------------------------------------------------------------------------*)

(*
  EXIST_TRANSITION Consequence Weakening Theorem:

               p EXIST_TRANSITION q in Pr, q ==> r
              -------------------------------------
                   p EXIST_TRANSITION r in Pr
*)

val EXIST_TRANSITION_thm1 = prove_thm
 ("EXIST_TRANSITION_thm1",
  (--`!(p:'a->bool) q r Pr.
     ((p EXIST_TRANSITION q) Pr /\ (!s. (q s) ==> (r s))) ==>
       ((p EXIST_TRANSITION r) Pr)`--),
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THENL
    [
     REWRITE_TAC [EXIST_TRANSITION]
    ,
     X_GEN_TAC (--`st:'a->'a`--) THEN
     REWRITE_TAC [EXIST_TRANSITION] THEN
     REPEAT STRIP_TAC THENL
       [
        ASSUME_TAC (UNDISCH_ALL (SPEC (--`!s:'a. q s ==> r s`--)
          (SPEC (--`!s:'a. p s /\ ~q s ==> q (st s)`--) AND_INTRO_THM))) THEN
        STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma0)) THEN
        ASM_REWRITE_TAC []
       ,
        RES_TAC THEN
        ASM_REWRITE_TAC []
       ]
    ]);

(*
  Impossibility EXIST_TRANSITION Theorem:

               p EXIST_TRANSITION false in Pr
              --------------------------------
                          ~p 
*)

val EXIST_TRANSITION_thm2 = prove_thm
  ("EXIST_TRANSITION_thm2",
   (--`!(p:'a->bool) Pr.
     ((p EXIST_TRANSITION False) Pr) ==> !s. (~*  p)s`--),
   STRIP_TAC THEN
   REWRITE_TAC [False,~* ] THEN
   REWRITE_TAC [BETA_CONV (--`(\s:'a. ~p s)s`--)] THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [EXIST_TRANSITION]
     ,
      X_GEN_TAC (--`st:'a->'a`--) THEN
      REWRITE_TAC [EXIST_TRANSITION] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC
     ]);

(*
  Always EXIST_TRANSITION Theorem:

               false EXIST_TRANSITION p in Pr
*)

val EXIST_TRANSITION_thm3 = prove_thm
  ("EXIST_TRANSITION_thm3",
   (--`!(p:'a->bool) st Pr. (False EXIST_TRANSITION p) (CONS st Pr)`--),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION,False]);

(*---------------------------------------------------------------------------*)
(*
  Theorems about ENSURES
*)
(*---------------------------------------------------------------------------*)

(*
  Reflexivity Theorem:

               p ensures p in Pr

  The theorem is only valid for non-empty programs
*)

val ENSURES_thm0 = prove_thm
  ("ENSURES_thm0",
   (--`!(p:'a->bool) q. (p ENSURES q) [] = F`--),
     REWRITE_TAC [ENSURES] THEN
     STRIP_TAC THEN
     REWRITE_TAC [UNLESS,EXIST_TRANSITION]);

val ENSURES_thm1 = prove_thm
  ("ENSURES_thm1",
   (--`!(p:'a->bool) st Pr. (p ENSURES p) (CONS st Pr)`--),
     REWRITE_TAC [ENSURES] THEN
     STRIP_TAC THEN
     REWRITE_TAC [UNLESS,EXIST_TRANSITION] THEN
     REWRITE_TAC [UNLESS_thm1,UNLESS_STMT] THEN
     REWRITE_TAC [BETA_CONV (--`(\s:'a. (p s /\ ~p s) ==> p (st s))s`--)] THEN
     REWRITE_TAC[NOT_AND,IMP_CLAUSES]);

(*
  Consequence Weakening Theorem:

               p ensures q in Pr, q ==> r
              ----------------------------
                   p ensures r in Pr
*)

val ENSURES_thm2 = prove_thm
  ("ENSURES_thm2",
   (--`!(p:'a->bool) q r Pr.
         ((p ENSURES q) Pr /\ (!s:'a. (q s) ==> (r s)))
        ==>
	 ((p ENSURES r) Pr)`--),
   REWRITE_TAC [ENSURES] THEN
   REPEAT STRIP_TAC THENL
     [
      ASSUME_TAC (UNDISCH_ALL (SPEC (--`!s:'a. q s ==> r s`--)
        (SPEC (--`((p:'a->bool) UNLESS q) Pr`--) AND_INTRO_THM))) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm3))
     ,
      ASSUME_TAC (UNDISCH_ALL (SPEC (--`!s:'a. q s ==> r s`--)
        (SPEC (--`((p:'a->bool) EXIST_TRANSITION q) Pr`--) AND_INTRO_THM))) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL EXIST_TRANSITION_thm1))
     ]);

(*
  Impossibility Theorem:

               p ensures false in Pr
              ----------------------
                       ~p 
*)

val ENSURES_thm3 = prove_thm
  ("ENSURES_thm3",
   (--`!(p:'a->bool) Pr. ((p ENSURES False) Pr) ==> !s. (~*  p)s`--),
   STRIP_TAC THEN LIST_INDUCT_TAC THENL
    [
     REWRITE_TAC [ENSURES,UNLESS,EXIST_TRANSITION,~* ,False]
    ,
     X_GEN_TAC (--`st:'a->'a`--) THEN
     REWRITE_TAC [ENSURES,UNLESS,EXIST_TRANSITION,False,~* ] THEN
     REPEAT STRIP_TAC THENL
       [
        REWRITE_TAC[BETA_CONV (--`(\s:'a. ~p s)s`--)] THEN
        ASM_REWRITE_TAC []
       ,
        ASSUME_TAC (SPEC_ALL EXIST_TRANSITION_thm2) THEN
        UNDISCH_TAC (--`((p:'a->bool) EXIST_TRANSITION (\s. F)) Pr`--) THEN
        REWRITE_TAC [(SYM (SPEC_ALL ~* )),(SYM (SPEC_ALL False))] THEN
        REPEAT STRIP_TAC THEN
        RES_TAC THEN
        ASM_REWRITE_TAC []
       ]
    ]);

(*
  Conjunction Theorem:

                   p unless q in Pr, p' ensures q' in Pr
              -----------------------------------------------
               p/\p' ensures (p/\q')\/(p'/\q)\/(q/\q') in Pr
*)

val ENSURES_thm4 = prove_thm
  ("ENSURES_thm4",
   (--`!(p:'a->bool) q p' q' Pr.
    (p UNLESS q) Pr /\ (p' ENSURES q') Pr ==>
      ((p /\* p') ENSURES (((p /\* q') \/*  (p' /\* q)) \/*  (q /\* q')))
        Pr`--),
   STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES,UNLESS,EXIST_TRANSITION,/\*,\/* ]
     ,
      X_GEN_TAC (--`st:'a->'a`--) THEN
      REWRITE_TAC [ENSURES,UNLESS,EXIST_TRANSITION] THEN
      DISCH_TAC THEN
      REPEAT STRIP_TAC THENL
        [
         UNDISCH_TAC
           (--`((!s:'a. (p  UNLESS_STMT q ) st s) /\ (p  UNLESS  q ) Pr) /\
            ((!s.  (p' UNLESS_STMT q') st s) /\ (p' UNLESS  q') Pr) /\
            ((!s. p' s /\ ~q' s ==> q' (st s)) \/
		(p' EXIST_TRANSITION q') Pr)`--)
           THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (UNDISCH_ALL
			(SPEC (--`!s:'a. (p' UNLESS_STMT q') st s`--)
			 (SPEC (--`!s:'a. (p  UNLESS_STMT q ) st s`--)
			  AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_STMT_thm3)) THEN
            ASM_REWRITE_TAC []
           ,
            ASSUME_TAC (UNDISCH_ALL
			(SPEC (--`!s:'a. (p' UNLESS_STMT q') st s`--)
			 (SPEC (--`!s:'a. (p  UNLESS_STMT q ) st s`--)
			  AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_STMT_thm3)) THEN
            ASM_REWRITE_TAC []
           ]
        ,
         UNDISCH_TAC
           (--`((!s:'a. (p  UNLESS_STMT q ) st s) /\ (p  UNLESS  q ) Pr) /\
            ((!s.   (p' UNLESS_STMT q') st s) /\ (p' UNLESS  q') Pr) /\
            ((!s. p' s /\ ~q' s ==> q'(st s)) \/
		(p' EXIST_TRANSITION q')Pr)`--)
               THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (UNDISCH_ALL (SPEC (--`((p':'a->bool) UNLESS q') Pr`--)
                                    (SPEC (--`((p:'a->bool)  UNLESS q ) Pr`--)
                        AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm4))
           ,
            ASSUME_TAC (UNDISCH_ALL (SPEC (--`((p':'a->bool) UNLESS q') Pr`--)
                                    (SPEC (--`((p:'a->bool)  UNLESS q) Pr`--)
                                     AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm4))
           ]
        ,
         UNDISCH_TAC
           (--`((!s:'a. (p  UNLESS_STMT q ) st s) /\ (p  UNLESS q ) Pr) /\
            ((!s.   (p' UNLESS_STMT q') st s) /\ (p' UNLESS q') Pr) /\
            ((!s. p' s /\ ~q' s ==> q'(st s)) \/
		(p' EXIST_TRANSITION q')Pr)`--)
                 THEN
         REPEAT STRIP_TAC THENL
           [
            UNDISCH_TAC (--`!s:'a. p' s /\ ~q' s ==> q'(st s)`--) THEN
            UNDISCH_TAC (--`!s:'a. (p' UNLESS_STMT q') st s`--) THEN
            UNDISCH_TAC (--`!s:'a. (p  UNLESS_STMT q ) st s`--) THEN
            REWRITE_TAC [UNLESS_STMT,/\*,\/* ] THEN
            CONV_TAC (DEPTH_CONV BETA_CONV) THEN
            REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC))),
                         (SYM (SPEC_ALL DISJ_ASSOC)),
                         NOT_CLAUSES,DE_MORGAN_THM] THEN
            REPEAT STRIP_TAC THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma1)) THEN
            ASM_REWRITE_TAC []
           ,
            RES_TAC THEN
            ASSUME_TAC (UNDISCH_ALL
               (SPEC (--`((p':'a->bool) EXIST_TRANSITION q')Pr`--)
               (SPEC (--`((p':'a->bool) UNLESS q')Pr`--)
                AND_INTRO_THM))) THEN
            UNDISCH_TAC
              (--`((p':'a->bool) UNLESS q') Pr /\
	          (p' EXIST_TRANSITION q') Pr`--) THEN
            REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL ENSURES)))] THEN
            STRIP_TAC THEN
            RES_TAC THEN
            UNDISCH_TAC (--`(((p:'a->bool) /\* p') ENSURES (((p /\* q') \/* 
                           (p' /\* q)) \/*  (q /\* q')))Pr`--) THEN
            REWRITE_TAC [ENSURES] THEN
            REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ]
        ]
     ]);

(*
  Conjunction Theorem:

                   p ensures q in Pr
              -------------------------
               p\/r ensures q\/r in Pr
*)

val ENSURES_thm5 = prove_thm
  ("ENSURES_thm5",
   (--`!(p:'a->bool) q r Pr.
      ((p ENSURES q) Pr) ==> (((p \/*  r) ENSURES (q \/*  r)) Pr)`--),
   STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES,EXIST_TRANSITION]
     ,
      X_GEN_TAC (--`st:'a->'a`--) THEN
      REWRITE_TAC [ENSURES,UNLESS,EXIST_TRANSITION] THEN
      DISCH_TAC THEN
      REPEAT STRIP_TAC THENL
        [
         UNDISCH_TAC
           (--`((!s:'a. (p UNLESS_STMT q) st s) /\ (p UNLESS q) Pr) /\
            ((!s. p s /\ ~q s ==> q (st s)) \/
		(p EXIST_TRANSITION q)Pr)`--) THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (SPECL [(--`r:'a->bool`--),(--`st:'a->'a`--)]
			UNLESS_STMT_thm0) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`!s:'a. (p UNLESS_STMT q) st s`--),
	       (--`!s:'a. (r UNLESS_STMT r) st s`--)]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`p:'a->bool`--),(--`q:'a->bool`--),(--`r:'a->bool`--),
	       (--`r:'a->bool`--),(--`st:'a->'a`--)]
               UNLESS_STMT_thm2)) THEN
            ASM_REWRITE_TAC []
           ,
            ASSUME_TAC (SPECL [(--`r:'a->bool`--),(--`st:'a->'a`--)]
			UNLESS_STMT_thm0) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`!s:'a. (p UNLESS_STMT q) st s`--),
	       (--`!s:'a. (r UNLESS_STMT r) st s`--)]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`p:'a->bool`--),(--`q:'a->bool`--),(--`r:'a->bool`--),
	       (--`r:'a->bool`--),(--`st:'a->'a`--)]
               UNLESS_STMT_thm2)) THEN
            ASM_REWRITE_TAC []
           ]
        ,
         UNDISCH_TAC
           (--`((!s:'a. (p UNLESS_STMT q) st s) /\ (p UNLESS q) Pr) /\
               ((!s. p s /\ ~q s ==> q (st s)) \/
		   (p EXIST_TRANSITION q)Pr)`--) THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (SPECL [(--`r:'a->bool`--),(--`Pr:('a->'a)list`--)]
			UNLESS_thm1) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`((p:'a->bool) UNLESS q) Pr`--),
	       (--`((r:'a->bool) UNLESS r) Pr`--)]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`p:'a->bool`--),(--`q:'a->bool`--),(--`r:'a->bool`--),
	       (--`r:'a->bool`--),(--`Pr:('a->'a)list`--)]
               UNLESS_thm7))
           ,
            ASSUME_TAC (SPECL [(--`r:'a->bool`--),(--`Pr:('a->'a)list`--)]
			UNLESS_thm1) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`((p:'a->bool) UNLESS q) Pr`--),
	       (--`((r:'a->bool) UNLESS r) Pr`--)]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              [(--`p:'a->bool`--),(--`q:'a->bool`--),(--`r:'a->bool`--),
	       (--`r:'a->bool`--),(--`Pr:('a->'a)list`--)]
               UNLESS_thm7))
           ]
        ,
         UNDISCH_TAC
          (--`((!s:'a. (p UNLESS_STMT q) st s) /\ (p UNLESS q) Pr) /\
              ((!s. p s /\ ~q s ==> q (st s)) \/
		  (p EXIST_TRANSITION q)Pr)`--) THEN
         REPEAT STRIP_TAC THENL
           [
            REWRITE_TAC [\/* ] THEN
            REWRITE_TAC [BETA_CONV (--`(\s:'a. p s \/ r s) s`--)] THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma2)) THEN
            ASM_REWRITE_TAC []
           ,
            ASSUME_TAC (UNDISCH_ALL  (SPECL
              [(--`((p:'a->bool) UNLESS q)Pr`--),
	       (--`((p:'a->bool) EXIST_TRANSITION q)Pr`--)]
               AND_INTRO_THM)) THEN
            UNDISCH_TAC
              (--`((p:'a->bool) UNLESS q) Pr /\
	          (p EXIST_TRANSITION q) Pr`--) THEN
            REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL ENSURES)))] THEN
            STRIP_TAC THEN
            RES_TAC THEN
            UNDISCH_TAC (--`(((p:'a->bool) \/*  r) ENSURES
			     (q \/*  r)) Pr`--) THEN
            REWRITE_TAC [ENSURES] THEN
            REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ]
        ]
     ]);

(*
 -----------------------------------------------------------------------------
  Corollaries about ENSURES
 -----------------------------------------------------------------------------
*)

(*
  Implies Corollary:

                   p => q
              -------------------
               p ensures q in Pr

  This corollary is only valid for non-empty programs.
*)

val ENSURES_cor1 = prove_thm
  ("ENSURES_cor1",
   (--`!(p:'a->bool) q st Pr.
    (!s. p s ==> q s) ==> (p ENSURES q) (CONS st Pr)`--),
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC_ALL ENSURES_thm1) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(--`((p:'a->bool) ENSURES p)(CONS st Pr)`--),(--`!s:'a. p s ==> q s`--)]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
     [(--`p:'a->bool`--),(--`p:'a->bool`--),(--`q:'a->bool`--),
      (--`CONS (st:'a->'a) Pr`--)]
      ENSURES_thm2)));

val ENSURES_cor2 = prove_thm
  ("ENSURES_cor2",
   (--`!(p:'a->bool) q Pr. (p ENSURES q) Pr ==> (p UNLESS q) Pr`--),
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES,EXIST_TRANSITION]
     ,
      X_GEN_TAC (--`st:'a->'a`--) THEN
      REWRITE_TAC [ENSURES,EXIST_TRANSITION,UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ,
         ASM_REWRITE_TAC []
        ,
         ASM_REWRITE_TAC []
        ,
         ASM_REWRITE_TAC []
        ]
     ]);

val ENSURES_cor3 = prove_thm
  ("ENSURES_cor3",
   (--`!(p:'a->bool) q r Pr.
        ((p \/*  q) ENSURES r)Pr ==> (p ENSURES (q \/*  r))Pr`--),
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(--`((p:'a->bool) \/*  q)`--),(--`r:'a->bool`--),
      (--`Pr:('a->'a)list`--)] ENSURES_cor2)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(--`p:'a->bool`--),(--`q:'a->bool`--),(--`r:'a->bool`--),
      (--`Pr:('a->'a)list`--)] UNLESS_cor4)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(--`((p:'a->bool) UNLESS (q \/*  r))Pr`--),
      (--`(((p:'a->bool) \/*  q) ENSURES r)Pr`--)]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(--`p:'a->bool`--),(--`((q:'a->bool) \/*  r)`--),
      (--`((p:'a->bool) \/*  q)`--),(--`r:'a->bool`--),
      (--`Pr:('a->'a)list`--)] ENSURES_thm4)) THEN
   UNDISCH_TAC (--`(((p:'a->bool) /\* (p \/*  q)) ENSURES
                (((p /\* r) \/*  ((p \/*  q) /\* (q \/*  r))) \/* 
                 ((q \/*  r) /\* r))) Pr`--) THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma,AND_ASSOC_lemma] THEN
   PURE_ONCE_REWRITE_TAC [SPECL
         [(--`((q:'a->bool) \/*  r)`--),
	  (--`r:'a->bool`--)] AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [AND_OR_EQ_AND_COMM_OR_lemma] THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL [(--`p:'a->bool`--),(--`q:'a->bool`--),(--`r:'a->bool`--)]
                           IMPLY_WEAK_lemma5) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    [(--`((p:'a->bool) ENSURES
      ((p /\* r) \/*  (((p \/*  q) /\* (q \/*  r)) \/*  r)))Pr`--),
     (--`!s:'a. ((p /\* r) \/*  (((p \/*  q) /\* (q \/*  r)) \/* r))s ==>
	 (q \/*  r)s`--)]
     AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
    [(--`p:'a->bool`--),
     (--`(((p:'a->bool) /\* r) \/* (((p \/*  q) /\* (q \/*  r)) \/* r))`--),
     (--`((q:'a->bool) \/*  r)`--),(--`Pr:('a->'a)list`--)]
     ENSURES_thm2)));

val ENSURES_cor4 = prove_thm
  ("ENSURES_cor4",
   (--`!(p:'a->bool) q r Pr. (p ENSURES (q \/*  r)) Pr ==>
              ((p /\* (~*  q)) ENSURES (q \/*  r)) Pr`--),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(--`((p:'a->bool) /\* (~*  q))`--),(--`((p:'a->bool) /\* q)`--),
      (--`((q:'a->bool) \/* r)`--),(--`Pr:('a->'a)list`--)] ENSURES_cor3)) THEN
   UNDISCH_TAC
     (--`(((p:'a->bool) /\* (~*  q)) ENSURES
	  ((p /\* q) \/* (q \/* r)))Pr`--) THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL OR_ASSOC_lemma))] THEN
   REWRITE_TAC [P_AND_Q_OR_Q_lemma]);

(*
  Consequence Weakening Corollary:

                  p ensures q in Pr
              -------------------------
               p ensures (q \/ r) in Pr
*)

val ENSURES_cor5 = prove_thm
 ("ENSURES_cor5",
   (--`!(p:'a->bool) q r Pr.
         (p ENSURES q) Pr ==> (p ENSURES (q \/*  r)) Pr`--),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL [(--`q:'a->bool`--),(--`r:'a->bool`--)]
	       IMPLY_WEAK_lemma_b) THEN
   ASSUME_TAC (SPECL
     [(--`p:'a->bool`--),(--`q:'a->bool`--),(--`(q:'a->bool) \/* r`--)]
	       ENSURES_thm2) THEN
   RES_TAC);

(*
  Always Corollary:

                  false ensures p in Pr
*)

val ENSURES_cor6 = prove_thm
  ("ENSURES_cor6",
   (--`!(p:'a->bool) st Pr. (False ENSURES p) (CONS st Pr)`--),
   REWRITE_TAC [ENSURES,UNLESS_cor7,EXIST_TRANSITION_thm3]);

val ENSURES_cor7 = prove_thm
  ("ENSURES_cor7",
   (--`!(p:'a->bool) q r Pr.
        (p ENSURES q) Pr /\ (r STABLE Pr)
       ==>
	((p /\* r) ENSURES (q /\*
 r))Pr`--),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC (ONCE_REWRITE_RULE [AND_COMM_lemma]
      (REWRITE_RULE [AND_False_lemma,OR_False_lemma] 
        (ONCE_REWRITE_RULE [OR_AND_COMM_lemma] 
          (REWRITE_RULE [AND_False_lemma,OR_False_lemma] (SPECL
            [(--`r:'a->bool`--),(--`False:'a->bool`--),
	     (--`p:'a->bool`--),(--`q:'a->bool`--),
             (--`Pr:('a->'a)list`--)] ENSURES_thm4))))));

close_theory();
export_theory();


(* Emacs editor information
|  Local variables:
|  mode:sml
|  sml-prog-name:"hol90"
|  End:
*)
