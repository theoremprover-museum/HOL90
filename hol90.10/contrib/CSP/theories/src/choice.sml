(* Trace Semantics for the process CHOICE.				*)
(* 									*)
(* FILE		  : choice.ml 						*)
(* 									*)
(* READS FILES	  : process_ty.th, rules_and_tacs.ml          		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : choice.th						*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION    : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)


new_theory "choice";

new_parent "process_ty";

map set_autoloads [
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = (["IS_PROCESS", "ALPHA_DEF", "TRACES_DEF"]),
 Theorems = ["PROCESS_LEMMA6", "APPEND_IN_TRACES", "TRACES_IN_STAR"]},
{Theory = "star",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NIL_IN_STAR", "CONS_STAR", "SUBSET_STAR"]}
];

map Add_to_sml.add_theory_to_sml ["process_ty", "star", "list_lib1"];

val event    = ty_antiq(==`:string`==);
val trace    = ty_antiq(==`:^event list`==);
val alphabet = ty_antiq(==`:^event set`==);


val WELL_DEF_ALPHA =
    new_definition
       ("WELL_DEF_ALPHA",
	(--`WELL_DEF_ALPHA A P =
         ? A'. (!x. x IN A ==> (ALPHA (P x) = A')) /\ (A SUBSET A')`--));

val [WELL_DEF_LEMMA1, WELL_DEF_LEMMA2] =
    map ((REWRITE_RULE [SUBSET_DEF]) o DISCH_ALL)
        (CONJUNCTS
         (SELECT_RULE
	  (ASSUME
	   (--`? A'. (!x. x IN A ==> (ALPHA (P x) = A')) /\ (A SUBSET A')`--))));

val WELL_DEF_LEMMA3 =
    (DISCH_ALL o GEN_ALL o (DISCH (--`(x:^event) IN A`--)) o
     (SUBS [SYM (UNDISCH (SPEC_ALL (UNDISCH WELL_DEF_LEMMA1)))]) o
     UNDISCH o SPEC_ALL o UNDISCH) WELL_DEF_LEMMA2;

val IS_PROCESS_choice =
    store_thm
       ("IS_PROCESS_choice",
	(--`! A P.
          (WELL_DEF_ALPHA A P) ==>
          IS_PROCESS
           ((@A'. (!x. x IN A ==> (ALPHA (P x) = A')) /\ (A SUBSET A')),
	    {[]} UNION {CONS a t | a IN A /\ t IN (TRACES (P a))})`--),
        REWRITE_TAC [WELL_DEF_ALPHA, IS_PROCESS, SUBSET_DEF, UNION_DEF] THEN
        SET_SPEC_TAC THEN
	REWRITE_TAC [IN_SING, APPEND_EQ_NIL] THEN
	REPEAT STRIP_TAC THEN
(*	IMP_RES_TAC CONS_MEMBER_LIST THEN *** replaced by later tactic      *)
	ASM_REWRITE_TAC [NIL_IN_STAR] THEN
	IMP_RES_TAC WELL_DEF_LEMMA1 THEN
	POP_ASSUM (SUBST1_TAC o SYM) THEN
	IMP_RES_TAC WELL_DEF_LEMMA3 THEN
	ASM_REWRITE_TAC [CONS_STAR] THEN
	IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] TRACES_IN_STAR) THEN
(* replacement tactic follows; adjusted to resolve with equality antecedent *)
        STRIP_ASSUME_TAC (MATCH_MP CONS_MEMBER_LIST
				   (ASSUME (--`APPEND s t = CONS (a:string) t'`--))) THEN
        ASM_REWRITE_TAC[] THEN
	DISJ2_TAC THEN
	EXISTS_TAC (--`a:^event`--) THEN
	EXISTS_TAC (--`r:^trace`--) THEN
	UNDISCH_TAC (--`t' IN (TRACES (P (a:^event)))`--) THEN
	ASM_REWRITE_TAC [APPEND_IN_TRACES]);

val choice_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_choice;

val DEST_PROCESS =
    TAC_PROOF
       (([],
	 (--`?f. !A P.
           WELL_DEF_ALPHA A P ==>
           ((ALPHA (f A P) =
             (@A'. (!x. x IN A ==> (ALPHA (P x) = A')) /\ (A SUBSET A'))) /\
            (TRACES (f A P) =
	     {[]} UNION {CONS a t | a IN A /\ t IN (TRACES (P a))}))`--)),
	EXISTS_TAC
	 (--`\A P.
	  ABS_process
           ((@A'. (!x. x IN A ==> (ALPHA (P x) = A')) /\ (A SUBSET A')),
            {[]} UNION {CONS a t | a IN A /\ t IN (TRACES (P a))})`--) THEN
        BETA_TAC THEN
	PURE_ONCE_REWRITE_TAC
	 [GEN_ALL (SPEC (--`ABS_process r`--) ALPHA_DEF),
	  GEN_ALL (SPEC (--`ABS_process r`--) TRACES_DEF)] THEN
	REPEAT GEN_TAC THEN
	DISCH_THEN (SUBST1_TAC o (MATCH_MP choice_LEMMA1)) THEN
	REWRITE_TAC []);

val choice = new_specification {name="choice",
				consts=[{const_name="choice",fixity=Prefix}],
				sat_thm=DEST_PROCESS};

val [ALPHA_choice, TRACES_choice] =
    map2 (fn x => fn y => save_thm (x, y))
         ["ALPHA_choice", "TRACES_choice"]
         (map (GEN_ALL o DISCH_ALL) (CONJUNCTS (UNDISCH (SPEC_ALL choice))));

val WELL_DEF_LEMMA3 =
    REWRITE_RULE
     (map (SYM o SPEC_ALL) [WELL_DEF_ALPHA, SUBSET_DEF])
     (DISCH_ALL (SYM (UNDISCH (SPEC (--`c:^event`--) (UNDISCH WELL_DEF_LEMMA1)))));

save_thm
     ("ALPHA_choice_SPEC",
      DISCH_ALL
	(GEN (--`c:^event`--)
	     (DISCH (--`(c:^event) IN A`--)
	            (TRANS
		     (UNDISCH
		      (ADD_ASSUM (--`(c:^event) IN A`--) (SPEC_ALL ALPHA_choice)))
		     (UNDISCH_ALL WELL_DEF_LEMMA3)))));

export_theory ();
