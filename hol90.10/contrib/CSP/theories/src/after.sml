(* Trace Semantics for the process AFTER.				*)
(* 									*)
(* FILE		  : after.ml 						*)
(* 									*)
(* READS FILES	  : process_ty.th, rules_and_tacs.ml          		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : after.th						*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION     : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)


new_theory "after";

new_parent "process_ty";

map set_autoloads [
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = (["IS_PROCESS", "ALPHA_DEF", "TRACES_DEF"]),
 Theorems = ["PROCESS_LEMMA6", "APPEND_IN_TRACES", "TRACES_IN_STAR"]},
{Theory = "star",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NIL_IN_STAR", "CONS_STAR", "APPEND_STAR"]},
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["APPEND_NIL"]}
];

map Add_to_sml.add_theory_to_sml ["process_ty", "star", "list_lib1"];

val IS_PROCESS_AFTER =
    store_thm
       ("IS_PROCESS_AFTER",
	(--`! P s.
           s IN (TRACES P) ==>
           IS_PROCESS (ALPHA P, {t | (APPEND s t) IN (TRACES P)})`--),
	REWRITE_TAC [IS_PROCESS, SUBSET_DEF] THEN
	SET_SPEC_TAC THEN
	REPEAT STRIP_TAC THENL
	[IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] TRACES_IN_STAR) THEN
	 UNDISCH_TAC (--`(APPEND s x) IN (STAR(ALPHA P))`--) THEN
	 REWRITE_TAC [APPEND_STAR] THEN
	 REPEAT STRIP_TAC,
	 ASM_REWRITE_TAC [APPEND_NIL],
	 UNDISCH_TAC (--`(APPEND s(APPEND s' t)) IN (TRACES P)`--) THEN
	 REWRITE_TAC [APPEND_ASSOC, APPEND_IN_TRACES]]);

val AFTER_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_AFTER;

val DEST_PROCESS =
    TAC_PROOF
       (([],
	 (--`?f. !P s.
           s IN (TRACES P) ==>
           ((ALPHA (f P s) = (ALPHA P)) /\
            (TRACES (f P s) = {t | (APPEND s t) IN (TRACES P)}))`--)),
	EXISTS_TAC
	 (--`\P s. ABS_process (ALPHA P, {t | (APPEND s t) IN (TRACES P)})`--) THEN
        BETA_TAC THEN
	PURE_ONCE_REWRITE_TAC
	 [GEN_ALL (SPEC (--`ABS_process r`--) ALPHA_DEF),
	  GEN_ALL (SPEC (--`ABS_process r`--) TRACES_DEF)] THEN
	REPEAT GEN_TAC THEN
	DISCH_THEN (SUBST1_TAC o (MATCH_MP AFTER_LEMMA1)) THEN
	REWRITE_TAC []);

val AFTER = new_specification {name="AFTER",
			       consts=[{const_name="/",fixity=Infix 450}],
			       sat_thm=DEST_PROCESS};

map2 (fn x => fn y => save_thm (x, y))
     ["ALPHA_AFTER", "TRACES_AFTER"]
     (map (GEN_ALL o DISCH_ALL) (CONJUNCTS (UNDISCH (SPEC_ALL AFTER))));

export_theory();
