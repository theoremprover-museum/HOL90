(* Extends The Basic Theory For TRACES In CSP                    	 *)
(* 									 *)
(* FILE		: star.ml     					         *)
(* DESCRIPTION	: Defines the 'a operator for finite traces and infinite *)
(*                 alphabets.                                            *)
(* 									 *)
(* READS FILES	: restrict.th, rules_and_tacs.ml                       	 *)
(* WRITES FILES : star.th						 *)
(*									 *)
(* AUTHOR	: Albert John Camilleri					 *)
(* AFFILIATION  : Hewlett-Packard Laboratories, Bristol			 *)
(* DATE		: 89.02.07						 *)
(* REVISED	: 91.10.01						 *)
(*              : 21.06.93 - BtG - ported to hol90                       *)


new_theory "star";

new_parent "restrict";

val trace = (==`:('a)list`==);

map set_autoloads [
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NOT_LENGTH_EQ"]},
{Theory = "restrict",
 Axioms = ([]:string list),
 Definitions = (["RESTRICT"]),
 Theorems = ["REST_CONS_THM"]}
];

map Add_to_sml.add_theory_to_sml ["list_lib1", "restrict"];

val STAR =
    new_definition
       ("STAR", (--`STAR (A:('a)set) = {s | RESTRICT s A = s}`--));

val NIL_IN_STAR =
    store_thm
       ("NIL_IN_STAR",
	(--`! A:('a)set. [] IN (STAR A)`--),
	REWRITE_TAC [STAR] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [RESTRICT]);

val SINGLE_STAR =
    store_thm
       ("SINGLE_STAR",
	(--`! x (A:('a)set). [x] IN (STAR A) = x IN A`--),
	REWRITE_TAC [STAR] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [RESTRICT] THEN
	REPEAT GEN_TAC THEN
	DISJ_CASES_TAC (SPEC (--`(x:'a) IN A`--) EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC[NOT_NIL_CONS]);

val CONS_STAR =
    store_thm
       ("CONS_STAR",
	(--`! a t (A:('a)set).
           (CONS a t) IN (STAR A) = (a IN A) /\ (t IN (STAR A))`--),
	REWRITE_TAC [STAR] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [RESTRICT] THEN
	REPEAT GEN_TAC THEN
	DISJ_CASES_TAC (SPEC (--`(a:'a) IN A`--) EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC [CONS_11, REST_CONS_THM]);

val APPEND_STAR =
    store_thm
       ("APPEND_STAR",
	(--`! s t (A:('a)set).
           (APPEND s t) IN (STAR A) = (s IN (STAR A) /\ t IN (STAR A))`--),
	LIST_INDUCT_TAC THEN
	ASM_REWRITE_TAC [APPEND, NIL_IN_STAR, CONS_STAR, CONJ_ASSOC]);

val STAR_INDUCT =
    store_thm
       ("STAR_INDUCT",
	(--`!A:('a)set.
          STAR A = {t | (t = []) \/ ((HD t) IN A /\ (TL t) IN (STAR A))}`--),
	GEN_TAC THEN
	REWRITE_TAC [EXTENSION] THEN
	SET_SPEC_TAC THEN
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [NIL_IN_STAR, CONS_STAR, NOT_CONS_NIL, HD, TL]);

val SUBSET_STAR =
    store_thm
       ("SUBSET_STAR",
	(--`! A B: ('a)set. (A SUBSET B) ==> ((STAR A) SUBSET (STAR B))`--),
	REWRITE_TAC [SUBSET_DEF] THEN
	REPEAT GEN_TAC THEN
	DISCH_TAC THEN
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [NIL_IN_STAR, CONS_STAR] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC);

export_theory();
