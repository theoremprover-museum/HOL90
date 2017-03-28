(* Trace Semantics for the process PARALLEL.				*)
(* 									*)
(* FILE		  : parallel.ml 					*)
(* 									*)
(* READS FILES	  : process_ty.th, rules_and_tacs.ml          		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : parallel.th					*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION     : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)


new_theory "parallel";

new_parent "process_ty";

map set_autoloads [
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = (["IS_PROCESS", "ALPHA_DEF", "TRACES_DEF"]),
 Theorems = ["PROCESS_LEMMA6", "APPEND_IN_TRACES", "TRACES_IN_STAR", "NIL_IN_TRACES"]},
{Theory = "star",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NIL_IN_STAR", "APPEND_STAR"]},
{Theory = "restrict",
 Axioms = ([]:string list),
 Definitions = (["RESTRICT"]),
 Theorems = ["DISTRIB_REST"]}
];

map Add_to_sml.add_theory_to_sml ["process_ty", "star", "restrict"];

val IS_PROCESS_PAR =
    store_thm
       ("IS_PROCESS_PAR",
	(--`! P Q.
          IS_PROCESS
           ((ALPHA P) UNION (ALPHA Q),
	    {s | (s IN (STAR ((ALPHA P) UNION (ALPHA Q)))) /\
                 ((RESTRICT s (ALPHA P)) IN (TRACES P)) /\
                 ((RESTRICT s (ALPHA Q)) IN (TRACES Q))})`--),
        REWRITE_TAC [IS_PROCESS, SUBSET_DEF] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC
	 [RESTRICT, NIL_IN_STAR, DISTRIB_REST, APPEND_STAR, NIL_IN_TRACES] THEN
        REPEAT STRIP_TAC THEN
	IMP_RES_TAC APPEND_IN_TRACES THEN
	ASM_REWRITE_TAC []);

val PAR_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_PAR;

val DEST_PROCESS =
    TAC_PROOF
       (([],
	 (--`?f. !P Q.
           ((ALPHA (f P Q) = ((ALPHA P) UNION (ALPHA Q))) /\
            (TRACES (f P Q) =
  	     {s | (s IN (STAR ((ALPHA P) UNION (ALPHA Q)))) /\
                  ((RESTRICT s (ALPHA P)) IN (TRACES P)) /\
                  ((RESTRICT s (ALPHA Q)) IN (TRACES Q))}))`--)),
	EXISTS_TAC
	 (--`\P Q.
	   ABS_process
	    ((ALPHA P) UNION (ALPHA Q),
	     {s | (s IN (STAR ((ALPHA P) UNION (ALPHA Q)))) /\
                  ((RESTRICT s (ALPHA P)) IN (TRACES P)) /\
                  ((RESTRICT s (ALPHA Q)) IN (TRACES Q))})`--) THEN
        BETA_TAC THEN
	REWRITE_TAC [ALPHA_DEF, TRACES_DEF, PAR_LEMMA1]);

val PAR = new_specification {name="PAR",
				consts=[{const_name="PAR",fixity=Infix 450}],
				sat_thm=DEST_PROCESS};
map2 (fn x => fn y => save_thm (x, y))
     ["ALPHA_PAR", "TRACES_PAR"]
     (map GEN_ALL (CONJUNCTS (SPEC_ALL PAR)));

export_theory();
