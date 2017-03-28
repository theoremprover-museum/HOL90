(* Trace Semantics for the process RUN.					*)
(* 									*)
(* FILE		  : run.ml 						*)
(* 									*)
(* READS FILES	  : process_ty.th			          	*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : run.th						*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION     : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)

new_theory "run";
(*
load_library "sets";
load_library "string";
*)
new_parent "process_ty";

map set_autoloads [
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = (["IS_PROCESS", "ALPHA_DEF", "TRACES_DEF"]),
 Theorems = ["PROCESS_LEMMA6"]},
{Theory = "star",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NIL_IN_STAR", "APPEND_STAR"]}
];

map Add_to_sml.add_theory_to_sml ["process_ty", "star"];

val IS_PROCESS_RUN =
    store_thm
       ("IS_PROCESS_RUN",
	(--`! A. IS_PROCESS(A, STAR A)`--),
        REWRITE_TAC [IS_PROCESS, SUBSET_DEF, APPEND_STAR, NIL_IN_STAR] THEN
        REPEAT STRIP_TAC);

val RUN_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_RUN;

val DEST_PROCESS =
    TAC_PROOF
       (([],
	 (--`?f. !A. ((ALPHA (f A)) = A) /\
                  ((TRACES (f A)) = (STAR A))`--)),
	EXISTS_TAC (--`\x. ABS_process (x, STAR x)`--) THEN
        BETA_TAC THEN
	REWRITE_TAC [ALPHA_DEF, TRACES_DEF, RUN_LEMMA1]);

val RUN = new_specification {name="RUN",
			     consts=[{const_name="RUN",fixity=Prefix}],
			     sat_thm=DEST_PROCESS};

map2 (fn x => fn y =>  save_thm (x, y))
     ["ALPHA_RUN", "TRACES_RUN"]
     (map GEN_ALL (CONJUNCTS (SPEC_ALL RUN)));

export_theory ();
