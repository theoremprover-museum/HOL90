(* Trace Semantics for the process STOP.				*)
(* 									*)
(* FILE		  : stop.ml 						*)
(* 									*)
(* READS FILES	  : process_ty.th		          		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : stop.th						*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION     : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)

new_theory "stop";

(*
load_library "sets";
load_library "string";
*)
new_parent "process_ty";

map set_autoloads [
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["APPEND_EQ_NIL"]},
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = (["IS_PROCESS", "ALPHA_DEF", "TRACES_DEF"]),
 Theorems = ["PROCESS_LEMMA6"]},
{Theory = "star",
 Axioms = ([]:string list),
 Definitions = (["STAR"]),
 Theorems = ["NIL_IN_STAR"]}
];

map Add_to_sml.add_theory_to_sml ["list_lib1", "process_ty", "star"];


val IS_PROCESS_STOP =
    store_thm
       ("IS_PROCESS_STOP",
	(--`! A. IS_PROCESS (A, {[]})`--),
        REWRITE_TAC [IS_PROCESS, SUBSET_DEF, IN_SING, APPEND_EQ_NIL] THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC [NIL_IN_STAR]);

val STOP_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_STOP;

val DEST_PROCESS =
    TAC_PROOF
       (([],
	 (--`?f. !x. ((ALPHA (f x)) = x) /\ ((TRACES (f x)) = {[]})`--)),
	EXISTS_TAC (--`\x.ABS_process (x, {[]})`--) THEN
        BETA_TAC THEN
	REWRITE_TAC [ALPHA_DEF, TRACES_DEF, STOP_LEMMA1]);

val STOP = new_specification {name="STOP",
			      consts=[{const_name="STOP",fixity=Prefix}],
			      sat_thm=DEST_PROCESS};

map2 (fn x => fn y =>  save_thm (x, y))
     ["ALPHA_STOP", "TRACES_STOP"]
     (map GEN_ALL (CONJUNCTS (SPEC_ALL STOP)));

export_theory ();
