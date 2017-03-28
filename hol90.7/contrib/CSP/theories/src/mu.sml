(* Trace Semantics for the recursive process MU.				*)
(* 									*)
(* FILE		  : mu.ml 						*)
(* 									*)
(* READS FILES	  : process_fix.th, rules_and_tacs.ml          		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : mu.th						*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION     : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)


new_theory "mu";

new_parent "process_fix";

map set_autoloads [
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = (["IS_PROCESS"]),
 Theorems = ["PROCESS_LEMMA6", "ALPHA_FST", "TRACES_SND",
	     "NIL_IN_TRACES", "APPEND_IN_TRACES", "TRACES_IN_STAR"]},
{Theory = "stop",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["ALPHA_STOP"]},
{Theory = "process_fix",
 Axioms = ([]:string list),
 Definitions = (["ITER", "LIM_PROC", "IT_UNION", "CONTINUOUS"]),
 Theorems = ["LIM_PROC_THM", "IS_PROCESS_LIMIT"]}
];

map Add_to_sml.add_theory_to_sml ["process_ty", "stop", "process_fix"];

val event    = ty_antiq(==`:string`==);
val trace    = ty_antiq(==`:^event list`==);
val alphabet = ty_antiq(==`:^event set`==);

val EXISTS_MU =
    store_thm
       ("EXISTS_MU",
	(--`?f. !A G.
         (CONTINUOUS G) ==> (f A G = (LIM_PROC (\n. ITER n G (STOP A))))`--),
	EXISTS_TAC (--`\ A G. LIM_PROC (\n. ITER n G (STOP A))`--) THEN
	BETA_TAC THEN
	REWRITE_TAC []);

val MU = new_specification {name="MU",
			    consts=[{const_name="MU",fixity=Prefix}],
			    sat_thm=EXISTS_MU};

(*
|- !G A.
    CHAIN(\n. ITER n G(STOP A)) ==>
    IS_PROCESS(A,IT_UNION(\n. TRACES(ITER n G(STOP A))))
*)
val IS_PROCESS_MU =
    save_thm
       ("IS_PROCESS_MU",
	GEN_ALL
	 (REWRITE_RULE
	  [ITER, ALPHA_STOP]
	  (BETA_RULE (SPEC (--`\n. ITER n G (STOP A)`--) IS_PROCESS_LIMIT))));

(*
|- !G A.
    CHAIN(\n. ITER n G(STOP A)) ==>
    CONTINUOUS G ==>
    IS_PROCESS(A,IT_UNION(\n. TRACES(ITER n G(STOP A))))

*)
val IS_PROCESS_MU' =
    store_thm
       ("IS_PROCESS_MU'",
	(--`!G A.
         CHAIN(\n. ITER n G(STOP A)) ==>
         (CONTINUOUS G) ==>
         IS_PROCESS(A,IT_UNION(\n. TRACES(ITER n G(STOP A))))`--),
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC IS_PROCESS_MU THEN
	ASM_REWRITE_TAC []);

(*
|- CHAIN(\n. ITER n G(STOP A)) ==>
   CONTINUOUS G ==>
   (MU A G = ABS_process(A,IT_UNION(\n. TRACES(ITER n G(STOP A)))))
*)

val MU_THM =
    DISCH_ALL
     (SUBS
	  [UNDISCH
	   (REWRITE_RULE
	    [ITER, ALPHA_STOP]
	    (BETA_RULE (SPEC (--`\n. ITER n G (STOP A)`--) LIM_PROC_THM)))]
	  (SPEC_ALL MU));

val ALPHA_MU =
    save_thm
       ("ALPHA_MU",
	DISCH_ALL
	 (DISCH (--`CONTINUOUS G`--)
	  (REWRITE_RULE
	   [SYM (UNDISCH_ALL (SPEC_ALL MU_THM))]
	   (MP (SPECL [(--`A:^alphabet`--), (--`IT_UNION(\n. TRACES(ITER n G(STOP A)))`--)]
		      ALPHA_FST)
	       (UNDISCH (SPEC_ALL IS_PROCESS_MU))))));

val TRACES_MU =
    save_thm
       ("TRACES_MU",
	DISCH_ALL
	 (DISCH (--`CONTINUOUS G`--)
	  (REWRITE_RULE
	   [SYM (UNDISCH_ALL (SPEC_ALL MU_THM))]
	   (MP (SPECL [(--`A:^alphabet`--), (--`IT_UNION(\n. TRACES(ITER n G(STOP A)))`--)]
		      TRACES_SND)
	       (UNDISCH (SPEC_ALL IS_PROCESS_MU))))));

export_theory();
