(* Some laws proved about the process AFTER.				*)
(* 									*)
(* FILE		  : after_laws.ml					*)
(* 									*)
(* READS FILES     : process.th, rules_and_tacs.ml          		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : after_laws.th					*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION    : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)

new_theory "after_laws";

new_parent "process";

val event    = ty_antiq(==`:string`==);
val trace    = ty_antiq(==`:^event list`==);
val alphabet = ty_antiq(==`:^event set`==);

map set_autoloads [
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["CONS_EQ_APPEND", "APPEND_EQ_NIL"]},
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["ALPHA_FST", "TRACES_SND", "APPEND_IN_TRACES",
     "NIL_IN_TRACES", "PROCESS_EQ_SPLIT"]},
{Theory = "prefix",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["ALPHA_PREFIX", "TRACES_PREFIX"]},
{Theory = "after",
 Axioms = ([]:string list),
 Definitions = (["AFTER"]),
 Theorems = ["TRACES_AFTER"]},
{Theory = "choice",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["TRACES_choice", "ALPHA_choice_SPEC"]}
];

map Add_to_sml.add_theory_to_sml ["choice", "after", "prefix", "process_ty", "list_lib1"];


val SET_ABBREV =
    store_thm
       ("SET_ABBREV",
	(--`! A. {x:'a | x IN A} = A`--),
	REWRITE_TAC [EXTENSION] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC []);

val AFTER_NIL =
    save_thm
       ("AFTER_NIL",
	REWRITE_RULE [NIL_IN_TRACES, APPEND, SET_ABBREV,
                      SYM (SPEC_ALL PROCESS_EQ_SPLIT)]
	             (SPECL [(--`P:process`--), (--`[]:^trace`--)] AFTER));

val TRACES_AFTER_THM =
    store_thm
       ("TRACES_AFTER_THM",
	(--`! s t P.
           ((APPEND s t) IN (TRACES P)) ==>
           ((s IN (TRACES P)) /\ (t IN (TRACES (P / s))))`--),
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC APPEND_IN_TRACES THEN
	IMP_RES_TAC TRACES_AFTER THEN
	ASM_REWRITE_TAC [] THEN
	SET_SPEC_TAC THEN
	ASM_REWRITE_TAC []);

val AFTER_APPEND =
    store_thm
       ("AFTER_APPEND",
	(--`! s t P.
           (APPEND s t) IN (TRACES P) ==>
           ((P / (APPEND s t)) = ((P / s) / t))`--),
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC TRACES_AFTER_THM THEN
	IMP_RES_TAC AFTER THEN
	ASM_REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [APPEND_ASSOC]);

val simplify_lemma =
    TAC_PROOF
       (([],
	 (--`! t c. (?t'. (APPEND[c]t = CONS c t') /\ t' IN (TRACES P)) =
	 	 t IN (TRACES P)`--)),
	REPEAT GEN_TAC THEN EQ_TAC THEN
	REWRITE_TAC [SYM (SPEC_ALL CONS_EQ_APPEND), CONS_11] THEN
	REPEAT STRIP_TAC THEN
	(EXISTS_TAC (--`t:^trace`--) ORELSE ALL_TAC) THEN
	ASM_REWRITE_TAC []);

val AFTER_PREFIX =
    store_thm
       ("AFTER_PREFIX",
        (--`! c P. (c IN (ALPHA P)) ==> (((c --> P) / [c]) = P)`--),
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC ALPHA_PREFIX THEN
        IMP_RES_THEN
         (ASSUME_TAC o SET_SPEC_RULE o
          (fn x => REWRITE_RULE [x, IN_UNION, IN_SING]
	   		    (SPECL [(--`c --> P`--), (--`[c:^event]`--)] AFTER)))
        TRACES_PREFIX THEN
        POP_ASSUM
         (STRIP_ASSUME_TAC o
	  (REWRITE_RULE [NIL_IN_TRACES, simplify_lemma, SET_ABBREV]) o
	  (SPEC (--`[]:^trace`--)) o
	  (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)) o
          REWRITE_RULE [APPEND_EQ_NIL, NOT_CONS_NIL, CONS_11]) THEN
        ASM_REWRITE_TAC [PROCESS_EQ_SPLIT]);

val simplify_lemma2 =
    TAC_PROOF
       (([],
	 (--`(?a t'. (APPEND[c]t = CONS a t') /\ a IN B /\ t' IN (TRACES(P a))) =
	  (c IN B /\ t IN (TRACES (P c)))`--)),
	EQ_TAC THEN
	REWRITE_TAC [SYM (SPEC_ALL CONS_EQ_APPEND), CONS_11] THEN
	REPEAT STRIP_TAC THEN
	(EXISTS_TAC (--`c:^event`--) ORELSE ALL_TAC) THEN
	(EXISTS_TAC (--`t:^trace`--) ORELSE ALL_TAC) THEN
	ASM_REWRITE_TAC []);

val simplify_lemma3 =
    TAC_PROOF
       (([],
	 (--`(?(a:^event)t.((c = a) /\ ([] = t)) /\ a IN B /\ t IN (TRACES(P a))) =
	  c IN B`--)),
	EQ_TAC THEN
	REWRITE_TAC [SYM (SPEC_ALL CONS_EQ_APPEND), CONS_11] THEN
	REPEAT STRIP_TAC THEN
	(EXISTS_TAC (--`c:^event`--) ORELSE ALL_TAC) THEN
	(EXISTS_TAC (--`[]:^trace`--) ORELSE ALL_TAC) THEN
	ASM_REWRITE_TAC [NIL_IN_TRACES]);

val AFTER_CHOICE_LEMMA =
    DISCH_ALL
     (ASM_REWRITE_RULE
      [SET_ABBREV]
      (UNDISCH
       (REWRITE_RULE
        [APPEND_EQ_NIL, NOT_CONS_NIL,CONS_11, simplify_lemma2, simplify_lemma3]
        (SET_SPEC_RULE
         (REWRITE_RULE [IN_UNION, IN_SING]
	 (SUBS
	  [UNDISCH_ALL
	   (SPECL [(--`P:^event->process`--),(--`B:^alphabet`--)] TRACES_choice)]
	  (ADD_ASSUM (--`WELL_DEF_ALPHA B P`--)
		     (SPECL [(--`choice B P`--), (--`[c:^event]`--)] AFTER))))))));


val AFTER_CHOICE =
    store_thm
       ("AFTER_CHOICE",
	(--`! c P B. (WELL_DEF_ALPHA B P) /\ (c IN B) ==>
                  (((choice B P) / [c]) = (P c))`--),
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC AFTER_CHOICE_LEMMA THEN
	IMP_RES_TAC ALPHA_choice_SPEC THEN
	ASM_REWRITE_TAC [PROCESS_EQ_SPLIT]);

export_theory();
