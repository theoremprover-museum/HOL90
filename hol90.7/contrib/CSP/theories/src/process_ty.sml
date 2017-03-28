(* Theory containing the type definition of a process and some basic	*)
(* theorems about processes in general.					*)
(* 									*)
(* FILE		  : process_ty.ml 					*)
(* 									*)
(* READS FILES	   : star.th                               		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : process_ty.th					*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION    : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)

new_theory "process_ty";

(* load_library "sets"; *)
(* load_library "string"; *)

new_parent "star";

val event    = ty_antiq(==`:string`==);
val trace    = ty_antiq(==`:^event list`==);
val alphabet = ty_antiq(==`:^event set`==);

map set_autoloads [
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["APPEND_EQ_NIL"]},
{Theory = "restrict",
 Axioms = ([]:string list),
 Definitions = (["RESTRICT"]),
 Theorems = []:string list},
{Theory = "star",
 Axioms = ([]:string list),
 Definitions = (["STAR"]),
 Theorems = []:string list}
];

map Add_to_sml.add_theory_to_sml ["list_lib1", "restrict", "star"];


val IS_PROCESS =
    new_definition
      ("IS_PROCESS",
       (--`IS_PROCESS (A:^alphabet, (TR:(^trace)set)) =
        (TR SUBSET (STAR A)) /\
        ([] IN TR) /\
        (!s t:^trace. ((APPEND s t) IN TR) ==> (s IN TR))`--));

val EXISTS_PROCESS =
    store_thm
       ("EXISTS_PROCESS",
	(--`? P. (\(A, TR). IS_PROCESS(A,TR)) P`--),
        EXISTS_TAC (--`(EMPTY:^alphabet, {[]:^trace})`--) THEN
	REWRITE_TAC [UNCURRY_DEF] THEN
	BETA_TAC THEN
	REWRITE_TAC [IS_PROCESS, SUBSET_DEF, STAR, IN_SING] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [APPEND_EQ_NIL] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [RESTRICT]);

val PROCESS_TYPE =
    new_type_definition
       {name="process",
	pred=(--`\(A,TR). IS_PROCESS(A,TR)`--),
	inhab_thm=EXISTS_PROCESS};

val [PROCESS_LEMMA1, PROCESS_LEMMA2, PROCESS_LEMMA3,
     PROCESS_LEMMA4, PROCESS_LEMMA5, PROCESS_LEMMA6] =
    map2 (fn x => fn y =>
           save_thm
            ("PROCESS_LEMMA"^x,
	      (REWRITE_RULE []
	       (BETA_RULE
	       (REWRITE_RULE
	        [UNCURRY_DEF]
	        (ONCE_REWRITE_RULE [SYM (SPEC_ALL PAIR)] y))))))
    ["1", "2", "3", "4", "5", "6"]
    (let val th = 
         define_new_type_bijections
         {name="process_ISO_DEF",ABS="ABS_process",
	  REP="REP_process",tyax=PROCESS_TYPE}
     in
     [prove_rep_fn_one_one th,
      prove_rep_fn_onto th,
      prove_abs_fn_one_one th,
      prove_abs_fn_onto th,
      CONJUNCT1 th,
      CONJUNCT2 th]
     end);
	 

val ALPHA_DEF =
    new_definition
       ("ALPHA_DEF",
	(--`ALPHA P = FST (REP_process P)`--));

val TRACES_DEF =
    new_definition
       ("TRACES_DEF",
	(--`TRACES P = SND (REP_process P)`--));

val ID_PROCESS =
    store_thm
       ("ID_PROCESS",
        (--`!P. ABS_process(ALPHA P,TRACES P) = P`--),
	REWRITE_TAC [ALPHA_DEF, TRACES_DEF, PROCESS_LEMMA5]);

val ID_PROCESS' =
    store_thm
       ("ID_PROCESS'",
        (--`!P. (ALPHA P,TRACES P) = (REP_process P)`--),
	REWRITE_TAC [ALPHA_DEF, TRACES_DEF, PAIR]);

val SPLIT_PROCESS =
    REWRITE_RULE
     [IS_PROCESS]
     (AP_TERM
       (--`IS_PROCESS`--)
       (SYM
        (SPEC (--`v:^alphabet#(^trace set)`--)
              (INST_TYPE [{residue= ==`:^alphabet`==,redex= ==`:'a`==},
			  {residue= ==`:(^trace set)`==,redex= ==`:'b`==}] PAIR))));

val PROC_TAC =
    (let val lemma =
     (fst
      (EQ_IMP_RULE (SPEC_ALL (REWRITE_RULE [SPLIT_PROCESS] PROCESS_LEMMA6))))
      in
     REWRITE_TAC [SPLIT_PROCESS, ALPHA_DEF, TRACES_DEF] THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC lemma THEN
     (UNDISCH_TAC (--`(APPEND s t) IN (SND(REP_process P))`--) ORELSE ALL_TAC) THEN
     ASM_REWRITE_TAC []
     end);


val proc_LEMMA1 =
    store_thm
       ("proc_LEMMA1",
	(--`!(P:process) (v:^alphabet#((^trace)set)).
	  ((P = ABS_process v) /\ (IS_PROCESS v))
          ==>
          [] IN (TRACES P)`--),
          PROC_TAC);

val proc_LEMMA2 =
    store_thm
       ("proc_LEMMA2",
	(--`!(P:process) (v:^alphabet#((^trace)set)).
	  ((P = ABS_process v) /\ (IS_PROCESS v))
          ==>
          (!s t. ((APPEND s t) IN (TRACES P)) ==> (s IN (TRACES P)))`--),
	PROC_TAC);

val proc_LEMMA3 =
    store_thm
       ("proc_LEMMA3",
	(--`!(P:process) (v:^alphabet#((^trace)set)).
	  ((P = ABS_process v) /\ (IS_PROCESS v))
          ==>
          ((TRACES P) SUBSET (STAR (ALPHA P)))`--),
	PROC_TAC);

val [NIL_IN_TRACES, APPEND_IN_TRACES, TRACES_IN_STAR] =
    map
     (fn (x,y) => 
      let val th1 = REWRITE_RULE [PAIR] (SPEC (--`P:process`--) PROCESS_LEMMA4)
	  val th2 = UNDISCH_ALL (SPEC_ALL y)
      in
      save_thm (x, GEN_ALL (CHOOSE ((--`v:(^alphabet#((^trace)set))`--), th1)
			    th2))end)
     [("NIL_IN_TRACES", proc_LEMMA1),
      ("APPEND_IN_TRACES", proc_LEMMA2),
      ("TRACES_IN_STAR", proc_LEMMA3)];

val ALPHA_FST =
    store_thm
       ("ALPHA_FST",
	(--`! x y. IS_PROCESS(x,y) ==> (ALPHA (ABS_process (x, y)) = x)`--),
	REWRITE_TAC [PROCESS_LEMMA6, ALPHA_DEF] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);

val TRACES_SND =
    store_thm
       ("TRACES_SND",
	(--`! x y. IS_PROCESS(x,y) ==> (TRACES (ABS_process (x, y)) = y)`--),
	REWRITE_TAC [PROCESS_LEMMA6, TRACES_DEF] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);

val PROCESS_EQ_SPLIT =
    store_thm
       ("PROCESS_EQ_SPLIT",
	(--`! P Q.
	   (P = Q) =
	   (((ALPHA P) = (ALPHA Q)) /\ ((TRACES P) = (TRACES Q)))`--),
	REWRITE_TAC
	 [ALPHA_DEF, TRACES_DEF, SYM (SPEC_ALL PAIR_EQ), PROCESS_LEMMA1]);

export_theory ();
