(* Builds Up A Basic Theory For TRACES In CSP                    	 *)
(* 									 *)
(* FILE		: traces.ml     					 *)
(* DESCRIPTION	: Defines TRACES as lists of EVENTS where, for the time  *)
(*                 being, EVENTS are represented by the type 'a.         *)
(*                 The theory consists of definitions and theorems       *)
(*                 regarding the following operators on TRACES:          *)
(*                 distributive, strict, iterate, restrict, 'a, and <=.  *)
(* 									 *)
(* READS FILES	: list_lib1.th                          		 *)
(* WRITES FILES : traces.th						 *)
(*									 *)
(* AUTHOR	: Albert J Camilleri					 *)
(* AFFILIATION  : Hewlett-Packard Laboratories, Bristol			 *)
(* DATE		: 89.02.03						 *)
(* MODIFIED	: 89.07.19						 *)
(* REVISED	: 91.10.01						 *)
(*              : 21.06.93 - BtG - ported to hol90                       *)

new_theory "traces";

new_parent "list_lib1";

set_autoloads
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["APPEND_ID", "APPEND_NIL"]};
Add_to_sml.add_theory_to_sml "list_lib1";


val trace = ty_antiq(==`:'a list`==);


(* ====================================================================== *)
(*                                                                        *)
(*                             STRICT PREDICATE                           *)
(*                                                                        *)
(* ====================================================================== *)

val TR_STRICT =
    new_definition
       ("TR_STRICT", (--`TR_STRICT (f:^trace->^trace) = (f [] = [])`--));


(* ====================================================================== *)
(*                                                                        *)
(*                          DISTRIBUTIVE PREDICATE                        *)
(*                                                                        *)
(* ====================================================================== *)

val TR_DIST =
    new_definition
       ("TR_DIST",
        (--`TR_DIST (f:^trace->^trace) =
         ! s t:^trace. (f (APPEND s t) = (APPEND (f s) (f t)))`--));


(*   THEOREM: All distributive functions on traces are strict.            *)

val TR_DIST_STRICT =
    store_thm
       ("TR_DIST_STRICT",
        (--`! f:^trace->^trace. (TR_DIST f) ==> (TR_STRICT f)`--),
	let val thm =
          (REWRITE_RULE
            [APPEND, APPEND_ID]
            (DISCH_ALL
              (SPECL [(--`[]:^trace`--),(--`[]:^trace`--)]
                     (ASSUME (--`(!s t:^trace. (f(APPEND s t):^trace) =
                              APPEND(f s)(f t))`--)))))
	in 
        REWRITE_TAC [TR_STRICT, TR_DIST] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC thm
	end );


(* ====================================================================== *)
(*                                                                        *)
(*                               ITERATION                                *)
(*                                                                        *)
(* ====================================================================== *)

val ITERATE =
    new_recursive_definition
    {def= --`(ITERATE 0 (t:^trace) = []) /\
             (ITERATE (SUC n) t = APPEND t (ITERATE n t))`--,
     fixity=Prefix,
     name = "ITERATE",
     rec_axiom = num_Axiom};

val ITER_COMM =
    store_thm
       ("ITER_COMM",
        (--`! (n:num) (t:^trace). ITERATE (SUC n) t = APPEND (ITERATE n t) t`--),
        INDUCT_TAC THENL
        [REWRITE_TAC[ITERATE,APPEND,APPEND_NIL],
         GEN_TAC THEN
         SUBST1_TAC (SPEC_ALL (CONJUNCT2 ITERATE)) THEN
         REWRITE_TAC[SPEC (--`SUC n`--) (CONJUNCT2 ITERATE)] THEN
         ASM_REWRITE_TAC[APPEND_ASSOC]]);

val ITER_APP =
    store_thm
       ("ITER_APP",
        (--`! (n:num) (s:^trace) (t:^trace).
           ITERATE (SUC n) (APPEND s t) =
           APPEND s (APPEND (ITERATE n (APPEND t s)) t)`--),
	let val thm =
        prove ((--`!a b c d e:('a)list.
                 APPEND (APPEND a b) (APPEND c (APPEND d e)) =
                 (APPEND a (APPEND (APPEND (APPEND b c) d) e))`--),
               REWRITE_TAC[APPEND_ASSOC])
	in 
        INDUCT_TAC THENL
        [REWRITE_TAC[ITERATE,APPEND,APPEND_NIL],
         REWRITE_TAC[SPEC (--`SUC n`--) (CONJUNCT2 ITERATE)] THEN
         ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[thm, SYM (SPEC_ALL (CONJUNCT2 ITERATE))] THEN
         ASM_REWRITE_TAC[]]
	end);

export_theory();
