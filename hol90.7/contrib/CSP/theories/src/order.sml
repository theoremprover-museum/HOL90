(* Extends The Basic Theory For TRACES In CSP                    	 *)
(* 									 *)
(* FILE		: order.ml     					         *)
(* DESCRIPTION	: Defines the <= operator for finite traces and infinite *)
(*                 alphabets. Also defines the operator (--`in`--) and	 *)
(*		  monotonic functions.                                   *)
(* 									 *)
(* READS FILES	: restrict.th                                   	 *)
(* WRITES FILES : order.th						 *)
(*									 *)
(* AUTHOR	: Albert John Camilleri					 *)
(* AFFILIATION  : Hewlett-Packard Laboratories, Bristol		 	 *)
(* DATE		: 89.02.07						 *)
(* REVISED	: 91.10.01						 *)
(*              : 21.06.93 - BtG - ported to hol90                       *)
(*                 Note: `in' changed to `In' due to naming restrictions *)

new_theory "order";

(* load_library "sets"; *)

new_parent "restrict";

set_autoloads 
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["APPEND_EQ_NIL", "APPEND_NIL", "APPEND_ID"]};

Add_to_sml.add_theory_to_sml "list_lib1";

val PREFIX =
    new_infix_definition
       ("PREFIX",
	--`!s t:('a)list. ($LEQ s t) = ?u:('a) list. (APPEND s u) = t`--,
	450);

val LEAST =
    store_thm
       ("LEAST",
	(--`! s:'a list. [] LEQ s`--),
	REWRITE_TAC [PREFIX, APPEND] THEN
	GEN_TAC THEN
	EXISTS_TAC (--`s:'a list`--) THEN
	REWRITE_TAC []);

val REFLEXIVE =
    store_thm
       ("REFLEXIVE",
	(--`! s:'a list. s LEQ s`--),
	REWRITE_TAC [PREFIX] THEN
	GEN_TAC THEN
	EXISTS_TAC (--`[]:'a list`--) THEN
	REWRITE_TAC [APPEND_NIL]);

val ANTI_SYMM =
    store_thm
       ("ANTI_SYM",
	(--`! s t:('a) list. (s LEQ t /\ t LEQ s) ==> (s = t)`--),
	REWRITE_TAC [PREFIX] THEN
	REPEAT STRIP_TAC THEN
	POP_ASSUM (ASSUME_TAC o SYM) THEN
	UNDISCH_TAC (--`APPEND (s:'a list) u = (t:'a list)`--) THEN
	ASM_REWRITE_TAC [SYM (SPEC_ALL APPEND_ASSOC)] THEN
	ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
	REWRITE_TAC [APPEND_ID, APPEND_EQ_NIL] THEN
	STRIP_TAC);

val TRANS_PREFIX =
    store_thm
       ("TRANS_PREFIX",
	(--`! s t v:('a) list. (s LEQ t /\ t LEQ v) ==> (s LEQ v)`--),
	REWRITE_TAC [PREFIX] THEN
	ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
	REPEAT STRIP_TAC THEN
	EXISTS_TAC (--`(APPEND (u:'a list) u')`--) THEN
	ASM_REWRITE_TAC [APPEND_ASSOC]);

val RIGHT_AND_EXISTS_TAC = CONV_TAC (DEPTH_CONV RIGHT_AND_EXISTS_CONV);

val ST_IND_PREFIX =
    store_thm
       ("ST_IND_PREFIX",
	(--`! (s:'a list) (t:'a list) (x:'a).
           ((APPEND [x] s) LEQ t) =
           ((~(t = [])) /\ (x = HD t) /\ (s LEQ (TL t)))`--),
	GEN_TAC THEN
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [PREFIX, APPEND_EQ_NIL, NOT_CONS_NIL,
	             HD, TL, APPEND, CONS_11] THEN
	RIGHT_AND_EXISTS_TAC THEN
	REWRITE_TAC[]);

val ST_IND_PREFIX' =
    save_thm ("ST_IND_PREFIX'", REWRITE_RULE [APPEND] ST_IND_PREFIX);

val TOT_ORDER_PREFIX =
    store_thm
       ("TOT_ORDER_PREFIX",
	(--`! s t v:('a)list.
           ((s LEQ v) /\ (t LEQ v)) ==> ((s LEQ t) \/ (t LEQ s))`--),
	REPEAT (LIST_INDUCT_TAC THEN
	        REWRITE_TAC [LEAST] THEN
	        GEN_TAC) THEN
	REWRITE_TAC [ST_IND_PREFIX', HD, TL, NOT_CONS_NIL] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC THEN
	ASM_REWRITE_TAC []);

val IN_TRACE =
    new_infix_definition
       ("IN_TRACE",
	(--`! s t:('a)list. $In s t = (? u v. t = (APPEND u (APPEND s v)))`--),
	450);

val MONOTONIC =
    new_definition
       ("MONOTONIC",
	(--`MONOTONIC (f:('a)list->('a)list) =
         ! s t:('a)list. s LEQ t ==> (f s) LEQ (f t)`--));

export_theory();
