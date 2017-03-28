(* Extends the basic theory of lists present in HOL88                  	 *)
(* 									 *)
(* FILE		: list_lib.ml     					 *)
(* DESCRIPTION	: Makes available some more specialised (yet commonly    *)
(*                 used) theorems than are present in the built-in list  *)
(*                 theory.                                               *)
(* 									 *)
(* READS FILES	: None                                  		 *)
(* WRITES FILES : list_lib1.th						 *)
(*									 *)
(* AUTHOR	: Albert J Camilleri					 *)
(* AFFILIATION  : Hewlett-Packard Laboratories, Bristol			 *)
(* DATE		: 89.02.03						 *)
(* REVISED	: 91.10.01						 *)
(*              : 21.06.93 - BtG - ported to hol90                       *)

new_theory "list_lib1";

val APPEND_ID =
    store_thm
       ("APPEND_ID",
        (--`! l l':('a)list. (l = (APPEND l l')) = (l' = [])`--),
	LIST_INDUCT_TAC THEN
	REWRITE_TAC[APPEND] THENL
        [REWRITE_TAC[SPECL [(--`l:'a list`--), (--`[]:'a list`--)]
	                   (INST_TYPE [{redex= ==`:'a`==,residue= ==`:'a list`==}
				      ] EQ_SYM_EQ)],
	 ASM_REWRITE_TAC[CONS_11]]);

val APPEND_NIL =
    store_thm
       ("APPEND_NIL",
	(--`! l:'a list. APPEND l [] = l`--),
	LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);

val LENGTH_LESS_EQ =
    store_thm
       ("LENGTH_LESS_EQ",
	(--`! (l1:('a)list) (l2:('a)list).
           LENGTH l1 <= LENGTH l2 ==> !a:'a. LENGTH l1 < LENGTH (CONS a l2)`--),
	REWRITE_TAC [LENGTH,
	             (ONCE_REWRITE_RULE [DISJ_SYM] LESS_THM),
		     LESS_OR_EQ]);

val NOT_LENGTH_EQ =
    store_thm
       ("NOT_LENGTH_EQ",
	(--`! l2 l1:('a)list. ~(LENGTH l1 = LENGTH l2) ==> ~(l1 = l2)`--),
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [LENGTH, LENGTH_NIL] THEN
	GEN_TAC THEN
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [NOT_NIL_CONS, LENGTH, CONS_11, INV_SUC_EQ] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC);

val APPEND_EQ_NIL =
    store_thm
       ("APPEND_EQ_NIL",
	(--`!l1 l2:'a list. ((APPEND l1 l2) = []) = ((l1 = []) /\ (l2 = []))`--),
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [APPEND, NOT_CONS_NIL]);

val NULL_EQ_NIL =
    store_thm
       ("NULL_EQ_NIL",
	(--`!l:'a list. (l = []) = (NULL l)`--),
	LIST_INDUCT_TAC THEN
	ASM_REWRITE_TAC [NULL_DEF, NOT_CONS_NIL]);

val HD_APPEND =
    store_thm
       ("HD_APPEND",
	(--`! l:('a)list. (~(l = [])) ==> (! l'. (HD (APPEND l l')) = (HD l))`--),
	REWRITE_TAC [NULL_EQ_NIL] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_THEN (ASSUME_TAC o SYM) CONS THEN
	ONCE_ASM_REWRITE_TAC [] THEN
	REWRITE_TAC [APPEND, HD]);

val TL_APPEND =
    store_thm
       ("TL_APPEND",
	(--`! l:('a)list.
           (~(l = [])) ==> (! l'. (TL (APPEND l l')) = (APPEND (TL l) l'))`--),
	REWRITE_TAC [NULL_EQ_NIL] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_THEN (ASSUME_TAC o SYM) CONS THEN
	ONCE_ASM_REWRITE_TAC [] THEN
	REWRITE_TAC [APPEND, TL]);

val ONE_MEMBER_LIST =
    store_thm
       ("ONE_MEMBER_LIST",
        (--`! s t (a:'a). ((APPEND s t) = [a]) ==> ((s = []) \/ (s = [a]))`--),
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [APPEND, CONS_11, APPEND_EQ_NIL] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);

val CONS_MEMBER_LIST =
    store_thm
       ("CONS_MEMBER_LIST",
        (--`! s s' t (a:'a).
	  ((APPEND s t) = (CONS a s')) ==>
	  ((s = []) \/ (?r. (s = (CONS a r)) /\ (s' = (APPEND r t))))`--),
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [APPEND, CONS_11, NOT_CONS_NIL] THEN
	REPEAT STRIP_TAC THEN
	EXISTS_TAC (--`s:'a list`--) THEN
	ASM_REWRITE_TAC []);

val CONS_EQ_APPEND =
    store_thm
       ("CONS_EQ_APPEND",
	(--`! (a:'a) l. CONS a l = (APPEND [a] l)`--),
	REWRITE_TAC [APPEND]);

export_theory();
