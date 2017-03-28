(* Extends The Basic Theory For TRACES In CSP                    	 *)
(* 									 *)
(* FILE		: restrict.sml    					 *)
(* DESCRIPTION	: Defines the restriction operator and proves some of    *)
(*                 its properties. Restriction is defined over finite    *)
(*                 traces and infinite alphabets.                        *)
(* 									 *)
(* LOADS LIBRARY : sets							 *)
(* READS FILES	 : traces.th, boolarith2.th                          	 *)
(* WRITES FILES  : restrict.th						 *)
(*									 *)
(* AUTHOR	: Albert J Camilleri					 *)
(* AFFILIATION	: Hewlett-Packard Laboratories, Bristol			 *)
(* DATE		: 89.02.06						 *)
(* REVISED	: 91.10.01						 *)
(*              : 21.06.93 - BtG - ported to hol90                       *)


new_theory "restrict";

(* load_library "sets"; *)

map new_parent ["traces", "boolarith2"];

map set_autoloads [
{Theory = "boolarith2",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["INV_SUC_LEQ", "LESS_EQ_0_N"]},
{Theory = "boolarith1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NOT_EQ_LEQ"]},
{Theory = "list_lib1",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NOT_LENGTH_EQ"]}];

map Add_to_sml.add_theory_to_sml ["list_lib1","boolarith1","boolarith2"];

val RESTRICT =
    new_list_rec_definition
       ("RESTRICT",
        (--`(RESTRICT [] (A:('a)set) = []) /\
         (RESTRICT (CONS (x:'a) t) (A:('a)set) =
            ((x IN A) => (CONS x (RESTRICT t A)) | (RESTRICT t A)))`--));

val STRICT_REST =
    store_thm
       ("STRICT_REST",
	(--`! A:('a)set. RESTRICT [] A = []`--),
	REWRITE_TAC [CONJUNCT1 RESTRICT]);

val DISTRIB_REST =
    store_thm
       ("DISTRIB_REST",
	(--`! s t (A:('a)set).
           RESTRICT (APPEND s t) A = (APPEND (RESTRICT s A) (RESTRICT t A))`--),
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [APPEND, RESTRICT] THEN
	REPEAT STRIP_TAC THEN
	DISJ_CASES_TAC (SPEC (--`(h:'a) IN (A:('a)set)`--) EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC[APPEND]);

val RESTR_EMPTY =
    store_thm
       ("RESTR_EMPTY",
	(--`! s:'a list. RESTRICT s {} = []`--),
	LIST_INDUCT_TAC THEN
	ASM_REWRITE_TAC [RESTRICT, NOT_IN_EMPTY]);

val REP_RESTR =
    store_thm
       ("REP_RESTR",
	(--`! s (A:('a)set) (B:('a)set).
	   (RESTRICT (RESTRICT s A) B) = (RESTRICT s (A INTER B))`--),
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [RESTRICT] THEN
	REPEAT GEN_TAC THEN
	DISJ_CASES_TAC (SPEC (--`(h:'a) IN (A:('a)set)`--) EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC [RESTRICT] THEN
	DISJ_CASES_TAC (SPEC (--`(h:'a) IN (B:('a)set)`--) EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC[IN_INTER]);

val LEQ_ID =
    GEN_ALL
     (REWRITE_RULE [SYM (SPEC_ALL ADD1)] (SPECL [(--`m:num`--),(--`1`--)] LESS_EQ_ADD));

val MAX_LEN_REST =
    store_thm
       ("MAX_LEN_REST",
	(--`! (A:('a)set) s. LENGTH (RESTRICT s A) <= LENGTH s`--),
	GEN_TAC THEN
	LIST_INDUCT_TAC THENL
	[REWRITE_TAC [RESTRICT,LENGTH,LESS_EQ_0_N],
	 GEN_TAC THEN
	 DISJ_CASES_TAC (SPEC (--`(h:'a) IN (A:('a)set)`--) EXCLUDED_MIDDLE) THEN
	 ASM_REWRITE_TAC[RESTRICT,LENGTH,INV_SUC_LEQ] THEN
	 ASSUME_TAC (SPEC (--`LENGTH (s:'a list)`--) LEQ_ID) THEN
	 IMP_RES_TAC LESS_EQ_TRANS THEN
	 ASM_REWRITE_TAC []]);

val REST_LEMMA =
    store_thm
       ("REST_LEMMA",
	(--`!(A:('a)set) (s:('a)list) a.
           ~((LENGTH (RESTRICT s A)) = (LENGTH (CONS a s)))`--),
	REWRITE_TAC
	  [NOT_EQ_LEQ,
	   LENGTH,
	   REWRITE_RULE
	     [GEN_ALL (SYM (SPEC_ALL (LESS_OR_EQ)))]
	     (ONCE_REWRITE_RULE [DISJ_SYM] LESS_THM),
	   MAX_LEN_REST]);

val REST_CONS_THM =
    save_thm
       ("REST_CONS_THM",
	GEN_ALL
	 (MP (SPECL [(--`CONS a (s:'a list)`--), (--`RESTRICT s (A:('a)set)`--)]
		    NOT_LENGTH_EQ)
	     (SPEC_ALL REST_LEMMA)));

export_theory();
