(* A supplementary theory of Boolean Algebra and Arithmetic theorems.    *)
(*                                                                       *)
(* FILE          : boolarith1.sml                                        *)
(* DESCRIPTION   : Extends the boolean and arithmetic built-in theories  *)
(*                 with some theorems which are needed for mechanizing   *)
(*                 csp.                                                  *)
(*                                                                       *)
(* LOADS LIBRARY : taut                                                  *)
(* READS FILES   : None                                                  *)
(* WRITES FILES  : boolarith1.thms                                       *)
(*                                                                       *)
(* AUTHOR        : Albert J Camilleri                                    *)
(* AFFILIATION   : Hewlett-Packard Laboratories, Bristol                 *)
(* DATE          : 85.11.15                                              *)
(* MODIFIED      : 89.07.20                                              *)
(* REVISED       : 91.10.01                                              *)
(*               : 21.06.93 - BtG - ported to hol90                      *)

new_theory "boolarith1";

(* Load the Tautology Checker                                            *)

(* load_library "taut"; -- already loaded in the saved image being used  *)

val NOT_EQ =
    save_thm ("NOT_EQ",
              Taut.TAUT_PROVE (--`!t1 t2. (t1 = t2) = (~t1 = ~t2)`--));

val DISJ_ASSOC =
    save_thm ("DISJ_ASSOC",
              Taut.TAUT_PROVE (--`!t1 t2 t3. t1 \/ t2 \/ t3 = (t1 \/ t2) \/ t3`--));

val LEFT_CONJ_DISTRIB =
    save_thm ("LEFT_CONJ_DISTRIB",
              Taut.TAUT_PROVE (--`!t1 t2 t3:bool.
                           (t1 /\ (t2 \/ t3)) = ((t1 /\ t2) \/ (t1 /\ t3))`--));

val RIGHT_CONJ_DISTRIB =
    save_thm ("RIGHT_CONJ_DISTRIB",
              Taut.TAUT_PROVE (--`!t1 t2 t3:bool.
                           ((t2 \/ t3) /\ t1) = ((t2 /\ t1) \/ (t3 /\ t1))`--));

val LEFT_DISJ_DISTRIB =
    save_thm ("LEFT_DISJ_DISTRIB",
              Taut.TAUT_PROVE (--`!t1 t2 t3:bool.
                           (t1 \/ (t2 /\ t3)) = ((t1 \/ t2) /\ (t1 \/ t3))`--));

val RIGHT_DISJ_DISTRIB =
    save_thm ("RIGHT_DISJ_DISTRIB",
              Taut.TAUT_PROVE (--`!t1 t2 t3:bool.
                           ((t2 /\ t3) \/ t1) = ((t2 \/ t1) /\ (t3 \/ t1))`--));

val LEFT_DISJ_CONJ =
    save_thm ("LEFT_DISJ_CONJ",
              Taut.TAUT_PROVE (--`!a b . a /\ b \/ b = b`--));

val GREATER_EQ =
    store_thm ("GREATER_EQ",
               (--`! a b:num. (a >= b) = (b <= a)`--),
               REPEAT STRIP_TAC THEN
               REWRITE_TAC [GREATER_OR_EQ,LESS_OR_EQ,GREATER] THEN
               SUBST_TAC [(SPECL
                            [(--`a:num`--),(--`b:num`--)]
                            (INST_TYPE [{residue= ==`:num`==,
					 redex = ==`:'a`==}] EQ_SYM_EQ))]
               THEN REWRITE_TAC[]);

val NOT_LEQ =
    store_thm ("NOT_LEQ",
               (--`!a b. (~(a <= b)) = (b < a)`--),
               REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)]);

val EQ_LEQ =
    store_thm ("EQ_LEQ",
               (--`! a b : num . (a = b) = ((a <= b) /\ (b <= a))`--),
               REPEAT STRIP_TAC THEN
               REWRITE_TAC [LESS_OR_EQ,
                            LEFT_CONJ_DISTRIB,
                            RIGHT_CONJ_DISTRIB,
                            LESS_ANTISYM] THEN
               SUBST_TAC [(SPECL
                            [(--`b:num`--),(--`a:num`--)]
                            (INST_TYPE [{residue= ==`:num`==,
					 redex= ==`:'a`==}] EQ_SYM_EQ))] THEN
               REWRITE_TAC [INST [{residue= --`((a:num) = b)`--,redex = --`t1:bool`--},
                                  {residue= --`b < a`--,redex= --`t2:bool`--}]
                                 (SPEC_ALL CONJ_SYM),
                            DISJ_ASSOC,
                            SYM (SPEC_ALL RIGHT_CONJ_DISTRIB),
                            LEFT_DISJ_CONJ]);

val NOT_EQ_LEQ =
    store_thm ("NOT_EQ_LEQ",
               (--`! a b : num . ~(a = b) = ((a < b) \/ (b < a))`--),
               REPEAT STRIP_TAC THEN
               REWRITE_TAC [INST [{residue= --`~((a:num) = b)`--,
				   redex= --`t1:bool`--},
                                  {residue= --`((a < b) \/ (b < a))`--,
				   redex= --`t2:bool`--}]
                                 (SPEC_ALL NOT_EQ),
                            DE_MORGAN_THM,
                            NOT_LESS] THEN
               SUBST_TAC [SPECL [(--`b <= a`--),(--`a <= b`--)] CONJ_SYM] THEN
               REWRITE_TAC [EQ_LEQ]);

val LESS_LESSEQ =
    store_thm ("LESS_LESSEQ",
               (--`!a b. (a < b) = ((a + 1) <= b)`--),
               REWRITE_TAC [SYM (SPEC_ALL ADD1), LESS_EQ]);

export_theory();
