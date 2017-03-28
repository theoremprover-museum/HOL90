(* Some laws proved about the process PAR.                               *)
(*                                                                       *)
(* FILE            : par_laws.ml                                         *)
(*                                                                       *)
(* READS FILES     : process.th, rules_and_tacs.ml                       *)
(* LOADS LIBRARIES : sets, string, taut                                  *)
(* WRITES FILES    : par_laws.th                                         *)
(*                                                                       *)
(* AUTHOR          : Albert J Camilleri                                  *)
(* AFFILIATION     : Hewlett-Packard Laboratories, Bristol               *)
(* DATE            : 89.03.15                                            *)
(* REVISED         : 91.10.01                                            *)
(*                 : 21.06.93 - BtG - ported to hol90                    *)

new_theory "par_laws";

new_parent "process";

val event    = ty_antiq(==`:string`==);
val trace    = ty_antiq(==`:^event list`==);
val alphabet = ty_antiq(==`:^event set`==);

map set_autoloads [
{Theory = "process_ty",
 Axioms = ([]:string list),
 Definitions = ([]:string list),
 Theorems = ["NIL_IN_TRACES", "TRACES_IN_STAR", "ID_PROCESS",
     "ALPHA_FST", "PROCESS_EQ_SPLIT"]},
{Theory = "restrict",
 Axioms = ([]:string list),
 Definitions = (["RESTRICT"]:string list),
 Theorems = ["STRICT_REST", "DISTRIB_REST", "REP_RESTR"]},
{Theory = "star",
 Axioms = ([]:string list),
 Definitions = (["STAR"]),
 Theorems = ["NIL_IN_STAR", "CONS_STAR"]}
];

map Add_to_sml.add_theory_to_sml ["list_lib1", "restrict", "star", "process_ty",
				  "stop", "run", "prefix", "parallel", "restrict"];

val INTER_UNION_IMP =
    store_thm
       ("INTER_UNION_IMP",
        (--`! x (A:('a)set) (B:('a)set). x IN (A INTER B) ==> x IN (A UNION B)`--),
        REWRITE_TAC [IN_INTER, IN_UNION] THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC []);

val PAR_SYM =
    store_thm
       ("PAR_SYM",
        (--`! P Q: process. P PAR Q = Q PAR P`--),
        REPEAT STRIP_TAC THEN
        REWRITE_TAC [PROCESS_EQ_SPLIT, PAR] THEN
        SUBST_TAC
         [SPECL [(--`ALPHA Q`--), (--`ALPHA P`--)]
                (INST_TYPE [{residue= ==`:^event`==,redex= ==`:'a`==}] UNION_COMM)] THEN
        REWRITE_TAC
         [CONJ_DISCH
           (--`s IN (STAR((ALPHA P) UNION (ALPHA Q)))`--)
           (ADD_ASSUM
            (--`s IN (STAR((ALPHA P) UNION (ALPHA Q)))`--)
            (SPECL [(--`(RESTRICT s (ALPHA Q)) IN (TRACES Q)`--),
                    (--`(RESTRICT s (ALPHA P)) IN (TRACES P)`--)] CONJ_SYM))]);

val INT_UNI_LEMMA =
    TAC_PROOF (([], (--`! A B:('a)set. (A UNION B) INTER A = A`--)),
               REWRITE_TAC [EXTENSION, IN_UNION, IN_INTER] THEN
               REPEAT GEN_TAC THEN
               BOOL_CASES_TAC (--`(x:'a) IN A`--) THEN
               REWRITE_TAC []);

val INT_UNI_LEMMA' =
    GEN_ALL (SUBS [SPECL [(--`A:('a)set`--), (--`B:('a)set`--)] UNION_COMM]
                  (SPEC_ALL INT_UNI_LEMMA));

val PAR_ASSOC =
    store_thm
       ("PAR_ASSOC",
        (--`! P Q R: process. (P PAR (Q PAR R)) = ((P PAR Q) PAR R)`--),
        REPEAT STRIP_TAC THEN
        REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
        SUBST_TAC (CONJUNCTS (SPECL [(--`P:process`--), (--`Q PAR R`--)] PAR)) THEN
        SUBST_TAC (CONJUNCTS (SPECL [(--`P PAR Q`--), (--`R:process`--)] PAR)) THEN
        REWRITE_TAC [ALPHA_PAR, TRACES_PAR, UNION_ASSOC, STAR] THEN
        SET_SPEC_TAC THEN
        REWRITE_TAC [REP_RESTR, INTER_IDEMPOT, INT_UNI_LEMMA,
                     INT_UNI_LEMMA', CONJ_ASSOC]);

val CONS_RESTR =
    TAC_PROOF
       (([],
         (--`!(a:'a) s A. RESTRICT (CONS a s) A = RESTRICT (APPEND [a] s) A`--)),
        REWRITE_TAC [APPEND]);

val PAR_STOP_TRACES =
    TAC_PROOF
       (([],
         (--`s IN (STAR (ALPHA P)) /\
          (RESTRICT s (ALPHA P)) IN (TRACES P) /\
          (RESTRICT s (ALPHA P) = []) = (s = [])`--)),
        EQ_TAC THENL
        [SPEC_TAC ((--`s:^trace`--), (--`s:^trace`--)) THEN
         LIST_INDUCT_TAC THENL
         [REWRITE_TAC [NIL_IN_STAR, STRICT_REST, NIL_IN_TRACES],
          REWRITE_TAC [CONS_STAR] THEN
          REPEAT STRIP_TAC THEN
          UNDISCH_TAC (--`RESTRICT(CONS h s)(ALPHA P) = []`--) THEN
          ASM_REWRITE_TAC [RESTRICT, NOT_CONS_NIL]],
         STRIP_TAC THEN
         ASM_REWRITE_TAC [NIL_IN_STAR, STRICT_REST, NIL_IN_TRACES]]);

val PAR_STOP =
    store_thm
       ("PAR_STOP",
        (--`! P:process. P PAR (STOP (ALPHA P)) = (STOP (ALPHA P))`--),
        REWRITE_TAC [PROCESS_EQ_SPLIT, PAR, ALPHA_STOP, TRACES_STOP,
                     STOP, UNION_IDEMPOT, EXTENSION, IN_SING] THEN
        SET_SPEC_TAC THEN
        REWRITE_TAC [PAR_STOP_TRACES]);

val PAR_RUN_TRACES =
    TAC_PROOF
       (([],
         (--`{s | s IN (STAR (ALPHA P)) /\
               (RESTRICT s (ALPHA P)) IN (TRACES P) /\
               (RESTRICT s (ALPHA P)) IN (STAR (ALPHA P))} =
          (TRACES P)`--)),
        REWRITE_TAC [EXTENSION] THEN
        SET_SPEC_TAC THEN
        GEN_TAC THEN
        EQ_TAC THENL
        [SUBST_TAC
         [SET_SPEC_RULE
          (SPEC (--`x:^trace`--)
                (REWRITE_RULE
                 [EXTENSION]
                 (SPEC (--`ALPHA P`--)
		  (INST_TYPE [{residue= ==`:^event`==, redex= ==`:'a`==}] STAR))))] THEN
         STRIP_TAC THEN
         UNDISCH_TAC (--`(RESTRICT x(ALPHA P)) IN (TRACES P)`--) THEN
         ASM_REWRITE_TAC [],
         STRIP_TAC THEN
         IMP_RES_TAC
          (SET_SPEC_RULE (REWRITE_RULE [STAR, SUBSET_DEF] TRACES_IN_STAR)) THEN
         IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] TRACES_IN_STAR) THEN
         ASM_REWRITE_TAC []]);

val PAR_RUN =
    store_thm
       ("PAR_RUN",
        (--`! P:process. P PAR (RUN (ALPHA P)) = P`--),
        REWRITE_TAC
         [PROCESS_EQ_SPLIT, PAR, ALPHA_RUN, TRACES_RUN,
          UNION_IDEMPOT, PAR_RUN_TRACES, ID_PROCESS]);

val PREFIX_PAR_1 =
    store_thm
       ("PREFIX_PAR_1",
        (--`!c P Q. (c IN ((ALPHA P) INTER (ALPHA Q))) ==>
                 ((c --> P) PAR (c --> Q) = (c --> (P PAR Q)))`--),
        let val blemma  = Taut.TAUT_PROVE (--`!a b c. ((a /\ b) ==> c) = (a ==> (b ==>c))`--)
            val blemma' =
          Taut.TAUT_PROVE
          (--`!a b c d. (a ==> (b ==> (c ==> d))) = (a ==> (c ==> (b ==> d)))`--)
	in
	REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC
          (REWRITE_RULE
            [SYM (SPEC_ALL ALPHA_PAR)]
            (SPECL [(--`c:string`--), (--`ALPHA P`--), (--`ALPHA Q`--)]
                   (INST_TYPE [{residue= ==`:^event`==,redex= ==`:'a`==}] INTER_UNION_IMP))) THEN
        UNDISCH_TAC (--`c IN ((ALPHA P) INTER (ALPHA Q))`--) THEN
        REWRITE_TAC [IN_INTER] THEN
        STRIP_TAC THEN
        IMP_RES_TAC ALPHA_PREFIX THEN
        IMP_RES_TAC TRACES_PREFIX THEN
        ASM_REWRITE_TAC
         [ALPHA_PAR, TRACES_PAR, EXTENSION, IN_UNION, IN_SING] THEN
        SET_SPEC_TAC THEN
        GEN_TAC THEN
        EQ_TAC THENL
        [DISJ_CASES_TAC (SPEC (--`x:^trace = []`--) EXCLUDED_MIDDLE) THEN
         ASM_REWRITE_TAC [] THEN
         IMP_RES_TAC (REWRITE_RULE [(SYM o SPEC_ALL) NULL_EQ_NIL] CONS) THEN
         POP_ASSUM ((fn x => ONCE_ASM_REWRITE_TAC [x]) o SYM) THEN
         ASM_REWRITE_TAC [RESTRICT, CONS_STAR, IN_UNION, blemma] THEN
         DISCH_THEN STRIP_ASSUME_TAC THENL
         [ALL_TAC , ONCE_REWRITE_TAC [blemma']] THEN
         ASM_REWRITE_TAC [NOT_CONS_NIL, CONS_11] THEN
         DISCH_TAC THEN
         DISCH_THEN STRIP_ASSUME_TAC THEN
         ASM_REWRITE_TAC [NOT_CONS_NIL, CONS_11] THEN
         REPEAT STRIP_TAC THEN
         EXISTS_TAC (--`TL (x:^trace)`--) THEN
         ASM_REWRITE_TAC [],
         REPEAT STRIP_TAC THEN
         ASM_REWRITE_TAC [NIL_IN_STAR, RESTRICT, CONS_STAR, IN_UNION] THEN
         DISJ2_TAC THENL
         [EXISTS_TAC (--`RESTRICT t (ALPHA P)`--),
          EXISTS_TAC (--`RESTRICT t (ALPHA Q)`--)] THEN
         ASM_REWRITE_TAC [RESTRICT]]
	end);

val Sets_Lemma =
    let val th =
        REWRITE_RULE [SUBSET_DEF, IN_INSERT, NOT_IN_EMPTY]
                     (ASSUME (--`{(c:^event);(d:^event)} SUBSET A`--)) 
	val th1 = REWRITE_RULE [] (SPEC (--`c:^event`--) th)
	val th2 = REWRITE_RULE [] (SPEC (--`d:^event`--) th)
    in
	DISCH_ALL (CONJ th1 th2)
    end;

val PREFIX_PAR_2_LEMMA =
    TAC_PROOF
       (([(--`~(c:^event = d)`--), (--`c IN (ALPHA P)`--), (--`c IN (ALPHA Q)`--),
                            (--`d IN (ALPHA P)`--), (--`d IN (ALPHA Q)`--)],
         (--`!x:^trace.
          (x IN (STAR((ALPHA P) UNION (ALPHA Q))) /\
           ((RESTRICT x(ALPHA P) = []) \/
            (?t. (RESTRICT x(ALPHA P) = CONS c t) /\ t IN (TRACES P))) /\
           ((RESTRICT x(ALPHA Q) = []) \/
            (?t. (RESTRICT x(ALPHA Q) = CONS d t) /\ t IN (TRACES Q)))) =
          (x = [])`--)),
       let val lemma1 =
          TAC_PROOF
           (([], (--`!(h:^event) (c:^event) A. ((c IN A) /\ (h = c)) ==> (h IN A)`--)),
            REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])
       in
        LIST_INDUCT_TAC THENL
        [REWRITE_TAC [NIL_IN_STAR, RESTRICT],
         GEN_TAC THEN
         REWRITE_TAC [CONS_STAR] THEN
         DISJ_CASES_TAC
          (SPEC (--`h IN ((ALPHA P) UNION (ALPHA Q))`--) EXCLUDED_MIDDLE) THENL
         [UNDISCH_TAC (--`h IN ((ALPHA P) UNION (ALPHA Q))`--) THEN
          REWRITE_TAC [IN_UNION] THEN
          REPEAT STRIP_TAC THENL
          [DISJ_CASES_TAC (SPEC (--`h = (c:^event)`--) EXCLUDED_MIDDLE),
           DISJ_CASES_TAC (SPEC (--`h = (d:^event)`--) EXCLUDED_MIDDLE)] THEN
          IMP_RES_TAC lemma1 THEN
          ASM_REWRITE_TAC [RESTRICT, NOT_CONS_NIL, CONS_11] THEN
          SUBST_TAC
           [SPECL [(--`d:^event`--), (--`c:^event`--)]
                  (INST_TYPE [{residue= ==`:^event`==,redex= ==`:'a`==}] EQ_SYM_EQ)] THEN
          ASM_REWRITE_TAC [],
          ASM_REWRITE_TAC [NOT_CONS_NIL]]]
	end);

val PREFIX_PAR_2 =
    store_thm
       ("PREFIX_PAR_2",
        (--`!c d P Q.
          ({c;d} SUBSET ((ALPHA P) INTER (ALPHA Q)) /\ ~(c = d)) ==>
          ((c --> P) PAR (d --> Q) = (STOP ((ALPHA P) UNION (ALPHA Q))))`--),
        REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC Sets_Lemma THEN
        IMP_RES_TAC
          (REWRITE_RULE
            [SYM (SPEC_ALL ALPHA_PAR)]
            (SPECL [(--`c:string`--), (--`ALPHA P`--), (--`ALPHA Q`--)]
                   (INST_TYPE [{residue= ==`:^event`==,redex= ==`:'a`==}] INTER_UNION_IMP))) THEN
        UNDISCH_TAC (--`c IN ((ALPHA P) INTER (ALPHA Q))`--) THEN
        UNDISCH_TAC (--`d IN ((ALPHA P) INTER (ALPHA Q))`--) THEN
        REWRITE_TAC [IN_INTER] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC ALPHA_PREFIX THEN
        IMP_RES_TAC TRACES_PREFIX THEN
        ASM_REWRITE_TAC [ALPHA_PAR, TRACES_PAR, ALPHA_STOP, TRACES_STOP,
                         EXTENSION, IN_UNION, IN_SING] THEN
        SET_SPEC_TAC THEN
        ACCEPT_TAC PREFIX_PAR_2_LEMMA);

export_theory ();
