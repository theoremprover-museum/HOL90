(*--------------------------------------------------------------------------*)
(*                  Copyright (c) Jim Grundy 1992                           *)
(*                  All rights reserved                                     *)
(*                                                                          *)
(* Jim Grundy, hereafter referred to as `the Author', retains the copyright *)
(* and all other legal rights to the Software contained in this file,       *)
(* hereafter referred to as `the Software'.                                 *)
(*                                                                          *)
(* The Software is made available free of charge on an `as is' basis. No    *)
(* guarantee, either express or implied, of maintenance, reliability,       *)
(* merchantability or suitability for any purpose is made by the Author.    *)
(*                                                                          *)
(* The user is granted the right to make personal or internal use of the    *)
(* Software provided that both:                                             *)
(* 1. The Software is not used for commercial gain.                         *)
(* 2. The user shall not hold the Author liable for any consequences        *)
(*    arising from use of the Software.                                     *)
(*                                                                          *)
(* The user is granted the right to further distribute the Software         *)
(* provided that both:                                                      *)
(* 1. The Software and this statement of rights are not modified.           *)
(* 2. The Software does not form part or the whole of a system distributed  *)
(*    for commercial gain.                                                  *)
(*                                                                          *)
(* The user is granted the right to modify the Software for personal or     *)
(* internal use provided that all of the following conditions are observed: *)
(* 1. The user does not distribute the modified software.                   *)
(* 2. The modified software is not used for commercial gain.                *)
(* 3. The Author retains all rights to the modified software.               *)
(*                                                                          *)
(* Anyone seeking a licence to use this software for commercial purposes is *)
(* invited to contact the Author.                                           *)
(*--------------------------------------------------------------------------*)
(*==========================================================================*)
(* CONTENTS: creates the theorey window                                     *)
(*==========================================================================*)
(*$Id: mk_window.sml,v 1.1.1.1.6.2 1997/07/15 13:10:19 kxs Exp $*)

val path = 
   (!Globals.HOLdir)^"library/window/theories/"^SysParams.theory_file_type^"/"

val _ = Lib.clean_directory path;
val _ = theory_path := path::(!theory_path);

new_theory "window";

val PMI_DEF = new_infix_definition
    ("PMI_DEF", (--`(<== a b) = ($==> b a)`--), 200);

(* |- !x. x ==> x                                                           *)
val IMP_REFL_THM = 
    prove
    (
        (--`!x. x ==> x`--)
    ,
        GEN_TAC THEN
        DISCH_TAC THEN
        (ASM_REWRITE_TAC [])
    );

    save_thm("IMP_REFL_THM",IMP_REFL_THM);

(* |- !x y z. (x ==> y) /\ (y ==> z) ==> x ==> z                            *)
val IMP_TRANS_THM =
    prove
    (
        (--`!x y z. ((x ==> y) /\ (y ==> z)) ==> (x ==> z)`--)
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC (--`x:bool`--)) THEN
        (BOOL_CASES_TAC (--`y:bool`--)) THEN
        (REWRITE_TAC [])
    );

    save_thm("IMP_TRANS_THM",IMP_TRANS_THM);

(* |- !x. x <== x                                                           *)
val PMI_REFL_THM =
    prove
    (
        (--`!x. x <== x`--)
    ,
        GEN_TAC THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        DISCH_TAC THEN
        (ASM_REWRITE_TAC [])
    );

    save_thm("PMI_REFL_THM",PMI_REFL_THM);
    
(* |- !x y z. x <== y /\ y <== z ==> x <== z                                *)
val PMI_TRANS_THM =
    prove
    (
        (--`!x y z. ((x <==y) /\ (y <== z)) ==> (x <== z)`--)
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC (--`x:bool`--)) THEN
        (BOOL_CASES_TAC (--`y:bool`--)) THEN
        (REWRITE_TAC [PMI_DEF])
    );

    save_thm("PMI_TRANS_THM",PMI_TRANS_THM);


val COND1_THM = store_thm("COND1_THM",

        (--`!R A B C D. (!x:'a. R x x) ==>
            (A ==> R B D) ==> (R (A => B | C) (A => D | C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        DISCH_TAC THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (ASM_REWRITE_TAC [])
    );

val COND2_THM = store_thm("COND2_THM",

        (--`!R A B C D. (!x:'a. R x x) ==>
            ((~A) ==> R C D) ==> (R (A => B | C) (A => B | D))`--)
    ,
        (REPEAT GEN_TAC) THEN
        DISCH_TAC THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (ASM_REWRITE_TAC [])
    );


val BODY2_THM = store_thm("BODY2_THM",

        (--`!(c:'a) (f:'a->'b) (g:'a->'b) (r:'b->'b->bool).
            (!v:'a. (v=c) ==> (r (f v) (g v))) ==> (r (f c) (g c))`--)
    ,
        (REPEAT STRIP_TAC) THEN
        (REWRITE_TAC 
            [
                REWRITE_RULE []
                    (SPEC (--`c:'a`--)
                        (ASSUME (--`
                                !v:'a. (v = c) ==> (r:'b->'b->bool)(f v)(g v)
                            `--)))])
    );


val LET_THM = store_thm("LET_THM",

        (--`!(c:'a) (f:'a->'b) (g:'a->'b) (r:'b->'b->bool).
            (!v:'a. (v=c) ==> (r (f v) (g v))) ==>
                (r (LET f c) (LET g c))`--)
    ,
        (REPEAT STRIP_TAC) THEN
        (PURE_ONCE_REWRITE_TAC [LET_DEF]) THEN
        BETA_TAC THEN
        (REWRITE_TAC
            [REWRITE_RULE
                []
                (SPEC (--`c:'a`--)
                      (ASSUME
                        (--`!v:'a. (v = c) ==> (r:'b->'b->bool)(f v)(g v)`--)
                      ))])
    );

val CONJ1_THM = store_thm("CONJ1_THM",

        (--`!A B C. (B ==> (A = C)) ==> ((A /\ B) = (C /\ B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val CONJ2_THM = store_thm("CONJ2_THM",
        (--`!A B C. (A ==> (B = C)) ==> ((A /\ B) = (A /\ C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val IMP1_THM = store_thm("IMP1_THM",
        (--`!A B C. (~B ==> (A = C)) ==> ((A ==> B) = (C ==> B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val IMP2_THM = store_thm("IMP2_THM",
        (--`!A B C. (A ==> (B = C)) ==> ((A ==> B) = (A ==> C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val PMI1_THM = store_thm("PMI1_THM",

        (--`!A B C. (B ==> (A = C)) ==> ((A <== B) = (C <== B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (PURE_REWRITE_TAC [PMI_DEF]) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val PMI2_THM = store_thm("PMI2_THM",

        (--`!A B C. (~A ==> (B = C)) ==> ((A <== B) = (A <== C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (PURE_REWRITE_TAC [PMI_DEF]) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val DISJ1_THM = store_thm("DISJ1_THM",

        (--`!A B C. (~B ==> (A = C)) ==> ((A \/ B) = (C \/ B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val DISJ2_THM = store_thm("DISJ2_THM",

        (--`!A B C. (~A ==> (B = C)) ==> ((A \/ B) = (A \/ C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC (--`A:bool`--) THEN
        BOOL_CASES_TAC (--`B:bool`--) THEN
        REWRITE_TAC []
    );

val DNEG_THM = save_thm("DNEG_THM", CONJUNCT1 NOT_CLAUSES);

val NOT_DISJ_THM = save_thm("NOT_DISJ_THM", 
   GENL [(--`t1:bool`--),(--`t2:bool`--)]
        (CONJUNCT2 (SPEC_ALL DE_MORGAN_THM)));

val NOT_IMP_THM = store_thm("NOT_IMP_THM",
    (--`!t1 t2. ~(t1 ==> t2) = t1 /\ ~t2`--),
    (REWRITE_TAC [IMP_DISJ_THM,NOT_DISJ_THM]));

val NOT_PMI_THM = store_thm("NOT_PMI_THM",
(--`!t1 t2. ~(t1 <== t2) = ~t1 /\ t2`--),
    (REPEAT STRIP_TAC) THEN
     (BOOL_CASES_TAC (--`t1:bool`--)) THEN
     (REWRITE_TAC [PMI_DEF]));

val COND_ABF_THM = store_thm("COND_ABF_THM",
(--`!t1 t2. (t1 => t2 | F) = (t1 /\ t2)`--), 
     (REPEAT STRIP_TAC) THEN
     (BOOL_CASES_TAC (--`t1:bool`--)) THEN
     (REWRITE_TAC [COND_CLAUSES]));

val COND_AFC_THM = store_thm("COND_AFC_THM",
(--`!t1 t3. (t1 => F | t3) = (~t1 /\ t3)`--), 
     (REPEAT STRIP_TAC) THEN
     (BOOL_CASES_TAC (--`t1:bool`--)) THEN
     (REWRITE_TAC [COND_CLAUSES]));


(* used in src/imp_close.sml *)

val IMP_CONJ1_THM = store_thm("IMP_CONJ1_THM",

        (--`!A B C. (B ==> (A ==> C)) ==> ((A /\ B) ==> (C /\ B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val IMP_CONJ2_THM = store_thm("IMP_CONJ2_THM",

        (--`!A B C. (A ==> (B ==> C)) ==> ((A /\ B) ==> (A /\ C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );

val IMP_IMP1_THM = store_thm("IMP_IMP1_THM",

        (--`!A B C. (~B ==> (A <== C)) ==> ((A ==> B) ==> (C ==> B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );

val IMP_IMP2_THM = store_thm("IMP_IMP2_THM",

        (--`!A B C. (A ==> (B ==> C)) ==> ((A ==> B) ==> (A ==> C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );

val IMP_PMI1_THM = store_thm("IMP_PMI1_THM",

        (--`!A B C. (B ==> (A ==> C)) ==> ((A <== B) ==> (C <== B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val IMP_PMI2_THM = store_thm("IMP_PMI2_THM",

        (--`!A B C. (~A ==> (B <== C)) ==> ((A <== B) ==> (A <== C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val IMP_DISJ1_THM = store_thm("IMP_DISJ1_THM",

        (--`!A B C. (~B ==> (A ==> C)) ==> ((A \/ B) ==> (C \/ B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val IMP_DISJ2_THM = store_thm("IMP_DISJ2_THM",

        (--`!A B C. (~A ==> (B ==> C)) ==> ((A \/ B) ==> (A \/ C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val IMP_NEG_THM = store_thm("IMP_NEG_THM",

        (--`!A B. (A <== B) ==> (~A ==> ~B)`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_CONJ1_THM = store_thm("PMI_CONJ1_THM",

        (--`!A B C. (B ==> (A <== C)) ==> ((A /\ B) <== (C /\ B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_CONJ2_THM = store_thm("PMI_CONJ2_THM",

        (--`!A B C. (A ==> (B <== C)) ==> ((A /\ B) <== (A /\ C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_IMP1_THM = store_thm("PMI_IMP1_THM",

        (--`!A B C. (~B ==> (A ==> C)) ==> ((A ==> B) <== (C ==> B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_IMP2_THM = store_thm("PMI_IMP2_THM",

        (--`!A B C. (A ==> (B <== C)) ==> ((A ==> B) <== (A ==> C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_PMI1_THM = store_thm("PMI_PMI1_THM",

        (--`!A B C. (B ==> (A <== C)) ==> ((A <== B) <== (C <== B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_PMI2_THM = store_thm("PMI_PMI2_THM",

        (--`!A B C. (~A ==> (B ==> C)) ==> ((A <== B) <== (A <== C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_DISJ1_THM = store_thm("PMI_DISJ1_THM",

        (--`!A B C. (~B ==> (A <== C)) ==> ((A \/ B) <== (C \/ B))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_DISJ2_THM = store_thm("PMI_DISJ2_THM",

        (--`!A B C. (~A ==> (B <== C)) ==> ((A \/ B) <== (A \/ C))`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (BOOL_CASES_TAC (--`B:bool`--)) THEN
        (REWRITE_TAC [])
    );


val PMI_NEG_THM = store_thm("PMI_NEG_THM",

        (--`!A B. (A ==> B) ==> (~A <== ~B)`--)
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC (--`A:bool`--)) THEN
        (REWRITE_TAC [])
    );

export_theory();
