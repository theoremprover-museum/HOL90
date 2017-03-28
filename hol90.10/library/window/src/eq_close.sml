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
(* CONTENTS: window infernce rules preserving equality                      *)
(*==========================================================================*)
(*$Id: eq_close.sml,v 1.1.1.1.6.1 1997/07/15 13:09:26 kxs Exp $*)

structure EqClose : sig end =
struct

structure windowTheoryLoaded = windowTheoryLoaded;
open ML_ext Hol_ext Lib CoreHol;
open Term Dsyntax Thm Theory Drule Conv Rules Relations BasicClose;

 
val CONJ1_THM = windowTheoryLoaded.CONJ1_THM;

(*        (B |- A = C)                                                      *)
(* --------------------------    CONJ1_CLOSE "A /\ B"                       *)
(*  (|- (A /\ B) = (C /\ B))                                                *)
fun CONJ1_CLOSE tm th =
    let val {conj1=a,conj2=b} = dest_conj tm
        and  c = rand (concl th)
    in
        MP (SPECL [a,b,c] CONJ1_THM) (DISCH b th)
    end;

val CONJ2_THM = windowTheoryLoaded.CONJ2_THM;

(*        (A |- B = C)                                                      *)
(* --------------------------    CONJ2_CLOSE "A /\ B"                       *)
(*  (|- (A /\ B) = (A /\ C))                                                *)
fun CONJ2_CLOSE tm th =
    let val {conj1=a,conj2=b} = dest_conj tm
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] CONJ2_THM) (DISCH a th)
    end;

val IMP1_THM = windowTheoryLoaded.IMP1_THM;
            
(*         (~B |- A = C)                                                    *)
(* ----------------------------  IMP1_CLOSE "A ==> B"                       *)
(*  (|- (A ==> B) = (C ==> B))                                              *)
fun IMP1_CLOSE tm th = 
    let val {ant=a,conseq=b} = dest_imp tm
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP1_THM) (DISCH (mk_neg b) th)
    end;

val IMP2_THM = windowTheoryLoaded.IMP2_THM;

(*         (A |- B = C)                                                     *)
(* ----------------------------  IMP2_CLOSE "A ==> B"                       *)
(*  (|- (A ==> B) = (A ==> C))                                              *)
fun IMP2_CLOSE tm th =
    let val {ant=a,conseq=b} = dest_imp tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP2_THM) (DISCH a th)
    end;

val PMI1_THM = windowTheoryLoaded.PMI1_THM;

(*         (B |- A = C)                                                     *)
(* ----------------------------  PMI1_CLOSE "A <== B"                       *)
(*  (|- (A <== B) = (C <== B))                                              *)
fun PMI1_CLOSE tm th = 
    let val {conseq=a,ant=b} = dest_pmi tm
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI1_THM) (DISCH b th)
    end;

val PMI2_THM = windowTheoryLoaded.PMI2_THM;

(*         (~A |- B = C)                                                    *)
(* ----------------------------  PMI2_CLOSE "A <== B"                       *)
(*  (|- (A <== B) = (A <== C))                                              *)
fun PMI2_CLOSE tm th = 
    let val {conseq=a,ant=b} = dest_pmi tm
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI2_THM) (DISCH (mk_neg a) th)
    end;

val DISJ1_THM = windowTheoryLoaded.DISJ1_THM;

(*        (~B |- A = C)                                                     *)
(* --------------------------    DISJ1_CLOSE "A \/ B"                       *)
(*  (|- (A \/ B) = (C \/ B))                                                *)
fun DISJ1_CLOSE tm th =
    let val {disj1=a,disj2=b} = dest_disj tm
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] DISJ1_THM) (DISCH (mk_neg b) th)
    end;

val DISJ2_THM = windowTheoryLoaded.DISJ2_THM

(*        (~A |- B = C)                                                     *)
(* ---------------------------   DISJ2_CLOSE "B \/ C"                       *)
(*  (|- (A \/ B) = (A \/ C))                                                *)
fun DISJ2_CLOSE tm th =
    let val {disj1=a,disj2=b} = dest_disj tm
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] DISJ2_THM) (DISCH (mk_neg a) th)
    end;

(* Put all those rules in the data base.                                    *)

val dummy =
(
store_rule
    (
        [RATOR,RAND],
        is_conj,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (rand tm))),
        CONJ1_CLOSE
    );
store_rule
    (
        [RAND],
        is_conj,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (rand (rator tm)))),
        CONJ2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_trueimp,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand tm)))),
        IMP1_CLOSE
    );
store_rule
    (
        [RAND],
        is_trueimp,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (rand (rator tm)))),
        IMP2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_pmi,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (rand tm))),
        PMI1_CLOSE
    );
store_rule
    (
        [RAND],
        is_pmi,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand (rator tm))))),
        PMI2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_disj,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand tm)))),
        DISJ1_CLOSE
    );
store_rule
    (
        [RAND],
        is_disj,
        K (K equiv_tm),
        K (K equiv_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand (rator tm))))),
        DISJ2_CLOSE
    )
);

end;
