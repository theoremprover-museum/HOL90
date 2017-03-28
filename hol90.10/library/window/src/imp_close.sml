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
(* CONTENTS: window inference preserving implication (and backward implies) *)
(*==========================================================================*)
(*$Id: imp_close.sml,v 1.1.1.1.6.1 1997/07/15 13:09:34 kxs Exp $*)

structure ImpClose : sig end =

struct

structure windowTheoryLoaded = windowTheoryLoaded;
open ML_ext Hol_ext Lib CoreHol;
open Term Dsyntax Thm Theory Drule Conv Rules Relations BasicClose;

val IMP_CONJ1_THM = windowTheoryLoaded.IMP_CONJ1_THM;

(*        (B |- A ==> C)                                                     *)
(* ----------------------------  IMP_CONJ1_CLOSE "A /\ B"                    *)
(*  (|- (A /\ B) ==> (C /\ B))                                               *)
fun IMP_CONJ1_CLOSE tm th =
    let val {conj1=a,conj2=b} = dest_conj tm
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_CONJ1_THM) (DISCH b th)
    end;

val IMP_CONJ2_THM = windowTheoryLoaded.IMP_CONJ2_THM;

(*        (A |- B ==> C)                                                     *)
(* ----------------------------  IMP_CONJ2_CLOSE "A /\ B"                    *)
(*  (|- (A /\ B) ==> (A /\ C))                                               *)
fun IMP_CONJ2_CLOSE tm th =
    let val {conj1=a,conj2=b} = dest_conj tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_CONJ2_THM) (DISCH a th)
    end;

val IMP_IMP1_THM = windowTheoryLoaded.IMP_IMP1_THM;

(*         (~B |- A <== C)                                                   *)
(* ------------------------------    IMP_IMP1_CLOSE "A ==> B"                *)
(*  (|- (A ==> B) ==> (C ==> B))                                             *)
fun IMP_IMP1_CLOSE tm th = 
    let val {ant=a,conseq=b} = dest_imp tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_IMP1_THM) (DISCH (mk_neg b) th)
    end;

val IMP_IMP2_THM = windowTheoryLoaded.IMP_IMP2_THM;

(*         (A |- B ==> C)                                                    *)
(* ------------------------------    IMP_IMP2_CLOSE "A ==> B"                *)
(*  (|- (A ==> B) ==> (A ==> C))                                             *)
fun IMP_IMP2_CLOSE tm th =
    let val {ant=a,conseq=b} = dest_imp tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_IMP2_THM) (DISCH a th)
    end;
    
val IMP_PMI1_THM = windowTheoryLoaded.IMP_PMI1_THM;

(*         (B |- A ==> C)                                                    *)
(* ------------------------------    IMP_PMI1_CLOSE "A <== B"                *)
(*  (|- (A <== B) ==> (C <== B))                                             *)
fun IMP_PMI1_CLOSE tm th =
    let val {conseq=a,ant=b} = dest_pmi tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_PMI1_THM) (DISCH b th)
    end;

val IMP_PMI2_THM = windowTheoryLoaded.IMP_PMI2_THM;
    
(*         (~A |- B <== C)                                                   *)
(* ------------------------------    IMP_PMI2_CLOSE "A <== B"                *)
(*  (|- (A <== B) ==> (A <== C))                                             *)
fun IMP_PMI2_CLOSE tm th = 
    let val {conseq=a,ant=b} = dest_pmi tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_PMI2_THM) (DISCH (mk_neg a) th)
    end;

val IMP_DISJ1_THM = windowTheoryLoaded.IMP_DISJ1_THM;

(*        (~B |- A ==> C)                                                    *)
(* ----------------------------  IMP_DISJ1_CLOSE "A \/ B"                    *)
(*  (|- (A \/ B) ==> (C \/ B))                                               *)
fun IMP_DISJ1_CLOSE tm th =
    let val {disj1=a,disj2=b} = dest_disj tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_DISJ1_THM) (DISCH (mk_neg b) th)
    end;

val IMP_DISJ2_THM = windowTheoryLoaded.IMP_DISJ2_THM;

(*        (~A |- B ==> C)                                                    *)
(* ----------------------------  IMP_DISJ2_CLOSE "A \/ B"                    *)
(*  (|- (A \/ B) ==> (A \/ C))                                               *)
fun IMP_DISJ2_CLOSE tm th =
    let val {disj1=a,disj2=b} = dest_disj tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] IMP_DISJ2_THM) (DISCH (mk_neg a) th)
    end;

val IMP_NEG_THM = windowTheoryLoaded.IMP_NEG_THM;

(*   (|- A <== B)                                                            *)
(* ----------------   IMP_NEG_CLOSE "~A"                                     *)
(*  (|- ~A ==> ~B)                                                           *)
fun IMP_NEG_CLOSE (tm:term) th =
    let val {conseq=a,ant=b} = dest_pmi (concl th) in
        MP (SPECL [a,b] IMP_NEG_THM) th
    end;

(*      (|- A ==> B)                                                         *)
(* -----------------------   IMP_ALL_CLOSE "!v.A"                            *)
(*  (|- (!v.A) ==> (!v.B)                                                    *)
fun IMP_ALL_CLOSE tm th =
    let val v = #Bvar(dest_forall tm) in
        DISCH tm (GEN v (MP th (SPEC v (ASSUME tm))))
    end;

(*      (|- B ==> A)                                                         *)
(* -----------------------   IMP_EXISTS_CLOSE "?v.A"                         *)
(*  (|- (?v.B) ==> (?v.A)                                                    *)
fun IMP_EXISTS_CLOSE tm th =
    let val v = #Bvar(dest_exists tm) in
	EXISTS_IMP v th
    end;

val PMI_CONJ1_THM = windowTheoryLoaded.PMI_CONJ1_THM;

(*        (B |- A <== C)                                                     *)
(* ----------------------------  PMI_CONJ1_CLOSE "A /\ B"                    *)
(*  (|- (A /\ B) <== (C /\ B))                                               *)
fun PMI_CONJ1_CLOSE tm th =
    let val {conj1=a,conj2=b} = dest_conj tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_CONJ1_THM) (DISCH b th)
    end;

val PMI_CONJ2_THM = windowTheoryLoaded.PMI_CONJ2_THM;

(*        (A |- B <== C)                                                     *)
(* ----------------------------  PMI_CONJ2_CLOSE "A /\ B"                    *)
(*  (|- (A /\ B) <== (A /\ C))                                               *)
fun PMI_CONJ2_CLOSE tm th =
    let val {conj1=a,conj2=b} = dest_conj tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_CONJ2_THM) (DISCH a th)
    end;

val PMI_IMP1_THM = windowTheoryLoaded.PMI_IMP1_THM;

(*         (~B |- A ==> C)                                                   *)
(* ------------------------------    PMI_IMP1_CLOSE "A ==> B"                *)
(*  (|- (A ==> B) <== (C ==> B))                                             *)
fun PMI_IMP1_CLOSE tm th =
    let val {ant=a,conseq=b} = dest_imp tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_IMP1_THM) (DISCH (mk_neg b) th)
    end;

val PMI_IMP2_THM = windowTheoryLoaded.PMI_IMP2_THM;

(*         (A |- B <== C)                                                    *)
(* ------------------------------    PMI_IMP2_CLOSE "A ==> B"                *)
(*  (|- (A ==> B) <== (A ==> C))                                             *)
fun PMI_IMP2_CLOSE tm th =
    let val {ant=a,conseq=b} = dest_imp tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_IMP2_THM) (DISCH a th)
    end;

val PMI_PMI1_THM = windowTheoryLoaded.PMI_PMI1_THM;

(*         (B |- A <== C)                                                    *)
(* ------------------------------    PMI_PMI1_CLOSE "A <== B"                *)
(*  (|- (A <== B) <== (C <== B))                                             *)
fun PMI_PMI1_CLOSE tm th =
    let val {conseq=a,ant=b} = dest_pmi tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_PMI1_THM) (DISCH b th)
    end;

val PMI_PMI2_THM = windowTheoryLoaded.PMI_PMI2_THM;

(*         (~A |- B ==> C)                                                   *)
(* ------------------------------    PMI_PMI2_CLOSE "A <== B"                *)
(*  (|- (A <== B) <== (A <== C))                                             *)
fun PMI_PMI2_CLOSE tm th =
    let val {conseq=a,ant=b} = dest_pmi tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_PMI2_THM) (DISCH (mk_neg a) th)
    end;

val PMI_DISJ1_THM = windowTheoryLoaded.PMI_DISJ1_THM;

(*        (~B |- A <== C)                                                    *)
(* ----------------------------  PMI_DISJ1_CLOSE "A \/ B"                    *)
(*  (|- (A \/ B) <== (C \/ B))                                               *)
fun PMI_DISJ1_CLOSE tm th =
    let val {disj1=a,disj2=b} = dest_disj tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_DISJ1_THM) (DISCH (mk_neg b) th)
    end;

val PMI_DISJ2_THM = windowTheoryLoaded.PMI_DISJ2_THM;

(*        (~A |- B <== C)                                                    *)
(* ----------------------------  PMI_DISJ2_CLOSE "A \/ B"                    *)
(*  (|- (A \/ B) <== (A \/ C))                                               *)
fun PMI_DISJ2_CLOSE tm th =
    let val {disj1=a,disj2=b} = dest_disj tm 
        and c = rand (concl th)
    in
        MP (SPECL [a,b,c] PMI_DISJ2_THM) (DISCH (mk_neg a) th)
    end;

val PMI_NEG_THM = windowTheoryLoaded.PMI_NEG_THM;

(*   (|- A ==> B)                                                            *)
(* ----------------   PMI_NEG_CLOSE "~A"                                     *)
(*  (|- ~A <== ~B)                                                           *)
fun PMI_NEG_CLOSE (tm:term) th =
    let val {ant=a,conseq=b} = dest_imp (concl th) in
        MP (SPECL [a,b] PMI_NEG_THM) th
    end;

(*      (|- A <== B)                                                         *)
(* -----------------------   PMI_ALL_CLOSE "!v.A"                            *)
(*  (|- (!v.A) <== (!v.B)                                                    *)
fun PMI_ALL_CLOSE tm th =
    let val b = rand (concl th)
        and v = #Bvar(dest_forall tm)
    in
        IMP_PMI (IMP_ALL_CLOSE (mk_forall {Bvar=v,Body=b}) (PMI_IMP th))
    end;

(*      (|- B <== A)                                                         *)
(* -----------------------   PMI_EXIST_CLOSE "?v.A"                          *)
(*  (|- (?v.B) <== (?v.A)                                                    *)
fun PMI_EXISTS_CLOSE tm th =
    let val v = #Bvar(dest_exists tm) in
	EXISTS_PMI v th
    end;

(* Put all these rules in the database.                                      *)

val dummy =
(
store_rule
    (
        [RATOR,RAND],
        is_conj,
        K (K imp_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (rand tm))),
        IMP_CONJ1_CLOSE
    );
store_rule
    (
        [RAND],
        is_conj,
        K (K imp_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (rand (rator tm)))),
        IMP_CONJ2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_trueimp,
        K (K pmi_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand tm)))),
        IMP_IMP1_CLOSE
    );
store_rule
    (
        [RAND],
        is_trueimp,
        K (K imp_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (rand (rator tm)))),
        IMP_IMP2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_pmi,
        K (K imp_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (rand tm))),
        IMP_PMI1_CLOSE
    );
store_rule
    (
        [RAND],
        is_pmi,
        K (K pmi_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand (rator tm))))),
        IMP_PMI2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_disj,
        K (K imp_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand tm)))),
        IMP_DISJ1_CLOSE
    );
store_rule
    (
        [RAND],
        is_disj,
        K (K imp_tm),
        K (K imp_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand (rator tm))))),
        IMP_DISJ2_CLOSE
    );
store_rule
    (
        [RAND],
        is_neg,
        K (K pmi_tm),
        K (K imp_tm),
        K [],
        IMP_NEG_CLOSE
    );
store_rule
    (
        [RAND,BODY],
        is_forall,
        K (K imp_tm),
        K (K imp_tm),
        K [],
        IMP_ALL_CLOSE
        );
store_rule
    (
        [RAND,BODY],
        is_exists,
        K (K imp_tm),
        K (K imp_tm),
        K [],
        IMP_EXISTS_CLOSE
        );
store_rule
    (
        [RATOR,RAND],
        is_conj,
        K (K pmi_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (rand tm))),
        PMI_CONJ1_CLOSE
    );
store_rule
    (
        [RAND],
        is_conj,
        K (K pmi_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (rand (rator tm)))),
        PMI_CONJ2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_trueimp,
        K (K imp_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand tm)))),
        PMI_IMP1_CLOSE
    );
store_rule
    (
        [RAND],
        is_trueimp,
        K (K pmi_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (rand (rator tm)))),
        PMI_IMP2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_pmi,
        K (K pmi_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (rand tm))),
        PMI_PMI1_CLOSE
    );
store_rule
    (
        [RAND],
        is_pmi,
        K (K imp_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand (rator tm))))),
        PMI_PMI2_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_disj,
        K (K pmi_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand tm)))),
        PMI_DISJ1_CLOSE
    );
store_rule
    (
        [RAND],
        is_disj,
        K (K pmi_tm),
        K (K pmi_tm),
        (fn tm => SMASH (ASSUME (mk_neg (rand (rator tm))))),
        PMI_DISJ2_CLOSE
    );
store_rule
    (
        [RAND],
        is_neg,
        K (K imp_tm),
        K (K pmi_tm),
        K [],
        PMI_NEG_CLOSE
    );
store_rule
    (
        [RAND,BODY],
        is_forall,
        K (K pmi_tm),
        K (K pmi_tm),
        K [],
        PMI_ALL_CLOSE
        );
store_rule
    (
        [RAND,BODY],
        is_exists,
        K (K pmi_tm),
        K (K pmi_tm),
        K [],
        PMI_EXISTS_CLOSE
        )
);

end;
