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
(* CONTENTS: reflexivity, transitivity, strengh and window rules tables.    *)
(*==========================================================================*)
(*$Id: relations.sml,v 1.1.1.1.6.1 1997/07/15 13:09:47 kxs Exp $*)

structure Relations :
    sig
      type term
      type thm
        val add_relation : thm * thm -> unit
        val reflexive : term -> thm
        val transitive : thm -> thm
        val add_weak : thm -> unit
        val weaken : term -> thm -> thm
        val is_weaker : term -> term -> bool
    end =

struct

type term = CoreHol.Term.term
type thm = CoreHol.Thm.thm;

open windowTheoryLoaded Lib CoreHol;
open ML_ext Hol_ext;
open Term Dsyntax Thm Match Drule Parse Tactical Tactic Rewrite Conv Resolve;
infix THEN;


(* Simple matching MP.                                                      *)
fun FAST_MATCH_MP th1 th2 =
    let val matcher = match_term (#ant (dest_imp (concl th1))) (concl th2)
    in
        MP (INST_TY_TERM matcher th1) th2
    end;

(* MATCH_IMP_TRANS takes two thorems of the form                            *)
(*   (|- A ==> B) and  (|- Y ==> Z).                                        *)
(* It matches B to Y or Y to B and returns                                  *)
(* (|- (match A) ==> (match Z)                                              *)
fun MATCH_IMP_TRANS th1 th2 =
    let val {ant=A,conseq=B} = dest_imp (concl th1)
        and {ant=Y,conseq=Z} = dest_imp (concl th2)
    in
            (IMP_TRANS (INST_TY_TERM (match_term B Y) th1) th2)
        handle _ =>
            (IMP_TRANS th1 (INST_TY_TERM (match_term Y B) th2))
    end handle _ => WIN_ERR{function="MATCH_IMP_TRANS",message=""};


(* The functions below maintain reflexivity and transitivity information    *)
(* about the relations used with the window inference library.              *)
(* To add a relation `R' to the system, call the function add_rel           *)
(* as follows:                                                              *)
(*  add_rel (|- !x. x R x) (|- !x y z. ((x R y) ==> (y R z)) ==> (x R z))   *)
(*                                                                          *)
(* From then on the function `reflexive' will work as follows:              *)
(*                                                                          *)
(* ------- reflexive "t R t"                                                *)
(*  t R t                                                                   *)
(*                                                                          *)
(* and the function `transitive' will work as follows:                      *)
(*  (H |- t R u /\ u R v)                                                   *)
(* ---------------------------- transitive                                  *)
(*       H |- t R v                                                         *)
(*                                                                          *)
(* and the function `known_relation' will henceforth return true for `R'.   *)
local
    (* check_refl_thm takes a theorem of the following form:                *)
    (*   |- !x y. (x = y) ==> (x R y)                                       *)
    (* and returns the relation R.                                          *)
    (* If the theorem it is given is not of the correct form, then it fails.*)
    fun check_refl_th th =
        let val tm = concl th in
        let val {Bvar=x,Body} = dest_forall tm in
        let val R = assert is_const (rator (rator Body)) in
            if tm = (--`!^x. ^R ^x ^x`--) then R else fail ()
        end end end 
        handle _ =>
            WIN_ERR{function="add_relation",
                    message="reflexive theorem is not of the correct form"}
    (* check_trans_thm takes a theorem of the following form:               *)
    (*   |- !x y. ((x R y) /\ (y R z)) ==> (x R z)                          *)
    (* and returns the relation R.                                          *)
    (* If the theorem it is given is not of the correct form, then it fails.*)
    fun check_trans_th th =
        let val tm = concl th in
        let val ([x,y,z],b) = strip_forall tm in
        let val R = assert is_const (rator (rator (rand b))) in
            if tm = (--`!^x ^y ^z. ((^R ^x ^y) /\ (^R ^y ^z)) ==> (^R ^x ^z)`--)
            then R else fail ()
        end end end
        handle _ =>
            WIN_ERR{function="addrelation",
                    message="transitive theorem is not of the correct form"}
    val refl_tbl = ref ([]:thm list)
    val trans_tbl = ref ([]:thm list)
    val rel_tbl = ref ([]:term list)
in
    fun add_rel (refl_th,trans_th) = 
        let val rR = check_refl_th refl_th
            and tR = check_trans_th trans_th
        in
            if not (rR = tR) then
                WIN_ERR{function="add_relation",
                        message="relations not the same"}
            else
                refl_tbl := refl_th::(!refl_tbl);
                trans_tbl := (SPEC_ALL trans_th)::(!trans_tbl);
                rel_tbl := rR::(!rel_tbl)
        end
    fun reflexive tm = tryfirst (fn t => (PART_MATCH I t tm)) (!refl_tbl)
    fun transitive t1t2 = tryfirst (fn t => (FAST_MATCH_MP t t1t2)) (!trans_tbl)
    fun known_relation R = exists (can (C match_term R)) (!rel_tbl)
end;

(* A list of theorems stating which relations are stonger than which.       *)
val weakenings = ref ([] : thm list);

(* A table which stores for each relation the list of relations that        *)
(* are stonger than it.   This information can be infered from the          *)
(* weakenings table and is only duplicated here to increase                 *)
(* performance.                                                             *)

val weak_table = ref ([] : (term * (term list)) list);

(* weaker r1 r2 is true if the relation r1 is recorded as being             *)
(* weaker than relation r2.                                                 *)
fun weaker r1 r2 = 
    let val x = genvar (dom r1) 
        and y = genvar (dom r2) in
    let val con = mk_imp
                    {   ant=(list_mk_comb (r2,[x,y])),
                        conseq=(list_mk_comb (r1,[x,y]))    }
    in
        exists (can ((C match_term con) o concl)) (!weakenings)
    end end handle _ => false;

(* Add a theorem that asserts one relation is stronger than another to      *)
(* the data base of information about relations.                            *)
local
    (* check_weak_thm takes a theorem of the following form:                *)
    (*   |- !x y. (x S y) ==> (x R y)                                       *)
    (* and returns the pair (S,R)                                           *)
    (* If the theorem it is given is not of the correct form, then it fails.*)
    fun check_weak_thm th = 
        let val ([],all_x_y_Sxy_imp_Rxy) = dest_thm th in
        let val ([x,y],Sxy_imp_Rxy) = strip_forall all_x_y_Sxy_imp_Rxy in
        let val {ant,conseq} = dest_imp Sxy_imp_Rxy in
        let val S = rator (rator ant)
            and R = rator (rator conseq)
        in
            if (known_relation S) andalso (known_relation R) andalso
               ((--`!^x ^y. (^S ^x ^y) ==> (^R ^x ^y)`--) = all_x_y_Sxy_imp_Rxy)
            then
                SPEC_ALL th
            else
                fail ()
        end end end end
        handle _ =>
            WIN_ERR{function="check_weak_thm",
                message="theorem not of the correct form, or relation unknown"};
    (* rel_str r gives a list of relations stronger than r,                 *)
    (* in order of increasing strength.                                     *)
    (* This verion only works for the functions actually stored,            *)
    (* like it might know that "=:*->*->bool" is stronger than itsself      *)
    (* if that is stored (which it will be), but it wont be able to         *)
    (* infer the "=:num->num->bool" is stronger than itsself.              *)
    fun rel_str r =
        let val ss = map (rator o rator o rand o rator o concl) (!weakenings) in
        let val mss = mapfilter
                        (fn s => inst (match_type (type_of s) (type_of r)) s) ss
        in
            sort weaker (term_setify (filter (weaker r) mss))
        end end;
    (* Removes redundant theorems from a list of weakening theorems.        *)
    fun crush [] = []
     |  crush (t::ts) =
            if exists (can ((C match_term (concl t)) o concl)) ts then
                crush ts
            else
                t::(crush ts)
in
    fun add_weak th =
        let val wth = check_weak_thm th in
            weakenings :=
                crush
                (  wth
                :: (!weakenings)
                @  (mapfilter (MATCH_IMP_TRANS wth) (!weakenings))
                @  (mapfilter (C MATCH_IMP_TRANS wth) (!weakenings))
                );
            let val wrs = term_setify
                            (map (rator o rator o rand o concl) (!weakenings))
            in
                weak_table := combine (wrs, map rel_str wrs)
            end
        end
end;

(*  (H |- t R s)                                                            *)
(* -------------- weaken "Q"                                                *)
(*  (H |- t Q s)                                                            *)
fun weaken (Q : term) (th : thm) =
    let val R = rator (rator (concl th)) in
        if Q = R then
            (* The else clause will handle this case too,   *)
            (* but it is faster not to do any searching.    *)
            th
        else
            tryfirst (fn t => let val th1 = FAST_MATCH_MP t th in
                              let val R = rator (rator (concl th1)) in
                                  INST_TY_TERM (match_term R Q) th1
                              end end
                     )
                     (!weakenings)
    end;

(* Faster version of weaker.                                                *)
local
    fun relative_strengths r =
        let val (s,sl) = first (can ((C match_term r) o fst)) (!weak_table) in
        let val mtch = snd (match_term s r) in
            map (inst mtch) sl
        end end
in
    fun is_weaker r1 r2 = mem r2 (relative_strengths r1)
end;



fun add_relation(refl_thm,trans_thm) =
    (
        add_rel(refl_thm,trans_thm);
        let val ty = type_of (bndvar (rand (concl refl_thm)))
            and r = rator (rator (body (rand (concl refl_thm)))) in
        let val (x,y) = (genvar ty,genvar ty) in
        let val th1 = 
                prove
                    (
                        (--`!^x ^y. (^x = ^y) ==> (^r ^x ^y)`--)
                    ,
                        GEN_TAC THEN
                        GEN_TAC THEN
                        DISCH_TAC THEN
                        (ONCE_ASM_REWRITE_TAC []) THEN
                        (MATCH_ACCEPT_TAC refl_thm)
                    )
            and th2 = GENL [x,y] (SPEC (--`^r ^x ^y`--) IMP_REFL_THM)
        in
            add_weak th1;
            add_weak th2
        end end end
    );

end;
