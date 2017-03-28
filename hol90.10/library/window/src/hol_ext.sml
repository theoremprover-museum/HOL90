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
(* CONTENTS: miscelaneous HOL utility functions                             *)
(*==========================================================================*)
(*$Id: hol_ext.sml,v 1.1.1.1.6.1 1997/07/15 13:09:32 kxs Exp $*)

structure Hol_ext : Hol_ext_sig =
struct

type hol_type = CoreHol.Type.hol_type
type term = CoreHol.Term.term
type thm = CoreHol.Thm.thm
type goal = Abbrev.goal
type conv = Abbrev.conv

open windowTheoryLoaded;
open Lib ML_ext Exception CoreHol Parse;
open Type Term Dsyntax Thm Theory Drule Conv Add_to_sml;


open Rsyntax;
val true_tm = (--`T`--)
val false_tm = (--`F`--)
val imp_tm = (--`==>`--)
val pmi_tm = (--`<==`--)
val equiv_tm = (--`= :bool->bool->bool`--);

(* (bndvar (--`\v.b`--)) = (--`v`--)                                        *)
val bndvar = #Bvar o dest_abs;

(* (term_mem tm tms) = tm mem tms.                                          *)
fun term_mem tm tms = exists (fn t => aconv t tm) tms;

(* (term_subset l1 l2) = (!x. (x mem l1) ==> (x mem l2))                    *)
fun term_subset (l1 : term list) (l2 : term list) =
    all (fn t => exists (aconv t) l2) l1;

(* (term_setify tl) = the subset of tl with all the distinct terms.         *)
fun term_setify [] = []
 |  term_setify (h::t) = h::(term_setify (filter (fn a => not (aconv h a)) t));

(* (term_intersect l1 l2) = l1 intersection l2.                             *)
fun term_intersect l1 l2 =
    term_setify (filter (fn t => exists (aconv t) l2) l1);

(* (term_union l1 l2) = l1 union l2.                                        *)
fun term_union l1 l2 = term_setify (l1 @ l2);

(* term_subtract l1 l2 = (l1 - l2)                                          *)
fun term_subtract l1 l2 = filter (fn e => not (term_mem e l2)) l1;

(* better_thm t1 t2 = true, iff t1 t2 share the same conclusion and t1's    *)
(*   hyptheses are a subset of those of t2.                                 *)
fun better_thm t1 t2 = (aconv (concl t1) (concl t2)) andalso
                       (term_subset (hyp t1) (hyp t2));

(* better_goal c1 c2 = true, iff c1 c2 share the same conclusion and c1's   *)
(*   hypotheses are a subset of those of c2.                                *)
fun better_goal (c1:goal) (c2:goal) =
    (aconv (snd c1) (snd c2)) andalso (term_subset (fst c1) (fst c2));

(* (thm_subset l1 l2) = (!x. (x mem l1) ==> (x mem l2))                     *)
fun thm_subset (l1 : thm list) (l2 : thm list) = 
    all (fn t1 => exists (fn t2 => better_thm t2 t1) l2) l1;    

(* Check to see if two theorem sets are equal.                              *)
fun  thm_set_equal l1 l2 = (thm_subset l1 l2) andalso (thm_subset l2 l1);

(* (goal_subset l1 l2) = (!x. (x mem l1) ==> (x mem l2))                    *)
fun goal_subset (l1 : goal list) (l2 : goal list) = 
    all (fn c1 => exists (fn c2 => better_goal c2 c1) l2) l1;   

(* Check to see if two goal sets are equal.                                 *)
fun goal_set_equal l1 l2 = (goal_subset l1 l2) andalso (goal_subset l2 l1);

(* Crush out all the redundant theorems in a set.                           *)
fun thm_setify [] = []
 |  thm_setify (t::ts) =
        if (exists (fn u => better_thm u t) ts) then
            thm_setify ts
        else
            t::(thm_setify (filter (fn u => not (better_thm t u)) ts));

(* Crush out all the redundant conjectures in a set.                        *)
fun goal_setify ([] : goal list) = []
 |  goal_setify (g::gs) =
        if (exists (fn u => better_goal u g) gs) then
            goal_setify gs
        else
            g::(goal_setify (filter (fn u => not (better_goal g u)) gs));

(* thm_subtract l1 l2 = (l1 - l2)                                           *)
fun thm_subtract l1 l2 =
    filter (fn u => not (exists (fn v => better_thm v u) l2)) l1;

(* goal_subtract l1 l2 = (l1 - l2)                                          *)
fun goal_subtract l1 l2 =
    filter (fn u => not (exists (fn v => better_goal v u) l2)) l1;

(* fun_type [t1,t2,...tn] = makes the type ":t1 -> t2 -> ... tn".           *)
fun fun_type ts = 
    if (length ts) < 2 then
        WIN_ERR{function="fun_type",message="not enough arguments"}
    else
        end_itlist (fn ty1 => fn ty2 => mk_type{Tyop="fun",Args=[ty1,ty2]}) ts;
                                        
(* is_fun t = true, iff t is a function.                                    *)
fun is_fun tm =
    let val ty = type_of tm in
        (not (is_vartype ty)) andalso ((#Tyop (dest_type ty)) = "fun")
    end;

(* dom f = the domain of f                                                  *)
fun dom f = hd (#Args (dest_type (type_of f)))
    handle _ => WIN_ERR{function="dom", message="not applied to a function"};

(* ran f = the range of f                                                   *)
fun ran f = hd (tl (#Args (dest_type (type_of f))))
    handle _ => WIN_ERR{function="ran", message="not applied to a function"};

(* (is_trueimp t) = true, iff t = (--`t ==> u`--).                          *)
fun is_trueimp t = (is_imp t) andalso (not (is_neg t));

(* (is_pmi t) = true, iff t = (--`t <== u`--).                              *)
fun is_pmi t = (is_comb t) andalso
               (is_comb (rator t)) andalso
               ((rator (rator t)) = pmi_tm);

(* (dest_pmi (--`a <== b`--)) = ((--`a`--), (--`b`--))                      *)
fun dest_pmi tm =
    let val {Rator=rat,Rand=a} = dest_comb tm in
        let val {Rator=ratrat,Rand=c} = dest_comb rat in
            if ratrat = pmi_tm then
                {ant=a,conseq=c}
            else
                WIN_ERR{function="dest_pmi",message=""}
        end
    end
    handle _ => WIN_ERR{function="dest_pmi",message="not an \"<==\""};

(* IMP_PMI_CONV (--`A ==> B`--) = (|- (A ==> B) = (B <== A))                *)
fun IMP_PMI_CONV tm =
    let val {ant,conseq} = dest_imp tm in
        SYM (SPECL [conseq,ant] PMI_DEF)
    end;

(*  (|- t ==> u)                                                            *)
(* --------------    IMP_PMI                                                *)
(*  (|- u <== t)                                                            *)
val IMP_PMI = CONV_RULE IMP_PMI_CONV;

(* PMI_IMP_CONV (--`A <== B`--) = (|- (A <== B) = (B ==> A))                *)
fun PMI_IMP_CONV tm =
    let val {ant,conseq} = dest_pmi tm in
        SPECL [conseq,ant] PMI_DEF
    end;

(*  (|- u <== t)                                                            *)
(* --------------    PMI_IMP                                                *)
(*  (|- t ==> u)                                                            *)
val PMI_IMP = CONV_RULE PMI_IMP_CONV;

(*  (|- t <== u /\ u <== v)                                                 *)
(* -------------------------                                                *)
(*       (|- t <== v)                                                       *)
fun PMI_TRANS t1 t2 = IMP_PMI (IMP_TRANS (PMI_IMP t2) (PMI_IMP t1));

(*       A |- t1 ==> t2                                                     *)
(* --------------------------  EXISTS_PMI (--`x`--)                         *)
(*  A |- (?x.t1) ==> (?x.t2)   [where x is not free in A]                   *)
fun EXISTS_PMI x th = IMP_PMI (EXISTS_IMP x (PMI_IMP th));

(* Smashes a theorem into lots of little theorems.                          *)
(* SMASH is based on CONJUNCTS, but as well as smashing                     *)
(*   (H |- A1 /\ A2) into [(H |- A1); (H |- H2)],                           *)
(*   SMASH also smashes                                                     *)
(*   (H |- ~(A1 \/ A2) into [(H |- ~A1); (H |- ~A2)]                        *)
(*   and                                                                    *)
(*   (H |- ~(A ==> B) into [(H |- A); (H |- ~B)]                            *)
(*   and                                                                    *)
(*   (H |- ~(A <== B) into [(H |- ~A); (H |- B)]                            *)
(*   and                                                                    *)
(*   (H |- A => B | F) into [(H |- A); (H |- B)]                            *)
(*   and                                                                    *)
(*   (H |- A => F | C) into [(H |- ~A); (H |- C)]                           *)
local
    val DNEG_THM = theorem "window" "DNEG_THM"
    val NOT_DISJ_THM = theorem "window" "NOT_DISJ_THM"
    val NOT_IMP_THM = theorem "window" "NOT_IMP_THM"
    val NOT_PMI_THM = theorem "window" "NOT_PMI_THM"
    val COND_ABF_THM = theorem "window" "COND_ABF_THM"
    val COND_AFC_THM = theorem "window" "COND_AFC_THM"
    fun BREAK t = flatten (map TWEAK (CONJUNCTS t))
    and TWEAK t =
        let val c = concl t in
            if is_neg c then
                let val randc = rand c in
                    if is_neg randc then
                        let val th = SPEC (rand randc) DNEG_THM in
                            BREAK (EQ_MP th t)
                        end
                    else if is_disj randc then
                        let val th =
                            SPECL [rand (rator randc), rand randc] NOT_DISJ_THM
                        in
                            BREAK (EQ_MP th t)
                        end
                    else if is_imp randc then
                        let val th = SPECL [rand (rator randc), rand randc]
                                        NOT_IMP_THM
                        in
                            BREAK (EQ_MP th t)
                        end
                    else if is_pmi randc then
                        let val th = SPECL [rand (rator randc), rand randc]
                                        NOT_PMI_THM
                        in
                            BREAK (EQ_MP th t)
                        end
                    else [t]
                end
            else if is_cond c then
                let val ratorc = rator c in
                    if ((rand c) = false_tm) then
                        let val th = SPECL [rand (rator ratorc), rand ratorc]
                                        COND_ABF_THM
                        in
                           BREAK (EQ_MP th t)
                        end
                    else if (rand ratorc) = false_tm then
                        let val th = SPECL [rand (rator ratorc), rand c]
                            COND_AFC_THM
                        in
                            BREAK (EQ_MP th t)
                        end
                    else [t]
                end
            else [t]
        end
in
    val SMASH = BREAK
end;

(* smash breaks a term into lots of little terms.                           *)
(* smash is to SMASH as conjuncts is to CONJUNCTS.                          *)
fun smash (t : term) = map concl (SMASH (ASSUME t));

(*  (H1 ?- t)   (H2 ?- u)                                                   *)
(* ----------------------- prove_hyp                                        *)
(*  (H1 u (H2 - {t}) ?- u)                                                  *)
fun prove_hyp ((H1,t):goal) ((H2,u):goal) =
    (term_setify (filter (fn h => not (aconv h t)) (H1 @ H2)), u):goal;

end;
