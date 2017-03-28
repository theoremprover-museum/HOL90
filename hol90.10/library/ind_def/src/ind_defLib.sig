(* ===================================================================== *)
(* FILE          : ind_defLib.sig                                        *)
(* DESCRIPTION   : Signature for Tom Melham's inductive definition       *)
(*                 package. Translated from hol88.                       *)
(*                                                                       *)
(* ===================================================================== *)


signature ind_defLib_sig =
sig
   type term
   type fixity
   type thm
   type tactic
   type conv
   type thm_tactic

val prove_inductive_set_exists
  : term * term list -> {hypotheses : term list,side_conditions : term list,
                         conclusion: term} list -> thm
val new_inductive_definition
  : {name:string, fixity:fixity,patt:term*term list,
     rules: {hypotheses : term list,side_conditions : term list,
     conclusion: term} list}
    -> {desc : thm list, induction_thm :thm}
val derive_induction : conv
val derive_rule : term -> (thm -> thm) * conv -> thm -> thm
val derive_strong_induction : thm list * thm -> thm
val derive_cases_thm : thm list * thm -> thm
val REDUCE : conv
val RULE_INDUCT_THEN : thm -> thm_tactic -> thm_tactic -> tactic
val RULE_TAC : thm_tactic
end;
