(* ===================================================================== *)
(* FILE          : inductive_def.sig                                     *)
(* DESCRIPTION   : Signature for Tom Melham's inductive definition       *)
(*                 package. Translated from hol88.                       *)
(*                                                                       *)
(* ===================================================================== *)


signature Inductive_def_sig =
sig
val prove_inductive_set_exists
  : term * term list -> {hypotheses : term list,side_conditions : term list,
                         conclusion: term} list -> thm
val new_inductive_definition
  : {name:string, fixity:Term.fixity,patt:term*term list,
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
