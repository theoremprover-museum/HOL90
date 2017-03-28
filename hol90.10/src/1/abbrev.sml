(* --------------------------------------------------------------------
 * Define some type abbreviations.  
 *-------------------------------------------------------------------*)

structure Abbrev =
struct
   local
      open CoreHol.Thm
      open CoreHol.Term
   in
      type conv = term -> thm
      type goal = (term list * term)
      type validation = thm list -> thm
      type tactic_result = goal list * validation;
      type tactic = goal -> tactic_result;
      type thm_tactic = thm -> tactic
      type thm_tactical = thm_tactic -> thm_tactic;
   end;
end;
