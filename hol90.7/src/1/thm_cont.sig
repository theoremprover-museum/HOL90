(* ===================================================================== *)
(* FILE          : thm_cont.sig                                          *)
(* DESCRIPTION   : Signature for theorem continuations. Translated from  *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHOR        : (c) Larry Paulson and others,                         *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Thm_cont_sig =
sig
structure Thm : Thm_sig
val THEN_TCL : thm_tactical * thm_tactical -> thm_tactical
val ORELSE_TCL : thm_tactical * thm_tactical -> thm_tactical
val REPEAT_TCL : thm_tactical -> thm_tactical
val REPEAT_GTCL : thm_tactical -> (Thm.thm -> tactic) -> thm_tactic
val ALL_THEN : thm_tactical
val NO_THEN : thm_tactical
val EVERY_TCL : thm_tactical list -> thm_tactical
val FIRST_TCL : thm_tactical list -> thm_tactical
val CONJUNCTS_THEN2 : thm_tactic -> thm_tactical
val CONJUNCTS_THEN : thm_tactical
val DISJ_CASES_THEN2 : thm_tactic -> thm_tactical
val DISJ_CASES_THEN : thm_tactical
val DISJ_CASES_THENL : thm_tactic list -> thm_tactic
val DISCH_THEN : thm_tactic -> tactic
val X_CHOOSE_THEN : Thm.Term.term -> thm_tactical
val CHOOSE_THEN : thm_tactical
val X_CASES_THENL : (('a list -> 'b list -> ('a * 'b) list) ->
                  thm_tactic list -> (Thm.Term.term list * thm_tactic) list) ->
                  thm_tactic list -> thm_tactic
val X_CASES_THEN : Thm.Term.term list list -> thm_tactical
val CASES_THENL : thm_tactic list -> thm_tactic
val STRIP_THM_THEN : thm_tactical
end;
