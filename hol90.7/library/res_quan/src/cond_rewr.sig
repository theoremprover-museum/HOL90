(* =====================================================================*)
(* FILE          : cond_rewr.sig                                        *)
(* DESCRIPTION   : Signature for conditional rewriting conversions and  *)
(*                 tactics 					        *)
(* AUTHOR	 : P Curzon 					        *)
(* DATE		 : May 1993						*)
(*                                                                      *)
(* =====================================================================*)

signature Cond_rewrite_sig =
sig
val COND_REWR_TAC: (term->term->(term subst * hol_type subst) list)->thm_tactic
val search_top_down: term -> term -> (term subst * hol_type subst) list
val COND_REWR_CANON: thm -> thm
val COND_REWRITE1_TAC: thm_tactic
val COND_REWR_CONV: (term->term->(term subst * hol_type subst) list)
                         -> thm -> conv
val COND_REWRITE1_CONV: thm list -> thm -> conv
end;
