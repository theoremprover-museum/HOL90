(* ========================================================================= 
 * Workhorse first order automation: first order tableaux with equality.     
 * ========================================================================= *)

signature tabLib_sig =
sig
 type term
 type thm
 type tactic
 type conv

    val TAB : term -> thm
    val TAB_CONV : thm list -> conv
    val TAB_TAC : thm list -> tactic

end (* sig *)

