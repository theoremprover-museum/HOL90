(*=======================================================================
 * Support for AC reasoning.
 *=====================================================================*)

signature AC_sig =
sig
  type term
  type thm
  type conv
    val AC : (thm * thm) -> term -> thm
    val AC_CANON_GEN_CONV : (thm * thm) -> (term -> term -> bool) -> conv
    val AC_CANON_CONV : (thm * thm) -> conv
    val ASSOC_CONV : thm -> conv
    val CONJ_ACI : term -> thm
    val DISTRIB_CONV : thm * thm -> conv
end (* sig *)

