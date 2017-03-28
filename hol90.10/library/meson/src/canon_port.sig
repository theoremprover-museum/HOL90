signature Canon_Port_sig = 
sig
 type term
 type thm
 type conv
 type tactic
 type thm_tactic

  val freesl: term list -> term list
  val get_thm_heads : thm -> (term*int)list * (term*int) list 
                          -> (term*int)list * (term*int) list
  val GEN_FOL_CONV : (term*int)list * (term*int) list -> conv
  val NNF_CONV : conv
  val NNFC_CONV : conv
  val DELAMB_CONV : conv
  val PROP_CNF_CONV : conv
  val PRESIMP_CONV  : conv
  val SKOLEM_CONV : conv
  val REFUTE_THEN : thm_tactic -> tactic
end;

