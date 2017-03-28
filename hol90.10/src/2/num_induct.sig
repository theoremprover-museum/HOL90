signature Num_induct_sig =
sig
   structure Thm : Thm_sig;
   val INDUCT : Thm.thm * Thm.thm -> Thm.thm
   val INDUCT_TAC : Abbrev.tactic
end;
