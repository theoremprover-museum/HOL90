signature Preterm_sig =
sig
  structure Term : Term_sig
  datatype preterm = Var of {Name : string, Ty : Term.Type.hol_type}
                   | Const of {Name : string, Ty : Term.Type.hol_type}
                   | Comb of {Rator : preterm, Rand : preterm}
                   | Abs of {Bvar : preterm, Body : preterm}
                   | Constrained of (preterm * Term.Type.hol_type)
                   | Antiq of Term.term

  val typecheck :preterm -> preterm
  val typecheck_cleanup : preterm -> Term.term
  val preterm_to_term : preterm -> Term.term
end;


signature Public_preterm_sig =
sig
  structure Term : Public_term_sig
  type preterm
  val typecheck :preterm -> preterm
  val typecheck_cleanup : preterm -> Term.term
  val preterm_to_term : preterm -> Term.term
end;
