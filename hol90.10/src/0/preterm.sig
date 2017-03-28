signature Preterm_sig =
sig
  structure Term : Term_sig
  datatype preterm = Var of {Name : string, Ty : Term.Type.hol_type}
                   | Const of {Name : string, Ty : Term.Type.hol_type}
                   | Comb of {Rator : preterm, Rand : preterm}
                   | Abs of {Bvar : preterm, Body : preterm}
                   | Constrained of (preterm * Term.Type.hol_type)
                   | Antiq of Term.term

  val TC :(int,Term.Type.hol_type)Lib.istream -> preterm -> unit
  val shrink_type : (Term.Type.hol_type * Term.Type.hol_type) list 
                    -> Term.Type.hol_type -> Term.Type.hol_type
  val tyVars : preterm -> Term.Type.hol_type list
  val cleanup : preterm -> Term.term
  val typecheck :(int,Term.Type.hol_type)Lib.istream -> preterm -> Term.term
  val preterm_to_term : preterm -> Term.term
end;


signature Public_preterm_sig = 
sig
  structure Term : Public_term_sig
  datatype preterm = Var of   {Name : string, Ty : Term.Type.hol_type}
                   | Const of {Name : string, Ty : Term.Type.hol_type}
                   | Comb of  {Rator: preterm, Rand : preterm}
                   | Abs of   {Bvar : preterm, Body : preterm}
                   | Constrained of preterm * Term.Type.hol_type
                   | Antiq of Term.term

  val typecheck :(int,Term.Type.hol_type)Lib.istream -> preterm -> Term.term
end;
