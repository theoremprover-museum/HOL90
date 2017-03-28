signature Base_logic_sig =
sig
  structure Save_hol : Save_hol_sig
  structure Lexis : Lexis_sig
  structure Type : Public_type_sig
  structure Term : Public_term_sig
  structure Match : Match_sig
  structure Dsyntax : Dsyntax_sig
  structure Net : Net_sig
  structure Thm : Thm_sig
  structure Theory : Theory_sig

  structure Add_to_sml : Add_to_sml_sig
  structure Library : Library_sig
  structure Install : Install_sig

  structure Const_spec : Const_spec_sig
  structure Type_def : Type_def_sig
  structure Const_def : Const_def_sig

  structure Min : Mk_min_sig
  structure Exists : Mk_exists_sig
sharing Type = Term.Type
sharing Term = Match.Term = Dsyntax.Term = Net.Term = Thm.Term
sharing Thm = Theory.Thm
sharing Theory = Const_spec.Theory = Type_def.Theory = Const_def.Theory
sharing type Exists.thm = Theory.Thm.thm
end;
