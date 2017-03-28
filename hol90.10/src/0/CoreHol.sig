signature CoreHolSig =
sig
  structure Type : Public_type_sig
  structure Term : Public_term_sig
  structure Match : Match_sig
  structure Net : Net_sig
  structure Preterm : Preterm_sig
  structure Dsyntax : Dsyntax_sig
  structure Hol_pp : Hol_pp_sig
  structure Thm : Thm_sig
  structure Theory : Theory_sig
  structure Const_spec : Const_spec_sig
  structure Type_def : Type_def_sig
  structure Const_def : Const_def_sig
end;
