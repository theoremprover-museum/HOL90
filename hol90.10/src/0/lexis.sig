(* ===================================================================== *)
(* FILE          : lexis.sig                                             *)
(* DESCRIPTION   : Signature for functions defining lexical structure    *)
(*                 of hol90 types and terms.                             *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Lexis_sig =
sig
  val allowed_user_type_var : string -> bool
  val allowed_type_constant : string -> bool
  val allowed_term_constant : string -> bool
  val ok_identifier : string -> bool
  val ok_symbolic : string -> bool
  val ok_sml_identifier : string -> bool
  val ok_thy_index : string -> bool
  val is_num_literal : string -> bool
  val is_string_literal : string -> bool
end;
