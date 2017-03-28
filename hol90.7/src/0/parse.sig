(* ===================================================================== *)
(* FILE          : parse.sig                                             *)
(* DESCRIPTION   : Signature for the type and term parsers.              *)
(*                                                                       *)
(* CHANGED       : For Tim Griffin and Roderick, June 4 1992             *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Parse_sig =
sig
structure Parse_support : Parse_support_sig
val type_parser : Parse_support.Preterm.Term.term frag list -> 
                  Parse_support.Preterm.Term.Type.hol_type
val preterm_parser : Parse_support.Preterm.Term.term frag list -> 
                  Parse_support.Preterm.preterm
val term_parser : Parse_support.Preterm.Term.term frag list -> 
                  Parse_support.Preterm.Term.term
val type_spec_parser
 : Parse_support.Preterm.Term.term frag list ->
   {ty_name:string,
    clauses : {constructor:string, 
               args:Parse_support.arg list} list}

val -- : Parse_support.Preterm.Term.term frag list -> 'a -> 
         Parse_support.Preterm.Term.term
val == : Parse_support.Preterm.Term.term frag list -> 'a -> 
         Parse_support.Preterm.Term.Type.hol_type

val string_to_type : string -> Parse_support.Preterm.Term.Type.hol_type
val string_to_preterm : string -> Parse_support.Preterm.preterm
val string_to_term : string -> Parse_support.Preterm.Term.term
val string_to_type_spec
 : string -> {ty_name:string,
              clauses : {constructor:string,
                         args:Parse_support.arg list} list}
end;
