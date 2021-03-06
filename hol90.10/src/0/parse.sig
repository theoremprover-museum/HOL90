(* ===================================================================== *)
(* FILE          : parse.sig                                             *)
(* DESCRIPTION   : Signature for the type and term parsers.              *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Parse_sig =
sig
  structure Parse_support : Parse_support_sig

  val parse0 : (int,Parse_support.Preterm.Term.Type.hol_type) Lib.istream 
                -> string 
                  ->  Parse_support.Preterm.Term.term list
                    -> Parse_support.parse

  val type_parser : Parse_support.Preterm.Term.term Portable.frag list 
                    -> Parse_support.Preterm.Term.Type.hol_type
  val term_parser : Parse_support.Preterm.Term.term Portable.frag list 
                     -> Parse_support.Preterm.Term.term
  val preterm_parser 
     : (int,Parse_support.Preterm.Term.Type.hol_type) Lib.istream 
        -> Parse_support.Preterm.Term.term Portable.frag list 
          -> Parse_support.Preterm.preterm

  val -- : Parse_support.Preterm.Term.term Portable.frag list 
             -> 'a -> Parse_support.Preterm.Term.term
  val == : Parse_support.Preterm.Term.term Portable.frag list 
            -> 'a -> Parse_support.Preterm.Term.Type.hol_type

  val string_to_type : string -> Parse_support.Preterm.Term.Type.hol_type

  val string_to_preterm 
    : (int,Parse_support.Preterm.Term.Type.hol_type) Lib.istream 
       -> string -> Parse_support.Preterm.preterm
  val string_to_term : string -> Parse_support.Preterm.Term.term

  val type_spec_parser
   : Parse_support.Preterm.Term.term Portable.frag list -> {ty_name:string,
                             clauses : {constructor:string, 
                                        args:Parse_support.arg list} list}
  val string_to_type_spec
   : string -> {ty_name:string,
                clauses : {constructor:string,
                           args:Parse_support.arg list} list}
end;
