(* ===================================================================== *)
(* FILE          : define_type.sig                                       *)
(* DESCRIPTION   : Signature for the (concrete) recursive type definition*)
(*                 facility. Translated from hol88.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* Note in the following that                                            *)
(*                                                                       *)
(*     datatype args = Rec_occ | Hty of hol_type                          *)
(*                                                                       *)
(* It's defined in 0/parse_support.sml                                   *)
(* ===================================================================== *)


signature Define_type_sig =
sig
val dtype : {save_name:string,ty_name:string,
             clauses:{constructor:string, 
                      args:Parse_support.arg list,
                      fixity:Term.fixity} list}
            -> thm
val define_type : {name:string, 
                   type_spec: term frag list, 
                   fixities : Term.fixity list} -> thm
val string_define_type : string -> string -> Term.fixity list -> thm
end;
