(* ===================================================================== *)
(* FILE          : mk_exists.sml                                         *)
(* DESCRIPTION   : The definition of the existential quantifier.         *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Exists : Exists_sig =
struct

structure Min = Min; (* create dependency on "min" theory *)
structure ExistsDef = EXISTS_DEF(structure Theory = CoreHol.Theory
                                 structure Dsyntax = CoreHol.Dsyntax);

val _ = CoreHol.Theory.new_theory "bool";

val EXISTS_DEF = 
    ExistsDef.new_binder_definition
     ("EXISTS_DEF",  Parse.term_parser `? = \P:'a->bool. P ($@ P)`);

val _ = CoreHol.Theory.close_theory();
val _ = CoreHol.Theory.export_theory();

end; (* MK_EXISTS *)
