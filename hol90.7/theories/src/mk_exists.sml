(* ===================================================================== *)
(* FILE          : mk_exists.sml                                         *)
(* DESCRIPTION   : The definition of the existential quantifier.         *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


functor MK_EXISTS (structure Globals : Globals_sig
		   structure Theory : Theory_sig
                   structure Exists_def : Exists_def_sig
                   structure Parse : Parse_sig
                   sharing
                     Theory = Exists_def.Theory
                   and
                     Parse.Parse_support.Preterm.Term = Theory.Thm.Term)
                : Mk_exists_sig =
struct
type thm = Theory.Thm.thm;

val -- = Parse.--;

(* The only use of the primitive principle of definition *)
val _ = 
if Globals.remake_theory_files
    then
	(Theory.new_theory "bool";
	 Exists_def.new_binder_definition("EXISTS_DEF",
					  --`? = \P:'a->bool. P ($@ P)`--);
	 Theory.close_theory())
else Theory.load_theory "bool"

val EXISTS_DEF = Theory.definition "bool" "EXISTS_DEF"

end; (* MK_EXISTS *)
