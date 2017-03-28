(* ===================================================================== *)
(* FILE          : mk_min.sml                                            *)
(* DESCRIPTION   : The Mother of All Theories.                           *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


functor MK_MIN (structure Globals : Globals_sig
		structure Theory : Theory_sig
                structure Dsyntax : Dsyntax_sig
                structure Parse : Parse_sig
                sharing
                  Theory.Thm.Term = Parse.Parse_support.Preterm.Term =
                  Dsyntax.Term) : Mk_min_sig =
struct
open Parse;

val _ =
if Globals.remake_theory_files
    then
     (Theory.new_theory "min";
      Theory.new_type{Name = "bool", Arity = 0};
      Theory.new_type{Name = "ind", Arity = 0};
      Theory.new_type{Name = "fun", Arity = 2};

      Theory.new_infix{Name = "=", Ty = ==`:'a -> 'a -> bool`==, Prec=100};
      Theory.new_infix{Name = "==>", Ty = ==`:bool->bool->bool`==, Prec=200};
      Theory.new_binder{Name = "@",  Ty = ==`:('a -> bool) -> 'a`==};

      Theory.close_theory())
else Theory.load_theory "min";


end; (* MK_MIN *)
