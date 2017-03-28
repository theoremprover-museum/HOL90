(* ===================================================================== *)
(* FILE          : mk_min.sml                                            *)
(* DESCRIPTION   : The Mother of All Theories.                           *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)



(*----------------------------------------------------------------------
 * I modified this to make it a simple structure instead of a
 * functor.  I couldn't see any benefit accruing out of the use of a
 * functor here, parameterized over Term, Theorem, Parser etc.  
 * Maybe theories could be parameterized over other things 
 * (e.g. other theories), but not these core things surely?
 *                         DRS
 *--------------------------------------------------------------------*)

structure Min : Min_sig = 
struct

val TYPE = Parse.type_parser

open CoreHol.Theory;

val _ = new_theory "min";
val _ = new_type{Name = "bool", Arity = 0};
val _ = new_type{Name = "ind",  Arity = 0};
val _ = new_type{Name = "fun",  Arity = 2};

val _ = new_infix{Name = "=",   Ty=TYPE `: 'a -> 'a -> bool`,    Prec=100};
val _ = new_infix{Name = "==>", Ty=TYPE `: bool -> bool -> bool`, Prec=200};
val _ = new_binder{Name = "@",  Ty=TYPE `: ('a -> bool) -> 'a`};

val _ = export_theory();

end;
