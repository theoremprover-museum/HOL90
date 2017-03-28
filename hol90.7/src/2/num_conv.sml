(* ===================================================================== *)
(* FILE          : num_conv.sml                                          *)
(* DESCRIPTION   : num_conv maps a number constant to a theorem equating *)
(*                 it with the successor of its predecessor. Translated  *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHOR        : T.Melham                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : 87.08.23                                              *)
(*                 September 11, 1991                                    *)
(* ===================================================================== *)


structure Num_conv : Num_conv_sig =
struct

fun NUM_CONV_ERR{function,message} = HOL_ERR{origin_structure ="Num_conv",
					     origin_function = function,
					     message = message}

(* axiom scheme for numerals                                         *)

local
val N = ==`:num`==
val SUC = --`SUC`--
fun int_to_term n = mk_const{Name = int_to_string n, Ty = N}
fun term_to_int t = string_to_int(#Name(dest_const t))
                    handle _ => raise NUM_CONV_ERR{function = "term_to_int",
						   message = ""}
in
fun num_CONV t =
   let val n = term_to_int t 
   in
   if (n<1) 
   then raise NUM_CONV_ERR{function = "num_CONV",
                           message = 
			    (Lib.int_to_string n)^" is not a successor"}
   else Thm.mk_drule_thm([], 
         mk_eq{lhs = t, rhs = mk_comb{Rator = SUC, Rand = int_to_term(n-1)}})
   end
end;

end; (* Num_conv *)
