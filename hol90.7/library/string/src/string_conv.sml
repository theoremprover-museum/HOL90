(* =====================================================================*)
(* FILE		 : string_conv.ml                                       *)
(* DESCRIPTION   : define the axiom scheme for character strings.	*)
(*									*)
(*									*)
(* AUTHOR	: T. Melham						*)
(* DATE		: 87.08.23						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATOR    : Konrad Slind, University of Calgary                  *)
(* =====================================================================*)

structure String_conv : sig
                          val string_CONV : conv
                        end =
struct

fun STRING_CONV_ERR m = HOL_ERR{origin_structure="String_conv",
                                origin_function = "string_CONV",
                                message = m};
open Rsyntax;

(* ---------------------------------------------------------------------*)
(* string_CONV  "defines" the infinite family of constants:		*)
(*									*)
(*	'a'  = STRING(ASCII F T T F F F F T)``				*)
(*	'ab' = STRING(ASCII F T T F F F F T)`b`				*)
(*									*)
(*	 ... etc							*)
(*									*)
(* The auxiliary function bits n m computes the representation in n 	*)
(* bits of m (MOD 2**n)							*)
(* ---------------------------------------------------------------------*)
local
val T = --`T`--
and F = --`F`--
and A = --`ASCII`--
fun bits 0 _ = []
  | bits n m = 
       let val hm = m div 2 
       in (if (hm*2 = m) then F else T) :: (bits (n-1) hm)
       end
in
fun string_CONV tm =
   let val {Name = str, Ty = ty} = dest_const tm
       val _ = assert (fn t => #Tyop(dest_type t) = "string") ty
   in
   if (str = "\"\"") 
   then raise STRING_CONV_ERR "empty string"
   else case (explode str)
        of ("\""::h::t) =>
           let val code = rev (bits 8 (ord h))
               val tm1 = mk_comb {Rator = (--`STRING`--),
                                  Rand = (list_mk_comb(A,code))}
               val def = mk_comb {Rator=tm1,
                                  Rand=mk_const{Name=implode("\""::t),Ty=ty}}
               in Thm.mk_drule_thm([], mk_eq {lhs = tm, rhs = def})
               end
           | _ => raise STRING_CONV_ERR "badly formed string literal"
   end
   handle e as HOL_ERR{origin_function = "string_CONV",...} => raise e
        | _ => raise STRING_CONV_ERR ""
end;

end; (* String_conv *)
