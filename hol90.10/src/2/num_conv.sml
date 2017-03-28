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

open CoreHol;

structure Thm = Thm;

open Exception;
open Lib;
open Thm;
open Parse;
open Dsyntax;
open Term;

fun NUM_CONV_ERR{function,message} = 
         HOL_ERR{origin_structure ="Num_conv",
                 origin_function = function,
                 message = message}

(* axiom scheme for numerals   *)

local val N = ==`:num`==
      val SUC = --`SUC`--
      val eq = --`$= :num->num->bool`--
      fun num_to_term n = mk_const{Name=int_to_string n, Ty=N}
      fun term_to_num t = string_to_int(#Name(dest_const t)) 
       handle _ => raise NUM_CONV_ERR{function="term_to_num",message = ""}
in
fun num_CONV t =
   let val n = term_to_num t 
   in if (n<1) 
   then raise NUM_CONV_ERR{function = "num_CONV",
                           message = int_to_string n^" is not a successor"}
   else let val th' = Thm.mk_drule_thm([], 
                         list_mk_comb(eq, [t,mk_comb{Rator = SUC, 
                                                Rand = num_to_term(n-1)}]))
        in Thm.note (STEP{Name="NUMCONV", Just=[JA_TERM t], Thm=th'},th') end
   end
end;

end; (* Num_conv *)
