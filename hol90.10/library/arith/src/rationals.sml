(*****************************************************************************)
(* FILE          : rationals.sml                                             *)
(* DESCRIPTION   : Abstract datatype and functions for rational arithmetic   *)
(*                 in ML.                                                    *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 7th August 1996                                           *)
(*****************************************************************************)

structure Rationals : Rationals_sig =
struct

open Int_extra;

val print = Lib.say;
val print_int = Lib.say o Lib.int_to_string;

(*===========================================================================*)
(* Rational arithmetic                                                       *)
(*===========================================================================*)

exception Rat_form;
exception Rat_inv;
exception Rat_div;

(*---------------------------------------------------------------------------*)
(* Abstract datatype for rational numbers and arithmetic                     *)
(*                                                                           *)
(* Rat         : (int * int) -> rat                                          *)
(* Numerator   : rat -> int                                                  *)
(* Denominator : rat -> int                                                  *)
(* rat_inv     : rat -> rat                                                  *)
(* rat_plus    : rat -> rat -> rat                                           *)
(* rat_minus   : rat -> rat -> rat                                           *)
(* rat_mult    : rat -> rat -> rat                                           *)
(* rat_div     : rat -> rat -> rat                                           *)
(* print_rat   : rat -> unit                                                 *)
(*---------------------------------------------------------------------------*)

datatype rat = rat of int * int;

fun Rat (i,j) =
   (if (i = 0) then rat (0,1)
    else let val g = gcd (abs i,abs j)
             val i' = i div g
             and j' = j div g
         in  if (j' < 0)
             then rat ((~i'),(~j'))
             else rat (i',j')
         end
   ) handle _ => raise Rat_form;

fun Numerator (rat (i,_)) = i;

fun Denominator (rat (_,j)) = j;

fun rat_inv (rat (i,j)) =
   if (i < 0) then rat ((~j),(~i))
   else if (i > 0) then rat (j,i)
   else raise Rat_inv;

fun rat_plus (rat (i1,j1)) (rat (i2,j2)) =
   let val g = gcd (j1,j2)
       val d1 = j1 div g
       and d2 = j2 div g
       val (i,j) = ((i1 * d2) + (i2 * d1),(j1 * d2))
   in  if (i = 0) then rat (0,1) else rat (i,j)
   end;

fun rat_minus (rat (i1,j1)) (rat (i2,j2)) =
   let val g = gcd (j1,j2)
       val d1 = j1 div g
       and d2 = j2 div g
       val (i,j) = ((i1 * d2) - (i2 * d1),(j1 * d2))
   in  if (i = 0) then rat (0,1) else rat (i,j)
   end;

fun rat_mult (rat (i1,j1)) (rat (i2,j2)) =
   if ((i1 = 0) orelse (i2 = 0))
   then rat (0,1)
   else let val g = gcd (abs i1,j2)
            and h = gcd (abs i2,j1)
            val i = (i1 div g) * (i2 div h)
            and j = (j1 div h) * (j2 div g)
        in  rat (i,j)
        end;

fun rat_div (rat (i1,j1)) (rat (i2,j2)) =
   if (i2 = 0) then raise Rat_div
   else if (i1 = 0) then rat (0,1)
   else let val g = gcd (abs i1,abs i2)
            and h = gcd (j1,j2)
            val i = (i1 div g) * (j2 div h)
            and j = (j1 div h) * (i2 div g)
        in  if (j < 0) then rat ((~i),(~j)) else rat (i,j)
        end;

fun print_rat (rat (i,j)) =
   if (j = 1)
   then print_int i
   else (print_int i; print "/"; print_int j);

(*---------------------------------------------------------------------------*)
(* rat_of_int : int -> rat                                                   *)
(*                                                                           *)
(* Conversion from integers to rationals                                     *)
(*---------------------------------------------------------------------------*)

fun rat_of_int i = Rat (i,1);

(*---------------------------------------------------------------------------*)
(* lower_int_of_rat : rat -> int                                             *)
(*                                                                           *)
(* Conversion from rationals to integers                                     *)
(*                                                                           *)
(* Computes the largest integer less than or equal to the rational.          *)
(*---------------------------------------------------------------------------*)

fun lower_int_of_rat r =
   let val n = Numerator r
       and d = Denominator r
   in  if (n < 0)
       then let val p = (n * d) in (((n - p) div d) + n) end
       else (n div d)
   end;

(*---------------------------------------------------------------------------*)
(* upper_int_of_rat : rat -> int                                             *)
(*                                                                           *)
(* Conversion from rationals to integers                                     *)
(*                                                                           *)
(* Computes the smallest integer greater than or equal to the rational.      *)
(*---------------------------------------------------------------------------*)

fun upper_int_of_rat r =
   let val n = Numerator r
       and d = Denominator r
   in  if (n > 0)
       then let val p = (n * d) in (((n - p) div d) + n) end
       else (n div d)
   end;

(*---------------------------------------------------------------------------*)
(* The rational number zero                                                  *)
(*---------------------------------------------------------------------------*)

val rat_zero = rat_of_int 0;

(*---------------------------------------------------------------------------*)
(* The rational number one                                                   *)
(*---------------------------------------------------------------------------*)

val rat_one = rat_of_int 1;

(*---------------------------------------------------------------------------*)
(* rat_less : rat -> rat -> bool                                             *)
(*                                                                           *)
(* Less-than for rationals                                                   *)
(*---------------------------------------------------------------------------*)

fun rat_less r1 r2 = Numerator (rat_minus r1 r2) < 0;

end
