(****************************************************************************)
(* FILE          : support.sml                                              *)
(* DESCRIPTION   : General ML functions to support decision code.           *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 3rd March 1995                                           *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 21st August 1996                                         *)
(****************************************************************************)

structure DecisionSupport =
struct

(*==========================================================================*)
(* Combinators.                                                             *)
(*==========================================================================*)

val C = Lib.C;

(*==========================================================================*)
(* Functions on lists.                                                      *)
(*==========================================================================*)

val flat = Lib.flatten;

val map2 = Lib.map2;

val filter = Lib.filter;

val mapfilter = Lib.mapfilter;

val exists = Portable.List.exists;

fun forall p [] = true
  | forall p (x::xs) = (p x) andalso (forall p xs);

val itlist = Lib.itlist;

val rev_itlist = Lib.rev_itlist;

exception NOT_FOUND = Lib.NOT_FOUND;
val assoc = Lib.assoc;

fun gen_assoc key x [] = raise NOT_FOUND
  | gen_assoc key x (y::ys) = if (key y = x) then y else gen_assoc key x ys;

val member = Lib.mem;

val el = Lib.el;

fun remove_duplicates p l =
   let fun remove [] keep = keep
         | remove (x::xs) keep =
          if (exists (fn x' => p (x,x')) keep)
          then remove xs keep
          else remove xs (x::keep)
   in  rev (remove l [])
   end;

fun duplicates l =
   let fun dupl [] = []
         | dupl (x::xs) = if (member x xs) then (x :: dupl xs) else dupl xs
   in  remove_duplicates (op =) (dupl l)
   end;

(*==========================================================================*)
(* Other general purpose functions.                                         *)
(*==========================================================================*)

fun upto from to =
   if (from > to)
   then []
   else from::(upto (from + 1) to);

fun pairings f (xs,ys) =
   flat (map (fn x => map (fn y => f (x,y)) ys) xs);

(*==========================================================================*)
(* Auxiliary functions on terms.                                            *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* Functions to extract the arguments from an application of a binary op.   *)
(*--------------------------------------------------------------------------*)

local val rand = CoreHol.Term.rand
      val rator = CoreHol.Term.rator
in
 val arg1 = rand o rator
 and arg2 = rand
end;

(*--------------------------------------------------------------------------*)
(* Function to extract the operator of a (possibly) nested application.     *)
(*--------------------------------------------------------------------------*)

val operator = #1 o CoreHol.Dsyntax.strip_comb;

(*--------------------------------------------------------------------------*)
(* Function to extract the name of a constant.                              *)
(*--------------------------------------------------------------------------*)

val name_of_const = #Name o Rsyntax.dest_const;

(*--------------------------------------------------------------------------*)
(* Function to extract the name of the operator.                            *)
(*--------------------------------------------------------------------------*)

val name_of_operator = name_of_const o operator;

(*--------------------------------------------------------------------------*)
(* Constants and discriminator functions for T (true) and F (false)         *)
(*--------------------------------------------------------------------------*)

val T = Parse.term_parser`T`
and F = Parse.term_parser`F`
and bool = Parse.type_parser`:bool`;

fun is_T tm = (tm = T)
and is_F tm = (tm = F);

(*--------------------------------------------------------------------------*)
(* Function to test for a boolean-valued equality.                          *)
(*--------------------------------------------------------------------------*)

fun is_bool_eq tm = (CoreHol.Dsyntax.is_eq tm) 
            andalso (CoreHol.Term.type_of (arg1 tm) = bool);

(*--------------------------------------------------------------------------*)
(* Function to test for a boolean-valued conditional expression.            *)
(*--------------------------------------------------------------------------*)

fun is_bool_cond tm = (CoreHol.Dsyntax.is_cond tm) 
              andalso (CoreHol.Term.type_of tm = bool);

(*==========================================================================*)
(* Auxiliary conversions.                                                   *)
(*==========================================================================*)

local
   open DecisionConv
in

(*--------------------------------------------------------------------------*)
(* BINOP_CONV : conv -> conv                                                *)
(*                                                                          *)
(* Applies a conversion to the arguments of a binary operator.              *)
(*--------------------------------------------------------------------------*)

fun BINOP_CONV conv = ARGS_CONV [conv,conv];

(*--------------------------------------------------------------------------*)
(* LEFT_CONV  : conv -> conv                                                *)
(* RIGHT_CONV : conv -> conv                                                *)
(*                                                                          *)
(* Applies a conversion to the first or second argument of a binary         *)
(* operator.                                                                *)
(*--------------------------------------------------------------------------*)

val LEFT_CONV = RATOR_CONV o RAND_CONV
and RIGHT_CONV = RAND_CONV;

(*--------------------------------------------------------------------------*)
(* BINDER_CONV : conv -> conv                                               *)
(*                                                                          *)
(* Applies a conversion to the body of a binding.                           *)
(*--------------------------------------------------------------------------*)

val BINDER_CONV = RAND_CONV o ABS_CONV;

(*--------------------------------------------------------------------------*)
(* DEPTH_BINDER_CONV : conv -> conv                                         *)
(*                                                                          *)
(* Applies conv to the body of a formula in prenex normal form.             *)
(*--------------------------------------------------------------------------*)

fun DEPTH_BINDER_CONV conv tm =
   if (CoreHol.Dsyntax.is_forall tm) orelse (CoreHol.Dsyntax.is_exists tm)
   then BINDER_CONV (DEPTH_BINDER_CONV conv) tm
   else conv tm;

(*--------------------------------------------------------------------------*)
(* DEPTH_FORALL_CONV : conv -> conv                                         *)
(*                                                                          *)
(* DEPTH_FORALL_CONV conv `!x1 ... xn. body` applies conv to `body`.        *)
(*--------------------------------------------------------------------------*)

fun DEPTH_FORALL_CONV conv tm =
   if (CoreHol.Dsyntax.is_forall tm)
   then BINDER_CONV (DEPTH_FORALL_CONV conv) tm
   else conv tm;

(*--------------------------------------------------------------------------*)
(* DEPTH_EXISTS_CONV : conv -> conv                                         *)
(*                                                                          *)
(* DEPTH_EXISTS_CONV conv `?x1 ... xn. body` applies conv to `body`.        *)
(*--------------------------------------------------------------------------*)

fun DEPTH_EXISTS_CONV conv tm =
   if (CoreHol.Dsyntax.is_exists tm)
   then BINDER_CONV (DEPTH_EXISTS_CONV conv) tm
   else conv tm;

(*--------------------------------------------------------------------------*)
(* DEPTH_CONJ_CONV : conv -> conv                                           *)
(*--------------------------------------------------------------------------*)

fun DEPTH_CONJ_CONV conv tm =
   if (CoreHol.Dsyntax.is_conj tm)
   then BINOP_CONV (DEPTH_CONJ_CONV conv) tm
   else conv tm;

(*--------------------------------------------------------------------------*)
(* DEPTH_DISJ_CONV : conv -> conv                                           *)
(*--------------------------------------------------------------------------*)

fun DEPTH_DISJ_CONV conv tm =
   if (CoreHol.Dsyntax.is_disj tm)
   then BINOP_CONV (DEPTH_DISJ_CONV conv) tm
   else conv tm;

end;

end; (* DecisionSupport *)
