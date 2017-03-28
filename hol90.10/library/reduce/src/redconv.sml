(*===========================================================================
== LIBRARY:     reduce (part III)                                          ==
==                                                                         ==
== DESCRIPTION: Global conversions, rules and tactics                      ==
==                                                                         ==
== AUTHOR:      John Harrison                                              ==
==              University of Cambridge Computer Laboratory                ==
==              New Museums Site                                           ==
==              Pembroke Street                                            ==
==              Cambridge CB2 3QG                                          ==
==              England.                                                   ==
==                                                                         ==
==              jrh@cl.cam.ac.uk                                           ==
==                                                                         ==
== DATE:        18th May 1991                                              ==
==                                                                         ==
== TRANSLATOR:  Kim Dam Petersen (kimdam@tfl.dk)                           ==
============================================================================*)

functor Redconv_funct (structure Boolconv : Boolconv_sig
		       structure Arithconv : Arithconv_sig) : Redconv_sig =
struct

(*open Core; (* open up all of the HOL 0/1 Core - could be replaced by more *)
           (* explicit opens to avoid endless recompilation of libraries  *)
           (* during system development                                   *)
*)

fun failwith function = raise 
 Exception.HOL_ERR{origin_structure = "Redconv",
                    origin_function = function,
                            message = ""};

open Boolconv;
open Arithconv;
open Conv;
open Lib;

(*-----------------------------------------------------------------------*)
(* RED_CONV - Try all the conversions in the library                     *)
(*-----------------------------------------------------------------------*)

val RED_CONV =
  let fun FAIL_CONV (s:string) tm = failwith s
  in
      itlist (curry (Conv.ORELSEC))
         [ADD_CONV,  AND_CONV,  BEQ_CONV,  COND_CONV,
          DIV_CONV,  EXP_CONV,   GE_CONV,    GT_CONV,
          IMP_CONV,   LE_CONV,   LT_CONV,   MOD_CONV,
          MUL_CONV,  NEQ_CONV,  NOT_CONV,    OR_CONV,
          PRE_CONV,  SBC_CONV,  SUC_CONV] (FAIL_CONV "RED_CONV")
  end;

(*-----------------------------------------------------------------------*)
(* REDUCE_CONV - Perform above reductions at any depth.                  *)
(*-----------------------------------------------------------------------*)

val REDUCE_CONV = DEPTH_CONV RED_CONV;

(*-----------------------------------------------------------------------*)
(* REDUCE_RULE and REDUCE_TAC - Inference rule and tactic versions.      *)
(*-----------------------------------------------------------------------*)

val REDUCE_RULE = CONV_RULE REDUCE_CONV;

val REDUCE_TAC = CONV_TAC REDUCE_CONV;

end
