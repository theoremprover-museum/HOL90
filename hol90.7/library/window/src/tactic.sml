(*--------------------------------------------------------------------------*)
(*                  Copyright (c) Jim Grundy 1992                           *)
(*                  All rights reserved                                     *)
(*                                                                          *)
(* Jim Grundy, hereafter referred to as `the Author', retains the copyright *)
(* and all other legal rights to the Software contained in this file,       *)
(* hereafter referred to as `the Software'.                                 *)
(*                                                                          *)
(* The Software is made available free of charge on an `as is' basis. No    *)
(* guarantee, either express or implied, of maintenance, reliability,       *)
(* merchantability or suitability for any purpose is made by the Author.    *)
(*                                                                          *)
(* The user is granted the right to make personal or internal use of the    *)
(* Software provided that both:                                             *)
(* 1. The Software is not used for commercial gain.                         *)
(* 2. The user shall not hold the Author liable for any consequences        *)
(*    arising from use of the Software.                                     *)
(*                                                                          *)
(* The user is granted the right to further distribute the Software         *)
(* provided that both:                                                      *)
(* 1. The Software and this statement of rights are not modified.           *)
(* 2. The Software does not form part or the whole of a system distributed  *)
(*    for commercial gain.                                                  *)
(*                                                                          *)
(* The user is granted the right to modify the Software for personal or     *)
(* internal use provided that all of the following conditions are observed: *)
(* 1. The user does not distribute the modified software.                   *)
(* 2. The modified software is not used for commercial gain.                *)
(* 3. The Author retains all rights to the modified software.               *)
(*                                                                          *)
(* Anyone seeking a licence to use this software for commercial purposes is *)
(* invited to contact the Author.                                           *)
(*--------------------------------------------------------------------------*)
(*==========================================================================*)
(* CONTENTS: tactics for interfacing subgoal and window proof.              *)
(*==========================================================================*)
(*$Id: tactic.sml,v 4.1 1994/09/10 03:42:51 jim Exp $*)

fun BEGIN_STACK_TAC thms = (fn (gl as (hyps,foc)) =>
    (BEGIN_STACK "TACTIC STACK" (mk_comb {Rator=pmi_tm, Rand=foc})  hyps thms;
     ALL_TAC gl)):tactic;

local
    fun repeat f a = (repeat f (f a)) handle _ => a
in
    fun END_STACK_TAC () = 
        let val th =
            win_thm (top_window (repeat CLOSE_WIN (GET_STACK "TACTIC STACK")))
        in
            END_STACK "TACTIC STACK";
            MATCH_MP_TAC (PMI_IMP th)
        end
end;
