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
(* CONTENTS: interactive front end to the window infernce library.          *)
(*==========================================================================*)
(*$Id: tty.sml,v 4.1 1994/09/10 03:42:51 jim Exp $*)

structure Tty :
    sig
        val PRINT_STACK : unit -> unit
    end =

struct

val stack_stream =
    System.PrettyPrint.mk_ppstream{
        linewidth = !System.Print.linewidth,
        flush = System.Print.flush,
        consumer = System.Print.say};

(* Give a friendly picture of the stack.                                    *)
(* Only the top window is displayed.                                        *)
(* Each of the hypotheses appears with a "!" infront of it.                 *)
(* Each of the lemmas appears with a "|" infront of it.                     *)
(* Each of the conjectures appears with a "?" infront of it.                *)
(* Each of the used conjectures appears with a "$" infront of it.           *)
(* Each of the bad conjectures appears with a "@" infront of it.            *)
(* The relation and focus are then printed last.                            *)
local
    open System.PrettyPrint
    open Hol_pp
    fun rel_pic (tm:term) = if (is_const tm) then #Name(dest_const tm) else "??"
in
    fun pp_stack ppstrm st =
        let val topwin = top_window st
            val hyps = disp_hypotheses topwin
            val cnjs = conjectures topwin
            val usedcnjs = used_conjectures topwin
            val badcnjs = bad_conjectures st
            val lems = lemmas topwin
            val rel = rel_pic (relation topwin)
            val rellen = length (explode rel)
            val all = ref (term_setify ((rev hyps)@(rev lems)@(rev cnjs)))
        in
            begin_block ppstrm INCONSISTENT 0;
                add_newline ppstrm;
                while not (null (!all)) do
                (
                    let val (c::cs) = (!all) in
                        add_string ppstrm (implode (replicate " " rellen));
                        (if (term_mem c badcnjs) then add_string ppstrm " @ "
                        else if (term_mem c usedcnjs) then
                            add_string ppstrm " $ "
                        else if (term_mem c hyps) then add_string ppstrm " ! "
                        else if (term_mem c lems) then add_string ppstrm " | "
                        else (* an unused conjecture *)
                            add_string ppstrm " ? ");
                        begin_block ppstrm INCONSISTENT (rellen + 4);
                            pp_term ppstrm c;
                        end_block ppstrm;
                        add_newline ppstrm;
                        all := cs
                    end
                );
                add_string ppstrm rel;
                add_string ppstrm " * ";
                begin_block ppstrm INCONSISTENT (rellen + 4);
                    pp_term ppstrm (focus topwin);
                end_block ppstrm;
                add_newline ppstrm;
            end_block ppstrm;
            flush_ppstream ppstrm
        end
end;

(* Print out the window stack.                                              *)
val PRINT_STACK = pp_stack stack_stream o CURRENT_STACK;

end;
open Tty;

(* Set up the signals so that they print out a fresh view of the stack      *)
(* anytime something happens.                                               *)
catch_signal beg_stack_sig (fn _ => PRINT_STACK ());
catch_signal set_stack_sig (fn _ => PRINT_STACK ());
catch_signal psh_win_sig PRINT_STACK;
catch_signal cng_win_sig PRINT_STACK;
catch_signal pop_win_sig PRINT_STACK;
