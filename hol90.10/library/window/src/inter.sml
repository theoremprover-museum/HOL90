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
(*$Id: inter.sml,v 1.1.1.1.6.1 1997/07/15 13:09:36 kxs Exp $*)

structure Interaction :
sig
 type term
 type thm
 type win_stack
 type 'a signal
    val CURRENT_STACK : unit -> win_stack
    val CURRENT_NAME : unit -> string
    val SET_MAX_HIST : int -> unit
    val beg_stack_sig : string signal
    val end_stack_sig : string signal
    val set_stack_sig : string signal
    val psh_win_sig : unit signal
    val pop_win_sig : unit signal
    val cng_win_sig : unit signal
    val BEGIN_STACK : string -> term -> term list -> thm list -> unit
    val END_STACK : string -> unit
    val SET_STACK : string -> unit
    val GET_STACK : string -> win_stack
    val ALL_STACKS : unit -> string list
    val DO : (win_stack -> win_stack) -> unit
    val UNDO : unit -> unit
    val REDO : unit -> unit
    val WIN_THM : unit -> thm
    val SAVE_WIN_THM : unit -> thm
end

=

struct

 type term = CoreHol.Term.term
 type thm = CoreHol.Thm.thm
 type win_stack = Win.win_stack
 type 'a signal = 'a Signal.signal;

open Lib CoreHol;
open Term Theory;
open ML_ext History Signal Defined WinCore Win;

(* We now set up functions to handle a table of win_stack histories.        *)
(* The table associates a name with each win_stack history.                 *)
(* There is also a pair cur_nam_st_hist with the name of the current        *)
(* win_stack history, and the win_stack history itself.                     *)
(* cur_nam_st_hist can also be undefined in the event of their being no     *)
(* current stack.                                                           *)

val stack_table = ref ([] : (string * win_stack history) list);

val cur_nam_st_hist =
    ref (UNDEFINED : (string * win_stack history) or_undefined);

local
    fun nam_st_hist () = value (!cur_nam_st_hist)
in
    (* The current stack history.                                           *)
    fun CURRENT_STACK_HIST () = snd (nam_st_hist ())
        handle _ =>  WIN_ERR{function="CURRENT_STACK_HIST",message="no stack"}
    (* The current stack .                                                  *)
    fun CURRENT_STACK () = present (CURRENT_STACK_HIST ())
        handle _ =>  WIN_ERR{function="CURRENT_STACK",message="no stack"}
    (* The name of the current stack.                                       *)
    fun CURRENT_NAME () = fst (nam_st_hist ())
        handle _ => WIN_ERR{function="CURRENT_NAME",message="no name"};
end;

val history_size = ref 20;

(* Set the size of the history on all stacks.                               *)
fun SET_MAX_HIST size = (
    map ((C set_size size) o snd) (!stack_table);
    history_size := size);

(* We also set up some signals which are made when the current stack        *)
(* changes. These are used to alert centaur so it can update its displayes. *)
(* They can also be used to set the window stripe on an xterm to the name   *)
(* of the current stack.   They are also used to print a fresh view of the  *)
(* stack when necessary.                                                    *)

(* This signal should be raised when a new stack is begun.                  *)
val beg_stack_sig : string signal = new_signal ()
(* This signal should be raised when a stack is killed.                     *)
and end_stack_sig : string signal = new_signal () 
(* This signal should be raised when the current stack is changed.          *)
and set_stack_sig : string signal = new_signal ();

(* This signal should be raised when a window is pushed onto the stack.     *)
val psh_win_sig : unit signal = new_signal ()
(* This signal is raised when a window is popped off the stack.             *)
and pop_win_sig : unit signal = new_signal ()
(* This signal should be raised whener the top window is changed.           *)
and cng_win_sig : unit signal = new_signal ();

(* Start a new stack.                                                       *)
(* The new stack becomes the current stack.                                 *)
fun BEGIN_STACK name relfoc hyps thms =
    if mem name (map fst (!stack_table)) then
        WIN_ERR{function="BEGIN_STACK",message="stack_exists"}
    else
        let val {Rator=rel,Rand=foc} = dest_comb relfoc in
        let val  new_nam_st_hist = 
                (
                    name,
                    (new_history
                        (!history_size)
                        (create_stack
                            (create_win rel foc (rev hyps) (rev thms))))
                )
        in
            cur_nam_st_hist := DEFINED new_nam_st_hist;
            stack_table := new_nam_st_hist::(!stack_table);
            signal beg_stack_sig name
        end end;

(* Dispose of a named stack.                                                *)
(* If the named stack is the current stack, then the current stack          *)
(*   is left undefined.                                                     *)
fun END_STACK name = 
    if mem name (map fst (!stack_table)) then
        ((if ((name = (CURRENT_NAME ())) handle _ => false) then
                cur_nam_st_hist := UNDEFINED
        else 
            ());
        stack_table := filter ((fn (n,_) => not (n = name))) (!stack_table);
        signal end_stack_sig name)
    else
        WIN_ERR{function="END_STACK",message="no such stack"};

(* Set the current stack the the stack named.                               *)
fun SET_STACK name =
    (
        cur_nam_st_hist := DEFINED (name, assoc name (!stack_table));
        signal set_stack_sig name
    ) handle _ => WIN_ERR{function="SET_STACK",message="no such stack"};

(* Return the named stack.                                                  *)
fun GET_STACK name = (present (assoc name (!stack_table)))
    handle _ =>  WIN_ERR{function="GET_STACK",message="no such stack"};

(* The names of all the stacks.                                             *)
fun ALL_STACKS () = map fst (!stack_table);

local
    fun signal_change f =
        let val stack_hist = CURRENT_STACK_HIST () in
        let val old_depth = depth_stack (present stack_hist)
            and new_depth = ((f stack_hist); depth_stack (present stack_hist))
        in
            if old_depth = new_depth then signal cng_win_sig ()
            else if old_depth < new_depth then signal psh_win_sig ()
            else (* old_depth > new_depth *) signal pop_win_sig ()
        end end
in
    fun DO f = signal_change (C dodo f)
    and UNDO () = signal_change undo
    and REDO () = signal_change redo
end;

(* The theorem help by the window on top of the stack.                      *)
fun WIN_THM () = win_thm (top_window (CURRENT_STACK ()));;

(* Save the theorem on the top of the window stack.                         *)
fun SAVE_WIN_THM () = save_thm (CURRENT_NAME (), WIN_THM ()) 
                      handle _ => WIN_ERR{function="SAVE_WIN_THM",message=""};

end;
