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
(*$Id: history.sml,v 4.1 1994/09/10 03:42:51 jim Exp $*)

(* A General History Mechanism is defined.                                  *)
abstype 'a history = HIST of (    (unit -> 'a)
                              * (('a -> 'a) -> unit)
                              * (unit -> unit)
                              * (unit -> unit)
                              * (int -> unit))
with
    (* Create a new history with intial size size and state state.          *)
    fun new_history size state =
        let val len = ref size
            and past = ref [state]
            and future = ref []
        in
            assert (fn n => n >= 1) size;
            HIST(   (* present *)
                fn () => hd (!past)
            ,   (* do *)    
                fn f =>
                    let val (hist as (pres::_)) = !past in
                        past := front (!len) ((f pres)::hist);
                        future := []
                    end
            ,   (* undo *)
                fn () => 
                    let val (pres::old) = !past in
                        assert (not o null) old;
                        past := old;
                        future := pres::(!future)
                    end handle _ =>
                            WIN_ERR{function="undo",message="nothing done"}
            ,   (* redo *)
                fn () =>
                    let val (new::newer) = (!future) in
                        past := front (!len) (new::(!past));
                        future := newer
                    end handle _ =>
                            WIN_ERR{function="redo",message="nothing to redo"}
            ,   (* set size *)
                fn size => (
                    assert (fn n => n >= 1) size;
                    len := size) handle _ =>
                        WIN_ERR{function="set_size",message="at least 1"}
            )
        end handle _ => WIN_ERR{function="set_size",message="at least 1"}
    (* Return the current state of the history.                             *)
    and present (HIST (f,_,_,_,_)) = f ()
    (* Makes (event (present hist)) the current state                       *)
    and dodo (HIST (_,f,_,_,_)) = f
    (* Undoes the last event.                                               *)
    and undo (HIST (_,_,f,_,_)) = f ()
    (* Undoes an undo, but only if no interveening event has occured.       *)
    and redo (HIST (_,_,_,f,_)) = f ()
    (* Set the maximum number of states saved, and hence that can be undone.*)
    and set_size (HIST (_,_,_,_,f)) = f
end;
