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

(* This module declares a new type of signals.                              *)
(* A signal is created with the new_signal function.                        *)
(* unit->unit functions can be associated with a signal with the            *)
(* catch_signal function.                                                   *)
(* When a signal is raised with the signal function, all those functions    *)
(* associated with the signal will be evaluated.                            *)
(* The functions associated with a signal can be cleared with the           *)
(* clear_signal function.                                                   *)

structure Signal : sig 
                      type 'a signal
                      val new_signal : unit -> 'a signal
                      val catch_signal : 'a signal -> ('a -> unit) -> unit
                      val clear_signal : 'a signal -> unit
                      val signal : 'a signal -> 'a -> unit
                   end =
struct

  abstype 'a signal = SIG of ('a -> unit) list ref
  with
      fun new_signal () = SIG (ref []);
      fun catch_signal (SIG s) action = (s := action::(!s));
      fun clear_signal (SIG s) = (s := []);
      fun signal (SIG s) x = ((map (fn f => f x) (!s)); ());
  end;

end;
