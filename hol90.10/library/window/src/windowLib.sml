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
(* CONTENTS: this file loads the compiled code for the library.             *)
(*==========================================================================*)
(* $Id: windowLib.sml,v 1.1.2.1 1997/07/15 13:10:07 kxs Exp $ *)


structure windowLib : windowLib_sig =
struct

type rewrites = Rewrite.rewrites;

structure windowTheoryLoaded = windowTheoryLoaded;
structure Hol_ext = Hol_ext;
open Relations Rules BasicClose EqClose ImpClose WinCore Win 
     Interaction Tty WinTactic;


val window_version =
    implode (rev (tl (tl (rev (tl (explode "$Revision: 1.1.2.1 $"))))));

local open windowTheoryLoaded
in
  val _ = add_relation (Drule.EQ_REFL, Drule.EQ_TRANS);
  val _ = add_relation (IMP_REFL_THM, IMP_TRANS_THM);
  val _ = add_relation (PMI_REFL_THM, PMI_TRANS_THM);
end;


(* Set up the signals so that they print out a fresh view of the stack      *)
(* anytime something happens.                                               *)
local val catch_signal = Signal.catch_signal
in
  val _ = catch_signal beg_stack_sig (fn _ => PRINT_STACK ());
  val _ = catch_signal set_stack_sig (fn _ => PRINT_STACK ());
  val _ = catch_signal psh_win_sig PRINT_STACK;
  val _ = catch_signal cng_win_sig PRINT_STACK;
  val _ = catch_signal pop_win_sig PRINT_STACK;
end;


val _ = let
           fun flush() = Portable.flush_out Portable.std_out
           val line1 = "window Library "^window_version^" loaded." 
           and line2 = "Copyright (c) Jim Grundy 1992"
           and line3 = "All rights reserved"
        in
           flush ();
           Portable.say ("\n"^line1^"\n"^line2^"\n"^line3^"\n");
           flush ()
       end;


(*---------------------------------------------------------------------------
 * Install path to online doc.
 *---------------------------------------------------------------------------*)
  val _ = Lib.cons_path (!Globals.HOLdir^"library/window/help/entries/") 
                        Globals.help_path;

end;
