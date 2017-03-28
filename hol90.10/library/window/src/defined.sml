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
(* CONTENTS: interactive front end to the window inference library.         *)
(*==========================================================================*)
(*$Id: defined.sml,v 1.1.1.1.6.1 1997/07/15 13:09:24 kxs Exp $*)

(* A simple type for values that may be undefined.                          *)

structure Defined : sig 
                       type 'a or_undefined
                       val UNDEFINED : 'a or_undefined
                       val DEFINED : 'a -> 'a or_undefined
                       val value : 'a or_undefined -> 'a
                    end =
struct

open ML_ext;

 abstype 'a or_undefined = UNDEF | DEF of 'a
 with
    val UNDEFINED = UNDEF
    val DEFINED = DEF
    fun value (DEF x) = x
     |  value UNDEF = WIN_ERR{function="value",message="undefined"}
 end;

end;

