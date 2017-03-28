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
(* CONTENTS: miscelaneous ml ultility functions                             *)
(*==========================================================================*)
(*$Id: ml_ext.sml,v 1.1.1.1.6.1 1997/07/15 13:09:45 kxs Exp $*)

structure ML_ext : ML_ext_sig  =
struct

open Exception;

(* The function that fails and tells the user something usefull.             *)
fun WIN_ERR{function=f,message=m} =
    raise HOL_ERR{origin_function=f,message=m,origin_structure="window"};

(* The function that just fails. The user should never get to see it.       *)
fun fail () = 
    raise WIN_ERR{function="fail",message="window library bug, please report"};

(* (tryfirst f xs) = the first (f x) that does not fail.                    *)
fun tryfirst f [] = WIN_ERR{function="tryfirst",message="no sucesses"}
 |  tryfirst f (x::xs) = (f x) handle _ => (tryfirst f xs);

(* (prefix xs ys) = (?zs. (xs @ zs) = ys)                                   *)
fun prefix [] _ = true
 |  prefix _ [] = false
 |  prefix (x::xs) (y::ys) = (x = y) andalso (prefix xs ys);

(* (after xs ys) = (@zs. (xs @ zs) = ys)                                    *)
fun after [] ys = ys
 |  after xs [] = WIN_ERR{function="after",message="nothing after"}
 |  after (x::xs) (y::ys) = 
        if x = y then
            after xs ys
        else
            WIN_ERR{function="after",message="not a prefix"};

(* replicate e n: make n coppies of e.                                      *)
fun replicate e n = 
    if n < 0 then WIN_ERR{function="replicate",message="negative count"}
    else if n = 0 then [] else e::(replicate e (n - 1));

(* merge sortfn (sort r xs) (sort r ys) = sort r (xs @ ys)                  *)
fun merge _ [] ys = ys
 |  merge _ xs [] = xs
 |  merge r (x::xs) (y::ys) =
        if r x y then
            x::(merge r xs (y::ys))
        else
            y::(merge r (x::xs) ys);

(* best r l = @e. mem e l /\ !e'. mem e l /\ ~(e' = e) ==> r e e'           *)
local
    fun better r x y = if r(x,y) then x else y
in
    fun best r = Lib.end_itlist (better r)
end;

(* front n l = the first n elements of the list l.                           *)
(* If there are less than n elements in l then l is returned.                *)
local
    fun frst n l =
        if (n = 0) orelse (null l) then
            []
        else
            (hd l)::(frst (n - 1) (tl l))
in
    fun front n =
        if n < 0 then
            WIN_ERR{function="front",message="negative count"}
        else
            frst n
end;

end;