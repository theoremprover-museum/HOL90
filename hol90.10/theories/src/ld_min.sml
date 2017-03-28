(* ===================================================================== *)
(* FILE          : mk_min.sml                                            *)
(* DESCRIPTION   : The Mother of All Theories.                           *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)



(*----------------------------------------------------------------------
 * I modified this to make it a simple structure instead of a
 * functor.  I couldn't see any benefit accruing out of the use of a
 * functor here, parameterized over Term, Theorem, Parser etc.  
 * Maybe theories could be parameterized over other things 
 * (e.g. other theories), but not these core things surely?
 *                         DRS
 *--------------------------------------------------------------------*)

structure Min : Min_sig = 
struct

open CoreHol
open Theory;

val _ = if (current_theory() <> "") andalso
           (Lib.mem "min" (current_theory() :: ancestry "-"))
        then () 
        else load_theory "min";

end; (* MK_MIN *)
