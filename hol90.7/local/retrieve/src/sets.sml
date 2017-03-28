(****************************************************************************)
(* FILE          : sets.sml                                                 *)
(* DESCRIPTION   : Functions for treating lists as sets.                    *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 1989                                                     *)
(*                                                                          *)
(* TRANSLATED BY : D.R.Syme                                                 *)
(* DATE          : 1995                                                     *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 26th September 1995                                      *)
(****************************************************************************)

structure RetrieveSets : RETRIEVE_SETS =
struct

(*--------------------------------------------------------------------------*)
(* no_rep : ''a list -> bool                                                *)
(*                                                                          *)
(* Function to determine whether a list contains any repetitions.           *)
(*--------------------------------------------------------------------------*)

fun no_rep [] = true
  | no_rep (x::xs) = if (mem x xs) then false else no_rep xs;

(*--------------------------------------------------------------------------*)
(* remove_rep : ''a list -> ''a list                                        *)
(*                                                                          *)
(* Function to remove any repetitions in a list.                            *)
(*--------------------------------------------------------------------------*)

fun remove_rep [] = []
  | remove_rep (x::xs) =
   if (mem x xs)
   then remove_rep xs
   else x::(remove_rep xs);

(*--------------------------------------------------------------------------*)
(* is_subset : ''a list -> ''a list -> bool                                 *)
(*                                                                          *)
(* Function to determine if one list (containing no repetitions) is a       *)
(* subset of another list (containing no repetitions).                      *)
(*                                                                          *)
(* The function tests if subl is a subset of l by subtracting (setwise) l   *)
(* from subl. If this gives a null list, then subl is a subset of l.        *)
(*--------------------------------------------------------------------------*)

fun is_subset l subl = null (subtract subl l);

end; (* RetrieveSets *)
