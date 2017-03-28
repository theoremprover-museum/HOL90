(* ===================================================================== *)
(* FILE          : ld_bool.sml                                           *)
(* DESCRIPTION   : The "bool" theory as a structure accessing the disk   *)
(*                 representation.                                       *)
(*                                                                       *)
(* AUTHOR        : Donald Syme                                           *)
(* DATE          : October 1995                                          *)
(* ===================================================================== *)


(*----------------------------------------------------------------------
 * Note: This loads the theory bool as a structure. The idea is that this
 * file could be generated automatically when the theory is created.
 *---------------------------------------------------------------------*)

structure boolThry : boolThrySig =
struct

open CoreHol;
structure Min = Min;    (* Create dependency on "min" theory *)
structure Exists = Exists; (* Create dependency on "exists" definition *)
open Theory;
open Lib;
open Exception;

val _ = if (current_theory() <> "") andalso
           (mem "bool" (current_theory() :: ancestry "-"))
        then () 
	else load_theory "bool";

fun def n = Lib.try (definition "bool") n;
fun ax n = Lib.try (axiom "bool") n;

val T_DEF      = def "TRUTH"
val FORALL_DEF = def "FORALL_DEF"
val AND_DEF    = def "AND_DEF"
val OR_DEF     = def "OR_DEF"
val F_DEF      = def "F_DEF"
val NOT_DEF    = def "NOT_DEF"
val EXISTS_UNIQUE_DEF = def "EXISTS_UNIQUE_DEF"
val LET_DEF     = def "LET_DEF"
val COND_DEF    = def "COND_DEF"
val ONE_ONE_DEF = def "ONE_ONE_DEF"
val ONTO_DEF    = def "ONTO_DEF"
val TYPE_DEFINITION = def "TYPE_DEFINITION"

val BOOL_CASES_AX   = ax "BOOL_CASES_AX"
val IMP_ANTISYM_AX  = ax "IMP_ANTISYM_AX"
val ETA_AX          = ax "ETA_AX"
val SELECT_AX       = ax "SELECT_AX"
val INFINITY_AX     = ax "INFINITY_AX"

end; (* MK_BOOL *)
