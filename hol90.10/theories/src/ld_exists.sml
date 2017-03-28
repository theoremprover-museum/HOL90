(* ===================================================================== *)
(* FILE          : ld_exists.sml                                         *)
(* DESCRIPTION   : Existential portion of bool theory as a structure.    *)
(*                                                                       *)
(* AUTHOR        : Donald Syme, University of Cambridge                  *)
(* DATE          : October 1995                                          *)
(* ===================================================================== *)


structure Exists : Exists_sig =
struct

open CoreHol;
open Min;        (* create dependency on "min" theory *)
structure Thm = Thm;
open Theory;

val _ = if (current_theory() <> "") andalso
           (Lib.mem "bool" (current_theory() :: ancestry "-"))
        then () 
	else load_theory "bool";

val EXISTS_DEF = Lib.try (definition "bool") "EXISTS_DEF";

end; (* MK_EXISTS *)

