(* =====================================================================*)
(* FILE          : nested_rec_def.sml                                   *)
(* DESCRIPTION   : the functor NestedRecTypeFunc applies DefTypeFunc    *)
(*                 and saves the resulting theorems away under the      *)
(*                 given names, and adds the appropriate bindings to    *)
(*                 sml.                                                 *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter                                          *)
(* DATE          : 94.03.13                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)


functor NestedRecTypeFunc(NestedRecTypeInput : NestedRecTypeInputSig)
    : sig end =
struct

structure DefType =
    DefTypeFunc (structure DefTypeInput = NestedRecTypeInput)

fun add_thm (name,thm) = add_to_sml[(name,save_thm(name,thm))]

val _ = add_thm(NestedRecTypeInput.New_Ty_Existence_Thm_Name,
		DefType.New_Ty_Existence_Thm)

val _ = add_thm(NestedRecTypeInput.New_Ty_Induct_Thm_Name,
		DefType.New_Ty_Induct_Thm)

val _ = add_thm(NestedRecTypeInput.New_Ty_Uniqueness_Thm_Name,
		DefType.New_Ty_Uniqueness_Thm)

val _ = add_thm(NestedRecTypeInput.Constructors_Distinct_Thm_Name,
		DefType.Constructors_Distinct_Thm)

val _ = add_thm(NestedRecTypeInput.Constructors_One_One_Thm_Name,
		DefType.Constructors_One_One_Thm)

val _ = add_thm(NestedRecTypeInput.Cases_Thm_Name, DefType.Cases_Thm)

end
