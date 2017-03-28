(* =====================================================================*)
(* FILE          : total_mut_rec_type_def.sml                           *)
(* DESCRIPTION   : the functor MutRecTypeFunc put together all the      *)
(*                 pieces for MutRecDefFunc and ConsThmsFunc, saves     *)
(*                 the resulting theorems away under the given names,   *)
(*                 and adds the appropriate bindings to sml.            *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter                                          *)
(* DATE          : 94.01.05                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)


functor MutRecTypeFunc(MutRecTypeInput : MutRecTypeInputSig) : sig end =
struct

structure MutRecDef =
    MutRecDefFunc (structure ExtraGeneralFunctions = ExtraGeneralFunctions
		   structure MutRecTyInput = MutRecTypeInput)

structure ConsThms = ConsThmsFunc(MutRecDef)

fun add_thm (name,thm) = add_to_sml[(name,save_thm(name,thm))]

val _ = add_thm(MutRecTypeInput.New_Ty_Existence_Thm_Name,
		MutRecDef.New_Ty_Existence_Thm)

val _ = add_thm(MutRecTypeInput.New_Ty_Induct_Thm_Name,
		MutRecDef.New_Ty_Induct_Thm)

val _ = add_thm(MutRecTypeInput.New_Ty_Uniqueness_Thm_Name,
		MutRecDef.New_Ty_Uniqueness_Thm)

val _ = add_thm(MutRecTypeInput.Constructors_Distinct_Thm_Name,
		ConsThms.mutual_constructors_distinct)

val _ = add_thm(MutRecTypeInput.Constructors_One_One_Thm_Name,
		ConsThms.mutual_constructors_one_one)

val _ = add_thm(MutRecTypeInput.Cases_Thm_Name, ConsThms.mutual_cases)

val _ = add_to_sml ConsThms.argument_extraction_definitions
end
