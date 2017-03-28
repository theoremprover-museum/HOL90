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

signature NestedRecTypeInputSig =
    sig
	val def_type_spec :
	    {type_name : string,
	     constructors : {name : string,
			     arg_info : DefTypeInfo.type_info list} list} list
	    
	val recursor_thms : CoreHol.Thm.thm list
	val New_Ty_Existence_Thm_Name : string
	val New_Ty_Induct_Thm_Name : string
	val New_Ty_Uniqueness_Thm_Name : string
	val Constructors_Distinct_Thm_Name : string
	val Constructors_One_One_Thm_Name : string
	val Cases_Thm_Name : string
    end;


functor NestedRecTypeFunc(NestedRecTypeInput : NestedRecTypeInputSig) =
struct

val save_thm = CoreHol.Theory.save_thm;


structure DefType = DefTypeFunc (NestedRecTypeInput);

fun add_thm (name,thm) = Add_to_sml.add_to_sml[(name,save_thm(name,thm))]

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
