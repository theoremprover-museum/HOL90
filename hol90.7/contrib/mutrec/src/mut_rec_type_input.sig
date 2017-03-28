(* =====================================================================*)
(* FILE          : mut_rec_type_input.sig                               *)
(* DESCRIPTION   : signatures for input to the functor MutRecDefFunc    *)
(*                 and the functor MutRecTypeFunc                       *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter and Myra VanInwegen, based on            *)
(*                 define_type                                          *)
(* DATE          : 92.08.08                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992, 1993, 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature MutRecTyInputSig =
    sig
	structure TypeInfo : TypeInfoSig
	type type_info
	sharing type TypeInfo.type_info = type_info
	val mut_rec_ty_spec
	    : {type_name : string,
	       constructors : {name : string,
			       arg_info : type_info list}list}list

    (* This should take a functor for defining a simple recursive datatype
     as an argument *)
    end


signature MutRecTypeInputSig =
    sig
	structure TypeInfo : TypeInfoSig
	type type_info
	sharing type TypeInfo.type_info = type_info
	val mut_rec_ty_spec
	    : {type_name : string,
	       constructors : {name : string,
			       arg_info : type_info list}list}list
	val New_Ty_Existence_Thm_Name : string
	val New_Ty_Induct_Thm_Name : string
	val New_Ty_Uniqueness_Thm_Name : string
	val Constructors_Distinct_Thm_Name : string
	val Constructors_One_One_Thm_Name : string
	val Cases_Thm_Name : string
    end
