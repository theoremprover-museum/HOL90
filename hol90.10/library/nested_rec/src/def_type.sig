(* =====================================================================*)
(* FILE          : def_type.sig                                         *)
(* DESCRIPTION   : Signatures for the functor DefTypeFunc, its input,   *)
(*                 output, and various substructures.                   *)
(*                                                                      *)
(* AUTHORS       : Healfdene Goguen, University of Edinburgh, and       *)
(*                 Elsa L. Gunter, AT&T Bell Laboratories               *)
(* DATE          : 92.08.01                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature DefTypeInfoSig =
    sig
     type hol_type
     datatype type_info =  
             existing of hol_type
           | type_op of {Tyop : string, Args : type_info list}
	   | being_defined of string
    end;
    
structure DefTypeInfo : DefTypeInfoSig =
    struct
       type hol_type = CoreHol.Type.hol_type
        datatype type_info = 
            existing of hol_type
          | type_op of {Tyop : string, Args : type_info list}
          | being_defined of string
    end;


signature DefTypeInputSig =
    sig
	val def_type_spec :
	    {type_name : string,
	     constructors : {name :string,
			     arg_info :DefTypeInfo.type_info list} list} list
	    
	val recursor_thms : CoreHol.Thm.thm list
    end;

signature RecursorThmsSig =
    sig
     type thm
	structure TypeInfo : TypeInfoSig
	type type_info
	sharing type TypeInfo.type_info = type_info
	val recursor_thms : thm list
	val tyop_prefix : string
    end;
    
signature TypeOpSig =
    sig
     type hol_type
     type term
     type thm
	structure TypeInfo : TypeInfoSig
	type type_info
	sharing type TypeInfo.type_info = type_info

	    val mk_symbolic_free_const_name : string -> string

	    val tyop_table :
		{name:string,
		 arity:int,
		 rec_thm:thm,
		 original_constructors : hol_type list -> term list,
		 make_type:(type_info list)->
		 {type_name : string,
		  constructors : {name : string,
				  arg_info : type_info list}
		  list}
		 } StringTable.table
    end;

signature DefTypeSig =
    sig
      type thm
	val New_Ty_Induct_Thm :thm
        val New_Ty_Uniqueness_Thm :thm
	val New_Ty_Existence_Thm :thm
	val Constructors_Distinct_Thm : thm
	val Constructors_One_One_Thm : thm
	val Cases_Thm : thm
    end;
