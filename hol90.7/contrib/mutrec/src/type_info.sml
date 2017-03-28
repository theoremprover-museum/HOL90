(* File: type_info.sml *)

signature TypeInfoSig =
    sig
	datatype type_info = existing of hol_type | being_defined of string
    end


structure TypeInfo : TypeInfoSig =
    struct
	datatype type_info = existing of hol_type | being_defined of string
    end
