(* File: HOFML/grammar.sml *)

(* Description: This file contains definitions of the syntax classes 
   used in the dynamic semantics of the ML Module system with higher
   order functors.  I define only those classes that are different
   from the corresponding classes in Standard ML.                    *)

local
structure HOFMLSignaturesInput : NestedRecTypeInputSig =
struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo    

val def_type_spec =
[
(* signature expressions *)

{type_name = "sigexp_h",
 constructors = 
     [{name = "SIGsigexp_h", arg_info = [being_defined "spec_h"]},
      {name = "SIGIDsigexp_h", arg_info = [existing sigid_ty]}]},

(* specifications *)

{type_name = "spec_h",
 constructors =
     [{name = "VALspec_h", arg_info = [existing valdesc_ty]},
      {name = "EXCEPTIONspec_h", arg_info = [existing exdesc_ty]},
      {name = "STRUCTUREspec_h", arg_info = [being_defined "strdesc_h"]},
      {name = "LOCALspec_h", arg_info = [being_defined "spec_h",
                                         being_defined "spec_h"]},
      {name = "OPENspec_h", 
       arg_info = [existing (mk_nonemptylist_ty (mk_long_ty strid_ty))]},
      {name = "INCLUDEspec_h", 
       arg_info = [existing (mk_nonemptylist_ty sigid_ty)]},
      {name = "EMPTYspec_h", arg_info = []},
      {name = "SEQspec_h", arg_info = [being_defined "spec_h",
                                       being_defined "spec_h"]},
      {name = "FUNCTORspec_h", arg_info = [existing funid_ty,
					   existing strid_ty,
					   being_defined "sigexp_h",
					   being_defined "sigexp_h"]}]},

(* structure descriptions *)

{type_name = "strdesc_h",
 constructors = 
     [{name = "STRIDstrdesc_h",
       arg_info = [existing strid_ty,
		   being_defined "sigexp_h",
		   type_op {Tyop = "option",
			    Args = [being_defined "strdesc_h"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name =  "HOFMLSignatures_rec_thm"
val New_Ty_Induct_Thm_Name = "HOFMLSignatures_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "HOFMLSignatures_unique_thm"
val Constructors_Distinct_Thm_Name = "HOFMLSignatures_constructors_distinct"
val Constructors_One_One_Thm_Name = "HOFMLSignatures_constructors_one_one"
val Cases_Thm_Name = "HOFMLSignatures_cases_thm"
end (* struct *)
in

structure HOFMLSignaturesDef =
    NestedRecTypeFunc (HOFMLSignaturesInput);
end;

val sigexp_h_ty = ==`:sigexp_h`==;
val spec_h_ty = ==`:spec_h`==;
val strdesc_h_ty = ==`:strdesc_h`==;


(* signature bindings *)

local
structure HOFMLSigbindInput : NestedRecTypeInputSig =
struct
structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "sigbind_h",
  constructors =
  [{name = "BINDsigbind_h",
    arg_info = [existing sigid_ty, existing sigexp_h_ty,
		type_op {Tyop = "option",
			 Args = [being_defined "sigbind_h"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "HOFMLSigbindrec_thm"
val New_Ty_Induct_Thm_Name = "HOFMLSigbindinduction_thm"
val New_Ty_Uniqueness_Thm_Name = "HOFMLSigbindunique_thm"
val Constructors_Distinct_Thm_Name = "HOFMLSigbindconstructors_distinct"
val Constructors_One_One_Thm_Name = "HOFMLSigbindconstructors_one_one"
val Cases_Thm_Name = "HOFMLSigbindcases_thm"
end (* struct *)
in
structure sigbindDef = NestedRecTypeFunc (HOFMLSigbindInput)
end;

val sigbind_h_ty = ==`:sigbind_h`==;


(* signature declarations *)

val sigdec_h_Axiom =
   define_type {name = "sigdec_h_Axiom",
                fixities = [Prefix, Prefix, Prefix],
                type_spec = `sigdec_h = SIGNATUREsigdec_h of sigbind_h
                                      | EMPTYsigdec_h
                                      | SEQsigdec_h of sigdec_h => sigdec_h`}
val sigdec_h_ty = == `:sigdec_h`==;

local
structure HOFMLStructuresInput  : NestedRecTypeInputSig =

struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[
(* structure expressions *)

{type_name = "strexp_h",
 constructors = 
    [{name = "STRUCTstrexp_h", arg_info = [being_defined "moddec_h"]},
     {name = "LONGSTRIDstrexp_h", arg_info = [existing (mk_long_ty strid_ty)]},
     {name = "APPstrexp_h", arg_info = [existing (mk_long_ty funid_ty), 
                                        being_defined "strexp_h"]},
     {name = "LETstrexp_h", arg_info = [being_defined "moddec_h",
                                        being_defined "strexp_h"]}]},

(* module declarations *)

{type_name = "moddec_h",
 constructors =
 [{name = "DECmoddec_h", arg_info = [existing dec_ty]},
  {name = "STRUCTUREmoddec_h", arg_info = [being_defined "strbind_h"]},
  {name = "LOCALmoddec_h", arg_info = [being_defined "moddec_h",
                                       being_defined "moddec_h"]},
  {name = "OPENmoddec_h",
   arg_info = [existing (mk_nonemptylist_ty(mk_long_ty strid_ty))]},
  {name = "EMPTYmoddec_h", arg_info = []},
  {name = "SEQmoddec_h", arg_info = [being_defined "moddec_h",
                                     being_defined "moddec_h"]},
  {name = "FUNCTORmoddec_h", arg_info = [being_defined "funbind_h"]}]},

(* structure bindings *)

{type_name = "strbind_h",
 constructors =
   [{name = "BINDstrbind_h",
     arg_info = [existing strid_ty,
		 type_op {Tyop = "option",
			  Args = [existing sigexp_h_ty]},
		 being_defined "strexp_h",
		 type_op {Tyop = "option",
			  Args = [being_defined "strbind_h"]}]}]},

(* functor bindings *)

{type_name = "funbind_h",
 constructors =
   [{name = "BINDfunbind_h",
     arg_info = [existing funid_ty,
		 existing strid_ty,
		 existing sigexp_h_ty,
		 type_op {Tyop = "option",
			  Args = [existing sigexp_h_ty]},
		 being_defined "strexp_h",
		 type_op {Tyop = "option",
			  Args = [being_defined "funbind_h"]}]},
    {name = "REBINDfunbind_h", arg_info = [existing funid_ty,
                                           existing (mk_long_ty funid_ty)]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "HOFMLStructures_rec_thm"
val New_Ty_Induct_Thm_Name = "HOFMLStructures_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "HOFMLStructures_unique_thm"
val Constructors_Distinct_Thm_Name = "HOFMLStructures_constructors_distinct"
val Constructors_One_One_Thm_Name = "HOFMLStructures_constructors_one_one"
val Cases_Thm_Name = "HOFMLStructures_cases_thm"
end (*struct*)
in
structure HOFMLStructuresDef = NestedRecTypeFunc (HOFMLStructuresInput);
end;


val strexp_h_ty = ==`:strexp_h`==;
val moddec_h_ty = ==`:moddec_h`==;
val strbind_h_ty = ==`:strbind_h`==;
val funbind_h_ty = ==`:funbind_h`==;


(* functor declarations have been absored into module declarations *)


(* top-level declarations *)

val topdec_h_Axiom =
  define_type {name = "topdec_h_Axiom",
               fixities = [Prefix, Prefix],
               type_spec = `topdec_h = MODDEC_H of moddec_h
                                     | SIGDEC_H of sigdec_h`}
val topdec_h_ty = ==`:topdec_h`==;


