(* File: ModML/grammar.sml *)

(* Description: This file contains the definitions of the syntax 
   classes of identifiers and descriptions *)

(* References: The "Definition", Sections 3.4, 7.1
               grammar.txt                          *)

(* signature identifiers *)

val sigid_Axiom = define_type{name = "sigid_Axiom",
                              fixities = [Prefix],
                              type_spec = `sigid = SIGID of string`};
val sigid_ty = ==`:sigid`==;

val sigid_induction_thm =
    save_thm("sigid_induction_thm", prove_induction_thm sigid_Axiom)
val sigid_cases_thm =
    save_thm("sigid_cases_thm", prove_cases_thm sigid_induction_thm)
val sigid_constructors_one_one =
    save_thm("sigid_constructors_one_one",
    prove_constructors_one_one sigid_Axiom)


val SIGID_arg_DEF = new_recursive_definition 
    {name = "SIGID_arg_DEF",
     fixity = Prefix,
     rec_axiom = sigid_Axiom,
     def = (--`SIGID_arg (SIGID s) = s`--)};


(* functor identifiers *)

val funid_Axiom = define_type{name = "funid_Axiom",
                              fixities = [Prefix],
                              type_spec = `funid = FUNID of string`};
val funid_ty = ==`:funid`==;

val funid_induction_thm =
    save_thm("funid_induction_thm", prove_induction_thm funid_Axiom)
val funid_cases_thm =
    save_thm("funid_cases_thm", prove_cases_thm funid_induction_thm)
val funid_constructors_one_one =
    save_thm("funid_constructors_one_one",
    prove_constructors_one_one funid_Axiom)


val FUNID_arg_DEF = new_recursive_definition 
    {name = "FUNID_arg_DEF",
     fixity = Prefix,
     rec_axiom = funid_Axiom,
     def = (--`FUNID_arg (FUNID s) = s`--)};

val less_funid_DEF = new_definition
("less_funid_DEF",
 (--`less_funid f1 f2 = ltstring (FUNID_arg f1) (FUNID_arg  f2)`--));


(* value descriptions *)

local
structure valdescInput : NestedRecTypeInputSig = 
struct
structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "valdesc",
 constructors =
 [{name = "VARvaldesc",
   arg_info = [existing (==`:var`==),
	       type_op {Tyop = "option",
			Args = [being_defined "valdesc"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "valdesc_rec_thm"
val New_Ty_Induct_Thm_Name = "valdesc_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "valdesc_unique_thm"
val Constructors_Distinct_Thm_Name = "valdesc_constructors_distinct"
val Constructors_One_One_Thm_Name = "valdesc_constructors_one_one"
val Cases_Thm_Name = "valdesc_cases_thm"
end (* struct *)
in
structure valdescDef = NestedRecTypeFunc (valdescInput)
end;

val valdesc_ty = ==`:valdesc`==;


(* exception descriptions *)

local
structure exdescInput : NestedRecTypeInputSig = 
struct
structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "exdesc",
 constructors =
 [{name = "EXCONexdesc",
   arg_info = [existing (==`:excon`==),
	       type_op {Tyop = "option",
			Args = [being_defined "exdesc"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "exdesc_rec_thm"
val New_Ty_Induct_Thm_Name = "exdesc_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "exdesc_unique_thm"
val Constructors_Distinct_Thm_Name = "exdesc_constructors_distinct"
val Constructors_One_One_Thm_Name = "exdesc_constructors_one_one"
val Cases_Thm_Name = "exdesc_cases_thm"
end (* struct *)
in
structure exdescDef = NestedRecTypeFunc (exdescInput)
end;

val exdesc_ty = ==`:exdesc`==;

