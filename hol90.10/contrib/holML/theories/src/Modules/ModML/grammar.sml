(* File: ModML/grammar.sml *)

(* Description: This file contains the definitions of the syntax 
   classes used in the dynamic semantics of the ML Module system. *)

(* References: The "Definition", Sections 3.4, 7.1
               grammar.txt                          *)

local
structure ModMLSignaturesInput : NestedRecTypeInputSig =
struct
structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[
(* signature expressions *)

{type_name = "sigexp",
 constructors = 
     [{name = "SIGsigexp", arg_info = [being_defined "spec"]},
      {name = "SIGIDsigexp", arg_info = [existing sigid_ty]}]},

(* specifications *)

{type_name = "spec",
 constructors =
     [{name = "VALspec", arg_info = [existing valdesc_ty]},
      {name = "EXCEPTIONspec", arg_info = [existing exdesc_ty]},
      {name = "STRUCTUREspec", arg_info = [being_defined "strdesc"]},
      {name = "LOCALspec", arg_info = [being_defined "spec",
                                       being_defined "spec"]},
      {name = "OPENspec", 
       arg_info = [existing (mk_nonemptylist_ty (mk_long_ty strid_ty))]},
      {name = "INCLUDEspec",
       arg_info = [existing (mk_nonemptylist_ty sigid_ty)]},
      {name = "EMPTYspec", arg_info = []},
      {name = "SEQspec", arg_info = [being_defined "spec",
                                     being_defined "spec"]}]},

(* structure descriptions *)

{type_name = "strdesc",
 constructors = 
     [{name = "STRIDstrdesc",
       arg_info = [existing strid_ty,
		   being_defined "sigexp",
		   type_op {Tyop = "option",
			    Args = [being_defined "strdesc"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "ModMLSignatures_rec_thm"
val New_Ty_Induct_Thm_Name = "ModMLSignatures_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "ModMLSignatures_unique_thm"
val Constructors_Distinct_Thm_Name = "ModMLSignatures_constructors_distinct"
val Constructors_One_One_Thm_Name = "ModMLSignatures_constructors_one_one"
val Cases_Thm_Name = "ModMLSignatures_cases_thm"
end (* struct *);
in
structure ModMLSignaturesDef = NestedRecTypeFunc (ModMLSignaturesInput);
end

val sigexp_ty = ==`:sigexp`==;
val spec_ty = ==`:spec`==;
val strdesc_ty = ==`:strdesc`==;


(* signature bindings *)
local
structure sigbindInput : NestedRecTypeInputSig =
struct
structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "sigbind",
  constructors =
  [{name = "BINDsigbind",
    arg_info = [existing sigid_ty, existing sigexp_ty,
		type_op {Tyop = "option",
			 Args = [being_defined "sigbind"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "sigbind_rec_thm"
val New_Ty_Induct_Thm_Name = "sigbind_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "sigbind_unique_thm"
val Constructors_Distinct_Thm_Name = "sigbind_constructors_distinct"
val Constructors_One_One_Thm_Name = "sigbind_constructors_one_one"
val Cases_Thm_Name = "sigbind_cases_thm"
end (* struct *)
in
structure sigbindDef = NestedRecTypeFunc (sigbindInput)
end;


val sigbind_ty = ==`:sigbind`==;


(* signature declarations *)

val sigdec_Axiom =
   define_type {name = "sigdec_Axiom",
                fixities = [Prefix, Prefix, Prefix],
                type_spec = `sigdec = SIGNATUREsigdec of sigbind
                                    | EMPTYsigdec
                                    | SEQsigdec of sigdec => sigdec`}
val sigdec_ty = == `:sigdec`==;

val sigdec_induction_thm =
    save_thm("sigdec_induction_thm", prove_induction_thm sigdec_Axiom)
val sigdec_cases_thm =
    save_thm("sigdec_cases_thm", prove_cases_thm sigdec_induction_thm)
val sigdec_constructors_one_one =
    save_thm("sigdec_constructors_one_one",
    prove_constructors_one_one sigdec_Axiom)
val sigdec_constructors_distinct =
    save_thm("sigdec_constructors_distinct",
	     prove_constructors_distinct sigdec_Axiom);

(*
(* functor signature expressions *)

val funsigexp_Axiom = 
    define_type {name = "funsigexp_Axiom",
                 fixities = [Prefix],
                 type_spec = `funsigexp =
		              FUNSIG of strid => sigexp => sigexp`}
val funsigexp_ty = ==`:funsigexp`==;

val funsigexp_induction_thm =
    save_thm("funsigexp_induction_thm", prove_induction_thm funsigexp_Axiom)
val funsigexp_cases_thm =
    save_thm("funsigexp_cases_thm", prove_cases_thm funsigexp_induction_thm)
val funsigexp_constructors_one_one =
    save_thm("funsigexp_constructors_one_one",
    prove_constructors_one_one funsigexp_Axiom)


(* functor descriptions *)

val fundesc_Axiom =
    define_type {name = "fundesc_Axiom",
                 fixities = [Prefix, Prefix],
                 type_spec = `fundesc =
		                FUNIDfundesc of funid => funsigexp
			      | ANDfundesc of funid => funsigexp => fundesc`}
val fundesc_ty = ==`:fundesc`==;

val fundesc_induction_thm =
    save_thm("fundesc_induction_thm", prove_induction_thm fundesc_Axiom)
val fundesc_cases_thm =
    save_thm("fundesc_cases_thm", prove_cases_thm fundesc_induction_thm)
val fundesc_constructors_one_one =
    save_thm("fundesc_constructors_one_one",
    prove_constructors_one_one fundesc_Axiom)
val fundesc_constructors_distinct =
    save_thm("fundesc_constructors_distinct",
	     prove_constructors_distinct fundesc_Axiom);


(* functor specifications *)

val funspec_Axiom =
    define_type {name = "funspec_Axiom",
                 fixities = [Prefix, Prefix, Prefix],
                 type_spec = `funspec = FUNCTORfunspec of fundesc
                                      | EMPTYfunspec
                                      | SEQfunspec of funspec => funspec`}
val funspec_ty = ==`:funspec`==;

val funspec_induction_thm =
    save_thm("funspec_induction_thm", prove_induction_thm funspec_Axiom)
val funspec_cases_thm =
    save_thm("funspec_cases_thm", prove_cases_thm funspec_induction_thm)
val funspec_constructors_one_one =
    save_thm("funspec_constructors_one_one",
    prove_constructors_one_one funspec_Axiom)
val funspec_constructors_distinct =
    save_thm("funspec_constructors_distinct",
	     prove_constructors_distinct funspec_Axiom);

*)

local
structure ModMLStructuresInput  : NestedRecTypeInputSig =

struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[
(* structure expressions *)

{type_name = "strexp",
 constructors = 
    [{name = "STRUCTstrexp", arg_info = [being_defined "strdec"]},
     {name = "LONGSTRIDstrexp", arg_info = [existing (mk_long_ty strid_ty)]},
     {name = "APPstrexp", arg_info = [existing funid_ty, 
                                      being_defined "strexp"]},
     {name = "LETstrexp", arg_info = [being_defined "strdec",
                                      being_defined "strexp"]}]},

(* structure declarations *)

{type_name = "strdec",
 constructors =
   [{name = "DECstrdec", arg_info = [existing dec_ty]},
    {name = "STRUCTUREstrdec", arg_info = [being_defined "strbind"]},
    {name = "LOCALstrdec", arg_info = [being_defined "strdec",
                                       being_defined "strdec"]},
    {name = "EMPTYstrdec", arg_info = []},
    {name = "SEQstrdec", arg_info = [being_defined "strdec",
                                     being_defined "strdec"]}]},

(* structure bindings *)
(*strbind ::= BINDstrbind strid (sigexp option) strexp (strbind option)*)
{type_name = "strbind",
 constructors =
   [{name = "BINDstrbind",
     arg_info = [existing strid_ty,
		 type_op {Tyop = "option",
			  Args = [existing sigexp_ty]},
		 being_defined "strexp",
		 type_op {Tyop = "option",
			  Args = [being_defined "strbind"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "ModMLStructures_rec_thm"
val New_Ty_Induct_Thm_Name = "ModMLStructures_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "ModMLStructures_unique_thm"
val Constructors_Distinct_Thm_Name = "ModMLStructures_constructors_distinct"
val Constructors_One_One_Thm_Name = "ModMLStructures_constructors_one_one"
val Cases_Thm_Name = "ModMLStructures_cases_thm"
end (*struct*)
in
structure ModMLStructuresDef = NestedRecTypeFunc (ModMLStructuresInput);
end;

val strexp_ty = ==`:strexp`==;
val strdec_ty = ==`:strdec`==;
val strbind_ty = ==`:strbind`==;


(* functor bindings *)
local
structure funbindInput : NestedRecTypeInputSig =
struct
structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "funbind",
 constructors =
 [{name = "BINDfunbind",
   arg_info = [existing funid_ty, existing strid_ty, existing sigexp_ty,
	       type_op {Tyop = "option",Args = [existing sigexp_ty]},
	       existing strexp_ty,
	       type_op {Tyop = "option",
			Args = [being_defined "funbind"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "funbind_rec_thm"
val New_Ty_Induct_Thm_Name = "funbind_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "funbind_unique_thm"
val Constructors_Distinct_Thm_Name = "funbind_constructors_distinct"
val Constructors_One_One_Thm_Name = "funbind_constructors_one_one"
val Cases_Thm_Name = "funbind_cases_thm"
end (* struct *)
in
structure funbindDef = NestedRecTypeFunc (funbindInput)
end;

val funbind_ty = ==`:funbind`==;


(* functor declarations *)

val fundec_Axiom =
  define_type {name = "fundec_Axiom",
               fixities = [Prefix, Prefix, Prefix],
               type_spec = `fundec = FUNCTORfundec of funbind
                                   | EMPTYfundec
                                   | SEQfundec of fundec => fundec`}
val fundec_ty = ==`:fundec`==;

val fundec_induction_thm =
    save_thm("fundec_induction_thm", prove_induction_thm fundec_Axiom)
val fundec_cases_thm =
    save_thm("fundec_cases_thm", prove_cases_thm fundec_induction_thm)
val fundec_constructors_one_one =
    save_thm("fundec_constructors_one_one",
    prove_constructors_one_one fundec_Axiom)
val fundec_constructors_distinct =
    save_thm("fundec_constructors_distinct",
	     prove_constructors_distinct fundec_Axiom);


(* top-level declarations *)

val topdec_Axiom =
  define_type {name = "topdec_Axiom",
               fixities = [Prefix, Prefix, Prefix],
               type_spec = `topdec = STRDEC of strdec
                                   | SIGDEC of sigdec
                                   | FUNDEC of fundec`}
val topdec_ty = ==`:topdec`==;

val topdec_induction_thm =
    save_thm("topdec_induction_thm", prove_induction_thm topdec_Axiom)
val topdec_cases_thm =
    save_thm("topdec_cases_thm", prove_cases_thm topdec_induction_thm)
val topdec_constructors_one_one =
    save_thm("topdec_constructors_one_one",
    prove_constructors_one_one topdec_Axiom)
val topdec_constructors_distinct =
    save_thm("topdec_constructors_distinct",
	     prove_constructors_distinct topdec_Axiom);


(* programs *)

local
structure programInput : NestedRecTypeInputSig = 
struct
structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "program",
 constructors =
 [{name = "SEQprogram",
   arg_info = [existing topdec_ty,
	       type_op {Tyop = "option",
			Args = [being_defined "program"]}]}]}]
val recursor_thms = [option_Axiom]
val New_Ty_Existence_Thm_Name = "program_rec_thm"
val New_Ty_Induct_Thm_Name = "program_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "program_unique_thm"
val Constructors_Distinct_Thm_Name = "program_constructors_distinct"
val Constructors_One_One_Thm_Name = "program_constructors_one_one"
val Cases_Thm_Name = "program_cases_thm"
end (* struct *)
in
structure programDef = NestedRecTypeFunc (programInput)
end;

val program_ty = ==`:program`==;
