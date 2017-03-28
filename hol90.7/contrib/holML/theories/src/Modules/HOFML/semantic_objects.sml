(* File: HOFML/semantic_objects.sml *)

(* Description: Definitions of the compound semantic objects used
   in the dynamic semantics of the ML Module system with higher-order
   functors *)

val prod_Axiom =
    prove((--`!f. ?!g. !(x:'a) (y:'b).((g(x,y)):'c) = (f x y)`--),
	  GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN
	  REPEAT STRIP_TAC THENL
	  [(EXISTS_TAC (--`UNCURRY (f:'a -> 'b -> 'c)`--) THEN
	    REWRITE_TAC [definition "pair" "UNCURRY_DEF"]),
	   (CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
	    PURE_ONCE_REWRITE_TAC
	    [SYM(SPEC_ALL (theorem "pair" "PAIR"))] THEN
	    ASM_REWRITE_TAC[])]);

local
structure HOFMLInterfacesInput  : NestedRecTypeInputSig =
struct

(* The following mutually recursive types are the components of the values
   (inteferaces) to which signatures evalutate. *)

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[

(* interfaces *)

{type_name = "int_h",
 constructors = 
    [{name = "INT_H", arg_info = [ being_defined "funintenv_h",
                                   being_defined "strintenv_h",
                                   existing (mk_set_ty var_ty),
                                   existing (mk_set_ty excon_ty)]}]},

(* structure interface environments *)

{type_name = "strintenv_h",
 constructors =
 [{name = "STRINTENV_H",
   arg_info =
   [type_op {Tyop = "finmap",
	     Args = [type_op {Tyop = "list",
			      Args = [type_op
				      {Tyop = "prod",
				       Args =
				       [existing strid_ty,
					being_defined "int_h"]}]}]}]}]},

(* functor interface environments *) 
(* This tells how to cut down the output of functors that are subcomponent
   of the structure that is thinned against the signature that evaluates to
   an inteface with this functor interface environment *)

{type_name = "funintenv_h",
 constructors =
 [{name = "FUNINTENV_H",
   arg_info =
   [type_op {Tyop = "finmap",
	     Args = [type_op {Tyop = "list",
			      Args = [type_op
				      {Tyop = "prod",
				       Args =
				       [existing funid_ty,
					being_defined "int_h"]}]}]}]}]}]

val recursor_thms = [finmap_Axiom,list_Axiom,prod_Axiom]
val New_Ty_Existence_Thm_Name = "HOFMLInterfaces_rec_thm"
val New_Ty_Induct_Thm_Name = "HOFMLInterfaces_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "HOFMLInterfaces_unique_thm"
val Constructors_Distinct_Thm_Name = "HOFMLInterfaces_distinct_thm"
val Constructors_One_One_Thm_Name = "HOFMLInterfaces_one_one_thm"
val Cases_Thm_Name = "HOFMLInterfaces_cases_thm"
end (* struct *)
in
structure HOFMLInterfacesDef = NestedRecTypeFunc (HOFMLInterfacesInput)
end;


val int_h_ty = ==`:int_h`==;
val strintenv_h_ty = ==`:strintenv_h`==;
val funintenv_h_ty = ==`:funintenv_h`==;


(* signature environments *)

val sigenv_h_Axiom =
    define_type {name = "sigenv_h",
                 fixities = [Prefix],
                 type_spec = `sigenv_h = SIGENV_H of (sigid ->int_h lift)`};

val sigenv_h_ty = ==`:sigenv_h`==;

val sigenv_h_induction_thm =
    save_thm("sigenv_h_induction_thm", prove_induction_thm sigenv_h_Axiom)
val sigenv_h_cases_thm =
    save_thm("sigenv_h_cases_thm", prove_cases_thm sigenv_h_induction_thm)
val sigenv_h_constructors_one_one =
    save_thm("sigenv_h_constructors_one_one",
    prove_constructors_one_one sigenv_h_Axiom)


(* interface bases *)

val intbasis_h_Axiom = 
   define_type {name = "intbasis_h",
                fixities = [Prefix],
                type_spec = 
                    `intbasis_h = INTBASIS_H of 
                                   sigenv_h => strintenv_h => funintenv_h`}

val intbasis_h_ty = ==`:intbasis_h`==;

val intbasis_h_induction_thm =
    save_thm("intbasis_h_induction_thm", prove_induction_thm intbasis_h_Axiom)
val intbasis_h_cases_thm =
    save_thm("intbasis_h_cases_thm", prove_cases_thm intbasis_h_induction_thm)
val intbasis_h_constructors_one_one =
    save_thm("intbasis_h_constructors_one_one",
    prove_constructors_one_one intbasis_h_Axiom)


(* The following mutually recursive types are the components of the values
   (higher-order environments and functor closures) to which structures
   and functors evaluate. *)

local
structure HOFMLBasesInput : NestedRecTypeInputSig  =
struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[
(* environments *)

{type_name = "env_h",
 constructors =
    [{name = "ENV_H", arg_info = [being_defined "funenv_h",
                                  being_defined "strenv_h",
                                  existing (==`:varenv`==),
                                  existing (==`:exconenv`==)]}]},

(* structure environments *)

{type_name = "strenv_h",
 constructors =
 [{name = "STRENV_H",
   arg_info = 
   [type_op {Tyop = "finmap",
	     Args =
	     [type_op {Tyop = "list",
		       Args = [type_op {Tyop = "prod",
					Args =
					[existing strid_ty,
					 being_defined "env_h"]}]}]}]}]},

(* functor environments *)

{type_name = "funenv_h",
 constructors = 
 [{name = "FUNENV_H",
   arg_info =
   [type_op {Tyop = "finmap",
	     Args =
	     [type_op {Tyop = "list",
		       Args = [type_op {Tyop = "prod",
					Args =
					[existing funid_ty,
                                         being_defined "funclos_h"]}]}]}]}]},

(* functor closures *)

{type_name = "funclos_h",
 constructors = 
 [{name = "FUNCLOS_H",
   arg_info = [existing strid_ty,
	       existing int_h_ty,
	       existing strexp_h_ty,
	       type_op {Tyop = "option", Args = [existing int_h_ty]},
	       being_defined "basis_h"]}]},

(* bases *)
(* The ultimate environments *)

{type_name = "basis_h",
 constructors =
    [{name = "BASIS_H", arg_info = [existing sigenv_h_ty,
                                    being_defined "env_h"]}]}]
val recursor_thms = [finmap_Axiom,list_Axiom,prod_Axiom,option_Axiom]
val New_Ty_Existence_Thm_Name = "HOFMLBases_rec_thm"
val New_Ty_Induct_Thm_Name = "HOFMLBases_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "HOFMLBases_unique_thm"
val Constructors_Distinct_Thm_Name = "HOFMLBases_distinct_thm"
val Constructors_One_One_Thm_Name = "HOFMLBases_one_one_thm"
val Cases_Thm_Name = "HOFMLBases_cases_thm"
end (* struct *)
in
structure HOFMLBasesDef = NestedRecTypeFunc (HOFMLBasesInput)
end;


val env_h_ty = ==`:env_h`==;
val strenv_h_ty = ==`:strenv_h`==;
val funclos_h_ty = ==`:funclos_h`==;
val basis_h_ty = ==`:basis_h`==;
val funenv_h_ty = ==`:funenv_h`==;


(* Basis packets *)

val basis_pack_h_Axiom =
    define_type{name= "basis_pack_h_Axiom", fixities = [Prefix,Prefix],
		type_spec = `basis_pack_h = BASISbp_h of basis_h
		                          | PACKbp_h of pack`};

val basis_pack_h_ty = ==`:basis_pack_h`==;

val basis_pack_h_induction_thm =
    save_thm("basis_pack_h_induction_thm",
	     prove_induction_thm basis_pack_h_Axiom)
val basis_pack_h_cases_thm =
    save_thm("basis_pack_h_cases_thm",
	     prove_cases_thm basis_pack_h_induction_thm)
val basis_pack_h_constructors_one_one =
    save_thm("basis_pack_h_constructors_one_one",
	     prove_constructors_one_one basis_pack_h_Axiom)
val basis_pack_h_constructors_distinct =
    save_thm("basis_pack_h_constructors_distinct",
	     prove_constructors_distinct basis_pack_h_Axiom);

(* structure environment packets *)

val strenv_pack_h_Axiom =
    define_type{name= "strenv_pack_h_Axiom", fixities = [Prefix,Prefix],
		type_spec = `strenv_pack_h = STRENVsp_h of strenv_h
		                           | PACKsp_h of pack`};
val strenv_pack_h_ty = ==`:strenv_pack_h`==;

val strenv_pack_h_induction_thm =
    save_thm("strenv_pack_h_induction_thm",
	     prove_induction_thm strenv_pack_h_Axiom)
val strenv_pack_h_cases_thm =
    save_thm("strenv_pack_h_cases_thm",
	     prove_cases_thm strenv_pack_h_induction_thm)
val strenv_pack_h_constructors_one_one =
    save_thm("strenv_pack_h_constructors_one_one",
    prove_constructors_one_one strenv_pack_h_Axiom)
val strenv_pack_h_constructors_distinct =
    save_thm("strenv_pack_h_constructors_distinct",
	     prove_constructors_distinct strenv_pack_h_Axiom);

(* environment packets *)

val env_pack_h_Axiom =
    define_type{name= "env_pack_h_Axiom", fixities = [Prefix,Prefix],
		type_spec = `env_pack_h = ENVep_h of env_h
		                        | PACKep_h of pack`};
val env_pack_h_ty = ==`:env_pack_h`==;

val env_pack_h_induction_thm =
    save_thm("env_pack_h_induction_thm",
	     prove_induction_thm env_pack_h_Axiom)
val env_pack_h_cases_thm =
    save_thm("env_pack_h_cases_thm",
	     prove_cases_thm env_pack_h_induction_thm)
val env_pack_h_constructors_one_one =
    save_thm("env_pack_h_constructors_one_one",
    prove_constructors_one_one env_pack_h_Axiom)
val env_pack_h_constructors_distinct =
    save_thm("env_pack_h_constructors_distinct",
	     prove_constructors_distinct env_pack_h_Axiom);
