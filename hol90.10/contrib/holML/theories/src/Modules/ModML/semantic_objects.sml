(* File: ModML/semantic_objects.sml *)

(* Description: Definitions of the compound semantic objects used
   in the dynamic semantics of the ML Module system. *)

(* References: The "Definition", section 7.2
               semantic_objects.txt          *)

(* structure environment packets *)

val strenv_pack_Axiom =
    define_type{name= "strenv_pack_Axiom", fixities = [Prefix,Prefix],
		type_spec = `strenv_pack = STRENVsp of strenv
		                         | PACKsp of pack`};
val strenv_pack_ty = ==`:strenv_pack`==;

val strenv_pack_induction_thm =
    save_thm("strenv_pack_induction_thm",
	     prove_induction_thm strenv_pack_Axiom)
val strenv_pack_cases_thm =
    save_thm("strenv_pack_cases_thm",
	     prove_cases_thm strenv_pack_induction_thm)
val strenv_pack_constructors_one_one =
    save_thm("strenv_pack_constructors_one_one",
    prove_constructors_one_one strenv_pack_Axiom)
val strenv_pack_constructors_distinct =
    save_thm("strenv_pack_constructors_distinct",
	     prove_constructors_distinct strenv_pack_Axiom);


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
structure ModMLInterfacesInput : NestedRecTypeInputSig = 
struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[

(* interfaces *)

{type_name = "int",
 constructors = 
 [{name = "BASICint", arg_info = [being_defined "intenv",
				  existing (mk_set_ty var_ty),
				  existing (mk_set_ty excon_ty)]}]},

(* interface environments *)

{type_name = "intenv",
 constructors =
 [{name = "INTENV",
   arg_info =
   [type_op {Tyop = "finmap",
	     Args = [type_op {Tyop = "list",
			      Args = [type_op {Tyop = "prod",
					       Args =
					       [existing strid_ty,
						being_defined "int"]}]}]}]}]}
]

val recursor_thms = [finmap_Axiom,list_Axiom,prod_Axiom]
val New_Ty_Existence_Thm_Name = "ModMLInterfaces_rec_thm"
val New_Ty_Induct_Thm_Name = "ModMLInterfaces_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "ModMLInterfaces_unique_thm"
val Constructors_Distinct_Thm_Name = "ModMLInterfaces_distinct_thm"
val Constructors_One_One_Thm_Name = "ModMLInterfaces_one_one_thm"
val Cases_Thm_Name = "ModMLInterfaces_cases_thm"
end (* struct *)
in
structure ModMLInterfacesDef = NestedRecTypeFunc (ModMLInterfacesInput)
end;

val int_ty = ==`:int`==;
val intenv_ty = ==`:intenv`==;


(* signature environments *)

val sigenv_Axiom =
    define_type {name = "sigenv",
                 fixities = [Prefix],
                 type_spec = `sigenv = SIGENV of (sigid -> int lift)`};

val sigenv_ty = ==`:sigenv`==;

val sigenv_induction_thm =
    save_thm("sigenv_induction_thm", prove_induction_thm sigenv_Axiom)
val sigenv_cases_thm =
    save_thm("sigenv_cases_thm", prove_cases_thm sigenv_induction_thm)
val sigenv_constructors_one_one =
    save_thm("sigenv_constructors_one_one",
    prove_constructors_one_one sigenv_Axiom)


(* interface bases *)

val intbasis_Axiom = 
   define_type {name = "intbasis",
                fixities = [Prefix],
                type_spec = `intbasis = INTBASIS of sigenv => intenv`}
val intbasis_ty = ==`:intbasis`==;

val intbasis_induction_thm =
    save_thm("intbasis_induction_thm", prove_induction_thm intbasis_Axiom)
val intbasis_cases_thm =
    save_thm("intbasis_cases_thm", prove_cases_thm intbasis_induction_thm)
val intbasis_constructors_one_one =
    save_thm("intbasis_constructors_one_one",
    prove_constructors_one_one intbasis_Axiom)


local
structure ModMLBasesInput : NestedRecTypeInputSig =
struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[

(* functor closures *)

{type_name = "funclos",
 constructors = 
    [{name = "FUNCLOS",
      arg_info = [existing strid_ty,
		  existing int_ty,
		  existing strexp_ty,
		  type_op {Tyop = "option",
			   Args = [existing int_ty]},
		  being_defined "basis"]}]},
  
(* bases *)

{type_name = "basis",
 constructors =
 [{name = "BASIS", arg_info = [being_defined "funenv",
			       existing sigenv_ty,
			       existing env_ty]}]},

(* functor environments *)

{type_name = "funenv",
 constructors = 
 [{name = "FUNENV",
   arg_info =
   [type_op {Tyop = "finmap",
	     Args =
	     [type_op {Tyop = "list",
		       Args = [type_op {Tyop = "prod",
					Args =
					[existing funid_ty,
					 being_defined "funclos"]}]}]}]}]}
]

val recursor_thms = [finmap_Axiom,list_Axiom,prod_Axiom,option_Axiom]
val New_Ty_Existence_Thm_Name = "ModMLBases_rec_thm"
val New_Ty_Induct_Thm_Name = "ModMLBases_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "ModMLBases_unique_thm"
val Constructors_Distinct_Thm_Name = "ModMLBases_distinct_thm"
val Constructors_One_One_Thm_Name = "ModMLBases_one_one_thm"
val Cases_Thm_Name = "ModMLBases_cases_thm"
end (* struct *)
in
structure ModMLBasesDef = NestedRecTypeFunc (ModMLBasesInput)
end;


val funclos_ty = ==`:funclos`==;
val basis_ty = ==`:basis`==;
val funenv_ty = ==`:funenv`==;


(* Basis packets *)

val basis_pack_Axiom =
    define_type{name= "basis_pack_Axiom", fixities = [Prefix,Prefix],
		type_spec = `basis_pack = BASISbp of basis
		                        | PACKbp of pack`};

val basis_pack_ty = ==`:basis_pack`==;

val basis_pack_induction_thm =
    save_thm("basis_pack_induction_thm", prove_induction_thm basis_pack_Axiom)
val basis_pack_cases_thm =
    save_thm("basis_pack_cases_thm", prove_cases_thm basis_pack_induction_thm)
val basis_pack_constructors_one_one =
    save_thm("basis_pack_constructors_one_one",
    prove_constructors_one_one basis_pack_Axiom)
val basis_pack_constructors_distinct =
    save_thm("basis_pack_constructors_distinct",
	     prove_constructors_distinct basis_pack_Axiom);



