(* File: MLenvInput.sml *)

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

(* And now our environments... 
   val ::= ASSGval | SVALval sval | BASval basval | CONval con | 
           APPCONval con val | EXVALval exval | RECORDval record |
	   ADDRval addr | CLOSUREval closure
   record ::= RECORD (((label#val)list) finmap)
   exval ::= NAMEexval exname | NAMEVALexval exname val
   closure ::= CLOSURE match env varenv
   env ::= ENV strenv varenv exconenv
   strenv ::= STRENV (((strid#env)list) finmap)
   varenv ::= VARENV (((var#val)list) finmap)

*)

structure MLenvInput  : NestedRecTypeInputSig =
struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "val",
  constructors =
      [{name = "ASSGval", arg_info = []},
       {name = "SVALval", arg_info = [existing sval_ty]},
       {name = "BASval", arg_info = [existing basval_ty]},
       {name = "CONval", arg_info = [existing con_ty]},
       {name = "APPCONval", arg_info = [existing con_ty,
					being_defined "val"]},
       {name = "EXVALval", arg_info = [being_defined "exval"]},
       {name = "RECORDval", arg_info = [being_defined "record"]},
       {name = "ADDRval", arg_info = [existing addr_ty]},
       {name = "CLOSUREval", arg_info = [being_defined "closure"]}]},
 {type_name = "record",
  constructors =
      [{name = "RECORD", arg_info = 
	[type_op {Tyop = "finmap", Args = 
		  [type_op {Tyop = "list", Args = 
			    [type_op {Tyop = "prod", Args = 
				      [existing label_ty, 
				       being_defined "val"]}]}]}]}]},
 {type_name = "exval",
  constructors =
      [{name = "NAMEexval", arg_info = [existing exname_ty]},
       {name = "NAMEVALexval", arg_info = [existing exname_ty,
					   being_defined "val"]}]},
 {type_name = "closure",
  constructors = 
      [{name = "CLOSURE", 
	arg_info = [existing match_ty, being_defined "env",
		    being_defined "varenv"]}]},
 {type_name = "env",
  constructors =
      [{name = "ENV", 
	arg_info = [being_defined "strenv", being_defined "varenv",
		    existing exconenv_ty]}]},
 {type_name = "strenv",
  constructors =
      [{name = "STRENV", arg_info = 
	[type_op {Tyop = "finmap", Args = 
		  [type_op {Tyop = "list", Args = 
			    [type_op {Tyop = "prod", Args = 
				      [existing strid_ty, 
				       being_defined "env"]}]}]}]}]},
 {type_name = "varenv",
  constructors =
      [{name = "VARENV", arg_info = 
	[type_op {Tyop = "finmap", Args = 
		  [type_op {Tyop = "list", Args = 
			    [type_op {Tyop = "prod", Args = 
				      [existing var_ty, 
				       being_defined "val"]}]}]}]}]}]
    val recursor_thms = [finmap_Axiom, list_Axiom, prod_Axiom]
    val New_Ty_Existence_Thm_Name = "env_existence"
    val New_Ty_Induct_Thm_Name = "env_induct"
    val New_Ty_Uniqueness_Thm_Name = "env_unique"
    val Constructors_One_One_Thm_Name = "env_constructors_one_one"
    val Constructors_Distinct_Thm_Name = "env_constructors_distinct"
    val Cases_Thm_Name = "env_cases"
end (* struct *)

structure EnvDef = NestedRecTypeFunc (MLenvInput);



