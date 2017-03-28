(* BASIC TERMS *)

(* STRUCTURE IDENTIFIERS
   strid ::= STRID string *)
val strid_Axiom = define_type{name="strid_Axiom",fixities = [Prefix],
			      type_spec = `strid = STRID of string`};
val strid_induction_thm = 
    save_thm("strid_induction_thm",prove_induction_thm strid_Axiom)
val strid_cases_thm =
    save_thm("strid_cases_thm", prove_cases_thm strid_induction_thm)
val strid_constructors_one_one =
    save_thm("strid_constructors_one_one",
	     prove_constructors_one_one strid_Axiom)
val STRID_arg_DEF = new_recursive_definition 
    {name = "STRID_arg_DEF",
     fixity = Prefix,
     rec_axiom = strid_Axiom,
     def = (--`STRID_arg(STRID s) = s`--)}
val less_strid_DEF = new_definition
("less_strid_DEF",
 --`less_strid l1 l2 = ltstring (STRID_arg l1) (STRID_arg l2)`--)


(* LONG IDENTIFIERS
   'a long ::= BASE 'a | QUALIFIED strid ('a long) *)
val long_Axiom = define_type{name="long_Axiom",fixities = [Prefix,Prefix],
			     type_spec = `long = BASE of 'a
			                       | QUALIFIED of strid => long`}
val long_induction_thm =
    save_thm("long_induction_thm", prove_induction_thm long_Axiom)
val long_cases_thm =
    save_thm("long_cases_thm", prove_cases_thm long_induction_thm)
val long_constructors_one_one =
    save_thm("long_constructors_one_one",
	     prove_constructors_one_one long_Axiom)
val long_constructors_distinct =
    save_thm("long_constructors_distinct",
	     prove_constructors_distinct long_Axiom)

(* long_base gives the base object in a (qualified) long object *)
val long_base_DEF = new_recursive_definition 
    {name = "long_base_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = (--`(long_base (BASE x) = (x:'a)) /\
	       (long_base (QUALIFIED strid long_x) = long_base long_x)`--)}
fun mk_long_ty ty = mk_type{Tyop = "long", Args = [ty]}


(* VARIABLES 
   var ::= VAR string *)
val var_Axiom = define_type{name="var_Axiom",fixities = [Prefix],
                            type_spec =`var = VAR of string`}
val var_induction_thm =
    save_thm("var_induction_thm", prove_induction_thm var_Axiom)
val var_cases_thm =
    save_thm("var_cases_thm", prove_cases_thm var_induction_thm)
val var_constructors_one_one =
    save_thm("var_constructors_one_one",prove_constructors_one_one var_Axiom)
val VAR_arg_DEF =
    new_recursive_definition{name = "VAR_arg_DEF", fixity = Prefix,
			     rec_axiom = var_Axiom,
			     def = (--`VAR_arg (VAR s) = s`--)}
val less_var_DEF = new_definition
("less_var_DEF",
 --`less_var l1 l2 = ltstring (VAR_arg l1) (VAR_arg l2)`--)

val var_ty = ==`:var`==


(* VALUE CONSTRUCTORS like nil, ::, true, false, ref
   con ::= CON string *)
val con_Axiom = define_type{name = "con_Axiom", fixities = [Prefix],
                            type_spec = `con = CON of string`}
val con_induction_thm =
    save_thm("con_induction_thm", prove_induction_thm con_Axiom)
val con_cases_thm =
    save_thm("con_cases_thm", prove_cases_thm con_induction_thm)
val con_constructors_one_one =
    save_thm("con_constructors_one_one", prove_constructors_one_one con_Axiom)
val con_ty = ==`:con`==


(* SPECIAL CONSTANTS -- like numbers or strings 
   scon ::= SCINT integer | SCSTR string *)
val scon_Axiom = define_type{name = "scon_Axiom", fixities = [Prefix,Prefix],
                             type_spec = `scon = SCINT of integer 
                                               | SCSTR of string`}
val scon_induction_thm =
    save_thm("scon_induction_thm", prove_induction_thm scon_Axiom)
val scon_cases_thm =
    save_thm("scon_cases_thm", prove_cases_thm scon_induction_thm)
val scon_constructors_one_one =
    save_thm("scon_constructors_one_one",prove_constructors_one_one scon_Axiom)
val scon_constructors_distinct =
    save_thm("scon_constructors_distinct",
	     prove_constructors_distinct scon_Axiom)
val scon_ty = ==`:scon`==

(* EXCEPTION CONSTRUCTORS
   excon ::= EXCON string *)
val excon_Axiom = define_type{name = "excon_Axiom",fixities = [Prefix],
                              type_spec = `excon = EXCON of string`}
val excon_induction_thm =
    save_thm("excon_induction_thm", prove_induction_thm excon_Axiom)
val excon_cases_thm =
    save_thm("excon_cases_thm", prove_cases_thm excon_induction_thm)
val excon_constructors_one_one =
    save_thm("excon_constructors_one_one",
	     prove_constructors_one_one excon_Axiom)
val EXCON_arg_DEF =
    new_recursive_definition{name = "EXCON_arg_DEF", fixity = Prefix,
			     rec_axiom = excon_Axiom,
			     def = (--`EXCON_arg (EXCON s) = s`--)}
val less_excon_DEF = new_definition
("less_excon_DEF",
 --`less_excon l1 l2 = ltstring (EXCON_arg l1) (EXCON_arg l2)`--)

val excon_ty = ==`:excon`==
    
(* record LABELS
   label ::= LABEL string *)
val label_Axiom = define_type{name = "label_Axiom", fixities = [Prefix],
                              type_spec = `label = LABEL of string`}
val label_induction_thm =
    save_thm("label_induction_thm", prove_induction_thm label_Axiom)
val label_cases_thm =
    save_thm("label_cases_thm", prove_cases_thm label_induction_thm)
val label_constructors_one_one =
    save_thm("label_constructors_one_one",
	     prove_constructors_one_one label_Axiom)
val LABEL_arg_DEF =
    new_recursive_definition{name = "LABEL_arg_DEF", fixity = Prefix,
			     rec_axiom = label_Axiom,
			     def = (--`LABEL_arg (LABEL s) = s`--)}
val less_label_DEF = new_definition
("less_label_DEF",
 --`less_label l1 l2 = ltstring (LABEL_arg l1) (LABEL_arg l2)`--)

val label_ty = ==`:label`==

(* definition for phrase type EXBIND
   exbind ::= EXBIND1 excon (exbind option) |
              EXBIND2 excon (excon long) (exbind option) *)

structure MLexbindInput  : NestedRecTypeInputSig =
struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "exbind",
  constructors =
      [{name = "EXBIND1",
	arg_info = [existing excon_ty,
		    type_op {Tyop = "option",
			     Args = [being_defined "exbind"]}]},
       {name = "EXBIND2",
	arg_info = [existing excon_ty,
		    existing (mk_long_ty excon_ty),
		    type_op {Tyop = "option",
			     Args = [being_defined "exbind"]}]}]}]
val recursor_thms = [theorem "more_list" "option_Axiom"]
val New_Ty_Existence_Thm_Name = "exbind_existence"
val New_Ty_Induct_Thm_Name = "exbind_induct"
val New_Ty_Uniqueness_Thm_Name = "exbind_unique"
val Constructors_Distinct_Thm_Name = "exbind_distinct"
val Constructors_One_One_Thm_Name = "exbind_one_one"
val Cases_Thm_Name = "exbind_cases"

end (* struct *)

structure exbind_def = NestedRecTypeFunc (MLexbindInput)

val exbind_ty = (==`:exbind`==);


(* definition for phrase types ATPAT, PATROW, PAT
   atpat ::= WILDCARDatpat | SCONatpat scon | VARatpat var |
             CONatpat (con long) | EXCONatpat (excon long) |
             RECORDatpat (patrow option) | PARatpat pat
   patrow ::= DOTDOTDOT | PATROW label pat (patrow option)
   pat ::= ATPATpat atpat | CONpat (con long) atpat |
           EXCONpat (excon long) atpat | LAYEREDpat var pat
   atexp ::= SCONatexp scon | VARatexp (var long) | CONatexp (con long) |
             EXCONatexp (excon long) | LETatexp dec exp | PARatexp exp |
             RECORDatexp (exprow option) *)

structure MLpatInput  : NestedRecTypeInputSig =

struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "atpat",
  constructors =
      [{name = "WILDCARDatpat", arg_info = []},
       {name = "SCONatpat", arg_info = [existing scon_ty]},
       {name = "VARatpat", arg_info = [existing var_ty]},
       {name = "CONatpat", arg_info = [existing (mk_long_ty con_ty)]},
       {name = "EXCONatpat", arg_info = [existing (mk_long_ty excon_ty)]},
       {name = "RECORDatpat",
	arg_info = [type_op {Tyop = "option",
                             Args = [being_defined "patrow"]}]},
       {name = "PARatpat", arg_info = [being_defined "pat"]}]},
 {type_name = "patrow",
  constructors =
      [{name = "DOTDOTDOT", arg_info = []},
       {name = "PATROW", 
	arg_info = [existing label_ty,
		    being_defined "pat",
		    type_op {Tyop = "option",
                             Args = [being_defined "patrow"]}]}]},
 {type_name = "pat",
  constructors =
      [{name = "ATPATpat", arg_info = [being_defined "atpat"]},
       {name = "CONpat", arg_info = [existing (mk_long_ty con_ty),
				     being_defined "atpat"]},
       {name = "EXCONpat", arg_info = [existing (mk_long_ty excon_ty),
				       being_defined "atpat"]},
       {name = "LAYEREDpat", arg_info = [existing var_ty,
					 being_defined "pat"]}]}]

    val recursor_thms = [theorem "more_list" "option_Axiom"]
    val New_Ty_Existence_Thm_Name = "pat_existence"
    val New_Ty_Induct_Thm_Name = "pat_induct"
    val New_Ty_Uniqueness_Thm_Name = "pat_unique"
    val Constructors_Distinct_Thm_Name = "pat_distinct"
    val Constructors_One_One_Thm_Name = "pat_one_one"
    val Cases_Thm_Name = "pat_cases"

end (* struct *)

val _ = Lib.say "\nDefining the pattern phrase types.\n";
structure PatDef = NestedRecTypeFunc (MLpatInput);
val _ = Lib.say "\nFinished defining pattern phrase types.\n";

val pat_ty = ==`:pat`==;

(* definitions for phrase types ATEXP, EXPROW, EXP, MATCH, MRULE, 
                                DEC, VALBIND
   exprow ::= EXPROW label exp (exprow option)
   exp ::= ATEXPexp atexp | APPexp exp atexp | HANDLEexp exp match |
           RAISEexp exp | FNexp match
   match ::= MATCH mrule (match option)
   mrule ::= MRULE pat exp
   dec ::= VALdec valbind | EXCEPTdec exbind | LOCALdec dec dec |
           OPENdec (strid long) nonemptylist | SEQdec dec dec | EMPTYdec
   valbind ::= PLAINvalbind pat exp (valbind option) |
               RECvalbind valbind *)

structure MLgramInput  : NestedRecTypeInputSig =
struct

structure DefTypeInfo = DefTypeInfo
open DefTypeInfo

val def_type_spec =
[{type_name = "atexp",
  constructors =
      [{name = "SCONatexp", arg_info = [existing scon_ty]},
       {name = "VARatexp", arg_info = [existing (mk_long_ty var_ty)]},
       {name = "CONatexp", arg_info = [existing (mk_long_ty con_ty)]},
       {name = "EXCONatexp", arg_info = [existing (mk_long_ty excon_ty)]},
       {name = "LETatexp", arg_info = [being_defined "dec",
				       being_defined "exp"]},
       {name = "PARatexp", arg_info = [being_defined "exp"]},
       {name = "RECORDatexp", 
	arg_info = [type_op {Tyop = "option",
                             Args = [being_defined "exprow"]}]}]},
 {type_name = "exprow",
  constructors =
      [{name = "EXPROW", 
	arg_info = [existing label_ty,
		    being_defined "exp",
		    type_op {Tyop = "option",
                             Args = [being_defined "exprow"]}]}]},
 {type_name = "exp",
  constructors =
      [{name = "ATEXPexp", arg_info = [being_defined "atexp"]},
       {name = "APPexp", arg_info = [being_defined "exp",
				     being_defined "atexp"]},
       {name = "HANDLEexp", arg_info = [being_defined "exp",
					being_defined "match"]},
       {name = "RAISEexp", arg_info = [being_defined "exp"]},
       {name = "FNexp", arg_info = [being_defined "match"]}]},
 {type_name = "match",
  constructors =
      [{name = "MATCH", 
	arg_info = [being_defined "mrule",
		    type_op {Tyop = "option",
                             Args = [being_defined "match"]}]}]},
 {type_name = "mrule",
  constructors =
      [{name = "MRULE", arg_info = [existing pat_ty,
				    being_defined "exp"]}]},
 {type_name = "dec",
  constructors = 
      [{name = "VALdec", arg_info = [being_defined "valbind"]},
       {name = "EXCEPTdec", arg_info = [existing exbind_ty]},
       {name = "LOCALdec", arg_info = [being_defined "dec",
				       being_defined "dec"]},
       {name = "OPENdec",
	arg_info = [existing (==`:(strid long) nonemptylist`==)]},
       {name = "SEQdec", arg_info = [being_defined "dec",
				     being_defined "dec"]},
       {name = "EMPTYdec", arg_info = []}]},
 {type_name = "valbind",
  constructors =
      [{name = "PLAINvalbind", 
	arg_info = [existing pat_ty,
		    being_defined "exp",
		    type_op {Tyop = "option",
                             Args = [being_defined "valbind"]}]},
       {name = "RECvalbind", arg_info = [being_defined "valbind"]}]}];

    val recursor_thms = [theorem "more_list" "option_Axiom"]
    val New_Ty_Existence_Thm_Name = "gram_existence"
    val New_Ty_Induct_Thm_Name = "gram_induct"
    val New_Ty_Uniqueness_Thm_Name = "gram_unique"
    val Constructors_Distinct_Thm_Name = "gram_distinct"
    val Constructors_One_One_Thm_Name = "gram_one_one"
    val Cases_Thm_Name = "gram_cases"
end (* struct *)

val _ = Lib.say "\nDefining the expression etc. phrase types.\n";
structure GramDef = NestedRecTypeFunc (MLgramInput);
val _ = Lib.say "\nFinished defining expression etc. phrase types.\n";

