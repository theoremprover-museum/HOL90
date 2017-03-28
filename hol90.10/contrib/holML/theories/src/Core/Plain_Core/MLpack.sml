(* File: MLpack.sml *)

(* the following types are to take care of evaluations that lead to 
    either a failure (for matches) or an exception packet *)

val pack_Axiom = define_type{name= "pack_Axiom", fixities = [Prefix],
			     type_spec = `pack = PACK of exval`};

val pack_induction_thm =
    save_thm("pack_induction_thm",prove_induction_thm pack_Axiom)
val pack_cases_thm =
    save_thm("pack_cases_thm", prove_cases_thm pack_induction_thm)
val pack_constructors_one_one =
    save_thm("pack_constructors_one_one",
	     prove_constructors_one_one pack_Axiom);

val PACK_arg_DEF =
    new_recursive_definition {name = "PACK_arg_DEF",
			      fixity = Prefix,
			      rec_axiom =  pack_Axiom,
			      def = (--`(PACK_arg (PACK ev) = ev)`--)};

val val_pack_Axiom =
    define_type{name= "val_pack_Axiom", fixities = [Prefix,Prefix],
		type_spec = `val_pack = VALvp of val
		                      | PACKvp of pack`};

val val_pack_induction_thm =
    save_thm("val_pack_induction_thm", prove_induction_thm val_pack_Axiom)
val val_pack_cases_thm =
    save_thm("val_pack_cases_thm", prove_cases_thm val_pack_induction_thm)
val val_pack_constructors_one_one =
    save_thm("val_pack_constructors_one_one",
    prove_constructors_one_one val_pack_Axiom)
val val_pack_constructors_distinct =
    save_thm("val_pack_constructors_distinct",
	     prove_constructors_distinct val_pack_Axiom);

val is_VALvp_DEF =
    new_recursive_definition {name = "is_VALvp_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_Axiom,
			      def = (--`(is_VALvp (VALvp v) = T) /\
				        (is_VALvp (PACKvp p) = F)`--)};

val is_PACKvp_DEF =
    new_recursive_definition {name = "is_PACKvp_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_Axiom,
			      def = (--`(is_PACKvp (PACKvp p) = T) /\
				        (is_PACKvp (VALvp v) = F)`--)};

val VALvp_arg_DEF =
    new_recursive_definition {name = "VALvp_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_Axiom,
			      def = (--`(VALvp_arg (VALvp v) = v)`--)};

val PACKvp_arg_DEF =
    new_recursive_definition {name = "PACKvp_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_Axiom,
			      def = (--`(PACKvp_arg (PACKvp v) = v)`--)};


val record_pack_Axiom =
    define_type{name= "record_pack_Axiom", fixities = [Prefix,Prefix],
		type_spec = `record_pack = RECORDrp of record
		                         | PACKrp of pack`}

val record_pack_induction_thm =
    save_thm("record_pack_induction_thm",
	     prove_induction_thm record_pack_Axiom)
val record_pack_cases_thm =
    save_thm("record_pack_cases_thm",
	     prove_cases_thm record_pack_induction_thm)
val record_pack_constructors_one_one =
    save_thm("record_pack_constructors_one_one",
	     prove_constructors_one_one record_pack_Axiom)
val record_pack_constructors_distinct =
    save_thm("record_pack_constructors_distinct",
	     prove_constructors_distinct record_pack_Axiom);

val is_RECORDrp_DEF =
    new_recursive_definition {name = "is_RECORDrp_DEF",
			      fixity = Prefix,
			      rec_axiom = record_pack_Axiom,
			      def = (--`(is_RECORDrp (RECORDrp r) = T) /\
				        (is_RECORDrp (PACKrp p) = F)`--)};

val RECORDrp_arg_DEF =
    new_recursive_definition {name = "RECORDrp_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = record_pack_Axiom,
			      def = (--`(RECORDrp_arg (RECORDrp r) = r)`--)};

val PACKrp_arg_DEF =
    new_recursive_definition {name = "PACKrp_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = record_pack_Axiom,
			      def = (--`(PACKrp_arg (PACKrp p) = p)`--)};

val val_pack_fail_Axiom =
    define_type{name= "val_pack_fail_Axiom",
		fixities = [Prefix,Prefix,Prefix],
		type_spec = `val_pack_fail = VALvpf of val
		                           | PACKvpf of pack
					   | FAILvpf`};

val val_pack_fail_induction_thm =
    save_thm("val_pack_fail_induction_thm",
	     prove_induction_thm val_pack_fail_Axiom)
val val_pack_fail_cases_thm =
    save_thm("val_pack_fail_cases_thm",
	     prove_cases_thm val_pack_fail_induction_thm)
val val_pack_fail_constructors_one_one =
    save_thm("val_pack_fail_constructors_one_one",
	     prove_constructors_one_one val_pack_fail_Axiom)
val val_pack_fail_constructors_distinct =
    save_thm("val_pack_fail_constructors_distinct",
	     prove_constructors_distinct val_pack_fail_Axiom);

val is_VALvpf_DEF =
    new_recursive_definition {name = "is_VALvpf_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_fail_Axiom,
			      def = (--`(is_VALvpf (VALvpf v) = T) /\
				        (is_VALvpf (PACKvpf p) = F) /\
					(is_VALvpf FAILvpf = F)`--)};

val is_PACKvpf_DEF =
    new_recursive_definition {name = "is_PACKvpf_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_fail_Axiom,
			      def = (--`(is_PACKvpf (VALvpf v) = F) /\
				        (is_PACKvpf (PACKvpf p) = T) /\
					(is_PACKvpf FAILvpf = F)`--)};

val VALvpf_arg_DEF =
    new_recursive_definition {name = "VALvpf_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_fail_Axiom,
			      def = (--`VALvpf_arg (VALvpf v) = v`--)};

val PACKvpf_arg_DEF =
    new_recursive_definition {name = "PACKvpf_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = val_pack_fail_Axiom,
			      def = (--`PACKvpf_arg (PACKvpf p) = p`--)};

val env_pack_Axiom =
    define_type{name= "env_pack_Axiom", fixities = [Prefix,Prefix],
		type_spec = `env_pack = ENVep of env
                                      | PACKep of pack`};

val env_pack_induction_thm =
    save_thm("env_pack_induction_thm", prove_induction_thm env_pack_Axiom)
val env_pack_cases_thm =
    save_thm("env_pack_cases_thm", prove_cases_thm env_pack_induction_thm)
val env_pack_constructors_one_one =
    save_thm("env_pack_constructors_one_one",
	     prove_constructors_one_one env_pack_Axiom)
val env_pack_constructors_distinct =
    save_thm("env_pack_constructors_distinct",
	     prove_constructors_distinct env_pack_Axiom);

val is_ENVep_DEF =
    new_recursive_definition {name = "is_ENVep_DEF",
			      fixity = Prefix,
			      rec_axiom = env_pack_Axiom,
			      def = (--`(is_ENVep (ENVep e) = T) /\
				        (is_ENVep (PACKep p) = F)`--)};

val ENVep_arg_DEF =
    new_recursive_definition {name = "ENVep_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = env_pack_Axiom,
			      def = (--`ENVep_arg (ENVep e) = e`--)};

val PACKep_arg_DEF =
    new_recursive_definition {name = "PACKep_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = env_pack_Axiom,
			      def = (--`PACKep_arg (PACKep p) = p`--) };

val varenv_pack_Axiom =
    define_type{name= "varenv_pack_Axiom", fixities = [Prefix,Prefix],
		type_spec = `varenv_pack = VARENVvep of varenv
		                         | PACKvep of pack`};

val varenv_pack_induction_thm =
    save_thm("varenv_pack_induction_thm",
	     prove_induction_thm varenv_pack_Axiom)
val varenv_pack_cases_thm =
    save_thm("varenv_pack_cases_thm",
	     prove_cases_thm varenv_pack_induction_thm)
val varenv_pack_constructors_one_one =
    save_thm("varenv_pack_constructors_one_one",
	     prove_constructors_one_one varenv_pack_Axiom)
val varenv_pack_constructors_distinct =
    save_thm("varenv_pack_constructors_distinct",
	     prove_constructors_distinct varenv_pack_Axiom);

val is_VARENVvep_DEF =
    new_recursive_definition {name = "is_VARENVvep_DEF",
			      fixity = Prefix,
			      rec_axiom = varenv_pack_Axiom,
			      def = (--`(is_VARENVvep (VARENVvep ve) = T) /\
				        (is_VARENVvep (PACKvep p) = F)`--)};

val VARENVvep_arg_DEF =
    new_recursive_definition {name = "VARENVvep_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = varenv_pack_Axiom,
			      def = (--`VARENVvep_arg (VARENVvep ve) = ve`--)};

val PACKvep_arg_DEF =
    new_recursive_definition {name = "PACKvep_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = varenv_pack_Axiom,
			      def = (--`PACKvep_arg (PACKvep ve) = ve`--)};

val exconenv_pack_Axiom =
    define_type{name= "exconenv_pack_Axiom", fixities = [Prefix,Prefix],
		type_spec = `exconenv_pack = EXCONENVeep of exconenv
		                           | PACKeep of pack`};

val exconenv_pack_induction_thm =
    save_thm("exconenv_pack_induction_thm",
	     prove_induction_thm exconenv_pack_Axiom)
val exconenv_pack_cases_thm =
    save_thm("exconenv_pack_cases_thm",
	     prove_cases_thm exconenv_pack_induction_thm)
val exconenv_pack_constructors_one_one =
    save_thm("exconenv_pack_constructors_one_one",
	     prove_constructors_one_one exconenv_pack_Axiom)
val exconenv_pack_constructors_distinct =
    save_thm("exconenv_pack_constructors_distinct",
	     prove_constructors_distinct exconenv_pack_Axiom);

val is_EXCONENVeep_DEF =
    new_recursive_definition {name = "is_EXCONENVeep_DEF",
			      fixity = Prefix,
			      rec_axiom = exconenv_pack_Axiom,
			      def =(--`(is_EXCONENVeep (EXCONENVeep ee) = T) /\
				       (is_EXCONENVeep (PACKeep p) = F)`--)};

val EXCONENVeep_arg_DEF =
    new_recursive_definition {name = "EXCONENVeep_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = exconenv_pack_Axiom,
			      def = (--`EXCONENVeep_arg (EXCONENVeep ee)
				        = ee`--)};

val PACKeep_arg_DEF =
    new_recursive_definition {name = "PACKeep_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = exconenv_pack_Axiom,
			      def = (--`PACKeep_arg (PACKeep ee) = ee`--)};

val varenv_fail_Axiom =
    define_type{name= "varenv_fail_Axiom", fixities = [Prefix,Prefix],
		    type_spec = `varenv_fail = VARENVvef of varenv
		                             | FAILvef`};

val varenv_fail_induction_thm =
    save_thm("varenv_fail_induction_thm",
	     prove_induction_thm varenv_fail_Axiom)
val varenv_fail_cases_thm =
    save_thm("varenv_fail_cases_thm",
	     prove_cases_thm varenv_fail_induction_thm)
val varenv_fail_constructors_one_one =
    save_thm("varenv_fail_constructors_one_one",
	     prove_constructors_one_one varenv_fail_Axiom)
val varenv_fail_constructors_distinct =
    save_thm("varenv_fail_constructors_distinct",
	     prove_constructors_distinct varenv_fail_Axiom);

val is_VARENVvef_DEF =
    new_recursive_definition {name = "is_VARENVvef_DEF",
			      fixity = Prefix,
			      rec_axiom = varenv_fail_Axiom,
			      def = (--`(is_VARENVvef (VARENVvef ve) = T) /\
				        (is_VARENVvef FAILvef = F)`--)};

val is_FAILvef_DEF =
    new_recursive_definition {name = "is_FAILvef_DEF",
			      fixity = Prefix,
			      rec_axiom = varenv_fail_Axiom,
			      def = (--`(is_FAILvef FAILvef = T) /\
				        (is_FAILvef (VARENVvef ve) = F)`--)};

val VARENVvef_arg_DEF = new_recursive_definition {name = "VARENVvef_arg_DEF",
			      fixity = Prefix,
			      rec_axiom = varenv_fail_Axiom,
			      def = (--`VARENVvef_arg (VARENVvef ve) = ve`--)};


