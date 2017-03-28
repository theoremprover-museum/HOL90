(* File: MLval_args.sml *)

(* Below we define functions on terms that are components of
   environments: the predicates that test for constructors and the
   functions to extract the args from the constructors. If, for the
   latter functions the constructor is not the one we are trying to
   extract an arg from, we'll return an arbitrary element of that type
   using Hilbert choice *)

val is_ASSGval_DEF = define_mutual_functions
    {rec_axiom = env_existence, fixities = NONE, name = "is_ASSGval_DEF",
     def = (--`(is_ASSGval ASSGval = T) /\ (is_ASSGval allelse = F)`--)};

val is_SVALval_DEF = define_mutual_functions
    {name = "is_SVALval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_SVALval (SVALval sv) = T) /\ (is_SVALval allelse = F)`--)};

val is_BASval_DEF = define_mutual_functions
    {name = "is_BASval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_BASval (BASval bv) = T) /\ (is_BASval allelse = F)`--)};

val is_CONval_DEF = define_mutual_functions
    {name = "is_CONval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_CONval (CONval c) = T) /\ (is_CONval allelse = F)`--)};

val is_APPCONval_DEF = define_mutual_functions
    {name = "is_APPCONval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_APPCONval (APPCONval c v) = T) /\
	    (is_APPCONval allelse = F)`--)};

val is_EXVALval_DEF = define_mutual_functions
    {name = "is_EXVALval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_EXVALval (EXVALval ev) = T) /\
	    (is_EXVALval allelse = F)`--)};

val is_RECORDval_DEF = define_mutual_functions
    {name = "is_RECORDval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_RECORDval (RECORDval r) = T) /\
	    (is_RECORDval allelse = F)`--)};

val is_ADDRval_DEF = define_mutual_functions
    {name = "is_ADDRval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_ADDRval (ADDRval a) = T) /\ (is_ADDRval allelse = F)`--)};

val is_CLOSUREval_DEF = define_mutual_functions
    {name = "is_CLOSUREval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_CLOSUREval (CLOSUREval cl) = T) /\
	    (is_CLOSUREval allelse = F)`--)};

val is_NAMEexval_DEF = define_mutual_functions
    {name = "is_NAMEexval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_NAMEexval (NAMEexval n) = T) /\
	    (is_NAMEexval (NAMEVALexval n v) = F)`--)};

val is_NAMEVALexval_DEF = define_mutual_functions
    {name = "is_NAMEVALexval_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(is_NAMEVALexval (NAMEexval n) = F) /\
	    (is_NAMEVALexval (NAMEVALexval n v) = T)`--)};
     
val RECORD_arg_DEF = define_mutual_functions
    {name = "RECORD_arg_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`RECORD_arg (RECORD f) = f`--}

val SVALval_arg_DEF = define_mutual_functions
    {name = "SVALval_arg_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`(SVALval_arg (SVALval s) = s) /\
              (SVALval_arg allelse = @x:sval.T)`--}

val ENV_arg1_DEF = define_mutual_functions
    {name = "ENV_arg1_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`(ENV_arg1 (ENV se ve ee) = se) /\
              (ENV_arg1 allelse = @x:strenv.T)`--}

val ENV_arg2_DEF = define_mutual_functions
    {name = "ENV_arg2_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`(ENV_arg2 (ENV se ve ee) = ve) /\
              (ENV_arg2 allelse = @x:varenv.T)`--}

val ENV_arg3_DEF = define_mutual_functions
    {name = "ENV_arg3_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`(ENV_arg3 (ENV se ve ee) = ee) /\
              (ENV_arg3 allelse = @x:exconenv.T)`--}

val VARENV_arg_DEF = define_mutual_functions
    {name = "VARENV_arg_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`VARENV_arg (VARENV f) = f`--}

val CLOSURE_arg1_DEF = define_mutual_functions
    {name = "CLOSURE_arg1_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`CLOSURE_arg1 (CLOSURE m e ve) = m`--}

val CLOSURE_arg2_DEF = define_mutual_functions
    {name = "CLOSURE_arg2_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`CLOSURE_arg2 (CLOSURE m e ve) = e`--}

val CLOSURE_arg3_DEF = define_mutual_functions
    {name = "CLOSURE_arg3_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`CLOSURE_arg3 (CLOSURE m e ve) = ve`--}

val CLOSUREval_arg_DEF = define_mutual_functions
    {name = "CLOSUREval_arg_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`(CLOSUREval_arg (CLOSUREval c) = c) /\
              (CLOSUREval_arg allelse = @x:closure.T) `--}

val STRENV_arg_DEF = define_mutual_functions
    {name = "STRENV_arg_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`STRENV_arg (STRENV f) = f`--}

(* some additional functions of records... *)
val label_in_rec_DEF = define_mutual_functions
    {name = "label_in_rec_DEF", rec_axiom = env_existence, fixities = NONE,
     def = --`label_in_rec (RECORD f) = \l. in_dom f l`--}

val label_in_rec_lemma = store_thm
("label_in_rec_lemma",
 --`!f l. label_in_rec (RECORD f) l = in_dom f l`--,
 define_mut_rewrite_TAC [label_in_rec_DEF]);

(* don't think we need this anymore
val remove_field_DEF = define_mutual_functions
    {name = "remove_field_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`(remove_field NONErec = \l. NONErec) /\
	    (remove_field (SOMErec l1 v r) = \l. (l1 = l) => r | 
		SOMErec l1 v (remove_field r l))`--)};

val remove_field_lemma = store_thm("remove_field_lemma",
(--`(!l.remove_field NONErec l = NONErec) /\
      (!l l1 v r. remove_field (SOMErec l1 v r) l =
       ((l1 = l) => r | SOMErec l1 v (remove_field r l)))`--),
define_mut_rewrite_TAC [remove_field_DEF]);
*)

val lookup_label_DEF = define_mutual_functions 
    {name = "lookup_label_DEF", rec_axiom = env_existence, fixities = NONE,
     def = --`lookup_label (RECORD f) = \l. finmap_lookup l f`--}

val lookup_label_lemma = store_thm
("lookup_label_lemma",
  --`!f l.lookup_label (RECORD f) l = finmap_lookup l f`--,
  define_mut_rewrite_TAC [lookup_label_DEF]);

val empty_record_DEF = new_definition
("empty_record_DEF", --`empty_record = RECORD empty_finmap`--)

(* We put the smallest first with insert_into_record *)
val insert_into_record_DEF = define_mutual_functions
    {name = "insert_into_record_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`insert_into_record (RECORD f) =
                  \l v. RECORD (finmap_insert less_label l v f)`--}

val insert_into_record_lemma = store_thm
("insert_into_record_lemma",
 --`!f l v. insert_into_record (RECORD f) l v = 
            RECORD (finmap_insert less_label l v f)`--,
 define_mut_rewrite_TAC [insert_into_record_DEF]);

(* rec1 + rec2 from the book corresponds here to add_record rec1 rec2 *)
val add_record_DEF = new_definition
("add_record_DEF",
 --`add_record rec1 rec2 = 
     RECORD (finmap_modify less_label (RECORD_arg rec1) (RECORD_arg rec2))`--);

(* rewrite replaces LABEL "1" = LABEL "1" with T, but not
   LABEL "1" = LABEL "2" with F, and we need this for lookup_label *)
val LABEL_11 = save_thm ("LABEL_11",
			 prove_constructors_one_one label_Axiom);

(* field1_val and field2_val are appied to record values. They are
   designed to extract the values of the fields
   with labels "1" and "2". intfield1 assumes that the field with label
   "1" is a special value containing an integer and returns that integer,
   similarly for intfield2 (with label "2" used instead of label "1")
   and strfield1 and strfield2 *)

val field1_val_DEF = define_mutual_functions
    {name = "field1_val_DEF", rec_axiom = env_existence, fixities = NONE,
     def = --`(field1_val (RECORDval r) = 
                      lower (lookup_label r (LABEL "1"))) /\
              (field1_val allelse = @x:val.T)`--}

val field2_val_DEF = define_mutual_functions
    {name = "field2_val_DEF", rec_axiom = env_existence, fixities = NONE,
     def = --`(field2_val (RECORDval r) = 
                      lower (lookup_label r (LABEL "2"))) /\
	      (field2_val allelse = @x:val.T)`--}

val intfield1_DEF = new_definition
("intfield1_DEF",
 --`intfield1 v = SVINT_arg (SVALval_arg (field1_val v))`--)

val intfield2_DEF = new_definition
("intfield2_DEF",
 --`intfield2 v = SVINT_arg (SVALval_arg (field2_val v))`--)

val strfield1_DEF = new_definition
("strfield1_DEF",
 --`strfield1 v = SVSTR_arg (SVALval_arg (field1_val v))`--)

val strfield2_DEF = new_definition
("strfield2_DEF",
 --`strfield2 v = SVSTR_arg (SVALval_arg (field2_val v))`--)


(* environment functions *)
val lookupstrid_DEF = define_mutual_functions
    {name = "lookupstrid_DEF", rec_axiom = env_existence, fixities = NONE,
     def = --`(lookupstrid_env (ENV se ve ee) = lookupstrid_strenv se) /\
       (lookupstrid_strenv (STRENV f) = \strid. finmap_lookup strid f)`--};

val lookupstrid_lemma = store_thm
("lookupstrid_lemma",
 --`(!se ve ee. lookupstrid_env (ENV se ve ee) = lookupstrid_strenv se) /\
    (!f strid. lookupstrid_strenv (STRENV f) strid = finmap_lookup strid f)`--,
 define_mut_rewrite_TAC [ETA_AX, lookupstrid_DEF]);

val lookuplongstrid_env_DEF = new_recursive_definition
    {name = "lookuplongstrid_env_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = --`(lookuplongstrid_env E (BASE s) =
                lookupstrid_strenv (ENV_arg1 E) s) /\
	      (lookuplongstrid_env E (QUALIFIED strid ls) =
	       (lookupstrid_strenv (ENV_arg1 E) strid = undefined
                => undefined
		 | lookuplongstrid_env
		   (lower(lookupstrid_strenv (ENV_arg1 E) strid)) ls))`--};

val lookupvar_DEF = define_mutual_functions
    {name = "lookupvar_DEF", rec_axiom = env_existence, fixities = NONE,
     def = --`(lookupvar_env (ENV se ve ee) = lookupvar_varenv ve) /\
       (lookupvar_varenv (VARENV f) = \v. finmap_lookup v f)`--};

val lookupvar_lemma = store_thm
("lookupvar_lemma",
 --`(!se ve ee.lookupvar_env (ENV se ve ee) = lookupvar_varenv ve) /\
    (!f v.lookupvar_varenv (VARENV f) v = finmap_lookup v f)`--,
 define_mut_rewrite_TAC [lookupvar_DEF]);

val lookupexcon_DEF = define_mutual_functions
    {name = "lookupexcon_DEF", rec_axiom = env_existence, fixities = NONE,
     def = --`(lookupexcon_env (ENV se ve ee) = lookupexcon_exconenv ee)`--};

val lookuplongvar_env_DEF =
    new_recursive_definition
    {name = "lookuplongvar_env_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = --`(lookuplongvar_env E (BASE v) =
		lookupvar_varenv (ENV_arg2 E) v) /\
	      (lookuplongvar_env E (QUALIFIED strid lv) =
		(lookupstrid_strenv (ENV_arg1 E) strid = undefined 
                 => undefined
		  | lookuplongvar_env
		    (lower(lookupstrid_strenv (ENV_arg1 E) strid)) lv))`--};

val lookuplongexcon_env_DEF =
    new_recursive_definition
    {name = "lookuplongexcon_env_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = --`(lookuplongexcon_env E (BASE ex) =
	        lookupexcon_exconenv (ENV_arg3 E) ex) /\
	      (lookuplongexcon_env E (QUALIFIED strid lex) =
	       (lookupstrid_strenv (ENV_arg1 E) strid = undefined
		=> undefined
		 | lookuplongexcon_env
		  (lower (lookupstrid_strenv (ENV_arg1 E) strid)) lex))`--};


val empty_varenv_DEF = new_definition
("empty_varenv_DEF", --`empty_varenv = VARENV empty_finmap`--)

(* We put the pair with the smallest var id first with insert_into_varenv. *)
val insert_into_varenv_DEF = define_mutual_functions
    {name = "insert_into_varenv_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`insert_into_varenv (VARENV f) =
                \var val. VARENV (finmap_insert less_var var val f)`--};

(* add_varenv VE1 VE2 implements VE1 + VE2, that is, VE1 modified by VE2.
   It puts the things in VE2 overwriting things in VE1 so the bindings in VE2
   will be used instead of the ones in VE1 if they have common variables.
   add_exconenv EE1 EE2 similarly implements EE1 + EE2 and
   add_strenv SE1 SE2 implements SE1 + SE2. *)

val add_varenv_DEF = new_definition
("add_varenv_DEF", --`add_varenv VE1 VE2 = 
 VARENV (finmap_modify less_var (VARENV_arg VE1) (VARENV_arg VE2))`--);

val empty_strenv_DEF = new_definition
("empty_strenv_DEF", --`empty_strenv = STRENV empty_finmap`--)

(* We put the pair with the smallest strid first with insert_into_strenv. *)
val insert_into_strenv_DEF = define_mutual_functions
    {name = "insert_into_strenv_DEF", rec_axiom = env_existence,
     fixities = NONE,
     def = --`insert_into_strenv (STRENV f) =
                \strid env. STRENV (finmap_insert less_strid strid env f)`--};

val insert_into_strenv_lemma = store_thm
("insert_into_strenv_lemma",
 --`!f s e. insert_into_strenv (STRENV f) s e =
            STRENV (finmap_insert less_strid s e f)`--,
 define_mut_rewrite_TAC [insert_into_strenv_DEF]);

val add_strenv_DEF = new_definition
("add_strenv_DEF",
 --`add_strenv SE1 SE2 = 
    STRENV (finmap_modify less_strid (STRENV_arg SE1) (STRENV_arg SE2))`--);

val add_env_DEF = define_mutual_functions
    {name = "add_env_DEF", rec_axiom = env_existence,  fixities = NONE,
     def = --`add_env (ENV se ve ee) = \e. ENV (add_strenv se (ENV_arg1 e))
                                     (add_varenv ve (ENV_arg2 e))
	                             (add_exconenv ee (ENV_arg3 e))`--};

(* this function does: add_nonemptylist_env [E1, E2, ... , EN-1, EN] = 
                       E1 + (E2 ... + (EN-1 + EN))   *)
val add_nonemptylist_env_DEF = new_recursive_definition 
    {name = "add_nonemptylist_env_DEF",
     fixity = Prefix,
     rec_axiom = nonemptylist_Axiom,
     def = (--`(add_nonemptylist_env (ONE E) = E) /\
	       (add_nonemptylist_env (MORE E Es) =
		  add_env E (add_nonemptylist_env Es))`--)};

(* rec_varenv does what Rec on pg 49 does. It uses a helper function
   rec_helper whose type is (var # val) list -> varenv -> (var # val) list.
   The (var # val) list is the list that represents the (pieces of) the 
   varenv we're operating on, and the varenv is the entire varenv (that
   will be placed as the third component in closures). *)
val rec_helper_DEF = new_recursive_definition
    {name = "rec_helper_DEF", fixity = Prefix, rec_axiom = list_Axiom,
     def = --`(rec_helper NIL VE = NIL) /\
              (rec_helper (CONS (h:var#val) t) VE =
	       (is_CLOSUREval (SND h) =>
		   (CONS 
		    ((FST h),
		     (CLOSUREval (CLOSURE 
				  (CLOSURE_arg1 (CLOSUREval_arg (SND h)))
				  (CLOSURE_arg2 (CLOSUREval_arg (SND h)))
				  VE)))
		    (rec_helper t VE)) |
		    CONS h (rec_helper t VE)))`--}
         

val rec_varenv_DEF = new_definition
("rec_varenv_DEF",
 --`rec_varenv VE = VARENV 
     (FINMAP (rec_helper (FINMAP_arg (VARENV_arg VE)) VE))`--)

(* gathering the variables from the variable environment *)

val vars_from_varenv_DEF = define_mutual_functions
    {name = "vars_from_varenv_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`vars_from_varenv (VARENV ve) = finmap_dom ve`--)};

val cut_varenv_DEF = define_mutual_functions
    {name = "cut_varenv_DEF", rec_axiom = env_existence, fixities = NONE,
     def = (--`cut_varenv (VARENV ve) =
	       \vars.VARENV (restrict_finmap ve vars)`--)};
