(* File: ModML/semantic_object_functions.sml *)

(* Description: This file contains functions that operate on the 
   compound semantic objects used in the dynamic semantics of the 
   ML Module system.  *)

(* References: The "Definition", Sections 4.3 and 7.2 *)



(* projection functions *)


val intenv_of_int_DEF =
    define_mutual_functions
    {name = "intenv_of_int_DEF", fixities = NONE,
     rec_axiom = ModMLInterfaces_rec_thm,
     def = (--`intenv_of_int (BASICint intenv vars excons) = intenv`--)};

val vars_of_int_DEF =
    define_mutual_functions
    {name = "vars_of_int_DEF", fixities = NONE,
     rec_axiom = ModMLInterfaces_rec_thm,
     def = (--`vars_of_int (BASICint intenv vars excons) = vars`--)};

val excons_of_int_DEF =
    define_mutual_functions
    {name = "excons_of_int_DEF", fixities = NONE,
     rec_axiom = ModMLInterfaces_rec_thm,
     def = (--`excons_of_int (BASICint intenv vars excons) = excons`--)};

val env_of_basis_DEF =
    define_mutual_functions 
    {name = "env_of_basis_DEF", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`env_of_basis (BASIS funenv sigenv env) = env`--)};

val INTENV_arg_DEF =
    define_mutual_functions
    {name = "INTENV_arg_DEF", fixities = NONE,
     rec_axiom = ModMLInterfaces_rec_thm,
     def = (--`INTENV_arg (INTENV il) = il`--)};

val FUNENV_arg_DEF =
    define_mutual_functions
    {name = "FUNENV_arg_DEF", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`FUNENV_arg (FUNENV f) = f`--)};

val SIGENV_arv_DEF = new_recursive_definition
     {name = "SIGENV_arv_DEF",
      fixity = Prefix,
      rec_axiom = sigenv_Axiom,
      def = (--`SIGENV_arg (SIGENV s) = s`--)};

(* empty objects *)

val empty_env_DEF = new_definition
        ("empty_env_DEF",
         (--`empty_env = (ENV empty_strenv empty_varenv empty_exconenv)`--));

val empty_intenv_DEF = new_definition
        ("empty_intenv_DEF",
         (--`empty_intenv = INTENV empty_finmap`--));

val empty_int_DEF = new_definition
        ("empty_int_DEF",
         (--`empty_int = (BASICint empty_intenv {} {})`--));

val empty_sigenv_DEF = new_definition
        ("empty_sigenv_DEF",
         (--`empty_sigenv = SIGENV (\x.undefined)`--));

val empty_funenv_DEF = new_definition
        ("empty_funenv_DEF",
         (--`empty_funenv = FUNENV (empty_finmap)`--));

(* insertion functions *)

val insert_into_funenv_DEF =
    define_mutual_functions
    {name = "insert_into_funenv_DEF", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`insert_into_funenv (FUNENV fl) =
              \funid fcl.FUNENV (finmap_insert less_funid funid fcl fl)`--)};


val insert_into_intenv_DEF =
    define_mutual_functions
    {name = "insert_into_intenv_DEF", fixities = NONE,
     rec_axiom = ModMLInterfaces_rec_thm,
     def = (--`insert_into_intenv (INTENV il) =
              \strid int.INTENV (finmap_insert less_strid strid int il)`--)};


val insert_into_sigenv_DEF = new_recursive_definition
     {name = "insert_into_sigenv",
      fixity = Prefix,
      rec_axiom = sigenv_Axiom,
      def = (--`insert_into_sigenv (SIGENV l) sigid i =
                SIGENV (\x. ((x = sigid) => lift i | l x))`--)};


(* one-element objects *)

val funenv_map_DEF = new_definition
        ("funenv_map_DEF",
         (--`funenv_map fi fc = FUNENV (FINMAP[(fi, fc)])`--));

val intenv_map_DEF = new_definition
        ("intenv_map_DEF",
         (--`intenv_map si i = INTENV (FINMAP[(si, i)])`--));

val sigenv_map_DEF = new_definition
        ("sigenv_map_DEF",
         (--`sigenv_map si i =
	  SIGENV (\x.((x = si) => lift i | undefined))`--));

val strenv_map_DEF = new_definition
        ("strenv_map_DEF",
         (--`strenv_map si e = STRENV (FINMAP[(si, e)])`--));

(* union and addition functions *)


val add_funenv_DEF = new_definition
("add_funenv_DEF",
 (--`add_funenv fe1 fe2 =
     FUNENV(finmap_modify less_funid (FUNENV_arg fe1) (FUNENV_arg fe2))`--));


val add_sigenv_DEF = new_definition
("add_sigenv_DEF",
 (--`add_sigenv s1 s2 = 
  SIGENV(\x. (((SIGENV_arg s1) x = undefined) => (SIGENV_arg s2) x
	     | (SIGENV_arg s1) x))`--));


val add_basis_aux_DEF = define_mutual_functions
    {name = "add_basis_aux_DEF", fixities = NONE,
     rec_axiom =  ModMLBases_rec_thm,
     def = (--`add_basis_aux (BASIS f2 s2 e2) =
     \f1 s1 e1. 
         BASIS (add_funenv f1 f2) (add_sigenv s1 s2) (add_env e1 e2)`--)};

val add_basis_DEF = define_mutual_functions
    {name = "add_basis_DEF", fixities = NONE,
     rec_axiom =  ModMLBases_rec_thm,
     def = (--`add_basis (BASIS f s e) = \b. add_basis_aux b f s e`--)};

val add_intenv_DEF = new_definition
("add_intenv_DEF",
 (--`add_intenv ie1 ie2 =
     INTENV(finmap_modify less_strid (INTENV_arg ie1) (INTENV_arg ie2))`--));

val add_int_aux_DEF = define_mutual_functions
    {name = "add_int_aux_DEF", fixities = NONE,
     rec_axiom =  ModMLInterfaces_rec_thm,
     def = (--`add_int_aux (BASICint i2 v2 e2) =
     \i1 v1 e1. 
         BASICint (add_intenv i1 i2) (v1 UNION v2) (e1 UNION e2)`--)};

val add_int_DEF = define_mutual_functions
    {name = "add_int_DEF", fixities = NONE,
     rec_axiom = ModMLInterfaces_rec_thm,
     def = (--`add_int (BASICint i v e) = \int. add_int_aux int i v e`--)};

val add_env_to_basis_DEF =  define_mutual_functions
    {name = "add_env_to_basis_DEF", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`add_env_to_basis (BASIS f s e) = 
               \e'. BASIS f s (add_env e e')`--)};

val add_funenv_to_basis_DEF =  define_mutual_functions
    {name = "add_funenv_to_basis_DEF", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`add_funenv_to_basis (BASIS f1 s1 e1) = 
     \f. BASIS (add_funenv f1 f) s1 e1`--)};

val add_sigenv_to_intbasis_DEF = new_recursive_definition
 {name = "add_sigenv_to_intbasis_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_Axiom,
  def =
(--`add_sigenv_to_intbasis (INTBASIS s i) s'
              = INTBASIS (add_sigenv s s') i`--)};

val add_intenv_to_intbasis_DEF = new_recursive_definition
 {name = "add_intenv_to_intbasis_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_Axiom,
  def =
(--`add_intenv_to_intbasis (INTBASIS s i) i'
              = INTBASIS s (add_intenv i i')`--)};

(* injection functions *)

val strenv_in_env_DEF = new_definition
 ("strenv_in_env_DEF",
  (--`strenv_in_env s = ENV s empty_varenv empty_exconenv`--));

val vars_in_int_DEF = new_definition
 ("vars_in_int_DEF",
  (--`vars_in_int x = BASICint empty_intenv x {}`--));

val excons_in_int_DEF = new_definition
 ("excons_in_int_DEF",
  (--`excons_in_int x = BASICint empty_intenv {} x`--));

val intenv_in_int_DEF = new_definition
 ("intenv_in_int_DEF",
  (--`intenv_in_int x = BASICint x {} {}`--));

val env_in_basis_DEF = new_definition
 ("env_in_basis_DEF",
  (--`env_in_basis e = BASIS empty_funenv empty_sigenv e`--));

val strenv_in_basis_DEF = new_definition
 ("strenv_in_basis_DEF",
  (--`strenv_in_basis s =  env_in_basis (strenv_in_env s)`--));

val sigenv_in_basis_DEF = new_definition
 ("sigenv_in_basis_DEF",
  (--`sigenv_in_basis s = BASIS empty_funenv s empty_env`--));

val funenv_in_basis_DEF = new_definition
 ("funenv_in_basis_DEF",
  (--`funenv_in_basis f = BASIS f empty_sigenv empty_env`--));

(* lookup functions *)

val lookup_longstrid_basis_DEF = define_mutual_functions
    {name = "define_mutual_functions", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`lookup_longstrid_basis (BASIS f s e) = 
      \ls. lookuplongstrid_env e ls`--)};

val lookup_strid_int_DEF = define_mutual_functions
    {name = "lookup_strid_int_DEF", fixities = NONE,
     rec_axiom = ModMLInterfaces_rec_thm,
     def = (--`(lookup_strid_int (BASICint ie v e) = 
                \strid. lookup_strid_intenv ie strid)/\
               (lookup_strid_intenv (INTENV il) =
		(\id. finmap_lookup id il))`--)};

val lookup_longstrid_intenv_DEF = 
     new_recursive_definition
    {name = "lookup_longstrid_intenv_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = (--`(lookup_longstrid_intenv i (BASE s) =
                  lookup_strid_intenv i s) /\
	       (lookup_longstrid_intenv i (QUALIFIED strid ls) =
		(lookup_strid_intenv i strid = undefined => undefined
		  |lookup_longstrid_intenv
		   (intenv_of_int
                      (lower(lookup_strid_intenv i strid))) ls))`--)};

val lookup_longstrid_intbasis_DEF = new_recursive_definition
 {name = "lookup_longstrid_intbasis_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_Axiom,
  def = (--`lookup_longstrid_intbasis (INTBASIS s i) ls =
            lookup_longstrid_intenv i ls`--)};

val lookup_funid_funenv_DEF = define_mutual_functions
    {name = "lookup_funid_funenv_DEF", fixities = NONE,
     rec_axiom =  ModMLBases_rec_thm,
     def = (--`(lookup_funid_funenv (FUNENV fl) =
		\funid.finmap_lookup funid fl)`--)};

val lookup_funid_basis_DEF = define_mutual_functions
    {name = "lookup_funid_basis_DEF", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`(lookup_funid_basis (BASIS f s e) = 
     \funid.lookup_funid_funenv f funid)`--)};

val lookup_sigid_sigenv_DEF = new_recursive_definition
 {name = "lookup_sigid_sigenv_DEF",
  fixity = Prefix,
  rec_axiom = sigenv_Axiom,
  def = (--`lookup_sigid_sigenv (SIGENV l) sigid = l sigid`--)};


val lookup_sigid_intbasis_DEF = new_recursive_definition
 {name = "lookup_sigid_intbasis_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_Axiom,
  def =
(--`lookup_sigid_intbasis (INTBASIS sigenv intenv) sigid =
    lookup_sigid_sigenv sigenv sigid`--)};

(* extracting interfaces *)

val Inter_DEF = define_mutual_functions
    {name = "Inter_DEF", fixities = NONE,
     rec_axiom = env_existence,
     def =(--`(Inter (ENV strenv varenv exconenv) =
		(BASICint (intenv_from_strenv strenv)
                          (vars_from_varenv varenv)
                          (excons_from_exconenv exconenv))) /\
	       (intenv_from_strenv (STRENV se) =
		INTENV(intenv_from_strenv_finmap se)) /\
	       (intenv_from_strenv_finmap (FINMAP fl) =
		FINMAP(intenv_from_strenv_list fl)) /\
	       (intenv_from_strenv_list [] = []) /\
	       (intenv_from_strenv_list (CONS s l) =
		CONS (intenv_from_strenv_pair s)(intenv_from_strenv_list l)) /\
	       (intenv_from_strenv_pair (strid,env) = (strid,Inter env))`--)};


val Inter_basis_DEF = define_mutual_functions
    {name = "Inter_basis_DEF", fixities = NONE,
     rec_axiom = ModMLBases_rec_thm,
     def = (--`Inter_basis (BASIS funenv sigenv env) = 
             INTBASIS sigenv (intenv_of_int (Inter env))`--)};


(* cutting down the environment *)

val cut_env_DEF = define_mutual_functions
    {name = "cut_env_DEF", fixities = NONE,
     rec_axiom = env_existence,
     def = (--`(cut_env (ENV strenv varenv exconenv) = 
                \int. ENV (cut_strenv strenv (intenv_of_int int))
                          (cut_varenv varenv (vars_of_int int))
                          (cut_exconenv exconenv (excons_of_int int))) /\
               (cut_strenv (STRENV se) =
                \intenv. STRENV (cut_strenv_finmap se intenv)) /\
               (cut_strenv_finmap (FINMAP fl) =
                \intenv. FINMAP (cut_strenv_list fl intenv)) /\
	       (cut_strenv_list [] = \intenv.[]) /\
	       (cut_strenv_list (CONS s l) = 
		\intenv. ((cut_strenv_pair s intenv = undefined)
			  => cut_strenv_list l intenv
			    | CONS (lower (cut_strenv_pair s intenv))
			           (cut_strenv_list l intenv))) /\
	       (cut_strenv_pair (strid,env) =
                \intenv. ((lookup_strid_intenv intenv strid = undefined)
			  => undefined
			    | lift(strid,
				   cut_env env
				   (lower(lookup_strid_intenv
					  intenv strid)))))`--)};


