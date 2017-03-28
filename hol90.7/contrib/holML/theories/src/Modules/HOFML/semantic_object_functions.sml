(* File: HOFML/semantic_object_functions.sml *)

(* argument functions *)

val STRENV_H_arg_DEF = define_mutual_functions
{name = "STRENV_H_arg_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`STRENV_H_arg (STRENV_H fe) = fe`--)};

val FUNENV_H_arg_DEF = define_mutual_functions
{name = "FUNENV_H_arg_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`FUNENV_H_arg (FUNENV_H se) = se`--)};

val SIGENV_H_arg_DEF = new_recursive_definition
{name = "SIGENV_H_arg_DEF",
 fixity = Prefix, rec_axiom = sigenv_h_Axiom,
 def = (--`SIGENV_H_arg (SIGENV_H se) = se`--)};

val STRINTENV_H_arg_DEF = define_mutual_functions
{name = "STRINTENV_H_arg_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`STRINTENV_H_arg (STRINTENV_H sie) = sie`--)};

val FUNINTENV_H_arg_DEF = define_mutual_functions
{name = "FUNINTENV_H_arg_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`FUNINTENV_H_arg (FUNINTENV_H fe) = fe`--)};

(* projection functions *)

val funenv_h_of_env_h_DEF = define_mutual_functions
{name = "funenv_h_of_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`funenv_h_of_env_h (ENV_H fe se ve ee) = fe`--)};

val strenv_h_of_env_h_DEF = define_mutual_functions
{name = "strenv_h_of_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`strenv_h_of_env_h (ENV_H fe se ve ee) = se`--)};

val varenv_of_env_h_DEF = define_mutual_functions
{name = "varenv_of_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`varenv_of_env_h (ENV_H fe se ve ee) = ve`--)};

val exconenv_of_env_h_DEF = define_mutual_functions
{name = "exconenv_of_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`exconenv_of_env_h (ENV_H fe se ve ee) = ee`--)};

val sigenv_h_of_basis_h_DEF = define_mutual_functions
{name = "sigenv_h_of_basis_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`sigenv_h_of_basis_h (BASIS_H sigenv_h env_h) = sigenv_h`--)};

val env_h_of_basis_h_DEF = define_mutual_functions
{name = "env_h_of_basis_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`env_h_of_basis_h (BASIS_H sigenv_h env_h) = env_h`--)};

val funintenv_h_of_int_h_DEF = define_mutual_functions
{name = "funintenv_h_of_int_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`funintenv_h_of_int_h (INT_H funintenv_h strintenv_h vars excons) = 
                            funintenv_h`--)};

val strintenv_h_of_int_h_DEF = define_mutual_functions
{name = "strintenv_h_of_int_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`strintenv_h_of_int_h (INT_H funintenv_h strintenv_h vars excons) = 
                            strintenv_h`--)};

val vars_of_int_h_DEF = define_mutual_functions
{name = "vars_of_int_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`vars_of_int_h (INT_H funintenv_h strintenv_h vars excons) = vars`--)};

val excons_of_int_h_DEF = define_mutual_functions
{name = "excons_of_int_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`excons_of_int_h (INT_H funintenv_h strintenv_h vars excons) = excons`--)};

val funintenv_h_of_intbasis_h_DEF = 
     new_recursive_definition
    {name = "funintenv_h_of_intbasis_h_DEF",
     fixity = Prefix,
     rec_axiom = intbasis_h_Axiom,
     def = (--`funintenv_h_of_intbasis_h (INTBASIS_H si st f) = f`--)};

val sigenv_h_of_intbasis_h_DEF = 
     new_recursive_definition
    {name = "sigenv_h_of_intbasis_h_DEF",
     fixity = Prefix,
     rec_axiom = intbasis_h_Axiom,
     def = (--`sigenv_h_of_intbasis_h (INTBASIS_H si st f) = si`--)};

val strintenv_h_of_intbasis_h_DEF = 
     new_recursive_definition
    {name = "strintenv_h_of_intbasis_h_DEF",
     fixity = Prefix,
     rec_axiom = intbasis_h_Axiom,
     def = (--`strintenv_h_of_intbasis_h (INTBASIS_H si st f) = st`--)};


(* empty objects *)

val empty_sigenv_h_DEF = new_definition
        ("empty_sigenv_h_DEF",
         (--`empty_sigenv_h = SIGENV_H (\x.undefined)`--));

val empty_strenv_h_DEF = new_definition
        ("empty_strenv_h_DEF",
         (--`empty_strenv_h = STRENV_H empty_finmap`--));

val empty_funenv_h_DEF = new_definition
        ("empty_funenv_h_DEF",
         (--`empty_funenv_h = FUNENV_H empty_finmap`--));

val empty_env_h_DEF = new_definition
    ("empty_env_h_DEF",
     (--`empty_env_h = 
      (ENV_H empty_funenv_h empty_strenv_h empty_varenv empty_exconenv)`--));

val empty_strintenv_h_DEF = new_definition
        ("empty_strintenv_h_DEF",
         (--`empty_strintenv_h = STRINTENV_H empty_finmap`--));

val empty_funintenv_h_DEF = new_definition
    ("empty_funintenv_h_DEF",
     (--`empty_funintenv_h = FUNINTENV_H empty_finmap`--));

val empty_int_h_DEF = new_definition
    ("empty_int_h_DEF",
     (--`empty_int_h = INT_H empty_funintenv_h empty_strintenv_h {} {}`--));

(* insertion functions *)

val insert_into_funenv_h_DEF = define_mutual_functions
{name = "insert_into_funenv_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`insert_into_funenv_h (FUNENV_H fe) =
	\funid fcl.FUNENV_H (finmap_insert less_funid funid fcl fe)`--)};


val insert_into_strenv_h_DEF = define_mutual_functions
{name = "insert_into_strenv_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`insert_into_strenv_h (STRENV_H se) =
        \strid e.STRENV_H (finmap_insert less_strid strid e se)`--)};


val insert_into_strintenv_h_DEF = define_mutual_functions
{name = "insert_into_strintenv_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`insert_into_strintenv_h (STRINTENV_H si) =
     \strid int_h.STRINTENV_H (finmap_insert less_strid strid int_h si)`--)};

val insert_into_funintenv_h_DEF = define_mutual_functions
{name = "insert_into_funintenv_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`insert_into_funintenv_h (FUNINTENV_H fi) =
     \funid int_h.FUNINTENV_H (finmap_insert less_funid funid int_h fi)`--)};

val insert_into_sigenv_h_DEF = new_recursive_definition
{name = "insert_into_sigenv_h_DEF",
 fixity = Prefix, rec_axiom = sigenv_h_Axiom,
 def = (--`insert_into_sigenv_h (SIGENV_H se) sigid int_h =
	   SIGENV_H (\x. ((x = sigid) => lift int_h | se x))`--)};


(* one-element objects *)

val funenv_h_map_DEF = new_definition
        ("funenv_h_map_DEF",
         (--`funenv_h_map fi fc = FUNENV_H (FINMAP[(fi, fc)])`--));

val funintenv_h_map_DEF = new_definition
        ("funintenv_h_map_DEF",
         (--`funintenv_h_map fi i = FUNINTENV_H (FINMAP[(fi, i)])`--));

val strintenv_h_map_DEF = new_definition
        ("strintenv_h_map_DEF",
         (--`strintenv_h_map si i = STRINTENV_H (FINMAP[(si, i)])`--));

val sigenv_h_map_DEF = new_definition
        ("sigenv_h_map_DEF",
         (--`sigenv_h_map si i =
	     SIGENV_H (\x.((x = si) => lift i | undefined))`--));

val strenv_h_map_DEF = new_definition
        ("strenv_h_map_DEF",
         (--`strenv_h_map si e = STRENV_H (FINMAP[(si, e)])`--));

(* union and addition functions *)

val add_funenv_h_DEF = new_definition("add_funenv_h_DEF",
(--`add_funenv_h fe1 fe2 =
     FUNENV_H(finmap_modify less_funid
	      (FUNENV_H_arg fe1) (FUNENV_H_arg fe2))`--));

val add_strenv_h_DEF = new_definition("add_strenv_h_DEF",
(--`add_strenv_h se1 se2 =
 STRENV_H(finmap_modify less_strid
	  (STRENV_H_arg se1) (STRENV_H_arg se2))`--));

val add_sigenv_h_DEF = new_definition
("add_sigenv_DEF",
 (--`add_sigenv_h s1 s2 = 
  SIGENV_H(\x. (((SIGENV_H_arg s1) x = undefined) => (SIGENV_H_arg s2) x
	     | (SIGENV_H_arg s1) x))`--));

val add_env_h_DEF = define_mutual_functions
{name = "add_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
def = (--`add_env_h (ENV_H fe se ve ee) = 
       \E. ENV_H (add_funenv_h fe (funenv_h_of_env_h E))
                 (add_strenv_h se (strenv_h_of_env_h E))
                 (add_varenv ve (varenv_of_env_h E))
                 (add_exconenv ee (exconenv_of_env_h E))`--)};

val add_basis_h_DEF = define_mutual_functions
{name = "add_basis_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`add_basis_h (BASIS_H s e) = 
      \B. BASIS_H (add_sigenv_h s (sigenv_h_of_basis_h B))
                  (add_env_h e (env_h_of_basis_h B))`--)};

val add_strintenv_h_DEF = new_definition("add_strintenv_h_DEF",
(--`add_strintenv_h SIE1 SIE2 =
 STRINTENV_H(finmap_modify less_strid
	     (STRINTENV_H_arg SIE2) (STRINTENV_H_arg SIE1))`--));


val add_funintenv_h_DEF = new_definition("add_funintenv_h_DEF",
(--`add_funintenv_h int_h int_h' = 
 FUNINTENV_H(finmap_modify less_funid
	     (FUNINTENV_H_arg int_h) (FUNINTENV_H_arg int_h'))`--));


val add_int_h_DEF = define_mutual_functions
{name = "add_int_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`add_int_h (INT_H fie sie v e) = 
       \int_h. INT_H (add_funintenv_h fie (funintenv_h_of_int_h int_h))
                     (add_strintenv_h sie (strintenv_h_of_int_h int_h))
                     (v UNION (vars_of_int_h int_h))
                     (e UNION (excons_of_int_h int_h))`--)};


val add_env_h_to_basis_h_DEF = new_definition
 ("add_env_h_to_basis_h_DEF",
  (--`add_env_h_to_basis_h b e = 
      BASIS_H (sigenv_h_of_basis_h b)
              (add_env_h (env_h_of_basis_h b) e)`--));

val add_funenv_h_to_env_h_DEF = new_definition
 ("add_funenv_h_to_env_h_DEF",
  (--`add_funenv_h_to_env_h e f = 
      ENV_H (add_funenv_h (funenv_h_of_env_h e) f)
            (strenv_h_of_env_h e)
            (varenv_of_env_h e)
            (exconenv_of_env_h e)`--));

val add_funenv_h_to_basis_h_DEF = new_definition
 ("add_funenv_h_to_basis_h_DEF",
  (--`add_funenv_h_to_basis_h b f = 
      BASIS_H (sigenv_h_of_basis_h b)
              (add_funenv_h_to_env_h (env_h_of_basis_h b) f)`--));

val add_funintenv_h_to_intbasis_h_DEF = new_recursive_definition
 {name = "add_funintenv_h_to_intbasis_h_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_h_Axiom,
  def =
(--`add_funintenv_h_to_intbasis_h (INTBASIS_H s i f) f'
              = INTBASIS_H s i (add_funintenv_h f f')`--)};

val add_sigenv_h_to_intbasis_h_DEF = new_recursive_definition
 {name = "add_sigenv_h_to_intbasis_h_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_h_Axiom,
  def =
(--`add_sigenv_h_to_intbasis_h (INTBASIS_H s i f) s'
              = INTBASIS_H (add_sigenv_h s s') i f`--)};

val add_strintenv_h_to_intbasis_h_DEF = new_recursive_definition
 {name = "add_strintenv_h_to_intbasis_h_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_h_Axiom,
  def =
(--`add_strintenv_h_to_intbasis_h (INTBASIS_H s sie f) sie'
              = INTBASIS_H s (add_strintenv_h sie sie') f`--)};

(* injection functions *)
 
val strenv_h_in_env_h_DEF = new_definition
    ("strenv_h_in_env_h_DEF",
     (--`strenv_h_in_env_h s = 
      ENV_H empty_funenv_h s empty_varenv empty_exconenv`--));

val funenv_h_in_env_h_DEF = new_definition
    ("funenv_h_in_env_h_DEF",
     (--`funenv_h_in_env_h f = 
      ENV_H f empty_strenv_h empty_varenv empty_exconenv`--));

val vars_in_int_h_DEF = new_definition
    ("vars_in_int_h_DEF",
     (--`vars_in_int_h x =
      INT_H empty_funintenv_h empty_strintenv_h x {}`--));

val excons_in_int_h_DEF = new_definition
    ("excons_in_int_h_DEF",
     (--`excons_in_int_h x =
      INT_H empty_funintenv_h empty_strintenv_h {} x`--));

val funintenv_h_in_int_h_DEF = new_definition
    ("funintenv_h_in_int_h_DEF",
     (--`funintenv_h_in_int_h x = INT_H x empty_strintenv_h {} {}`--));

val strintenv_h_in_int_h_DEF = new_definition
    ("strintenv_h_in_int_h_DEF",
     (--`strintenv_h_in_int_h x = INT_H empty_funintenv_h x {} {}`--));

val env_h_in_basis_h_DEF = new_definition
    ("env_h_in_basis_h_DEF",
     (--`env_h_in_basis_h e = BASIS_H (SIGENV_H (\x.undefined)) e`--));

val strenv_h_in_basis_h_DEF = new_definition
    ("strenv_h_in_basis_h_DEF",
     (--`strenv_h_in_basis_h s =  env_h_in_basis_h (strenv_h_in_env_h s)`--));

val sigenv_h_in_basis_h_DEF = new_definition
    ("sigenv_h_in_basis_h_DEF",
     (--`sigenv_h_in_basis_h s = BASIS_H s empty_env_h`--));

val funenv_h_in_basis_h_DEF = new_definition
    ("funenv_h_in_basis_h_DEF",
     (--`funenv_h_in_basis_h f =
      BASIS_H (SIGENV_H (\x.undefined)) (funenv_h_in_env_h f)`--));

(* lookup functions *)

val lookupstrid_env_h_DEF = define_mutual_functions
{name = "lookupstrid_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
  def = (--`(lookupstrid_env_h (ENV_H fe se ve ee) = 
                     \strid. lookupstrid_strenv_h se strid)/\
       (lookupstrid_strenv_h (STRENV_H s) =
        \strid. finmap_lookup strid s)`--)};

val lookuplongstrid_env_h_DEF =
     new_recursive_definition
    {name = "lookuplongstrid_env_h_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def =
   (--`(lookuplongstrid_env_h E (BASE s) =
        lookupstrid_strenv_h (strenv_h_of_env_h E) s) /\
       (lookuplongstrid_env_h E (QUALIFIED strid ls) =
        ((lookupstrid_strenv_h (strenv_h_of_env_h E) strid = undefined) 
          => undefined
          |lookuplongstrid_env_h
           (lower(lookupstrid_strenv_h
		  (strenv_h_of_env_h E) strid)) ls))`--)};

val lookupvar_env_h_DEF = define_mutual_functions
{name = "lookupvar_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
  def = (--`lookupvar_env_h (ENV_H fe se ve ee) =
            \v. lookupvar_varenv ve v`--)};

val lookupexcon_env_h_DEF = define_mutual_functions
{name = "lookupexcon_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
  def = (--`lookupexcon_env_h (ENV_H fe se ve ee) =
            \ec. lookupexcon_exconenv ee ec`--)};

val lookuplongvar_env_h_DEF =
    new_recursive_definition
    {name = "lookuplongvar_env_h_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = 
(--`(lookuplongvar_env_h E (BASE v) =
     lookupvar_varenv (varenv_of_env_h E) v) /\
    (lookuplongvar_env_h E (QUALIFIED strid lv) =
     ((lookupstrid_strenv_h (strenv_h_of_env_h E) strid = undefined)
      => undefined
       |lookuplongvar_env_h
        (lower(lookupstrid_strenv_h (strenv_h_of_env_h E) strid)) lv))`--)};

val lookuplongexcon_env_h_DEF =
    new_recursive_definition
    {name = "lookuplongexcon_env_h_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = 
(--`(lookuplongexcon_env_h E (BASE ex) =
     lookupexcon_exconenv (exconenv_of_env_h E) ex) /\
    (lookuplongexcon_env_h E (QUALIFIED strid lex) =
     ((lookupstrid_strenv_h (strenv_h_of_env_h E) strid = undefined)
      => undefined
       |lookuplongexcon_env_h
        (lower (lookupstrid_strenv_h (strenv_h_of_env_h E) strid)) lex))`--)};


val lookup_longstrid_basis_h_DEF = define_mutual_functions
{name = "lookup_longstrid_basis_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`lookup_longstrid_basis_h (BASIS_H s e) = 
      \ls. lookuplongstrid_env_h e ls`--)};

val lookup_strid_int_h_DEF= define_mutual_functions
{name = "lookup_strid_int_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
  def = (--`(lookup_strid_int_h (INT_H fie sie v e) = 
          \strid. lookup_strid_strintenv_h sie strid) /\
       (lookup_strid_strintenv_h (STRINTENV_H si) = 
	\strid. finmap_lookup strid si)`--)};


val lookup_longstrid_strintenv_h_DEF = 
     new_recursive_definition
    {name = "lookup_longstrid_strintenv_h_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = (--`(lookup_longstrid_strintenv_h i (BASE s) =
                  lookup_strid_strintenv_h i s) /\
	       (lookup_longstrid_strintenv_h i (QUALIFIED strid ls) =
		((lookup_strid_strintenv_h i strid = undefined) => undefined
		  | lookup_longstrid_strintenv_h
		   (strintenv_h_of_int_h
                      (lower(lookup_strid_strintenv_h i strid))) ls))`--)};

val lookup_longstrid_intbasis_h_DEF = new_recursive_definition
 {name = "lookup_longstrid_intbasis_h_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_h_Axiom,
  def = (--`lookup_longstrid_intbasis_h (INTBASIS_H s i f) ls =
            lookup_longstrid_strintenv_h i ls`--)};

val lookup_funid_funenv_h_DEF = define_mutual_functions
{name = "lookup_funid_funenv_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`(lookup_funid_funenv_h (FUNENV_H fe) =
      \funid. finmap_lookup funid fe)`--)};


val lookup_funid_funintenv_h_DEF =
define_mutual_functions
{name = "lookup_funid_funintenv_h_DEF",
 fixities = NONE, rec_axiom = HOFMLInterfaces_rec_thm,
 def = (--`(lookup_funid_funintenv_h (FUNINTENV_H fi) =
      \funid. finmap_lookup funid fi)`--)};


val lookup_longfunid_int_h_DEF = 
    new_recursive_definition
    {name = "lookup_longfunid_int_h_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def =
(--`(lookup_longfunid_int_h i (BASE funid) =
     lookup_funid_funintenv_h (funintenv_h_of_int_h i) funid) /\
    (lookup_longfunid_int_h i (QUALIFIED strid lf) =
     ((lookup_strid_strintenv_h (strintenv_h_of_int_h i) strid = undefined)
       => undefined
       | lookup_longfunid_int_h
            (lower (lookup_strid_strintenv_h 
                      (strintenv_h_of_int_h i) strid))
            lf))`--)};

val lookup_longfunid_intbasis_h_DEF = 
    new_recursive_definition
    {name = "lookup_longfunid_intbasis_h_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def =
(--`(lookup_longfunid_intbasis_h IB (BASE funid) =
     lookup_funid_funintenv_h (funintenv_h_of_intbasis_h IB) funid) /\
    (lookup_longfunid_intbasis_h IB (QUALIFIED strid lf) =
     ((lookup_strid_strintenv_h (strintenv_h_of_intbasis_h IB) strid =
       undefined)
       => undefined
       | lookup_longfunid_int_h
            (lower (lookup_strid_strintenv_h 
                      (strintenv_h_of_intbasis_h IB) strid))
            lf))`--)};

val lookup_funid_env_h_DEF = define_mutual_functions
{name = "lookup_funid_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`lookup_funid_env_h (ENV_H fe se ve ee) =
     \funid. lookup_funid_funenv_h fe funid`--)}; 

val lookup_longfunid_env_h_DEF =
    new_recursive_definition
    {name = "lookup_longfunid_env_h_DEF",
     fixity = Prefix,
     rec_axiom = long_Axiom,
     def = 
(--`(lookup_longfunid_env_h E (BASE funid) =
     lookup_funid_funenv_h (funenv_h_of_env_h E) funid) /\
    (lookup_longfunid_env_h E (QUALIFIED strid lf) =
     ((lookupstrid_strenv_h (strenv_h_of_env_h E) strid = undefined) 
       => undefined
       |lookup_longfunid_env_h
        (lower(lookupstrid_strenv_h (strenv_h_of_env_h E) strid)) lf))`--)};

val lookup_longfunid_basis_h_DEF = define_mutual_functions
{name = "lookup_longfunid_basis_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`(lookup_longfunid_basis_h (BASIS_H s e) = 
       \funid.lookup_longfunid_env_h e funid)`--)};


val lookup_sigid_sigenv_h_DEF = new_recursive_definition
 {name = "lookup_sigid_sigenv_h_DEF",
  fixity = Prefix,
  rec_axiom = sigenv_h_Axiom,
  def = 
(--`lookup_sigid_sigenv_h (SIGENV_H l) sigid = l sigid`--)}


val lookup_sigid_intbasis_h_DEF = new_recursive_definition
 {name = "lookup_sigid_intbasis_h_DEF",
  fixity = Prefix,
  rec_axiom = intbasis_h_Axiom,
  def =
(--`lookup_sigid_intbasis_h (INTBASIS_H si st f) sigid =
    lookup_sigid_sigenv_h si sigid`--)};

(* extracting interfaces *)

(* Now we have to define a function that extracts an interface from
   a structure expression.  This requires us to define functions
   to extract interfaces (or interface components) from several 
   other phrase classes that are used in building structure expressions. *)

val Inter_exbind_DEF = define_mutual_functions
 {name = "Inter_exbind_DEF",
  fixities = NONE,
  rec_axiom = exbind_existence,
  def =
(--`(Inter_exbind (EXBIND1 excon exbind_option) =
     {excon} UNION (Inter_exbind_option exbind_option)) /\
    (Inter_exbind (EXBIND2 excon longexcon exbind_option)  =
        {excon} UNION (Inter_exbind_option exbind_option)) /\
    (Inter_exbind_option NONE = {}) /\
    (Inter_exbind_option (SOME exbind) = Inter_exbind exbind)`--)};


val Inter_pat_DEF = define_mutual_functions
{name = "Inter_pat_DEF",
 fixities = NONE, rec_axiom = pat_existence,
 def = (--`(Inter_pat (ATPATpat atpat) = Inter_atpat atpat) /\

    (Inter_pat (CONpat longcon atpat) = Inter_atpat atpat) /\

    (Inter_pat (EXCONpat longexcon atpat) = Inter_atpat atpat) /\

    (Inter_pat (LAYEREDpat var pat) = {var} UNION (Inter_pat pat)) /\

    (Inter_atpat WILDCARDatpat = {}) /\

    (Inter_atpat (SCONatpat scon) = {}) /\

    (Inter_atpat (VARatpat var) = {var}) /\

    (Inter_atpat (CONatpat x) = {}) /\

    (Inter_atpat (EXCONatpat y) = {}) /\

    (Inter_atpat (RECORDatpat patrow_option) =
     Inter_patrow_option patrow_option) /\

    (Inter_atpat (PARatpat pat) = Inter_pat pat) /\

    (Inter_patrow DOTDOTDOT = {}) /\

    (Inter_patrow (PATROW label pat patrow_option) =
     (Inter_pat pat) UNION (Inter_patrow_option patrow_option)) /\

    (Inter_patrow_option NONE  = {}) /\

    (Inter_patrow_option (SOME patrow) = Inter_patrow patrow)`--)};


(* I really don't know if Inter_dec, etc are correct.  In fact I'm pretty sure
   that one particular clause (which I've marked) is wrong *)

val Inter_dec_DEF = define_mutual_functions
{name = "Inter_dec_DEF",
 fixities = NONE, rec_axiom = gram_existence,
 def = (--`(Inter_dec (VALdec valbind) = 
      \IB. vars_in_int_h (Inter_valbind valbind)) /\

    (Inter_dec (EXCEPTdec exbind) =
      \IB. excons_in_int_h (Inter_exbind exbind)) /\

    (Inter_dec (LOCALdec dec dec') = \IB. Inter_dec dec' IB) /\

    (Inter_dec (OPENdec l) =
      \IB. nonempty_FOLDL_WITH_INIT 
               add_int_h
               (nonempty_MAP
		 lower
		 (nonempty_MAP (lookup_longstrid_intbasis_h IB) l))) /\

    (Inter_dec (SEQdec dec dec') =
      \IB. add_int_h (Inter_dec dec IB) (Inter_dec dec' IB)) /\

    (Inter_dec EMPTYdec = \IB.empty_int_h) /\

    (Inter_valbind (PLAINvalbind pat exp valbind_option) =
       (Inter_pat pat) UNION (Inter_valbind_option valbind_option)) /\

     (* I believe this clause is wrong *)
     (* I believe it is right - Elsa *)
    (Inter_valbind (RECvalbind valbind) = Inter_valbind valbind) /\

    (Inter_valbind_option NONE = {}) /\

    (Inter_valbind_option (SOME valbind) = Inter_valbind valbind)`--)};


(* Now comes a group of functions that behave exactly like a corresponding
   group of evaluation relations:
      Inter_valdesc <-> eval_valdesc
      Inter_exdesc <-> eval_exdesc
      Inter_sigexp_h <-> eval_sigexp_h
      Inter_spec_h <-> eval_spec_h
      Inter_strdesc_h <-> eval_strdesc_h

   I haven't tried to exploit this correspondence since I think the 
   presentation of the semantics is cleaner (and closer to the Definition)
   if I don't.  Plus I don't know exactly how I would make use of the 
   correspondence.  *)


val Inter_valdesc_DEF = define_mutual_functions
 {name = "Inter_valdesc_DEF",
  fixities = NONE,
  rec_axiom = valdesc_rec_thm,
  def =
  (--`(Inter_valdesc (VARvaldesc var valdesc_option) =
       {var} UNION (Inter_valdesc_option valdesc_option)) /\
     (Inter_valdesc_option NONE = {}) /\
     (Inter_valdesc_option (SOME valdesc) = Inter_valdesc valdesc)`--)};

val Inter_exdesc_DEF = define_mutual_functions
 {name = "Inter_exdesc_DEF",
  fixities = NONE,
  rec_axiom = exdesc_rec_thm,
  def =
(--`(Inter_exdesc (EXCONexdesc excon exdesc_option) =
     {excon} UNION (Inter_exdesc_option exdesc_option)) /\
    (Inter_exdesc_option NONE = {}) /\
    (Inter_exdesc_option (SOME exdesc) = Inter_exdesc exdesc)`--)};


val Inter_sigexp_h_DEF = define_mutual_functions
{name = "Inter_sigexp_h_DEF",
 fixities = NONE, rec_axiom = HOFMLSignatures_rec_thm,
 def =
(--`(Inter_sigexp_h (SIGsigexp_h spec_h) = \IB. Inter_spec_h spec_h IB) /\

    (Inter_sigexp_h (SIGIDsigexp_h sigid) = 
       \IB. lower (lookup_sigid_intbasis_h IB sigid)) /\

    (Inter_spec_h (VALspec_h valdesc) =
       \IB. vars_in_int_h (Inter_valdesc valdesc)) /\

    (Inter_spec_h (EXCEPTIONspec_h exdesc) =
       \IB. excons_in_int_h (Inter_exdesc exdesc)) /\

    (Inter_spec_h (STRUCTUREspec_h strdesc) =
       \IB. strintenv_h_in_int_h (Inter_strdesc_h strdesc IB)) /\

    (Inter_spec_h (LOCALspec_h spec_h spec_h') =
       \IB. Inter_spec_h 
               spec_h'
               (add_funintenv_h_to_intbasis_h 
                   (add_strintenv_h_to_intbasis_h
                       IB
                       (strintenv_h_of_int_h (Inter_spec_h spec_h IB)))
                   (funintenv_h_of_int_h (Inter_spec_h spec_h IB)))) /\

    (Inter_spec_h (OPENspec_h l) =
       \IB. nonempty_FOLDL_WITH_INIT
               add_int_h
               (nonempty_MAP
                 lower
                 (nonempty_MAP (lookup_longstrid_intbasis_h IB) l))) /\

    (Inter_spec_h (INCLUDEspec_h l') =
       \IB. nonempty_FOLDL_WITH_INIT
               add_int_h
               (nonempty_MAP
                 lower
                 (nonempty_MAP (lookup_sigid_intbasis_h IB) l'))) /\

    (Inter_spec_h EMPTYspec_h = \IB. empty_int_h) /\

    (Inter_spec_h (SEQspec_h spec_h spec_h') =
       \IB. add_int_h
               (Inter_spec_h spec_h IB)
               (Inter_spec_h 
                  spec_h'
                  (add_funintenv_h_to_intbasis_h 
                     (add_strintenv_h_to_intbasis_h
                       IB
                       (strintenv_h_of_int_h (Inter_spec_h spec_h IB)))
                     (funintenv_h_of_int_h (Inter_spec_h spec_h IB))))) /\

    (Inter_spec_h (FUNCTORspec_h funid strid sigexp_h sigexp_h') =
       \IB. funintenv_h_in_int_h
               (funintenv_h_map 
                  funid
                  (Inter_sigexp_h 
                     sigexp_h'
                     (add_strintenv_h_to_intbasis_h
                        IB
                        (strintenv_h_map
			   strid
			   (Inter_sigexp_h sigexp_h IB)))))) /\

   (Inter_strdesc_h (STRIDstrdesc_h strid sigexp strdesc_h_option) =
       \IB. add_strintenv_h
               (strintenv_h_map strid (Inter_sigexp_h sigexp IB))
               (Inter_strdesc_h_option strdesc_h_option IB)) /\
   (Inter_strdesc_h_option NONE = \IB. empty_strintenv_h) /\
   (Inter_strdesc_h_option (SOME strdesc_h) = Inter_strdesc_h strdesc_h)`--)};



val Inter_strexp_h_DEF = define_mutual_functions
{name = "Inter_strexp_h_DEF",
 fixities = NONE, rec_axiom = HOFMLStructures_rec_thm,
 def = (--`(Inter_strexp_h (STRUCTstrexp_h moddec) = 
       \IB. Inter_moddec_h moddec IB) /\

    (Inter_strexp_h (LONGSTRIDstrexp_h longstrid) = 
       \IB. lower (lookup_longstrid_intbasis_h IB longstrid)) /\

    (Inter_strexp_h (APPstrexp_h longfunid strexp_h) =
       \IB. lower (lookup_longfunid_intbasis_h IB longfunid)) /\

    (Inter_strexp_h (LETstrexp_h moddec_h strexp_h) =
       \IB. Inter_strexp_h 
               strexp_h 
               (add_funintenv_h_to_intbasis_h
                   (add_strintenv_h_to_intbasis_h
                       IB
                       (strintenv_h_of_int_h
                           (Inter_moddec_h moddec_h IB)))
                   (funintenv_h_of_int_h
                       (Inter_moddec_h moddec_h IB)))) /\

    (Inter_moddec_h (DECmoddec_h dec) = \IB. Inter_dec dec IB) /\

    (Inter_moddec_h (STRUCTUREmoddec_h strbind) =
       \IB. strintenv_h_in_int_h (Inter_strbind_h strbind IB)) /\

    (Inter_moddec_h (LOCALmoddec_h moddec_h moddec_h') =
       \IB. Inter_moddec_h 
               moddec_h'
               (add_funintenv_h_to_intbasis_h
                   (add_strintenv_h_to_intbasis_h
                       IB
                       (strintenv_h_of_int_h
                           (Inter_moddec_h moddec_h IB)))
                   (funintenv_h_of_int_h
                       (Inter_moddec_h moddec_h IB)))) /\

    (Inter_moddec_h (OPENmoddec_h l) =
       \IB. nonempty_FOLDL_WITH_INIT 
               add_int_h
               (nonempty_MAP
		 lower
		 (nonempty_MAP (lookup_longstrid_intbasis_h IB) l))) /\

    (Inter_moddec_h EMPTYmoddec_h = \IB. empty_int_h) /\

    (Inter_moddec_h (SEQmoddec_h moddec_h moddec_h') =
       \IB. add_int_h
            (Inter_moddec_h moddec_h IB)
            (Inter_moddec_h 
               moddec_h'
               (add_funintenv_h_to_intbasis_h
                   (add_strintenv_h_to_intbasis_h
                       IB
                       (strintenv_h_of_int_h
                           (Inter_moddec_h moddec_h IB)))
                   (funintenv_h_of_int_h
                       (Inter_moddec_h moddec_h IB))))) /\

    (Inter_moddec_h (FUNCTORmoddec_h funbind) =
       \IB. funintenv_h_in_int_h (Inter_funbind_h funbind IB)) /\

    (Inter_strbind_h (BINDstrbind_h strid sigexp_h_option
		      strexp_h strbind_h_option)
     = \IB. add_strintenv_h 
                (strintenv_h_map strid
		 (Inter_sigexp_h_option sigexp_h_option IB))
                (Inter_strbind_h_option strbind_h_option IB)) /\

    (Inter_funbind_h (BINDfunbind_h
		      funid strid sigexp_h sigexp_h_option
		      strexp_h funbind_h_option) =
       \IB. add_funintenv_h
               (Inter_funbind_h_option funbind_h_option IB)
               (funintenv_h_map
		  funid
		  (Inter_sigexp_h_option sigexp_h_option
		     (add_strintenv_h_to_intbasis_h
		        IB
			(strintenv_h_map
			   strid
			   (Inter_sigexp_h sigexp_h IB)))))) /\

    (Inter_funbind_h (REBINDfunbind_h funid longfunid) =
       \IB. funintenv_h_map 
               funid (lower (lookup_longfunid_intbasis_h IB longfunid))) /\

    (Inter_sigexp_h_option NONE = \IB. empty_int_h) /\
    (Inter_sigexp_h_option (SOME sigexp_h) = Inter_sigexp_h sigexp_h) /\

    (Inter_strbind_h_option NONE = \IB. empty_strintenv_h) /\
    (Inter_strbind_h_option (SOME strbind_h) = Inter_strbind_h strbind_h)/\

    (Inter_funbind_h_option NONE = \IB. empty_funintenv_h) /\
    (Inter_funbind_h_option (SOME funbind_h) =
     Inter_funbind_h funbind_h)`--)};


val Inter_h_DEF = define_mutual_functions
{name = "Inter_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`(strintenv_h_from_strenv_h (STRENV_H sef) =
      STRINTENV_H (strint_h_finmap_from_strenv_h_finmap sef)) /\

     (strint_h_finmap_from_strenv_h_finmap (FINMAP sel) =
      FINMAP(strint_h_list_from_strenv_h_list sel)) /\

     (strint_h_list_from_strenv_h_list [] = []) /\
     (strint_h_list_from_strenv_h_list (CONS sep sel) =
      CONS(strid_int_h_from_strenv_h_pair sep)
          (strint_h_list_from_strenv_h_list sel)) /\

     (strid_int_h_from_strenv_h_pair (strid,env_h) = (strid,Inter_h env_h)) /\

     (funintenv_h_from_funenv_h (FUNENV_H fff) =
      FUNINTENV_H(funint_h_finmap_from_funenv_finmap fff)) /\

     (funint_h_finmap_from_funenv_finmap (FINMAP ffl) =
      FINMAP(funint_h_list_from_funenv_list ffl)) /\

     (funint_h_list_from_funenv_list [] = []) /\
     (funint_h_list_from_funenv_list (CONS ffp ffl) =
      CONS (funid_int_h_from_funid_funclos_h_pair ffp)
           (funint_h_list_from_funenv_list ffl)) /\

     (funid_int_h_from_funid_funclos_h_pair (funid,funclos_h) =
      (funid,Inter_funclos_h funclos_h)) /\


     (Inter_funclos_h (FUNCLOS_H strid int_h strexp_h int_h_option basis_h)=
      ((int_h_option = NONE)
       => Inter_strexp_h strexp_h (Inter_basis_h basis_h)
	 | SOME_arg int_h_option)) /\

     (Inter_h (ENV_H funenv_h strenv_h varenv exconenv) = 
         (INT_H (funintenv_h_from_funenv_h funenv_h)
                (strintenv_h_from_strenv_h strenv_h)
                (vars_from_varenv varenv)
                (excons_from_exconenv exconenv))) /\

     (Inter_basis_h (BASIS_H sigenv_h env_h) = 
             INTBASIS_H sigenv_h 
                        (strintenv_h_of_int_h (Inter_h env_h))
			(funintenv_h_of_int_h (Inter_h env_h)))`--)};


val cut_env_h_DEF = define_mutual_functions
{name = "cut_env_h_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`(cut_env_h (ENV_H funenv_h strenv_h varenv exconenv) = 
       \int_h. ENV_H (cut_funenv_h funenv_h (funintenv_h_of_int_h int_h))
                     (cut_strenv_h strenv_h (strintenv_h_of_int_h int_h))
                     (cut_varenv varenv (vars_of_int_h int_h))
                     (cut_exconenv exconenv (excons_of_int_h int_h))) /\

     (cut_strenv_h (STRENV_H sef) =
      \strintenv_h. STRENV_H (cut_strenv_h_finmap sef strintenv_h)) /\

     (cut_strenv_h_finmap (FINMAP sel) =
      \strintenv_h. FINMAP (cut_strenv_h_list sel strintenv_h)) /\

     (cut_strenv_h_list [] = \strintenv_h. []) /\
     (cut_strenv_h_list (CONS sep sel) =
      \strintenv_h. (cut_strenv_h_pair sep strintenv_h = undefined)
                    => cut_strenv_h_list sel strintenv_h
		      | CONS (lower (cut_strenv_h_pair sep strintenv_h))
			     (cut_strenv_h_list sel strintenv_h)) /\

     (cut_strenv_h_pair (strid,env_h) =
      \strintenv_h. (lookup_strid_strintenv_h strintenv_h strid = undefined)
                    => undefined
		      | lift (strid,
			      cut_env_h env_h
			      (lower (lookup_strid_strintenv_h
				      strintenv_h strid)))) /\
    
     (cut_funenv_h (FUNENV_H fff) = 
      \funintenv_h. FUNENV_H (cut_funenv_h_finmap fff funintenv_h)) /\

     (cut_funenv_h_finmap (FINMAP ffl) =
      \funintenv_h. FINMAP (cut_funenv_h_list ffl funintenv_h)) /\

     (cut_funenv_h_list [] = \funintenv_h. []) /\
     (cut_funenv_h_list (CONS ffp ffl) =
      \funintenv_h. (cut_funenv_h_pair ffp funintenv_h = undefined)
                    => cut_funenv_h_list ffl funintenv_h
		      | CONS (lower (cut_funenv_h_pair ffp funintenv_h))
			     (cut_funenv_h_list ffl funintenv_h)) /\

     (cut_funenv_h_pair (funid,funclos_h) =
      \funintenv_h. (lookup_funid_funintenv_h funintenv_h funid = undefined)
                    => undefined
		      | lift (funid,
			      cut_funclos_h funclos_h
			      (lower (lookup_funid_funintenv_h
				      funintenv_h funid)))) /\
			      

     (cut_funclos_h (FUNCLOS_H strid int_h strexp_h int_h_option basis_h) =
      \i. FUNCLOS_H strid int_h strexp_h (SOME i) basis_h)`--)};



(* To reduce higher-order environments to core environments. *)

val cut_env_h_to_env_DEF = define_mutual_functions
{name = "cut_env_h_to_env_DEF",
 fixities = NONE, rec_axiom = HOFMLBases_rec_thm,
 def = (--`(cut_env_h_to_env (ENV_H FE SE_h VE EE) =
      ENV (cut_strenv_h_to_strenv SE_h) VE EE) /\
    (cut_strenv_h_to_strenv (STRENV_H sef) =
     STRENV (cut_strenv_h_finmap_to_strenv_finmap sef)) /\
    (cut_strenv_h_finmap_to_strenv_finmap (FINMAP sel) =
     FINMAP(cut_strenv_h_list_to_strenv_list sel)) /\
    (cut_strenv_h_list_to_strenv_list [] = []) /\
    (cut_strenv_h_list_to_strenv_list (CONS sep sel) =
     CONS (cut_strenv_h_pair_to_strenv_pair sep)
          (cut_strenv_h_list_to_strenv_list sel)) /\
    (cut_strenv_h_pair_to_strenv_pair (strid,env_h) =
     (strid,cut_env_h_to_env env_h))`--)};


val env_in_env_h_DEF = define_mutual_functions
{name = "env_in_env_h_DEF",
 fixities = NONE, rec_axiom = env_existence,
 def = (--`(env_in_env_h (ENV strenv varenv exconenv) =
       ENV_H empty_funenv_h (strenv_in_strenv_h strenv) varenv exconenv) /\
    (strenv_in_strenv_h (STRENV sef) =
     STRENV_H (strenv_finmap_in_strenv_h_finmap sef)) /\
    (strenv_finmap_in_strenv_h_finmap (FINMAP sel) =
     FINMAP (strenv_list_in_strenv_h_list sel)) /\
    (strenv_list_in_strenv_h_list [] = []) /\
    (strenv_list_in_strenv_h_list (CONS sep sel) =
     CONS (strenv_pair_in_strenv_h_pair sep)
          (strenv_list_in_strenv_h_list sel)) /\
    (strenv_pair_in_strenv_h_pair (strid,env) =
     (strid, env_in_env_h env))`--)};
