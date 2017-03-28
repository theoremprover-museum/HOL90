(* File: MLsval.sml *)

(* special values, the value denotes by the constants in scon *)
val sval_Axiom = define_type{name = "sval_Axiom", fixities = [Prefix,Prefix],
                             type_spec = `sval = SVINT of integer 
                                               | SVSTR of string`};

(* value_of gives the value of a special constant *)
val value_of_DEF = new_recursive_definition 
    {name = "value_of_DEF", fixity = Prefix,
     rec_axiom = scon_Axiom,
     def = --`(value_of (SCINT i) = SVINT i) /\
              (value_of (SCSTR s) = SVSTR s)`--};


(* addresses *)
val addr_Axiom = define_type{name = "addr_Axiom", fixities = [Prefix],
                             type_spec = `addr = ADDR of num`}

val ADDR_arg_DEF  = new_recursive_definition 
    {name = "ADDR_arg_DEF", fixity = Prefix,
     rec_axiom = addr_Axiom,
     def = --`ADDR_arg (ADDR n) = n`--};
val addr_constructors_one_one =
    save_thm("addr_constructors_one_one",
             prove_constructors_one_one addr_Axiom)
val addr_induction_thm =
    save_thm("addr_induction_thm", prove_induction_thm addr_Axiom)
val addr_cases_thm =
    save_thm("addr_cases_thm", prove_cases_thm addr_induction_thm)

val less_addr_DEF = new_definition
("less_addr_DEF",
 --`less_addr a1 a2 = (ADDR_arg a1) < (ADDR_arg a2)`--)

(* basic values -- predefined identifiers *)
val basval_Axiom = define_type
    {name = "basval_Axiom",
     fixities = [Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
                 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
                 Prefix,Prefix],
     type_spec = `basval = Size | Chr | Ord | Explode | Implode | Abs 
                         | Div | Mod | Neg | Times | Plus | Minus | Eql 
                         | Noteql | Less | Greater | Lesseql | Greatereql`};

(* EXCEPTION NAMES -- each time we say exception <excon> a new "name" is 
   generated. An exception name is just a number with a constructor
   wrapped around it -- this makes it easy to keep track of the exception
   names that have been used and to generate new ones.
   exname ::= EXNAME num *)

val exname_Axiom = define_type{name = "exname_Axiom", fixities = [Prefix],
			       type_spec = `exname = EXNAME of num`};
val EXNAME_arg_DEF  = new_recursive_definition
    {name = "EXNAME_arg_DEF", fixity = Prefix,
     rec_axiom = exname_Axiom,
     def = --`EXNAME_arg (EXNAME n) = n`--};
val less_exname_DEF = new_definition
("less_exname_DEF",
 --`less_exname a1 a2 = (EXNAME_arg a1) < (EXNAME_arg a2)`--)

(* EXNAMESET -- the exception names that have been used so far -- this
   may be changed at some point to be "exname finite_set"
   exnameset ::= EXNAMESET (exname set)
 *)

val exnameset_Axiom =
    define_type{name = "exnameset_Axiom", fixities = [Prefix],
                    type_spec = `exnameset = EXNAMESET of (exname set)`};

val EXNAMESET_arg_DEF = new_recursive_definition
    {name = "EXNAMESET_arg_DEF", fixity = Prefix,
     rec_axiom = exnameset_Axiom,
     def = (--`(EXNAMESET_arg (EXNAMESET es) = es)`--)};

(* get the value (integer or string) within the sval, test for type *)
val SVINT_arg_DEF = new_recursive_definition 
    {name = "SVINT_arg_DEF", fixity = Prefix, 
     rec_axiom = sval_Axiom,
     def = --`SVINT_arg (SVINT i) = i`--};
val SVSTR_arg_DEF = new_recursive_definition 
    {name = "SVSTR_arg_DEF", fixity = Prefix, 
     rec_axiom = sval_Axiom,
     def = --`SVSTR_arg (SVSTR s) = s`--};
val is_SVINT_DEF = new_recursive_definition 
    {name = "is_SVINT_DEF", fixity = Prefix, 
     rec_axiom = sval_Axiom,
     def = --`(is_SVINT (SVINT i) = T) /\ (is_SVINT (SVSTR s) = F)`--};
val is_SVSTR_DEF = new_recursive_definition 
    {name = "is_SVSTR_DEF", fixity = Prefix, 
     rec_axiom = sval_Axiom,
     def = --`(is_SVSTR (SVSTR s) = T) /\ (is_SVSTR (SVINT i) = F)`--};


