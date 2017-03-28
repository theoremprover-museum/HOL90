(* MLinitialDynamicBasis.sml *)

(* explode_string: change a string into a list of one-char long strings
   its type is string -> val *)
val explode_str_DEF = new_recursive_definition
{def = 
 --`(explode_str "" = CONval (CON "nil")) /\
    (explode_str (STRING a s) =
     APPCONval (CON "::")
               (RECORDval
		(insert_into_record
		 (insert_into_record empty_record 
		  (LABEL "1") (SVALval (SVSTR (STRING a ""))))
		 (LABEL "2") (explode_str s))))`--,
 fixity = Prefix, name = "explode_str_DEF", 
 rec_axiom = theorem "string" "string_Axiom"};

(* for implode_str, if the value is (CONval c), we assume c is nil,
   and if it is (APPCONval c v) we assume c is :: and that the val v is a
   record with fields 1 (the character) and 2 (the rest of the list, which
   is the part we need to recurse on).
   Unfortunately, we can't just extract out the field with label 2
   and recurse on it, since the form of env_existence only allows
   recursion on constructor arguments. So we call implode_str on the
   value, and the RECORDval case will take care of it, calling implode10 on
   the record, which calls implode11 on the finite map, which calls 
   implode12 on the list, which calls implode13 on the label-value pair
   where the label is "2", and implode13 calls implode_str on the value
   associated with label "2". *)

val implode_DEF = define_mutual_functions 
    {name = "implode_DEF",
     rec_axiom = env_existence, fixities = NONE,
     def = --`(implode_str (CONval c) = "") /\
	      (implode_str (APPCONval c v) =
	          STRING (first_char (strfield1 v)) (implode_str v)) /\
	      (implode_str (RECORDval r) = implode10 r) /\
	      (implode_str allelse = @x:string.T) /\
	      (implode10 (RECORD fm) = implode11 fm) /\
	      (implode11 (FINMAP l) = implode12 l) /\
	      (implode12 (CONS h t) =
	          (FST h = LABEL "2" => implode13 h
		                      | implode12 t)) /\
	      (implode12 NIL = "") /\
	      (implode13 (lab, vl) = implode_str vl)`--};

val initial_varenv_data =
[(--`VAR ":="`--, --`ASSGval`--),
 (--`VAR "size"`--, --`BASval Size`--),
 (--`VAR "chr"`--, --`BASval Chr`--),
 (--`VAR "ord"`--, --`BASval Ord`--),
 (--`VAR "explode"`--, --`BASval Explode`--),
 (--`VAR "implode"`--, --`BASval Implode`--),
 (--`VAR "abs"`--, --`BASval Abs`--),
 (--`VAR "div"`--, --`BASval Div`--),
 (--`VAR "mod"`--, --`BASval Mod`--),
 (--`VAR "~"`--, --`BASval Neg`--),
 (--`VAR "*"`--, --`BASval Times`--),
 (--`VAR "+"`--, --`BASval Plus`--),
 (--`VAR "-"`--, --`BASval Minus`--),
 (--`VAR "="`--, --`BASval Eql`--),
 (--`VAR "<>"`--, --`BASval Noteql`--),
 (--`VAR "<"`--, --`BASval Less`--),
 (--`VAR ">"`--, --`BASval Greater`--),
 (--`VAR "<="`--, --`BASval Lesseql`--),
 (--`VAR ">="`--, --`BASval Greatereql`--)]

val initial_varenv = add_to_varenv initial_varenv_data 
                     (--`empty_varenv`--)

val initial_varenv_DEF = new_definition("initial_varenv_DEF",
  mk_eq{lhs = (--`initial_varenv:varenv`--),
	rhs = initial_varenv});

(* declare exception names for the exceptions that may be raised by
   APPLYing basvalues (basvalues are Size, Chr, Abs, Div, etc) and
   by such things as failed matches. *)
val Abs_en = --`EXNAME 0`--
val Div_en = --`EXNAME 1`--
val Mod_en = --`EXNAME 2`--
val Prod_en = --`EXNAME 3`--
val Neg_en = --`EXNAME 4`--
val Sum_en = --`EXNAME 5`--
val Diff_en = --`EXNAME 6`--
val Match_en = --`EXNAME 7`--
val Bind_en = --`EXNAME 8`--
val initial_exconenv_data =
[(--`EXCON "Bind"`--, Bind_en), (--`EXCON "Match"`--, Match_en),
 (--`EXCON "Diff"`--, Diff_en), (--`EXCON "Sum"`--, Sum_en),
 (--`EXCON "Neg"`--, Neg_en), (--`EXCON "Prod"`--, Prod_en),
 (--`EXCON "Mod"`--, Mod_en), (--`EXCON "Div"`--, Div_en),
 (--`EXCON "Abs"`--, Abs_en)];

val initial_exconenv =
    add_to_exconenv initial_exconenv_data (--`empty_exconenv`--)

val initial_exconenv_DEF = new_definition("initial_exconenv_DEF",
 mk_eq{lhs=(--`initial_exconenv:exconenv`--),
       rhs=initial_exconenv});

val initial_strenv_DEF = new_definition("initial_strenv_DEF",
(--`initial_strenv = empty_strenv`--));

val initial_env_DEF = new_definition("initial_env_DEF",
(--`initial_env  = ENV initial_strenv initial_varenv initial_exconenv`--));

val initial_state_DEF = new_definition("initial_state_DEF",
(--`initial_state = STATE (MEM empty_finmap)
                          (EXNAMESET {EXNAME 0; EXNAME 1; EXNAME 2;
				      EXNAME 3; EXNAME 4; EXNAME 5;
				      EXNAME 6; EXNAME 7; EXNAME 8})`--));
