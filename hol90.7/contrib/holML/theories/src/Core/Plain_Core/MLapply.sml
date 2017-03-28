(* DON'T NEED THIS

(* The definition of our equality predicate. It can only be applied to
   special values, nullary constructors, addresses, and values built out
   of such by record formation and constructor application. Since only
   things of equal types can be compared, we can assume quite a few
   things, for example, that a special value will only be compared
   against another special value. For CONval and APPCONval we need to
   check to see if the value is made with the same constructor since
   types can have both nullary constructors and constructors with
   arguments. We need to say that eq_val returns F for the constructors
   it can't be applied to (ASSGval, BASval, EXVALval, CLOSUREval, which
   are taken care of by the allelse clause) since define_mutual_functions
   requires the specification of *some* value for them. *)
val eq_def = 
--`(eq_val (SVALval sv) = \vl. SVALval sv = vl) /\
   (eq_val (CONval c) = \vl. CONval c = vl) /\
   (eq_val (ADDRval a) = \vl. ADDRval a = vl) /\
   (eq_val (RECORDval r) = \vl. RECORDval r = vl) /\
   (eq_val (APPCONval c v) =  \vl. is_APPCONval vl /\
    ((APPCONval_arg1 vl = c) /\ eq_val v (APPCONval_arg2 vl))) /\
   (eq_val allelse = \vl. F) /\
   (eq_record NONErec = \r2. NONErec = r2) /\
   (eq_record (SOMErec l v r) =
     \r2. is_SOMErec r2 /\ label_in_rec r2 l /\
	 eq_val v (lower(lookup_label r2 l)) /\ 
	 eq_record r (remove_field r2 l)) /\
   (eq_exval (NAMEexval n) = \ev. NAMEexval n = ev) /\
   (eq_exval (NAMEVALexval e v) = \ev. is_NAMEVALexval ev /\
     (NAMEVALexval_arg1 ev = e) /\ eq_val v (NAMEVALexval_arg2 ev))`--;
val eq_DEF = define_mutual_functions {name = "eq_DEF",
rec_axiom = env_exitence, fixities = NONE, def = eq_def};
val eq_DEF_lemma = store_thm("eq_DEF_lemma",
(--`(eq_val (SVALval sv) vl = (SVALval sv = vl)) /\
   (eq_val (CONval c) vl = (CONval c = vl)) /\
   (eq_val (ADDRval a) vl = (ADDRval a = vl)) /\
   (eq_val (RECORDval r) vl = (RECORDval r = vl)) /\
   (eq_val (APPCONval c v) vl = is_APPCONval vl /\
    (APPCONval_arg1 vl = c) /\ eq_val v (APPCONval_arg2 vl)) /\
   (eq_record NONErec r2 =  (NONErec = r2)) /\
   (eq_record (SOMErec l v r) r2 = is_SOMErec r2 /\ label_in_rec r2 l /\
	 eq_val v (lower(lookup_label r2 l)) /\ 
	 eq_record r (remove_field r2 l)) /\
   (eq_exval (NAMEexval n) ev = (NAMEexval n = ev)) /\
   (eq_exval (NAMEVALexval e v) ev = is_NAMEVALexval ev /\
     (NAMEVALexval_arg1 ev = e) /\ eq_val v (NAMEVALexval_arg2 ev))`--),
PURE_ONCE_REWRITE_TAC [eq_DEF] THEN BETA_TAC THEN
(REPEAT CONJ_TAC THEN REFL_TAC))

END OF DON'T NEED *)

(* A note about equality: It can only be applied to
   special values, nullary constructors, addresses, and values built out
   of such by record formation and constructor application. For these 
   things, equality is term equality. Records are the only questionable
   things here, and they are also done by terms since we order the items
   in the record values by the string ordering on the labels. We don't
   worry about equality for the other things, since the typechecker will
   prevent the equality predicate from being applied to them. *)

(* our apply function, which applies a base value (a basic function) to
   an argument. Note that the typechecker will guarantee that if a unary
   operation is being applied, its operand is an SVALval, and if a binary
   operation is being applied, then its operand is a record with label 1
   indicating the first argument and label 2 indicating the second arg. *)

val true_vp = --`VALvp (CONval (CON "true"))`--;
val false_vp = --`VALvp (CONval (CON "false"))`--;
val apply_def =
(--`(apply Size v =
     VALvp (SVALval (SVINT (string_size (SVSTR_arg (SVALval_arg v)))))) /\
    (apply Chr v =
     VALvp (SVALval (SVSTR (getchar (SVINT_arg (SVALval_arg v)))))) /\
    (apply Ord v =
     VALvp (SVALval (SVINT (ord_str (SVSTR_arg (SVALval_arg v)))))) /\
    (apply Explode v = VALvp (explode_str (SVSTR_arg (SVALval_arg v)))) /\
    (apply Implode v = VALvp (SVALval (SVSTR (implode_str v)))) /\
    (apply Abs v = 
     VALvp (SVALval (SVINT (integer_abs (SVINT_arg (SVALval_arg v)))))) /\
    (apply Div v =
     (intfield2 v = INT 0
      => PACKvp ^Div_pack
	| VALvp (SVALval (SVINT ((intfield1 v) div (intfield2 v)))))) /\
    (apply Mod v =
     (intfield2 v = INT 0
      => PACKvp ^Mod_pack
	| VALvp (SVALval (SVINT ((intfield1 v) mod (intfield2 v)))))) /\
    (apply Neg v =
     (SVINT_arg (SVALval_arg v) = INT 0
      => VALvp v
	| VALvp (SVALval (SVINT (neg (SVINT_arg (SVALval_arg v))))))) /\
    (apply Times v =
     VALvp (SVALval (SVINT ((intfield1 v) times (intfield2 v))))) /\
    (apply Plus v =
     VALvp (SVALval (SVINT ((intfield1 v) plus (intfield2 v))))) /\
    (apply Minus v =
     VALvp (SVALval (SVINT ((intfield1 v) minus (intfield2 v))))) /\
    (apply Eql v =
     ((field1_val v) = (field2_val v) => ^true_vp | ^false_vp)) /\
    (apply Noteql v = 
     ((field1_val v) = (field2_val v) => ^false_vp | ^true_vp)) /\
    (apply Less v =
     (is_SVINT (SVALval_arg (field1_val v))
      => ((intfield1 v) below (intfield2 v) => ^true_vp | ^false_vp)
       | (ltstring (strfield1 v) (strfield2 v) => ^true_vp | ^false_vp))) /\
    (apply Greater v =
     (is_SVINT (SVALval_arg (field1_val v))
      => ((intfield2 v) below (intfield2 v) => ^true_vp | ^false_vp)
       | (ltstring (strfield2 v) (strfield1 v) => ^true_vp | ^false_vp))) /\
    (apply Lesseql v =
     (is_SVINT (SVALval_arg (field1_val v))
      => ((intfield2 v) below (intfield1 v) => ^false_vp | ^true_vp)
       | (ltstring (strfield2 v) (strfield1 v) => ^false_vp | ^true_vp))) /\
    (apply Greatereql v =
     (is_SVINT (SVALval_arg (field1_val v))
      => ((intfield1 v) below (intfield2 v) => ^false_vp | ^true_vp)
       | (ltstring (strfield1 v) (strfield2 v) => ^false_vp | ^true_vp)))`--);


val apply_DEF = new_recursive_definition
{def = apply_def, fixity = Prefix, name = "apply_DEF", 
 rec_axiom = basval_Axiom};

