(* File: MLeval.sml *)

(* Now what I want to define are a bunch of functions, called eval_atexp,
   ..., eval_pat, that indicate whether one of the function arguments 
   (an expression of some sort), in a context specified by other arguments, 
   evaluates to a result and possibly a new context (both of which are
   also arguments). For example, the type of eval_atexp is
   atexp->state->env->state->val_pack->bool, and it indicates
   whether the atexp arg evaluates to the val_pack arg (which is either
   the resulting value or a packet -- a raised exception) in the
   environment and state given by the env and first state args, and resulting
   in the final state given by the second state arg. The arguments to
   other functions are similar: the first argument is the ML phrase we are
   evaluating, then comes the state and env we're evaluting in, and the last
   argument is the result of the evaluation. All functions except the
   pattern evaluations (eval_atpat, eval_patrow, and eval_pat) have a 
   second state argument indicating the resulting state (the 3 functions
   mentioned don't as pattern-matching doesn't change the state), and
   the matching functions (eval_match, eval_mrule, eval_atpat,
   eval_patrow, and eval_pat) have an argument (of type val or, in the case
   of eval_patrow, a record) indicating the value that is being matched
   against.

   These functions eval_*:<args>->bool define a bunch of relations, 
   indicating what evaluates to what. I will call these the evaluation
   relations.

   It would be nice to use define_mutual_functions to define this, but 
   evaluation isn't primative recursive. Look at rules 117 and 118 for
   evaluating functions: there we evaluate the result of a previous 
   evalution, not a subterm of the ML phrase we're evaluating. So, instead,
   we define a predicate (called eval_pred) on potential evaluation 
   relations that is true of all the relations iff they satisfy the 
   properties desired of ML evaluations.

   Notes on the rules: in the case of eval_exprow (EXPROW2 l ex er) I
   specify that the resulting record is the result of adding the label
   (l) and evaluated expression (ex) to the front of the result of
   evaluating the rest of the record (er). Since in the definition of
   lookup_label I return the val associated with the label closest to the
   front of the record list, this means that if in an exprow there were
   two different expression given to a label (for example, {a = 4, a = 7}),
   the first one would be the one that would be returned by
   lookup_label. Thus my record evaluation is technically incorrect,
   since according to rule 110 the results of evaluating the rest of the
   record should modify the result of evaluating the first label and
   expression, instead of vise versa. But I figure this slight twisting
   of the rules is OK since in an exprow there should be no duplicate
   labels.

   All through these rules I have not done any testing on values to make
   sure they are of the appropriate type before extracting them. For 
   example, when in an application, if exp evaluates to ASSGval, I
   assume that the atomic expression to which it is being applied is
   a record with labels "1" (an address) and "2" (a value).
   The typechecker would ensure that the values are of the appropriate
   types.

   I'd like to point out that the rules (and functions above for things
   like add_env) I've formulated specify precisely what resulting 
   environments, records, and states must look like to satisfy the 
   evaluation relations. For example, in order for 
   (eval_dec (VALdec vb) s1 e s2 ep) to be satisfied, there must exist
   a varenv_pack vep such that (eval_valbind vb s1 e s2 vep), and then
   the resulting env_pack ep is specified as a function of vep.
   
   Finally, I want to mention that the last case in the eval_exp
   (APPexp ex ae) is for rule 113, ie, for (exp atexp) when exp
   evaluates to an exception name.

*)

val eval_pred_def = 
--`!(eval_atexp:atexp->state->env->state->val_pack->bool)
    (eval_exprow:exprow->state->env->state->record_pack->bool)
    (eval_exp:exp->state->env->state->val_pack->bool)
    (eval_match:match->state->env->val->state->val_pack_fail->bool)
    (eval_mrule:mrule->state->env->val->state->val_pack_fail->bool)
    (eval_dec:dec->state->env->state->env_pack->bool)
    (eval_valbind:valbind->state->env->state->varenv_pack->bool).

eval_pred eval_atexp eval_exprow eval_exp eval_match eval_mrule
          eval_dec eval_valbind =

(* Atomic Expressions *)
(* Rule 103 *)

   (!s E scon.
       eval_atexp (SCONatexp scon) s E s (VALvp (SVALval (value_of scon)))) /\

(* Rule 104 *)

   (!s E longvar v. (lookuplongvar_env E longvar = lift v) ==>
       eval_atexp (VARatexp longvar) s E s (VALvp v)) /\

(* Rule 105 *)

   (!s E longcon con. (long_base longcon = con) ==>
       eval_atexp (CONatexp longcon) s E s (VALvp (CONval con))) /\

(* Rule 106 *)

   (!s E en longexcon. (lookuplongexcon_env E longexcon = lift en) ==>
       eval_atexp (EXCONatexp longexcon) s E s
	          (VALvp (EXVALval (NAMEexval en)))) /\

(* Rule 107a *)

   (!s E. eval_atexp (RECORDatexp NONE) s E s 
            (VALvp (RECORDval empty_record))) /\

(* Rule 107b *)

    (!s1 E s2 exprow r.
     eval_exprow exprow s1 E s2 (RECORDrp r) ==>
	 eval_atexp (RECORDatexp (SOME exprow)) s1 E s2
	            (VALvp (RECORDval (add_record empty_record r)))) /\

    (!s1 E s2 exprow p.
     eval_exprow exprow s1 E s2 (PACKrp p) ==>
	 eval_atexp (RECORDatexp (SOME exprow)) s1 E s2 (PACKvp p)) /\

(* Rule 108 *)

   (!s1 E s2 dec exp v.
    (?s' E'. eval_dec dec s1 E s' (ENVep E') /\
             eval_exp exp s' (add_env E E') s2 (VALvp v)) ==>
    eval_atexp (LETatexp dec exp) s1 E s2 (VALvp v)) /\

   (!s1 E s2 dec exp p.
    eval_dec dec s1 E s2 (PACKep p) ==>
	eval_atexp (LETatexp dec exp) s1 E s2 (PACKvp p)) /\

   (!s1 E s2 dec exp p.
    (?s' E'. eval_dec dec s1 E s' (ENVep E') /\
             eval_exp exp s' (add_env E E') s2 (PACKvp p)) ==>
        eval_atexp (LETatexp dec exp) s1 E s2 (PACKvp p)) /\

(* Rule 109 *)

   (!s1 E s2 exp vp. eval_exp exp s1 E s2 vp ==>
       eval_atexp (PARatexp exp) s1 E s2 vp) /\

(* Expression Rows *)
(* Rule 110a *)

   (!s1 E s2 lab exp v. 
    eval_exp exp s1 E s2 (VALvp v) ==>
	eval_exprow (EXPROW lab exp NONE) s1 E s2
                    (RECORDrp (insert_into_record empty_record lab v))) /\

   (!s1 E s2 lab exp exprow_op p.
    eval_exp exp s1 E s2 (PACKvp p) ==>
	eval_exprow (EXPROW lab exp exprow_op) s1 E s2 (PACKrp p)) /\


(* Rule 110b *)

   (!s1 E s2 lab exp exprow v r.
    (?s'. eval_exp exp s1 E s' (VALvp v) /\
          eval_exprow exprow s' E s2 (RECORDrp r)) ==>
    eval_exprow (EXPROW lab exp (SOME exprow)) s1 E s2
                (RECORDrp (add_record
			   (insert_into_record empty_record lab v) r))) /\

   (* the case of (EXPROW lab exp (SOME exprow)) when the exp evaluates
      to a packet is taken care of with 110a *)

   (!s1 E s2 lab exp exprow p.
    (?s' v. eval_exp exp s1 E s' (VALvp v) /\
          eval_exprow exprow s' E s2 (PACKrp p)) ==>
    eval_exprow (EXPROW lab exp (SOME exprow)) s1 E s2 (PACKrp p)) /\

(* Expressions *)
(* Rule 111 *)

   (!s1 E s2 atexp vp. eval_atexp atexp s1 E s2 vp ==>
       eval_exp (ATEXPexp atexp) s1 E s2 vp) /\

(* Rule 112 *)

   (!s1 E s2 exp atexp c v. 
    (?s'. eval_exp exp s1 E s' (VALvp(CONval c)) /\
          (~(c = CON "ref")) /\
	  eval_atexp atexp s' E s2 (VALvp v))  ==>
    eval_exp (APPexp exp atexp) s1 E s2 (VALvp (APPCONval c v))) /\

   (* This one is shared with rules 113, 114, 115, 116, 117 and 118 *)
   (!s1 E s2 exp atexp p. eval_exp exp s1 E s2 (PACKvp p) ==>
       eval_exp (APPexp exp atexp) s1 E s2 (PACKvp p)) /\

   (!s1 E s2 exp atexp p.
    (?s' c. eval_exp exp s1 E s' (VALvp(CONval c)) /\
	  (~(c = CON "ref")) /\
	  eval_atexp atexp s' E s2 (PACKvp p)) ==>
    eval_exp (APPexp exp atexp) s1 E s2 (PACKvp p)) /\


(* Rule 113 *)

   (!s1 E s2 exp atexp en v.
    (?s'. eval_exp exp s1 E s' (VALvp (EXVALval (NAMEexval en)))  /\
          eval_atexp atexp s' E s2 (VALvp v))  ==>
    eval_exp (APPexp exp atexp) s1 E s2 
        (VALvp (EXVALval (NAMEVALexval en v))))/\

   (* see Rule 112, case 2 *)

   (!s1 E s2 exp atexp p.
    (?s' en. eval_exp exp s1 E s' (VALvp (EXVALval (NAMEexval en)))  /\
           eval_atexp atexp s' E s2 (PACKvp p)) ==>
    eval_exp (APPexp exp atexp) s1 E s2 (PACKvp p)) /\


(* Rule 114 *)

   (!s E s'' exp atexp a v.
    (?s'. eval_exp exp s E s' (VALvp (CONval (CON "ref"))) /\
          eval_atexp atexp s' E s'' (VALvp v) /\
	  (a = new_addr s'')) ==>
    eval_exp (APPexp exp atexp) s E (insert_into_state_mem s'' a v)
             (VALvp (ADDRval a))) /\

   (* see Rule 112, case 2 *)

   (!s E s'' exp atexp p.
    (?s'. eval_exp exp s E s' (VALvp (CONval (CON "ref"))) /\
          eval_atexp atexp s' E s'' (PACKvp p)) ==>
    eval_exp (APPexp exp atexp) s E s'' (PACKvp p)) /\


(* Rule 115 *)

   (!s E s'' exp atexp a v.
    (?s'. eval_exp exp s E s' (VALvp ASSGval) /\
          eval_atexp atexp s' E s''
	     (VALvp (RECORDval (insert_into_record
				(insert_into_record empty_record
				 (LABEL "1") (ADDRval a))
				(LABEL "2") v)))) ==>
    eval_exp (APPexp exp atexp) s E (insert_into_state_mem s'' a v)
	     (VALvp (RECORDval empty_record))) /\

   (* see Rule 112, case 2 *)

   (!s E s'' exp atexp p.
    (?s'. eval_exp exp s E s' (VALvp ASSGval) /\
          eval_atexp atexp s' E s'' (PACKvp p)) ==>
    eval_exp (APPexp exp atexp) s E s'' (PACKvp p)) /\


(* Rule 116 *)

   (!s1 E s2 exp atexp v'. 
    (?s' b v. eval_exp exp s1 E s' (VALvp (BASval b)) /\
	  eval_atexp atexp s' E s2 (VALvp v) /\
	  ((apply b v) = v')) ==>  (* v' could be either a value or a pack *)
    eval_exp (APPexp exp atexp) s1 E s2 v') /\

   (* see Rule 112, case 2 *)

   (!s1 E s2 exp atexp p. 
    (?s' b. eval_exp exp s1 E s' (VALvp(BASval b)) /\
	  eval_atexp atexp s' E s2 (PACKvp p)) ==>
    eval_exp (APPexp exp atexp) s1 E s2 (PACKvp p)) /\


(* Rule 117 *)

   (!s1 E s4 exp atexp v'. 
    (?s2 s3 match E' VE v.
          eval_exp exp s1 E s2 (VALvp(CLOSUREval(CLOSURE match E' VE))) /\
	  eval_atexp atexp s2 E s3 (VALvp v) /\
	  eval_match match s3
	             (add_env E' (ENV empty_strenv (rec_varenv VE) 
				  empty_exconenv))
		     v s4 (VALvpf v')) ==>
    eval_exp (APPexp exp atexp) s1 E s4 (VALvp v')) /\

   (* see Rule 112, case 2 *)

   (* Shared with Rule 118 *)
   (!s1 E s3 exp atexp p.
    (?s2 match E' VE.
          eval_exp exp s1 E s2 (VALvp(CLOSUREval(CLOSURE match E' VE))) /\
	  eval_atexp atexp s2 E s3 (PACKvp p)) ==>
    eval_exp (APPexp exp atexp) s1 E s3 (PACKvp p)) /\

   (* Shared with Rule 118 *)
   (!s1 E s4 exp atexp p. 
    (?s2 s3 match E' VE v.
          eval_exp exp s1 E s2 (VALvp(CLOSUREval(CLOSURE match E' VE))) /\
	  eval_atexp atexp s2 E s3 (VALvp v) /\
	  eval_match match s3
	             (add_env E' (ENV empty_strenv (rec_varenv VE)
				  empty_exconenv))
		     v s4 (PACKvpf p)) ==>
    eval_exp (APPexp exp atexp) s1 E s4 (PACKvp p)) /\


(* Rule 118 *)

   (!s1 E s4 exp atexp. 
    (?s2 s3 match E' VE v.
          eval_exp exp s1 E s2 (VALvp(CLOSUREval(CLOSURE match E' VE))) /\
	  eval_atexp atexp s2 E s3 (VALvp v) /\
	  eval_match match s3
	             (add_env E' (ENV empty_strenv (rec_varenv VE)
				  empty_exconenv))
		     v s4 FAILvpf) ==>
    eval_exp (APPexp exp atexp) s1 E s4 (PACKvp ^Match_pack)) /\

   (* see Rule 112, case 2, and Rule 117, cases 3 & 4 *)


(* Rule 119 *)

   (!s1 E s2 exp match v. eval_exp exp s1 E s2 (VALvp v) ==>
     eval_exp (HANDLEexp exp match) s1 E s2 (VALvp v)) /\

   (* There are no other cases for this rule! *)


(* Rule 120 *)

   (!s1 E s2 exp match v.
    (?s' e. eval_exp exp s1 E s' (PACKvp (PACK e)) /\
            eval_match match s' E (EXVALval e) s2 (VALvpf v)) ==>
    eval_exp (HANDLEexp exp match) s1 E s2 (VALvp v)) /\

   (* Shared with Rule 121 *)
   (!s1 E s2 exp match p.
    (?s' e. eval_exp exp s1 E s' (PACKvp (PACK e)) /\
            eval_match match s' E (EXVALval e) s2 (PACKvpf p)) ==>
    eval_exp (HANDLEexp exp match) s1 E s2 (PACKvp p)) /\


(* Rule 121 *)

   (!s1 E s2 exp match e.
    (?s'. eval_exp exp s1 E s' (PACKvp (PACK e)) /\
            eval_match match s' E (EXVALval e) s2 FAILvpf) ==>
    eval_exp (HANDLEexp exp match) s1 E s2 (PACKvp (PACK e))) /\

   (* see Rule 120, case 2 *)


(* Rule 122 *)

   (!s1 E s2 exp e. eval_exp exp s1 E s2 (VALvp (EXVALval e)) ==>
       eval_exp (RAISEexp exp) s1 E s2 (PACKvp (PACK e))) /\

   (!s1 E s2 exp p. eval_exp exp s1 E s2 (PACKvp p) ==>
       eval_exp (RAISEexp exp) s1 E s2 (PACKvp p)) /\


(* Rule 123 *)

   (!s E match. eval_exp (FNexp match) s E s
                         (VALvp (CLOSUREval (CLOSURE match E empty_varenv)))) /\

(* Matches *)
(* Rule 124 *)

   (!s1 E s2 mrule match_op v v'. eval_mrule mrule s1 E v s2 (VALvpf v') ==>
       eval_match (MATCH mrule match_op) s1 E v s2 (VALvpf v')) /\

   (* Shared with Rule 125 & 126 *)
   (!s1 E s2 mrule match_op v p. eval_mrule mrule s1 E v s2 (PACKvpf p) ==>
       eval_match (MATCH mrule match_op) s1 E v s2 (PACKvpf p)) /\

(* Rule 125 *)

   (!s1 E s2 mrule v. eval_mrule mrule s1 E v s2 FAILvpf ==>
       eval_match (MATCH mrule NONE) s1 E v s2 FAILvpf) /\

   (* See Rule 124, case 2 *)

(* Rule 126 *)

   (!s1 E s2 mrule match v vpf.
    (?s'. eval_mrule mrule s1 E v s' FAILvpf /\
          eval_match match s' E v s2 vpf) ==>
    eval_match (MATCH mrule (SOME match)) s1 E v s2 vpf) /\

   (* see Rule 124, case 2 *)

(* Match Rules *)
(* Rule 127 *)

    (!s1 E s2 pat exp v v'.
     (?s' VE. eval_pat pat s1 E v s' (VARENVvef VE) /\
              eval_exp exp s'
	               (add_env E (ENV empty_strenv VE empty_exconenv))
		       s2
		       (VALvp v')) ==>
     eval_mrule (MRULE pat exp) s1 E v s2 (VALvpf v')) /\

    (* According to the Definition, patterns evaluate to VE/FAIL, but
       not to packets *)

    (!s1 E s2 pat exp v p.
     (?s' VE. eval_pat pat s1 E v s' (VARENVvef VE) /\
              eval_exp exp s'
	               (add_env E (ENV empty_strenv VE empty_exconenv))
		       s2
		       (PACKvp p)) ==>
     eval_mrule (MRULE pat exp) s1 E v s2 (PACKvpf p)) /\

(* Rule 128 *)

    (!s1 E s2 pat exp v. eval_pat pat s1 E v s2 FAILvef ==>
	eval_mrule (MRULE pat exp) s1 E v s2 FAILvpf) /\

    (* Again, according to the Definition, patterns evaluate to VE/FAIL,
       but not to packets *)


(* Declarations *)
(* Rule 129 *)

    (!s1 E s2 valbind VE. eval_valbind valbind s1 E s2 (VARENVvep VE) ==>
	eval_dec (VALdec valbind) s1 E s2
	         (ENVep (ENV empty_strenv VE empty_exconenv))) /\

    (!s1 E s2 valbind p.eval_valbind valbind s1 E s2 (PACKvep p) ==>
	eval_dec (VALdec valbind) s1 E s2 (PACKep p)) /\


(* Rule 130 *)

    (!s1 E s2 exbind EE. eval_exbind exbind s1 E s2 (EXCONENVeep EE) ==>
	eval_dec (EXCEPTdec exbind) s1 E s2
	         (ENVep (ENV empty_strenv empty_varenv EE))) /\


    (!s1 E s2 exbind p. eval_exbind exbind s1 E s2 (PACKeep p) ==>
	eval_dec (EXCEPTdec exbind) s1 E s2 (PACKep p)) /\


(* Rule 131 *)

    (!s1 E s2 dec1 dec2 E2.
     (?E1 s'. eval_dec dec1 s1 E s' (ENVep E1) /\
	      eval_dec dec2 s' (add_env E E1) s2 (ENVep E2)) ==>
     eval_dec (LOCALdec dec1 dec2) s1 E s2 (ENVep E2)) /\

    (!s1 E s2 dec1 dec2 p. eval_dec dec1 s1 E s2 (PACKep p) ==>
	eval_dec (LOCALdec dec1 dec2) s1 E s2 (PACKep p)) /\

    (!s1 E s2 dec1 dec2 p.
     (?E1 s'. eval_dec dec1 s1 E s' (ENVep E1) /\
	      eval_dec dec2 s' (add_env E E1) s2 (PACKep p)) ==>
     eval_dec (LOCALdec dec1 dec2) s1 E s2 (PACKep p)) /\

(* Rule 132 *)

    (!s E longstrid_1_n E_1_n.
     (nonempty_MAP (lookuplongstrid_env E) longstrid_1_n = 
      nonempty_MAP lift E_1_n) ==>
     eval_dec (OPENdec longstrid_1_n) s E s
              (ENVep (add_nonemptylist_env E_1_n))) /\

(* Rule 133 *)

    (!s E. eval_dec EMPTYdec s E s
              (ENVep (ENV empty_strenv empty_varenv empty_exconenv))) /\

(* Rule 134 *)

   (!s1 E s2 dec1 dec2 E1 E2.
     (?s'. eval_dec dec1 s1 E s' (ENVep E1) /\
	   eval_dec dec2 s' (add_env E E1) s2 (ENVep E2)) ==>
     eval_dec (SEQdec dec1 dec2) s1 E s2 (ENVep (add_env E1 E2))) /\

    (!s1 E s2 dec1 dec2 p. eval_dec dec1 s1 E s2 (PACKep p) ==>
	eval_dec (SEQdec dec1 dec2) s1 E s2 (PACKep p)) /\

(* changed this *)
    (!s1 E s2 dec1 dec2 p.
     (?E1 s'. eval_dec dec1 s1 E s' (ENVep E1) /\
	   eval_dec dec2 s' (add_env E E1) s2 (PACKep p)) ==>
     eval_dec (SEQdec dec1 dec2) s1 E s2 (PACKep p)) /\


(* Value Bindings *)
(* Rule 135a *)

    (!s1 E s2 pat exp VE.
     (?v s'. eval_exp exp s1 E s' (VALvp v) /\
             eval_pat pat s' E v s2 (VARENVvef VE)) ==>
     eval_valbind (PLAINvalbind pat exp NONE) s1 E s2 (VARENVvep VE)) /\

    (* Shared with Rule 136a *)
    (!s1 E s2 pat exp p. eval_exp exp s1 E s2 (PACKvp p) ==>
	 eval_valbind (PLAINvalbind pat exp NONE) s1 E s2 (PACKvep p)) /\

    (* Again, according to the Definition, patterns evaluate to VE/FAIL,
       but not to packets *)

(* Rule 135b *)

    (!s1 E s4 pat exp valbind VE VE'.
     (?v s2 s3. eval_exp exp s1 E s2 (VALvp v) /\
	        eval_pat pat s2 E v s3 (VARENVvef VE) /\
		eval_valbind valbind s3 E s4 (VARENVvep VE')) ==>
     eval_valbind (PLAINvalbind pat exp (SOME valbind)) s1 E s4
                  (VARENVvep (add_varenv VE VE'))) /\

    (* Shared with Rule 136b *)
    (!s1 E s2 pat exp valbind p. eval_exp exp s1 E s2 (PACKvp p) ==>
	eval_valbind (PLAINvalbind pat exp (SOME valbind)) s1 E s2
	             (PACKvep p)) /\

    (* Again, according to the Definition, patterns evaluate to VE/FAIL,
       but not to packets *)

(* changed this *)
    (!s1 E s4 pat exp valbind p.
     (?v VE s2 s3. eval_exp exp s1 E s2 (VALvp v) /\
	        eval_pat pat s2 E v s3 (VARENVvef VE) /\
		eval_valbind valbind s3 E s4 (PACKvep p)) ==>
     eval_valbind (PLAINvalbind pat exp (SOME valbind)) s1 E s4
                  (PACKvep p)) /\

(* RULE 136a *)

    (!s1 E s2 pat exp.
     (?v s'. eval_exp exp s1 E s' (VALvp v) /\
             eval_pat pat s' E v s2 FAILvef) ==>
     eval_valbind (PLAINvalbind pat exp NONE) s1 E s2 (PACKvep ^Bind_pack)) /\

    (* See Rule 135a, Case 2 *)

    (* Again, according to the Definition, patterns evaluate to VE/FAIL,
       but not to packets *)


(* RULE 136b *)

    (!s1 E s2 pat exp valbind.
     (?v s'. eval_exp exp s1 E s' (VALvp v) /\
             eval_pat pat s' E v s2 FAILvef) ==>
     eval_valbind (PLAINvalbind pat exp (SOME valbind)) s1 E s2
                  (PACKvep ^Bind_pack)) /\

    (* See Rule 135b, Case 2 *)

    (* Again, according to the Definition, patterns evaluate to VE/FAIL,
       but not to packets *)


(* Rule 137 *)

    (!s1 E s2 valbind VE. eval_valbind valbind s1 E s2 (VARENVvep VE) ==>
	eval_valbind (RECvalbind valbind) s1 E s2
                     (VARENVvep (rec_varenv VE))) /\

    (!s1 E s2 valbind p. eval_valbind valbind s1 E s2 (PACKvep p) ==>
	eval_valbind (RECvalbind valbind) s1 E s2 (PACKvep p))`--;

val eval_pred_DEF = new_definition ("eval_pred_DEF", eval_pred_def);

(* OK, now that we have our predicate, eval_pred, that tests if all
   the relations do what they are supposed to, we need to define the
   evaluation relations. We do this by basically saying that the
   evaluation relations are the smallest relations satisfying the
   predicate eval_pred. We do this by stating that, for a given
   relation, a tuple is in the relation if, for each possible evaluation
   relation (a relation that satisfies eval_pred) the tuple is in that
   relation. *)

val eval_atexp_DEF = new_definition 
    ("eval_atexp_DEF",
     --`eval_atexp ae s1 e s2 vp =
        !poss_eval_atexp poss_eval_exprow poss_eval_exp poss_eval_match
         poss_eval_mrule poss_eval_dec poss_eval_valbind.
        eval_pred poss_eval_atexp poss_eval_exprow poss_eval_exp
	 poss_eval_match poss_eval_mrule poss_eval_dec poss_eval_valbind ==>
	  poss_eval_atexp ae s1 e s2 vp`--);

val eval_exprow_DEF = new_definition 
    ("eval_exprow_DEF",
     --`eval_exprow er s1 e s2 rp =
        !poss_eval_atexp poss_eval_exprow poss_eval_exp poss_eval_match
         poss_eval_mrule poss_eval_dec poss_eval_valbind.
        eval_pred poss_eval_atexp poss_eval_exprow poss_eval_exp
         poss_eval_match poss_eval_mrule poss_eval_dec poss_eval_valbind ==>
	  poss_eval_exprow er s1 e s2 rp`--);

val eval_exp_DEF = new_definition 
    ("eval_exp_DEF",
     --`eval_exp ex s1 e s2 vp =
        !poss_eval_atexp poss_eval_exprow poss_eval_exp poss_eval_match
         poss_eval_mrule poss_eval_dec poss_eval_valbind.
        eval_pred poss_eval_atexp poss_eval_exprow poss_eval_exp
         poss_eval_match poss_eval_mrule poss_eval_dec poss_eval_valbind ==>
 	  poss_eval_exp ex s1 e s2 vp`--);

val eval_match_DEF = new_definition 
    ("eval_match_DEF",
     --`eval_match mat s1 v e s2 vpf =
        !poss_eval_atexp poss_eval_exprow poss_eval_exp poss_eval_match
         poss_eval_mrule poss_eval_dec poss_eval_valbind.
        eval_pred poss_eval_atexp poss_eval_exprow poss_eval_exp
         poss_eval_match poss_eval_mrule poss_eval_dec poss_eval_valbind ==>
	  poss_eval_match mat s1 v e s2 vpf`--);

val eval_mrule_DEF = new_definition 
    ("eval_mrule_DEF",
     --`eval_mrule mr s1 v e s2 vpf =
        !poss_eval_atexp poss_eval_exprow poss_eval_exp poss_eval_match
         poss_eval_mrule poss_eval_dec poss_eval_valbind.
        eval_pred poss_eval_atexp poss_eval_exprow poss_eval_exp
         poss_eval_match poss_eval_mrule poss_eval_dec poss_eval_valbind ==>
	  poss_eval_mrule mr s1 v e s2 vpf`--);

val eval_dec_DEF = new_definition 
    ("eval_dec_DEF",
     --`eval_dec d s1 e s2 ep =
        !poss_eval_atexp poss_eval_exprow poss_eval_exp poss_eval_match
         poss_eval_mrule poss_eval_dec poss_eval_valbind.
        eval_pred poss_eval_atexp poss_eval_exprow poss_eval_exp
         poss_eval_match poss_eval_mrule poss_eval_dec poss_eval_valbind ==>
	  poss_eval_dec d s1 e s2 ep`--);

val eval_valbind_DEF = new_definition 
    ("eval_valbind_DEF",
     --`eval_valbind vb s1 e s2 vep =
        !poss_eval_atexp poss_eval_exprow poss_eval_exp poss_eval_match
         poss_eval_mrule poss_eval_dec poss_eval_valbind.
        eval_pred poss_eval_atexp poss_eval_exprow poss_eval_exp
         poss_eval_match poss_eval_mrule poss_eval_dec poss_eval_valbind ==>
	  poss_eval_valbind vb s1 e s2 vep`--);


local
    val e_DEF =
        CONV_RULE (REDEPTH_CONV LEFT_IMP_EXISTS_CONV) eval_pred_DEF
    val eval_defs = [eval_atexp_DEF, eval_exprow_DEF, eval_exp_DEF,
		     eval_match_DEF, eval_mrule_DEF, eval_dec_DEF,
		     eval_valbind_DEF]
in
val EVAL_RULES_SATISFIED = store_thm("EVAL_RULES_SATISFIED",
(--`eval_pred eval_atexp eval_exprow eval_exp eval_match eval_mrule
    	      eval_dec eval_valbind`--),
EVAL_RULE_TAC (e_DEF :: eval_defs))

val eval_induction = save_thm("eval_induction",
PURE_ONCE_REWRITE_RULE[e_DEF]
(prove 
((--`!P_atexp P_exprow P_exp P_match P_mrule P_dec P_valbind.
eval_pred P_atexp P_exprow P_exp P_match P_mrule P_dec P_valbind ==>
((!ae s1 e s2 vp. eval_atexp ae s1 e s2 vp ==> P_atexp ae s1 e s2 vp) /\
 (!er s1 e s2 rp. eval_exprow er s1 e s2 rp ==> P_exprow er s1 e s2 rp) /\
 (!ex s1 e s2 vp. eval_exp ex s1 e s2 vp ==> P_exp ex s1 e s2 vp) /\
 (!mat s1 v e s2 vpf. eval_match mat s1 v e s2 vpf ==>
     P_match mat s1 v e s2 vpf) /\
 (!mr s1 v e s2 vpf. eval_mrule mr s1 v e s2 vpf ==>
     P_mrule mr s1 v e s2 vpf) /\
 (!d s1 e s2 ep. eval_dec d s1 e s2 ep ==> P_dec d s1 e s2 ep) /\
 (!vb s1 e s2 vep. eval_valbind vb s1 e s2 vep ==>
     P_valbind vb s1 e s2 vep))`--),
PURE_REWRITE_TAC eval_defs THEN REPEAT STRIP_TAC THEN RES_TAC)))
end;

