val SET_SPEC_TAC = CONV_TAC (DEPTH_CONV Gspec.SET_SPEC_CONV);
val SET_SPEC_RULE = CONV_RULE (DEPTH_CONV Gspec.SET_SPEC_CONV);

fun IN_TAC conv = CONV_TAC (DEPTH_CONV (Fset_conv.IN_CONV conv));
fun IN_RULE conv = CONV_RULE (DEPTH_CONV (Fset_conv.IN_CONV conv));

val RIGHT_AND_EXISTS_TAC = CONV_TAC (DEPTH_CONV RIGHT_AND_EXISTS_CONV);
val LEFT_AND_EXISTS_TAC = CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV);
val RIGHT_OR_EXISTS_TAC = CONV_TAC (DEPTH_CONV RIGHT_OR_EXISTS_CONV);
val LEFT_OR_EXISTS_TAC = CONV_TAC (DEPTH_CONV LEFT_OR_EXISTS_CONV);

fun ELIM_SELECT_RULE thm1 thm2 =
   let val {Bvar=vl, Body=tm} =
           dest_select (rhs (snd (strip_forall (concl thm2))))
       val imp = concl thm1
       val alpha = Type.mk_vartype "'a"
       val {ant=imp', conseq=LR} = dest_imp tm
       val {lhs=L,rhs=R} = dest_eq LR
       val Ea = (subst (fst (match_term imp' imp)) R)
       val th1 =
          DISCH_ALL
	    (ADD_ASSUM imp 
              (SPEC Ea (INST_TYPE [alpha |-> type_of L] EQ_REFL)))
   in
	ONCE_REWRITE_RULE
	    [GEN_ALL (SYM (SPEC_ALL thm2))]
	    (MP
	     (SELECT_RULE
	      (EXISTS
	       ((mk_exists{Bvar=L,
		           Body=(mk_imp{ant=imp,
				        conseq=(mk_eq {lhs=L,rhs=Ea})})}), Ea)
	       th1))
	     thm1)
   end
   handle HOL_ERR {origin_structure = origin_structure,
	           origin_function = origin_function,message = message}
   => raise HOL_ERR {origin_structure=origin_structure,
                     origin_function="ELIM_SELECT_RULE",
	             message=(origin_function^": "^message)};


(* ----------------------------------------------------------------------
 * Some simple list reasoning functions, in order to avoid loading in the
 * entire library of lists.
 *************************************************************************)

fun CSP_ERR{function,message} = 
     HOL_ERR{origin_structure="CSP library",
             origin_function = function,
             message = message};
open Rsyntax;

val % = Parse.term_parser;
val alpha_ty = ==`:'a`==
val bool_ty = ==`:bool`==


(* --------------------------------------------------------------------*)
(*   LIST_INDUCT: (thm # thm) -> thm			               *)
(*							               *)
(*     A1 |- t[[]]      A2 |- !tl. t[tl] ==> !h. t[CONS h t]           *)
(* ----------------------------------------------------------          *)
(*                   A1 u A2 |- !l. t[l]			       *)
(*							               *)
(* --------------------------------------------------------------------*)

fun LIST_INDUCT (base,step) =
   let val {Bvar,Body} = dest_forall(concl step)
       val {ant,conseq} = dest_imp Body
       val {Bvar=h,Body=con} = dest_forall conseq
       val P  = %`\^Bvar.^ant` 
       val b1 = genvar bool_ty
       val b2 = genvar bool_ty
       val base'  = EQ_MP (SYM(BETA_CONV (%`^P []`))) base 
       val step'  = DISCH ant (SPEC h (UNDISCH(SPEC Bvar step)))
       val hypth  = SYM(RIGHT_BETA(REFL (%`^P ^Bvar`)))
       val concth = SYM(RIGHT_BETA(REFL (%`^P(CONS ^h ^Bvar)`)))
       val IND    = SPEC P (INST_TYPE [{redex=alpha_ty, residue = type_of h}]
                                      list_INDUCT)
       val th1 = SUBST[{var=b1,thm=hypth},{var=b2,thm=concth}]
                      (%`^(concl step') = (^b1 ==> ^b2)`)
                      (REFL (concl step'))
       val th2 = GEN Bvar (DISCH (%`^P ^Bvar`)
                                 (GEN h(UNDISCH (EQ_MP th1 step'))))
       val th3 = SPEC Bvar (MP IND (CONJ base' th2))
   in
   GEN Bvar (EQ_MP (BETA_CONV(concl th3)) th3)
   end
   handle _ => raise CSP_ERR{function="LIST_INDUCT", message = ""};


(* --------------------------------------------------------------------*)
(*							               *)
(* LIST_INDUCT_TAC					               *)
(*							               *)
(*             [A] !l.t[l]				               *)
(*  ================================			               *)
(*   [A] t[[]],  [A,t[l]] !h. t[CONS h t]		               *)
(*							               *)
(* --------------------------------------------------------------------*)

val LIST_INDUCT_TAC  = INDUCT_THEN list_INDUCT ASSUME_TAC;

local val list_Axiom = theorem "list" "list_Axiom"
in
fun new_list_rec_definition (name,tm) =
  new_recursive_definition{name=name,rec_axiom=list_Axiom,def=tm,fixity=Prefix}

fun new_infix_list_rec_definition (name,tm,prec) =
   new_recursive_definition {name=name,rec_axiom=list_Axiom,def=tm,
                             fixity=Infix prec}
end;

