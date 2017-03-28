load_theory "List";
load_library_in_place num_lib; 
load_library_in_place arith_lib; 

Add_to_sml.add_theory_to_sml "arithmetic"; 
Add_to_sml.add_theory_to_sml "prim_rec"; 
Add_to_sml.add_theory_to_sml "num";

use "arith_thms.sml";

Add_to_sml.add_theory_to_sml "List";
Add_to_sml.add_theory_to_sml "pair";

(*-----------------------------------------------------------------------*)
(* Derived inference rules   	    					 *)
(*-----------------------------------------------------------------------*)

val MATCH_EQ_MP = fn eq => fn lh => EQ_MP (PART_MATCH lhs eq (concl lh)) lh;

val REWRITE1_TAC = fn t => REWRITE_TAC[t];

fun ARITH_TAC (asml,gl) =
    let val a = filter is_presburger asml in
    (MAP_EVERY (MP_TAC o ASSUME) a THEN CONV_TAC ARITH_CONV)(asml,gl)
    end;

val ARITH_PROVE = EQT_ELIM o ARITH_CONV;


(* ----------------------------------------------------------------------
 * Some simple list reasoning functions, in order to avoid loading in the
 * entire library of lists.
 *************************************************************************)

fun WORD_ERR{function,message} = 
     HOL_ERR{origin_structure="Word library",
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
   handle _ => raise WORD_ERR{function="LIST_INDUCT", message = ""};


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

(* --------------------------------------------------------------------*)
(*                                                                     *)
(* SNOC_INDUCT_TAC                                                     *)
(*                                                                     *)
(*             [A] !l.t[l]                                             *)
(*  ================================                                   *)
(*   [A] t[[]],  [A,t[l]] !h. t[SNOC x t]                              *)
(*                                                                     *)
(* --------------------------------------------------------------------*)
(* PC 11/7/94 *)

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;


(* --------------------------------------------------------------------*)
(* Definition by primitive recursion for lists		               *)
(* (For compatibility of new/old HOL.)			               *)
(* --------------------------------------------------------------------*)

local val list_Axiom = theorem "list" "list_Axiom"
in
fun new_list_rec_definition (name,tm) =
  new_recursive_definition{name=name,rec_axiom=list_Axiom,def=tm,fixity=Prefix}

fun new_infix_list_rec_definition (name,tm,prec) =
   new_recursive_definition {name=name,rec_axiom=list_Axiom,def=tm,
                             fixity=Infix prec}
end;


(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_INDUCT_TAC : tactic                                             *)
(*  A ?- !l1 l2. (LENGTH l1 = LENGTH l2) ==> t[l1, l2]                       *)
(* ==================================================== EQ_LENGTH_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(CONS h l1)/l1,(CONS h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_INDUCT_TAC =
 LIST_INDUCT_TAC THENL[
 LIST_INDUCT_TAC THENL[
   REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
   REWRITE_TAC[LENGTH,SUC_NOT]],
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_SUC,INV_SUC_EQ]
   THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];


(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_SNOC_INDUCT_TAC : tactic                                        *)
(* A ?- !l1 l2.(LENGTH l1 = LENGTH l2) ==> t[l1,l2]                          *)
(* =============================================== EQ_LENGTH_SNOC_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(SNOC h l1)/l1,(SNOC h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_SNOC_INDUCT_TAC =
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
      REWRITE_TAC[LENGTH,LENGTH_SNOC,SUC_NOT]],
     GEN_TAC THEN SNOC_INDUCT_TAC
     THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_SUC,INV_SUC_EQ]
     THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];

