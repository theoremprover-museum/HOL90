(*===========================================================================*)
(*                                                                           *)
(*   FILE:         gen_ind.sml  (previously num_tac.ml)                      *)
(*   AUTHORS:      E. L. Gunter                                              *)
(*   DATE:         23.3.89                                                   *)
(*   EDITOR:       Paul Curzon  July 1991                                    *)
(*   DESCRIPTION:  A rule and tactic for general induction.                  *)
(*   TRANSLATOR:   Paul Curzon   April 1993                                  *)
(*                                                                           *)
(*                                                                           *)
(*===========================================================================*)




structure Gen_induction : Gen_induction_sig =
struct

fun GEN_IND_ERR {function,message} =
               HOL_ERR{origin_structure = "Gen_induction",
                                           origin_function = function,
                                           message = message};


(*GEN_INDUCTION =
 |- !P. P 0 /\ (!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n)*)


(* GEN_INDUCT_RULE : thm -> thm -> thm

  A1 |- P(0)     A2 |- (!n. (!m. m < n ==> P(m)) ==> P(n))
--------------------------------------------------------
                  A1 u A2 |- !n. P(n)
*)

fun GEN_INDUCT_RULE (thm1:thm) (thm2:thm)=
(
 let val {Bvar = var1, Body = body1} = dest_forall(concl thm2)
 val {ant = test1, conseq = prop1} =  dest_imp body1
 val {Bvar = var2, Body = body2} = dest_forall test1
 val P = (--`\^var1.^prop1`--)
 val IND_thm = 
   ((fn thm => EQ_MP (((DEPTH_CONV BETA_CONV)o concl)thm) thm)
    (SPEC P 
     (EQ_MP 
      (ALPHA (--`!P.P 0/\(!n.(!m.m<n ==> P m) ==> P n) ==> (!n.P n)`--)
             (--`!P.P 0/\(!^var1.(!^var2.^var2<^var1 ==> P ^var2) ==> P ^var1)
                 ==> (!^var1.P ^var1)`--))
     (theorem "arithmetic" "GEN_INDUCTION")) ))
 in
 (MP IND_thm (CONJ thm1 thm2)) 
 end
)   handle HOL_ERR _ =>
	raise GEN_IND_ERR {function = "GEN_INDUCT_RULE",
			 message = "Bad theorem for GEN_INDUCT_RULE"}
;


(* GEN_INDUCT_TAC : tactic

                  [A] !n. P n
======================================================
 [A] P(0)        [A,(!m. m < n ==> P m)] P(n)
*)

fun GEN_INDUCT_TAC ((hypoth,aim):goal) =
(
 let val {Bvar = var, Body = prop} = dest_forall(aim)
 val var1=variant ((free_vars aim) @ (free_varsl hypoth)) var
 val prop1=subst [{residue = var1, redex = var}] prop
 val var2=variant (free_vars prop) (--`m:num`--)
 val assum=(--`!^var2.(^var2 < ^var1)==>
                 ^(subst [{residue = var2, redex = var}] prop)`--) 
 in
  ([(hypoth,(subst [{residue = (--`0`--), redex = var}] prop)),
    (assum :: hypoth,prop1)],
   (fn [thm1,thm2] => 
       ((fn thm => (EQ_MP (ALPHA (concl thm) aim) thm))
          (GEN_INDUCT_RULE thm1 (GEN var1 (DISCH assum thm2)))
       ) ))
 end

)    handle HOL_ERR _ =>
	raise GEN_IND_ERR {function = "GEN_INDUCT_TAC",
			 message = "Conclusion of goal has wrong form for GEN_INDUCT_TAC"}
;


end (* signature Gen_induction *)

