(*======================================================================*)
(* FILE		: integer_tactics.ml					*)
(* DESCRIPTION  : Defines rules and tactics for various arguments       *)
(*                special to the  integers.                             *)
(*									*)
(* AUTHOR	: E. L. Gunter						*)
(* DATE		: 89.7.17						*)
(* TRANSLATED   : 92.7.23						*)
(*									*)
(*======================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)


structure IntegerTactics : IntegerTactics_sig =

struct

(* structure loadIntegerthry = loadIntegerThry; *)

 type term = CoreHol.Term.term
 type thm = CoreHol.Thm.thm
 type tactic = Abbrev.tactic
 type conv = Abbrev.conv

open Exception Lib CoreHol;
open Type Term Dsyntax Thm Theory Drule Tactical Tactic Conv Parse;
open Rsyntax utilsLib;


fun INT_TAC_ERR {function, message} =
      HOL_ERR{origin_structure = "IntegerTactics",
	      origin_function = function,
	      message = message}

fun pass_ERR {function, error = HOL_ERR {origin_structure,
					 origin_function,
					 message}} =
    INT_TAC_ERR {function = function,
		 message = " From "^origin_structure^"."^origin_function^":\n"^
		           message}
  | pass_ERR {error,...} = raise error



(*---------------------------------------------------------------------------
 INT_CASES = |- !P. (!m. P(INT m)) /\ (!m. P(neg(INT m))) ==> (!M. P M) *)

(* INT_CASES_RULE : {int_case_thm:thm, neg_int_case_thm:thm} -> thm

  A1 |- !n1:num. P(INT n1)   A2 |- !n2:num. P(neg(INT n2))
------------------------------------------------------------
                  A1 u A2 |- !M:integer. P M
 *---------------------------------------------------------------------------*)

fun INT_CASES_RULE {int_case_thm = thm1, neg_int_case_thm = thm2} =
    let val {Bvar = var1,Body = prop1} = dest_forall (concl thm1)
	     handle HOL_ERR _ =>
		 raise INT_TAC_ERR {function = "INT_CASES_RULE",
				    message = "int_case_thm not forall"}
	val {Bvar = var2,Body = prop2} = dest_forall (concl thm2)
	     handle HOL_ERR _ =>
		 raise INT_TAC_ERR {function = "INT_CASES_RULE",
				    message = "neg_int_case_thm not forall"}
	val M = variant
	           ((var1::free_vars prop1)@(var2::free_vars prop2))
		   (--`M:integer`--)
	val P = subst
	         [{residue = M,
		   redex = mk_comb{Rator = (--`INT`--), Rand = var1}}]
		 prop1
		 handle HOL_ERR _ =>
		     raise INT_TAC_ERR {function = "INT_CASES_RULE",
                         message ="int_case_thm is not quantified over :num"}
    in
		   MP (BETA_RULE (SPEC
				  (mk_abs{Bvar = M,Body = P})
				  (theorem "integer" "INT_CASES")))
		      (CONJ thm1 thm2)
		      handle e =>
			  raise pass_ERR{function = "INT_CASES_RULE",
					 error = e}
    end



(* INT_CASES_TAC : tactic

                         [A] !N:integer. P N
============================================================================
 [A] !n:num. P (INT n)   [A,!n:num. P (INT n)] !n:num. P (neg(INT n))

  INT_CASES_TAC allows a reduction of a problem about all integers to
  two problems about natural numbers.  After making this reduction one
  can proceed by induction on the natural numbers.
*)


fun INT_CASES_TAC (asl,gl) =
    let
	val {Bvar,Body = prop} = dest_forall gl
	     handle HOL_ERR _ =>
		 raise INT_TAC_ERR {function = "INT_CASES_TAC",
				    message = "goal not forall"}
	val n = variant (Bvar :: free_vars prop) (--`n:num`--)
	val fst_gl =
	      mk_forall
	       {Bvar = n,
		Body = subst [{residue = mk_comb{Rator = (--`INT`--),
						 Rand = n},
			       redex = Bvar}]
			     prop}
	       handle e =>
		   raise pass_ERR{function = "INT_CASES_TAC", error = e}
	val snd_gl =
	      mk_forall
	       {Bvar = n,
		Body = subst [{residue = mk_comb{Rator = (--`neg`--),
						 Rand =
						   mk_comb{Rator = (--`INT`--),
							   Rand = n}},
			       redex = Bvar}]
			     prop}
	       handle e =>
		   raise pass_ERR{function = "INT_CASES_TAC", error = e}
    in
	    ([(asl,fst_gl),(fst_gl::asl,snd_gl)],
	     fn [thm1,thm2] =>
	        CONV_RULE (GEN_ALPHA_CONV Bvar)
		(INT_CASES_RULE {int_case_thm = thm1,
				 neg_int_case_thm =
				   MP (DISCH (concl thm1) thm2) thm1})
	      | _ => raise INT_TAC_ERR{function = "INT_CASES_TAC",
				       message = "wrong number of theorems"})
	    handle e => raise pass_ERR{function = "INT_CASES_TAC", error = e}
    end


(****************************************************************************)

(* SIMPLE_INT_CASES_RULE and SIMPLE_INT_CASES_TAC allow a reduction of a
  problem about all integers to the three cases where the integer is
  positive, where it is negative, and where it is zero.
*)

(* SIMPLE_INT_CASES_RULE : {pos_case_thm:thm,
			    neg_case_thm:thm,
			    zero_case_thm:thm} -> thm

      A1 |- !N:integer. POS N ==> P N 
      A2 |- !N:integer. NEG N ==> P N
              A3 |- P (INT 0)
     ---------------------------------
      A1 u A2 u A3 |- !N:integer. P N
*)

fun SIMPLE_INT_CASES_RULE {pos_case_thm = thm1,
			   neg_case_thm = thm2,
			   zero_case_thm = thm3} =
    let
        val (V,prop) =
		  (fn{Bvar,Body}=>(Bvar,#conseq(dest_imp Body)))
		  (dest_forall (concl thm1))
	val N = variant
	         (all_varsl (concl thm3 ::(hyp thm1 @ hyp thm2 @ hyp thm3)))
		 V
	val PN = subst [{residue = N, redex = V}] prop
	val Neq = mk_eq{lhs=N,rhs = (--`INT 0`--)}
	val NEG_N = mk_comb{Rator =(--`NEG`--),Rand = N}
	val Thm3 = DISCH Neq
	                 (EQ_MP (SYM (BETA_RULE
                            (AP_TERM (mk_abs{Bvar=N,Body=PN}) (ASSUME Neq))))
                            thm3)
	val disj = mk_disj{disj1 = NEG_N, disj2 = Neq}
	val thm4 = DISCH disj
			 (MP (MP (MP (SPECL [PN,NEG_N,Neq] OR_ELIM_THM)
				     (ASSUME disj))
			         (SPEC N thm2))
			     Thm3)
    in
	GEN N (MP (MP
		   (MP(SPECL [PN,mk_comb{Rator=(--`POS`--),Rand=N},disj]
		             OR_ELIM_THM)
		      (CONJUNCT1 (SPEC N (theorem"integer" "TRICHOTOMY"))))
		   (SPEC N thm1))
	          thm4)
    end handle e => raise pass_ERR{function = "SIMPLE_INT_CASES_RULE",
				   error = e}


(* SIMPLE_INT_CASES_TAC : tactic

                   [A] !N:integer. P N
==============================================================================
 [A] !N. POS N ==> P N  [A,!N. POS N ==> P N] !N. NEG N ==> P N  [A] P(INT 0)

*)


fun SIMPLE_INT_CASES_TAC (asl,gl) =
    let
	val {Bvar=N,Body=prop} = dest_forall gl
	val fst_gl = mk_forall{Bvar =N,
			       Body=mk_imp{ant=mk_comb{Rator=(--`POS`--),
						       Rand=N},
					   conseq=prop}}
	val snd_gl = mk_forall{Bvar =N,
			       Body=mk_imp{ant=mk_comb{Rator=(--`NEG`--),
						       Rand=N},
					   conseq=prop}}
	val trd_gl = subst [{residue=(--`INT 0`--),redex=N}] prop
    in
	([(asl,fst_gl),(fst_gl::asl,snd_gl),(asl,trd_gl)],
	 fn [thm1,thm2,thm3]=>
	      SIMPLE_INT_CASES_RULE {pos_case_thm = thm1,
				     neg_case_thm =
				       MP(DISCH(concl thm1)thm2)thm1,
				     zero_case_thm= thm3}
	  | _ => raise INT_TAC_ERR{function = "SIMPLE_INT_CASES_TAC",
				   message = "wrong number of theorems"})
    end handle e => raise pass_ERR{function = "SIMPLE_INT_CASES_TAC",
				   error = e}




(****************************************************************************)

(* INT_MIN_RULE, INT_MAX_RULE, INT_MIN_TAC, and INT_MAX_TAC are for
  showing that minimum and maximun elements for bounded subsets of
  the integers exist.
*)

(* INT_MIN_RULE : {non_empty_thm:thm, bnd_below_thm:thm} -> thm

  A1 |- ?M:integer. S1 M    A2 |- ?K1. !N. N below K1 ==> ~S1 N
  -------------------------------------------------------------
     A1 u A2 |- ?GLB. S1 GLB /\ (!N1. N below GLB ==> ~S1 N)

*)

fun INT_MIN_RULE {non_empty_thm, bnd_below_thm} =
    let
	val S1 = rand(concl non_empty_thm)
	val DISC1 = SPEC S1 (theorem"integer" "DISCRETE")
	val DISC = if is_abs S1
		       then CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) DISC1
		   else DISC1
    in
	MP (CONJUNCT1 (MP DISC non_empty_thm)) bnd_below_thm
    end handle e => raise pass_ERR{function = "INT_MIN_RULE",
				   error = e}



(* INT_MIN_TAC : term -> tactic
                 S1

                   [A] Goal
   =============================================
     [A, S1 MIN, !N. N below MIN ==> ~S1 N] Goal
     [A] ?M:integer. S1 M
     [A, S1 M] ?LB. !N. N below LB ==> ~S1 N
*)

fun INT_MIN_TAC S1 (asl,gl) =
    if not (type_of S1 = (==`:integer -> bool`==))
	then raise INT_TAC_ERR{function = "INT_MIN_TAC",
			       message =
			        "Term is not a predicate over the integers."}
    else
	(let
	     val varlist = all_vars S1 @ all_vars gl @ all_varsl asl
	     val M = variant varlist (--`M:integer`--)
	     val N = variant varlist (--`N:integer`--)
	     val MIN = variant varlist (--`GLB:integer`--)
	     val LB = variant varlist (--`LB:integer`--)
	     val SM = rhs (concl (DEPTH_CONV BETA_CONV (mk_comb{Rator =S1,
								Rand = M})))
	     val SMIN = subst [{residue = MIN, redex = M}] SM
	     val SN = subst [{residue = N,redex = M}] SM
	     val negSN = mk_neg SN
	     val N_below = mk_comb {Rator = (--`$below`--),Rand = N}
	     val N_below_MIN_imp =
		 mk_forall
	          {Bvar = N,
		   Body = mk_imp
		           {ant = mk_comb{Rator = N_below,Rand = MIN},
			    conseq = negSN}}
	     val SMIN_conj = mk_conj{conj1 = SMIN,conj2 = N_below_MIN_imp}
	     val choose_MIN = mk_select{Bvar = MIN, Body = SMIN_conj}
	     val thm5 = ASSUME SMIN_conj
	 in
	     ([(SMIN::N_below_MIN_imp::asl,gl),
	       (asl,mk_exists{Bvar = M, Body = SM}),
	       (SM::asl,
		mk_exists
	        {Bvar = LB,
		 Body = mk_forall
		         {Bvar =N,
			  Body = mk_imp
		                  {ant = mk_comb{Rator = N_below,Rand = LB},
				   conseq = negSN}}})],
	     fn [thm1,thm2,thm3] =>
	      let
		  val thm4 =
		        SELECT_RULE
			 (INT_MIN_RULE 
			  {non_empty_thm = thm2,
			   bnd_below_thm =
			     MP (SPEC (mk_select {Bvar = M, Body = SM})
			              (GEN M (DISCH SM thm3)))
			        (SELECT_RULE thm2)})
	      in
		  MP (SPEC choose_MIN (GEN MIN (DISCH SMIN_conj
		       (PROVE_HYP (CONJUNCT2 thm5)
			(PROVE_HYP (CONJUNCT1 thm5) thm1)))))
		     thm4
	      end
	      | _ => raise INT_TAC_ERR{function = "INT_MIN_TAC",
				       message = "wrong number of theorems"})
	 end handle e => raise pass_ERR{function = "INT_MIN_TAC",
					error = e})


(* INT_MAX_RULE : {non_empty_thm:thm, bnd_above_thm:thm} -> thm

  A1 |- ?M:integer. S1 M    A2 |- ?K1. !N. K1 below N ==> ~S1 N
  -------------------------------------------------------------
     A1 u A2 |- ?MAX. S1 MAX /\ (!N1. MAX below N1 ==> ~S1 N1)
*)

fun INT_MAX_RULE {non_empty_thm, bnd_above_thm} =
    let
	val S1 = rand(concl non_empty_thm)
	val DISC1 = SPEC S1 (theorem "integer" "DISCRETE")
	val DISC = if is_abs S1
		       then CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) DISC1
		   else DISC1
    in
	MP (CONJUNCT2 (MP DISC non_empty_thm)) bnd_above_thm
    end handle e => raise pass_ERR{function = "INT_MIN_RULE",
				   error = e}



(* INT_MAX_TAC : term -> tactic
                 S1

                   [A] Goal
   =============================================
     [A, S1 MAX. !N. MAX below N ==> ~S1 N] Goal
     [A] ?M:integer. S1 M
     [A, S1 M] ?UB. !N. UB below N ==> ~S1 N
*)

fun INT_MAX_TAC S1 (asl,gl) =
    if not (type_of S1 = (==`:integer -> bool`==))
	then raise INT_TAC_ERR{function = "INT_MAX_TAC", 
                               message =
			        "Term is not a predicate over the integers."}
    else
	(let
             val varlist = all_vars S1 @ all_vars gl @ all_varsl asl
             val M = variant varlist (--`M:integer`--)
             val N = variant varlist (--`N:integer`--)
	     val MAX = variant varlist (--`LUB:integer`--)
	     val UB = variant varlist (--`UB:integer`--)

             val SM = rhs (concl (DEPTH_CONV BETA_CONV (mk_comb{Rator =S1,
                                                                Rand = M})))
	     val SMAX = subst [{residue = MAX, redex = M}] SM
             val SN = subst [{residue = N,redex = M}] SM
             val negSN = mk_neg SN
	     val MAX_below_N_imp =
                 mk_forall
                  {Bvar = N,
                   Body = mk_imp
                           {ant = mk_comb{Rator = mk_comb
					           {Rator = (--`$below`--),
						    Rand = MAX},
					  Rand = N},
                            conseq = negSN}}
	     val SMAX_conj = mk_conj{conj1 = SMAX,conj2 = MAX_below_N_imp}
	     val choose_MAX = mk_select{Bvar = MAX, Body = SMAX_conj}
	     val thm5 = ASSUME SMAX_conj
	 in
	     ([(SMAX::MAX_below_N_imp::asl,gl),
	       (asl,mk_exists{Bvar = M, Body = SM}),
	       (SM::asl,
                mk_exists
                {Bvar = UB,
                 Body = mk_forall
                         {Bvar =N,
                          Body = mk_imp
                                  {ant = mk_comb
				          {Rator = mk_comb
                                                    {Rator = (--`$below`--),
						     Rand = UB},
					   Rand = N},
				   conseq = negSN}}})],
             fn [thm1,thm2,thm3] =>
              let
                  val thm4 =
                        SELECT_RULE
                         (INT_MAX_RULE
			  {non_empty_thm = thm2,
			   bnd_above_thm =
			     MP (SPEC (mk_select {Bvar = M, Body = SM})
				      (GEN M (DISCH SM thm3)))
			        (SELECT_RULE thm2)})
	      in
		  MP (SPEC choose_MAX (GEN MAX (DISCH SMAX_conj
                       (PROVE_HYP (CONJUNCT2 thm5)
			(PROVE_HYP (CONJUNCT1 thm5) thm1)))))
		     thm4
	      end
               | _ => raise INT_TAC_ERR{function = "INT_MAX_TAC",
					message = "wrong number of theorems"})
	 end handle e => raise pass_ERR{function = "INT_MAX_TAC",
					error = e})

(***************************************************************************)


(* INT_RIGHT_ASSOC_TAC : term -> tactic  (term = (a plus b) plus c)

   A |-  t((a plus b) plus c)
---------------------------------
   A |-  t(a plus (b plus c))

*)

fun INT_RIGHT_ASSOC_TAC tm (asl,gl) =
    if (not((rator (rator tm)) = (--`$plus`--)) orelse
	not((rator(rator(rand (rator tm)))) = (--`$plus`--)))
	handle HOL_ERR _ =>
	    raise INT_TAC_ERR{function = "INT_RIGHT_ASSOC_TAC",
			      message =
			      "Term not of form (--`(a plus b) plus c`--)."}
	then raise INT_TAC_ERR{function = "INT_RIGHT_ASSOC_TAC",
			       message =
			       "Term not of form (--`(a plus b) plus c`--)."}
    else
	let
	    val a = rand(rator(rand (rator tm)))
	    val b = rand(rand (rator tm))
	    val c = rand tm
	in
	    SUBST1_TAC (SPECL [a,b,c] (theorem"integer" "PLUS_GROUP_ASSOC"))
	               (asl,gl)
	end


(* INT_LEFT_ASSOC_TAC : term -> tactic  (term = a plus (b plus c))

   A |-  t(a plus (b plus c))
---------------------------------
   A |-  t((a plus b) plus c)

*)

fun INT_LEFT_ASSOC_TAC tm (asl,gl) =
    if (not((rator (rator tm)) = (--`$plus`--)) orelse
	not((rator(rator (rand tm)))= (--`$plus`--)))
	handle HOL_ERR _ =>
	    raise INT_TAC_ERR{function = "INT_RIGHT_ASSOC_TAC",
			      message =
			      "Term not of form (--`(a plus b) plus c`--)."}
        then raise INT_TAC_ERR{function = "INT_RIGHT_ASSOC_TAC",
                               message =
                               "Term not of form (--`(a plus b) plus c`--)."}
    else
	let
	    val a = rand(rator tm)
	    val b = rand(rator (rand tm))
	    val c = rand (rand tm)
	in
	    SUBST1_TAC (SYM (SPECL [a,b,c] 
                            (theorem"integer" "PLUS_GROUP_ASSOC")))
	    (asl,gl)
	end;

end  (* structure IntegerTactics *)
