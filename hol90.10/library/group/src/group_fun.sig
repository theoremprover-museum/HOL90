(*======================================================================*)
(* FILE		: group_fun.sig						*)
(* DESCRIPTION  : gives the input signature GroupSig and body		*)
(*		  signature GroupFunSig for the functor GroupFunFunc.	*)
(*									*)
(*									*)
(* AUTHOR	: E. L. Gunter						*)
(* DATE		: 91.25.12						*)
(*									*)
(*======================================================================*)

(* Copyright 1991 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

(* The signature of the formal parameter to the functor GroupFunFunc *)
signature GroupSig =
    sig
	val IsGroupThm : CoreHol.Thm.thm
            (*
	       The conclusion of IsGroupThm must state GROUP(G,prod)
	       for some predicate G and operation prod.
	    *)

	val InstStructureName : string
	    (*
	       The string InstStructureName should be the name of the
	       structure to be created by applying the functor GroupFunFunc
	       to this structure as its argument
	    *)
    end



(* The signature of the body of the functor GroupFunFunc *)
signature GroupFunSig =
 sig
    type term
    type thm
    type tactic

	val GROUP_TAC : thm list -> tactic
	val GROUP_ELT_TAC : tactic
	    (*
	       GROUP_ELT_TAC is a tactic for solving routine goals of
	       group membership. 
	       GROUP_TAC is like GROUP_ELT_TAC, accecpt that you can supply
	       an additional list of theorems to be used in reducing goals.
	    *)

	val GROUP_RIGHT_ASSOC_TAC : term -> tactic
            (*
	       GROUP_RIGHT_ASSOC_TAC (prod (prod a b) c) :

	         A |-  t(prod (prod a b) c)
		----------------------------
		 A |-  t(prod a (prod b c))

	       GROUP_RIGHT_ASSOC_TAC uses GROUP_ELT_TAC to handle the group
	       membership requirements which arise.
	    *)

	val GROUP_LEFT_ASSOC_TAC : term -> tactic
	    (*
	       GROUP_LEFT_ASSOC_TAC (prod a (prod b c)) :

	         A |-  t(prod a (prod b c))
		----------------------------
		 A |-  t(prod (prod a b) c)

	       GROUP_LEFT_ASSOC_TAC uses GROUP_ELT_TAC to handle the group
	       membership requirements which arise.
	    *)

	val return_GROUP_thm : {elt_gp_thm_name:string,
				rewrites: thm list} -> thm
	    (*
	       return_GROUP_thm returns the intstantiated and simplfied
	       version of a theorem from elt_gp.th.

	       The string <elt_gp_thm_name> is the name of the elt_gp.th
	       theorem to be instantiated; the list of theorems <rewrites>
	       are for use in simplifying the instantiated theorem.
	    *)

	val include_GROUP_thm : {elt_gp_thm_name : string,
				 current_thm_name : string,
				 rewrites : thm list} -> thm
	    (*
	        include_GROUP_thm instantiates a named theorem from elt_gp.th,
		simplifies it, stores the result in the current theory, and
		returns it.

		The string <elt_gp_thm_name> is the name of the elt_gp.th
		theorem to be instantiated; the string <current_thm_name> is
		the name under which the resultant theorem will be store in
		the current theory; the list of theorems <rewrites> are for
		use in simplifying the instantiated theorem, prior to storing.
	     *)

	val return_GROUP_theory : {thm_name_prefix:string,
				   rewrites:thm list} -> (string * thm)list
	    (*
	       return_GROUP_theory returns the list of all pairs of names of
	       theorems, prefixed by the given string <thm_name_prefix>,
	       together with the instantiated and simplfied version of the
	       corresponding theorem from elt_gp.th.
	       
	       The string <thm_name_prefix> is the prefix to be added to
	       all names of the theorems from  elt_gp.th; the list of
	       theorems <rewrites> are for use in simplifying the
	       instantiated theorems.
	    *)

	val include_GROUP_theory : {thm_name_prefix:string,
				     rewrites: thm list} -> unit
            (*
	       include_GROUP_theory instantiates all the theorems from
	       elt_gp.th, simplifies them using <rewrites>, removes all
	       trivial theorems, stores the resulting theorems in the current
	       theory under their old name prefixed by the given string
	       <thm_name_prefix>, and binds them in the current environment
	       to the names under which they were stored.

	       The string <thm_name_prefix> is the prefix to be added to the
	       names of all the theorems from elt_gp.th after instantiation;
	       the list <rewrites> of theorems are for use in simplifying the
	       instantiated theorem, prior to storing.
	    *)

    end (* signature GroupFunSig *)
