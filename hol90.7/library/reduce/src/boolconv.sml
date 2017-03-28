(*===========================================================================
== LIBRARY:     reduce (Part I)                                            ==
==                                                                         ==
== DESCRIPTION: Conversions for reducing boolean expressions.              ==
==                                                                         ==
== AUTHOR:      John Harrison                                              ==
==              University of Cambridge Computer Laboratory                ==
==              New Museums Site                                           ==
==              Pembroke Street                                            ==
==              Cambridge CB2 3QG                                          ==
==              England.                                                   ==
==                                                                         ==
==              jrh@cl.cam.ac.uk                                           ==
==                                                                         ==
== DATE:        18th May 1991                                              ==
==                                                                         ==
== TRANSLATOR:  Kim Dam Petersen (kimdam@tfl.dk)                           ==
============================================================================*)

functor Boolconv_funct (structure Dest : Dest_sig) : Boolconv_sig =
struct

fun failwith function = raise HOL_ERR{origin_structure = "Boolconv",
                                      origin_function = function,
                                      message = ""};
exception fail;

open Rsyntax;
open Dest;

(*-----------------------------------------------------------------------*)
(* NOT_CONV "~F"  = |-  ~F = T                                           *)
(* NOT_CONV "~T"  = |-  ~T = F                                           *)
(* NOT_CONV "~~t" = |- ~~t = t                                           *)
(*-----------------------------------------------------------------------*)

val NOT_CONV =
    let val [c1,c2,c3] = CONJUNCTS
	(prove((--`(~T = F) /\ (~F = T) /\ (!t. ~~t = t)`--),
	       REWRITE_TAC[NOT_CLAUSES]))
	and T = (--`T`--)
	and F = (--`F`--)
	and notop = (--`$~`--)
    in
	fn tm =>
	(let val [xn] = dest_op notop tm
	 in
	     if xn = T then c1
	     else if xn = F then c2
	     else
		 let val [xn] = dest_op notop xn
		 in
		     SPEC xn c3
		 end
	 end) handle _ => failwith "NOT_CONV"
    end;

(*-----------------------------------------------------------------------*)
(* AND_CONV "T /\ t" = |- T /\ t = t                                     *)
(* AND_CONV "t /\ T" = |- t /\ T = t                                     *)
(* AND_CONV "F /\ t" = |- F /\ t = F                                     *)
(* AND_CONV "t /\ F" = |- t /\ F = F                                     *)
(* AND_CONV "t /\ t" = |- t /\ t = t                                     *)
(*-----------------------------------------------------------------------*)

val AND_CONV =
    let val [c1,c2,c3,c4,c5] = CONJUNCTS
	(prove((--`(!t. T /\ t = t) /\
		   (!t. t /\ T = t) /\
		   (!t. F /\ t = F) /\
		   (!t. t /\ F = F) /\
		   (!t. t /\ t = t)`--),
	       REWRITE_TAC[AND_CLAUSES]))
	and T = (--`T`--)
	and F = (--`F`--)
	and andop = (--`$/\`--)
	and zv = (--`z:bool`--)
	and beqop = (--`$= :bool->bool->bool`--)
    in
	fn tm =>
	(let val [xn,yn] = dest_op andop tm
	 in
	     if xn = T then SPEC yn c1
	     else if yn = T then SPEC xn c2
	     else if xn = F then SPEC yn c3
	     else if yn = F then SPEC xn c4
	     else if xn = yn then SPEC xn c5
	     else if aconv xn yn then
		 SUBST [{thm= ALPHA xn yn, var= zv}]
		 (mk_comb{Rator=
			  mk_comb{Rator= beqop,
				  Rand= mk_comb{Rator= mk_comb{Rator= andop,
							       Rand= xn},
						Rand= zv}},
			  Rand= xn})
		 (SPEC xn c5)
	     else raise fail
	 end) handle _ => failwith "AND_CONV"
    end;

(*-----------------------------------------------------------------------*)
(* OR_CONV "T \/ t" = |- T \/ t = T                                      *)
(* OR_CONV "t \/ T" = |- t \/ T = T                                      *)
(* OR_CONV "F \/ t" = |- F \/ t = t                                      *)
(* OR_CONV "t \/ F" = |- t \/ F = t                                      *)
(* OR_CONV "t \/ t" = |- t \/ t = t                                      *)
(*-----------------------------------------------------------------------*)

val OR_CONV =
    let val [c1,c2,c3,c4,c5] = CONJUNCTS
	(prove((--`(!t. T \/ t = T) /\
		   (!t. t \/ T = T) /\
		   (!t. F \/ t = t) /\
		   (!t. t \/ F = t) /\
		   (!t. t \/ t = t)`--),
	       REWRITE_TAC[OR_CLAUSES]))
	and T = (--`T`--)
	and F = (--`F`--)
	and orop = (--`$\/`--)
	and zv = (--`z:bool`--)
	and beqop = (--`$= :bool->bool->bool`--)
    in
	fn tm =>
	(let val [xn,yn] = dest_op orop tm
	 in
	     if xn = T then SPEC yn c1
	     else if yn = T then SPEC xn c2
	     else if xn = F then SPEC yn c3
	     else if yn = F then SPEC xn c4
	     else if xn = yn then SPEC xn c5
	     else if aconv xn yn then
		 SUBST [{thm= ALPHA xn yn, var= zv}]
		 (mk_comb{Rator=
			  mk_comb{Rator= beqop,
				  Rand= mk_comb{Rator= mk_comb{Rator= orop,
							       Rand= xn},
						Rand= zv}},
			  Rand= xn})
		 (SPEC xn c5)
	    else raise fail
	 end) handle _ => failwith "OR_CONV"
    end;

(*-----------------------------------------------------------------------*)
(* IMP_CONV "T ==> t" = |- T ==> t = t                                   *)
(* IMP_CONV "t ==> T" = |- t ==> T = T                                   *)
(* IMP_CONV "F ==> t" = |- F ==> t = T                                   *)
(* IMP_CONV "t ==> F" = |- t ==> F = ~t                                  *)
(* IMP_CONV "t ==> t" = |- t ==> t = T                                   *)
(*-----------------------------------------------------------------------*)

val IMP_CONV =
    let val [c1,c2,c3,c4,c5] = CONJUNCTS
	(prove((--`(!t. (T ==> t) = t) /\
		   (!t. (t ==> T) = T) /\
		   (!t. (F ==> t) = T) /\
		   (!t. (t ==> F) = ~t) /\
		   (!t. (t ==> t) = T)`--),
	       REWRITE_TAC[IMP_CLAUSES]))
	and T = (--`T`--)
	and F = (--`F`--)
	and impop = (--`$==>`--)
	and zv = (--`z:bool`--)
	and beqop = (--`$= :bool->bool->bool`--)
    in
	fn tm =>
	(let val [xn,yn] = dest_op impop tm
	 in
	     if xn = T then SPEC yn c1
	     else if yn = T then SPEC xn c2
	     else if xn = F then SPEC yn c3
	     else if yn = F then SPEC xn c4
	     else if xn = yn then SPEC xn c5
	     else if aconv xn yn then
		 SUBST [{thm= ALPHA xn yn, var= zv}]
		 (mk_comb{Rator=
			  mk_comb{Rator= beqop,
				  Rand= mk_comb{Rator= mk_comb{Rator= impop,
							       Rand= xn},
						Rand= zv}},
			  Rand= T})
		 (SPEC xn c5)
	     else raise fail
	 end) handle _ => failwith "IMP_CONV"
    end;

(*-----------------------------------------------------------------------*)
(* BEQ_CONV "T = t" = |- T = t = t                                       *)
(* BEQ_CONV "t = T" = |- t = T = t                                       *)
(* BEQ_CONV "F = t" = |- F = t = ~t                                      *)
(* BEQ_CONV "t = F" = |- t = F = ~t                                      *)
(* BEQ_CONV "t = t" = |- t = t = T                                       *)
(*-----------------------------------------------------------------------*)

val BEQ_CONV =
    let val [c1,c2,c3,c4,c5] = CONJUNCTS
	(prove((--`(!t. (T = t) = t) /\
		   (!t. (t = T) = t) /\
		   (!t. (F = t) = ~t) /\
		   (!t. (t = F) = ~t) /\
		   (!t:bool. (t = t) = T)`--),
	       REWRITE_TAC[EQ_CLAUSES]))
	and T = (--`T`--)
	and F = (--`F`--)
	and beqop = (--`$= :bool->bool->bool`--)
	and zv = (--`z:bool`--)
    in
	fn tm =>
	(let val [xn,yn] = dest_op beqop tm
	 in
	     if xn = T then SPEC yn c1
	     else if yn = T then SPEC xn c2
	     else if xn = F then SPEC yn c3
	     else if yn = F then SPEC xn c4
	     else if xn = yn then SPEC xn c5
	     else if aconv xn yn then EQT_INTRO (ALPHA xn yn)
	     else raise fail
	 end) handle _ => failwith "BEQ_CONV"
    end;

(*-----------------------------------------------------------------------*)
(* COND_CONV "F => t1 | t2" = |- (T => t1 | t2) = t2                     *)
(* COND_CONV "T => t1 | t2" = |- (T => t1 | t2) = t1                     *)
(* COND_CONV "b => t  | t"  = |- (b => t | t)   = t                      *)
(*-----------------------------------------------------------------------*)

val COND_CONV =
    let val [c1,c2,c3] = CONJUNCTS
	(prove((--`(!t1 t2. (T => t1 | t2) = (t1:'a)) /\
	           (!t1 t2. (F => t1 | t2) = (t2:'a)) /\
		   (!b t. (b => t | t) = (t:'a))`--),
	       REWRITE_TAC[COND_CLAUSES, COND_ID]))
	and T = (--`T`--)
	and F = (--`F`--)
	and ty = (==`:'a`==)
    in
	fn tm =>
	(let val {cond= b, larm= t1, rarm= t2} = dest_cond tm
	 in
	     if b = T then SPECL[t1,t2] (INST_TYPE[{residue= type_of t1,
						    redex= ty}] c1)
	     else if b = F then SPECL[t1,t2] (INST_TYPE[{residue= type_of t1,
							 redex= ty}] c2)
	     else if t1 = t2 then SPECL[b,t1] (INST_TYPE[{residue= type_of t1,
							  redex= ty}] c3)
	     else if aconv t1 t2 then
		 TRANS (AP_TERM (rator tm) (ALPHA t2 t1))
		 (SPECL [b, t1] (INST_TYPE [{residue= type_of t1,
					     redex= ty}] c3))
		  else raise fail
	 end) handle _ => failwith "COND_CONV"
    end;

end
