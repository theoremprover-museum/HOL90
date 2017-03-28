(*======================================================================*)
(* FILE		: mk_elt_gp.sml						*)
(* DESCRIPTION  : creates the standard first-order theory of groups.	*)
(*                The resulting theory file is called elt_gp.th		*)
(*									*)
(*									*)
(* AUTHOR	: E. L. Gunter						*)
(* DATE		: 89.3.21						*)
(* TRANSLATED   : 91.22.12						*)
(*									*)
(*======================================================================*)

(* Copyright 1991 by AT&T Bell Laboratories *)

new_theory "elt_gp";

(*
   A group is a set G together with a binary operation prod such that:
     0. G is closed under prod
     1. prod is associative
     2. there exists a left identity e for prod
     3. every element of G has a left inverse in G with respect to e.
*)

val GROUP_DEF = new_definition("GROUP_DEF",
  (--`GROUP ((G:'a -> bool),prod) =
         (!x.!y.((G x) /\ (G y)) ==> (G (prod x y))) /\
         (!x.!y.!z.((G x) /\ (G y) /\ (G z)) ==>
            ((prod (prod x y) z) = (prod x (prod y z)))) /\
         (?e.(G e) /\ (!x.(G x) ==> (prod e x = x)) /\
            (!x.(G x) ==> ?y.(G y) /\ (prod y x = e)))`--))

(*
val GROUP_DEF =
  |- !G prod.
       GROUP (G,prod) =
       (!x y. G x /\ G y ==> G (prod x y)) /\
       (!x y z.
         G x /\ G y /\ G z ==>
         (prod (prod x y) z = prod x (prod y z))) /\
       (?e.
         G e /\
         (!x. G x ==> (prod e x = x)) /\
         (!x. G x ==> (?y. G y /\ (prod y x = e)))) :thm
*)


val CLOSURE =
      save_thm("CLOSURE",
	       DISCH_ALL
	       (CONJUNCT1
		(UNDISCH
		 (fst (EQ_IMP_RULE (SPEC_ALL GROUP_DEF))))))

(*
val CLOSURE =
  |- GROUP (G,prod) ==> (!x y. G x /\ G y ==> G (prod x y)) :thm
*)


val ID_DEF = new_definition ("ID_DEF",
  (--`ID(G,prod):'a =
          @e.(G e /\ (!x. G x ==> (prod e x = x)) /\
            (!x. G x ==> ?y. G y /\ (prod y x = e)))`--))

(*
val ID_DEF =
  |- !G prod.
       ID (G,prod) =
       (@e.
         G e /\
         (!x. G x ==> (prod e x = x)) /\
         (!x. G x ==> (?y. G y /\ (prod y x = e)))) :thm
*)

val GROUP_ASSOC =
      save_thm ("GROUP_ASSOC",
		DISCH_ALL
		(CONJUNCT1
		 (CONJUNCT2
		  (UNDISCH 
		   (fst (EQ_IMP_RULE (SPEC_ALL GROUP_DEF)))))))

(*
val GROUP_ASSOC =
  |- GROUP (G,prod) ==>
     (!x y z.
       G x /\ G y /\ G z ==> (prod (prod x y) z = prod x (prod y z)))
  :thm
*)


val ID_LEMMA = store_thm("ID_LEMMA",
(--`GROUP(G,prod) ==> 
      G (ID(G,prod):'a) /\
      (!x. G x ==> (prod (ID(G,prod)) x = x)) /\
      (!x. G x ==> (prod x (ID(G,prod)) = x)) /\
      (!x. G x ==> ?y. G y /\ (prod y x = ID(G,prod)))`--),
    let
	val id_facts =
	    PURE_ONCE_REWRITE_RULE
	     [(SYM(SPEC_ALL ID_DEF))]
	     (SELECT_RULE
	      (CONJUNCT2
	       (CONJUNCT2
		(PURE_ONCE_REWRITE_RULE
		 [GROUP_DEF]
		 (ASSUME (--`GROUP((G:'a -> bool),prod)`--))))))
	val inv_exists =
	    (--`!x:'a. G x ==> (?y. G y /\ (prod y x = ID(G,prod)))`--)
	val x = (--`x:'a`--)
	val y = (--`y:'a`--)
        val yprime = (--`y':'a`--)
	val id = (--`ID((G:'a -> bool),prod)`--)
	val id_is_id = (--`!x:'a. G x ==> (prod(ID(G,prod))x = x)`--)
	val prod_y_id_is_x = (--`prod y' (ID(G,prod)) = (x:'a)`--)
    in
DISCH_TAC THEN
((REPEAT CONJ_TAC) THEN 
 (STRIP_ASSUME_TAC id_facts) THEN
 ((FIRST_ASSUM ACCEPT_TAC) ORELSE ALL_TAC)) THEN
(REPEAT STRIP_TAC) THEN
(STRIP_ASSUME_TAC
 (UNDISCH (SPEC x (ASSUME inv_exists)))) THEN
(STRIP_ASSUME_TAC
 (UNDISCH (SPEC y (ASSUME inv_exists)))) THEN
(SUPPOSE_TAC prod_y_id_is_x) THENL
[((NEW_SUBST1_TAC
   (SYM
    (BETA_RULE
     (AP_TERM
      (--`\X:'a.(prod X (ID(G,prod)))`--)
      (ASSUME(--`prod y' (ID(G,prod)) = (x:'a)`--)))))) THEN
  (NEW_SUBST1_TAC
   (UNDISCH_ALL
    (hd (IMP_CANON
	 (SPECL [yprime,id,id] (UNDISCH GROUP_ASSOC)))))) THEN
  (NEW_SUBST1_TAC
   (UNDISCH
    (SPEC id (ASSUME id_is_id)))) THEN
  (FIRST_ASSUM ACCEPT_TAC)),
((NEW_SUBST1_TAC
  (SYM
   (AP_TERM
    (--`(prod:'a -> 'a -> 'a) y'`--)
    (ASSUME (--`prod y (x:'a) = ID(G,prod)`--))))) THEN
 (NEW_SUBST1_TAC
  (SYM
   (UNDISCH_ALL
    (hd (IMP_CANON
	 (SPECL [yprime,y,x] (UNDISCH GROUP_ASSOC))))))) THEN
 (ASM_REWRITE_TAC[]) THEN
 (ACCEPT_TAC (UNDISCH (SPEC x (ASSUME id_is_id)))))]
    end)

(*
val ID_LEMMA =
  |- GROUP (G,prod) ==>
     G (ID (G,prod)) /\
     (!x. G x ==> (prod (ID (G,prod)) x = x)) /\
     (!x. G x ==> (prod x (ID (G,prod)) = x)) /\
     (!x. G x ==> (?y. G y /\ (prod y x = ID (G,prod)))) :thm
*)


val INV_DEF = new_definition ("INV_DEF",
  (--`INV(G,prod)(x:'a) = (@y.(G y) /\ (prod y x = ID(G,prod)))`--))

(*
val INV_DEF =
  |- !G prod x. INV (G,prod) x = (@y. G y /\ (prod y x = ID (G,prod))) :thm
*)


val INV_CLOSURE = store_thm ("INV_CLOSURE",
(--`GROUP((G:'a -> bool),prod) ==>(!x. (G x) ==> (G (INV (G,prod) x)))`--),
(REPEAT STRIP_TAC) THEN
(ACCEPT_TAC
 (CONJUNCT1
  (PURE_ONCE_REWRITE_RULE
   [(SYM (SPEC_ALL INV_DEF))]
   (SELECT_RULE
    (UNDISCH
     (SPEC (--`x:'a`--)
      (CONJUNCT2
       (CONJUNCT2
	(CONJUNCT2
	 (UNDISCH ID_LEMMA)))))))))));

(*
val INV_CLOSURE =
  |- GROUP (G,prod) ==> (!x. G x ==> G (INV (G,prod) x)) :thm
*)


structure Group : GroupSig =
    struct
	val IsGroupThm = ASSUME (--`GROUP((G:'a -> bool),prod)`--)
	val InstStructureName = "GenGroupTac"
    end
structure GenGroupTac = GroupFunFunc(Group)
open GenGroupTac

val LEFT_RIGHT_INV = store_thm ("LEFT_RIGHT_INV",
(--`GROUP((G:'a -> bool),prod) ==>
    (!x y.((G x) /\ (G y)) ==>
	 ((prod y x = ID(G,prod)) ==>
	     (prod x y = ID(G,prod))))`--),
let
    val prod = (--`prod: 'a -> 'a -> 'a`--)
    val prod_x_y =  (--`(prod: 'a -> 'a -> 'a) x y`--)
    val x = (--`x:'a`--)
    val y = (--`y:'a`--)
    val yprime = (--`y':'a`--)
in
(REPEAT STRIP_TAC) THEN
(STRIP_ASSUME_TAC (PURE_ONCE_REWRITE_RULE [GROUP_DEF] Group.IsGroupThm)) THEN
(STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
(STRIP_ASSUME_TAC
 ((UNDISCH o (SPEC y))
  (ASSUME (--`!(x:'a). G x ==> (?y. G y /\ (prod y x = ID(G,prod)))`--)))) THEN
((NEW_SUBST1_TAC
  ((SYM o UNDISCH o (SPEC prod_x_y))
   (ASSUME (--`!(x:'a). G x ==> (prod(ID(G,prod))x = x)`--)))) THENL
 [ALL_TAC,GROUP_ELT_TAC]) THEN
(NEW_SUBST1_TAC
 (SYM
  (AP_THM
   (AP_TERM prod (ASSUME (--`(prod:'a -> 'a -> 'a) y' y = ID(G,prod)`--)))
   prod_x_y))) THEN
 (NEW_SUBST1_TAC
  ((UNDISCH_ALL o hd o IMP_CANON o (SPECL [yprime,y,prod_x_y]))
   (ASSUME
    (--`!x y z:'a. G x /\ G y /\ G z ==>
	           (prod(prod x y)z = prod x(prod y z))`--)))) THEN
 (NEW_SUBST1_TAC
  ((SYM o UNDISCH_ALL o hd o IMP_CANON o (SPECL [y,x,y]))
   (ASSUME (--`!x y z:'a. G x /\ G y /\ G z ==>
    (prod(prod x y)z = prod x(prod y z))`--)))) THEN
 (ASM_REWRITE_TAC
  [((UNDISCH o (SPEC y))
    (ASSUME (--`!x:'a. G x ==> (prod(ID(G,prod))x = x)`--)))])
end)

(*
val LEFT_RIGHT_INV =
  |- GROUP (G,prod) ==>
     (!x y.
       G x /\ G y ==>
       (prod y x = ID (G,prod)) ==>
       (prod x y = ID (G,prod))) :thm
*)


val INV_LEMMA = store_thm("INV_LEMMA",
(--`GROUP(G,prod) ==>
    (!x:'a.((G x) ==>
	    ((prod (INV(G,prod)x) x = ID(G,prod)) /\
	     (prod x (INV(G,prod)x) = ID(G,prod)))))`--),
let
    val x = (--`x:'a`--)
in
DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
(STRIP_ASSUME_TAC
 (((SUBS [(SYM (SPEC_ALL INV_DEF))]) o SELECT_RULE o UNDISCH o (SPEC x) o
   CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o UNDISCH)
  ID_LEMMA)) THEN
 (ASSUME_TAC
  ((UNDISCH_ALL o hd o IMP_CANON o (SPECL [x,(--`INV(G,prod)x:'a`--)]) o
    UNDISCH)
   LEFT_RIGHT_INV)) THEN
 (REPEAT STRIP_TAC) THEN (FIRST_ASSUM ACCEPT_TAC)
end)

(*
val INV_LEMMA =
  |- GROUP (G,prod) ==>
     (!x.
       G x ==>
       (prod (INV (G,prod) x) x = ID (G,prod)) /\
       (prod x (INV (G,prod) x) = ID (G,prod))) :thm
*)


val LEFT_CANCELLATION = store_thm("LEFT_CANCELLATION",
(--`GROUP(G,prod) ==>
    (!x:'a.!y.!z.(G x) /\ (G y) /\ (G z) ==>
	((prod x y) = (prod x z)) ==> (y = z))`--),
let
    val x = (--`x:'a`--)
    val y = (--`y:'a`--)
    val z = (--`z:'a`--)
in
(REPEAT STRIP_TAC) THEN
(STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
(STRIP_ASSUME_TAC ((UNDISCH o (SPEC x) o UNDISCH) INV_LEMMA)) THEN
(NEW_SUBST1_TAC
 ((SYM o UNDISCH o (SPEC y))
  (ASSUME (--`!x:'a. G x ==> (prod(ID(G,prod))x = x)`--)))) THEN
(NEW_SUBST1_TAC
 ((SYM o UNDISCH o (SPEC z))
  (ASSUME (--`!x:'a. G x ==> (prod(ID(G,prod))x = x)`--)))) THEN
(NEW_SUBST1_TAC
 (SYM (ASSUME (--`prod (INV(G,prod)x:'a) x = ID(G,prod)`--)))) THEN
(GROUP_RIGHT_ASSOC_TAC (--`prod(prod(INV(G,prod)(x:'a))x)y`--)) THEN
(GROUP_RIGHT_ASSOC_TAC (--`prod(prod(INV(G,prod)(x:'a))x)z`--)) THEN
(NEW_SUBST1_TAC (ASSUME (--`(prod:'a -> 'a -> 'a) x y = prod x z`--))) THEN
REFL_TAC
end)

(*
val LEFT_CANCELLATION =
  |- GROUP (G,prod) ==>
     (!x y z. G x /\ G y /\ G z ==> (prod x y = prod x z) ==> (y = z)):thm
*)


val RIGHT_CANCELLATION = store_thm ("RIGHT_CANCELLATION",
(--`GROUP(G,prod) ==>
    (!x:'a.!y.!z.(G x) /\ (G y) /\ (G z) ==>
	(((prod y x) = (prod z x)) ==> (y = z)))`--),
let
    val x = (--`x:'a`--)
    val y = (--`y:'a`--)
    val z = (--`z:'a`--)
in
(REPEAT STRIP_TAC) THEN
(STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
(STRIP_ASSUME_TAC (UNDISCH (SPEC x (UNDISCH INV_LEMMA)))) THEN
(NEW_SUBST1_TAC
 ((SYM o UNDISCH o (SPEC y))
  (ASSUME (--`!x:'a. G x ==> (prod x (ID(G,prod)) = x)`--)))) THEN
(NEW_SUBST1_TAC
 ((SYM o UNDISCH o (SPEC z))
  (ASSUME (--`!x:'a. G x ==> (prod x (ID(G,prod)) = x)`--)))) THEN
(NEW_SUBST1_TAC
 (SYM (ASSUME (--`prod x (INV(G,prod)x:'a) = ID(G,prod)`--)))) THEN
 (GROUP_LEFT_ASSOC_TAC (--`prod (y:'a)(prod x(INV(G,prod)x))`--)) THEN
 (GROUP_LEFT_ASSOC_TAC (--`prod (z:'a)(prod x(INV(G,prod)x))`--)) THEN
 (NEW_SUBST1_TAC (ASSUME (--`(prod:'a -> 'a -> 'a) y x = prod z x`--))) THEN
 REFL_TAC
end)

(*
val RIGHT_CANCELLATION =
  |- GROUP (G,prod) ==>
     (!x y z. G x /\ G y /\ G z ==> (prod y x = prod z x) ==> (y = z)):thm
*)


val RIGHT_ONE_ONE_ONTO = store_thm("RIGHT_ONE_ONE_ONTO",
(--`GROUP((G:'a -> bool),prod) ==>
    (!x y. ((G x) /\ (G y)) ==>
	(?z. (G z) /\ ((prod x z) = y) /\
	 (!u. ((G u) /\ ((prod x u) = y)) ==> (u = z))))`--),
let
    val x = (--`x:'a`--)
    val y = (--`y:'a`--)
    val u = (--`u:'a`--)
    val prod_inv_x_y = (--`(prod:'a -> 'a -> 'a) (INV(G,prod)x:'a) y`--)
in
DISCH_TAC THEN
(STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
((REPEAT GEN_TAC) THEN STRIP_TAC) THEN
(STRIP_ASSUME_TAC (UNDISCH (SPEC x (UNDISCH INV_LEMMA)))) THEN
(EXISTS_TAC prod_inv_x_y) THEN
(ASM_CONJ1_TAC THENL [GROUP_ELT_TAC,ALL_TAC]) THEN
ASM_CONJ1_TAC THENL
[((GROUP_LEFT_ASSOC_TAC (--`prod x(prod(INV(G,prod)x)(y:'a))`--)) THEN
   (NEW_SUBST1_TAC
    (ASSUME (--`prod (x:'a) (INV(G,prod)x) = ID(G,prod)`--))) THEN
   ((ACCEPT_TAC o UNDISCH o (SPEC y))
     (ASSUME (--`!x:'a. G x ==> (prod(ID(G,prod))x = x)`--)))),
  ((REPEAT STRIP_TAC) THEN
   (MP_IMP_TAC
    ((UNDISCH o UNDISCH o UNDISCH o hd o IMP_CANON o
      (SPECL [x,u,prod_inv_x_y]) o UNDISCH)
     LEFT_CANCELLATION)) THEN
   (ASM_REWRITE_TAC[]))]
end)

(*
val RIGHT_ONE_ONE_ONTO =
  |- GROUP (G,prod) ==>
     (!x y.
       G x /\ G y ==>
       (?z.
         G z /\
         (prod x z = y) /\
         (!u. G u /\ (prod x u = y) ==> (u = z)))) :thm
*)


val LEFT_ONE_ONE_ONTO = store_thm("LEFT_ONE_ONE_ONTO",
(--`GROUP((G:'a -> bool),prod) ==>
    (!x y. ((G x) /\ (G y)) ==>
	(?z. (G z) /\ ((prod z x) = y) /\
	 (!u. ((G u) /\ ((prod u x) = y)) ==> (u = z))))`--),
let
    val x = (--`x:'a`--)
    val y = (--`y:'a`--)
    val u = (--`u:'a`--)
    val prod_y_inv_x = (--`(prod:'a -> 'a -> 'a) y (INV(G,prod)x:'a)`--)
in
DISCH_TAC THEN
(STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
((REPEAT GEN_TAC) THEN STRIP_TAC) THEN
(STRIP_ASSUME_TAC (UNDISCH (SPEC x (UNDISCH INV_LEMMA)))) THEN
(EXISTS_TAC prod_y_inv_x) THEN
(ASM_CONJ1_TAC THENL [GROUP_ELT_TAC,ALL_TAC]) THEN
ASM_CONJ1_TAC THENL
[((GROUP_RIGHT_ASSOC_TAC (--`prod(prod (y:'a)(INV(G,prod)x))x`--)) THEN
   (NEW_SUBST1_TAC
    (ASSUME (--`prod (INV(G,prod)x) (x:'a) = ID(G,prod)`--))) THEN
   ((ACCEPT_TAC o UNDISCH o (SPEC y))
     (ASSUME (--`!x:'a. G x ==> (prod x(ID(G,prod)) = x)`--)))),
  ((REPEAT STRIP_TAC) THEN
   (MP_IMP_TAC
    ((UNDISCH o UNDISCH o UNDISCH o hd o IMP_CANON o
      (SPECL [x,u,prod_y_inv_x]) o UNDISCH)
     RIGHT_CANCELLATION)) THEN
   (ASM_REWRITE_TAC[]))]
end)

(*
val LEFT_ONE_ONE_ONTO =
  |- GROUP (G,prod) ==>
     (!x y.
       G x /\ G y ==>
       (?z.
         G z /\
         (prod z x = y) /\
         (!u. G u /\ (prod u x = y) ==> (u = z)))) :thm
*)


val UNIQUE_ID = store_thm ("UNIQUE_ID",
(--`GROUP(G,prod) ==>
    (!e:'a.((G e) /\ 
	    ((?x.((G x) /\ (prod e x = x))) \/
	     (?x.(G x) /\ (prod x e = x))) ==>
	(e = ID(G,prod))))`--),
let
    val x = (--`x:'a`--)
    val e = (--`e:'a`--)
    val id = (--`ID(G,prod):'a`--)
in
DISCH_TAC THEN
(STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
(REPEAT STRIP_TAC) THENL
[(RES_TAC THEN
  (MP_IMP_TAC
   ((UNDISCH o UNDISCH o UNDISCH o hd o IMP_CANON o (SPECL [x,e,id]) o UNDISCH)
    RIGHT_CANCELLATION)) THEN
  (ASM_REWRITE_TAC[])),
 (RES_TAC THEN
  (MP_IMP_TAC
   ((UNDISCH o UNDISCH o UNDISCH o hd o IMP_CANON o (SPECL [x,e,id]) o UNDISCH)
    LEFT_CANCELLATION)) THEN
  (ASM_REWRITE_TAC[]))]
end)

(*
val UNIQUE_ID =
  |- GROUP (G,prod) ==>
     (!e.
       G e /\
       ((?x. G x /\ (prod e x = x)) \/
       (?x. G x /\ (prod x e = x))) ==>
       (e = ID (G,prod))) :thm
*)


val UNIQUE_INV = store_thm ("UNIQUE_INV",
(--`GROUP(G,prod) ==>
    !x:'a. (G x) ==>
    (!u.((G u) /\ (prod u x = ID(G,prod))) ==> (u = (INV(G,prod)x)))`--),
let
    val x = (--`x:'a`--)
    val u = (--`u:'a`--)
    val inv_x = (--`INV(G,prod)x:'a`--)
in
(REPEAT STRIP_TAC) THEN
(STRIP_ASSUME_TAC ((UNDISCH o (SPEC x) o UNDISCH) INV_LEMMA)) THEN
((use_thm
  {theorem = ((UNDISCH o UNDISCH o UNDISCH o hd o IMP_CANON o
	       (SPECL [x,u,inv_x]) o UNDISCH)
	      RIGHT_CANCELLATION),
  thm_tactic = MP_IMP_TAC}) THENL
 [ALL_TAC,GROUP_ELT_TAC]) THEN
(ASM_REWRITE_TAC [])
end)

(*
val UNIQUE_INV =
  |- GROUP (G,prod) ==>
     (!x.
       G x ==>
       (!u. G u /\ (prod u x = ID (G,prod)) ==> (u = INV (G,prod) x))) :thm
*)


val INV_ID_LEMMA = store_thm("INV_ID_LEMMA",
(--`GROUP(G,prod) ==>
  ((INV(G,prod)(ID(G,prod)):'a) = (ID(G,prod)))`--),
let
    val id = (--`ID(G,prod):'a`--)
in
DISCH_TAC THEN
(NEW_MATCH_ACCEPT_TAC
 (SYM (UNDISCH (SPEC id (UNDISCH (SPEC_ALL (UNDISCH UNIQUE_INV))))))) THEN
ASM_CONJ1_TAC THENL
[GROUP_ELT_TAC,
 (ACCEPT_TAC
  (UNDISCH (SPEC id (CONJUNCT1 (CONJUNCT2 (UNDISCH ID_LEMMA))))))]
end)

(*
 val INV_ID_LEMMA =
  |- GROUP (G,prod) ==> (INV (G,prod) (ID (G,prod)) = ID (G,prod)):thm
*)


val INV_INV_LEMMA = store_thm("INV_INV_LEMMA",
(--`GROUP(G,prod) ==>
    (!x:'a.(G x) ==> ((INV(G,prod)(INV(G,prod)x)) = x))`--),
let
    val x = (--`x:'a`--)
    val inv_x = (--`INV(G,prod)x:'a`--)
in
(REPEAT STRIP_TAC) THEN
(STRIP_ASSUME_TAC (UNDISCH (SPEC x (UNDISCH INV_LEMMA)))) THEN
(PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ]) THEN
((use_thm
  {theorem = ((UNDISCH o hd o IMP_CANON o (SPEC x) o UNDISCH o
	      (SPEC inv_x) o UNDISCH)
	      UNIQUE_INV),
   thm_tactic = MP_IMP_TAC}) THENL
 [ALL_TAC,GROUP_ELT_TAC]) THEN
(FIRST_ASSUM ACCEPT_TAC)
end)

(*
val INV_INV_LEMMA =
  |- GROUP (G,prod) ==>
     (!x. G x ==> (INV (G,prod) (INV (G,prod) x) = x)) :thm
*)


val DIST_INV_LEMMA = store_thm("DIST_INV_LEMMA",
(--`GROUP(G,prod) ==>
    !x y:'a.((G x) /\ (G y)) ==>
    (prod (INV(G,prod)x) (INV(G,prod)y) = INV (G,prod) (prod y x))`--),
(REPEAT STRIP_TAC) THEN
(IMP_RES_TAC (CONJUNCT2 (UNDISCH ID_LEMMA))) THEN
(IMP_RES_TAC  INV_LEMMA) THEN
((use_thm
  {theorem = ((UNDISCH o hd o IMP_CANON o
	       (SPEC (--`prod(INV(G,prod)x)(INV(G,prod)y):'a`--)) o UNDISCH o
	       (SPEC (--`(prod:'a -> 'a -> 'a) y  x`--)) o UNDISCH)
	      UNIQUE_INV),
   thm_tactic = MP_IMP_TAC}) THENL
 [ALL_TAC,GROUP_ELT_TAC,GROUP_ELT_TAC]) THEN
(GROUP_RIGHT_ASSOC_TAC
 (--`prod(prod(INV(G,prod)x)(INV(G,prod)y))(prod y(x:'a))`--)) THEN
(GROUP_LEFT_ASSOC_TAC (--`prod(INV(G,prod)(y:'a))(prod y x)`--)) THEN
(ASM_REWRITE_TAC[]))

(*
val DIST_INV_LEMMA =
  |- GROUP (G,prod) ==>
     (!x y.
       G x /\ G y ==>
       (prod (INV (G,prod) x) (INV (G,prod) y) =
       INV (G,prod) (prod y x))) :thm
*)

val _ = export_theory ();
val _ = close_theory ();
