(*-----------------------------------------------------------------------------

   File:         mk_example01.ml

   Author:       (c) Copyright Flemming Andersen 1990
   Date:         January 9, 1990

   Description:  

     This example was taken from the book:

	Parallel Program Design, A Foundation
	K. Mani Chandy & Jayadev Misra
	Page 168 - 170.

     The example is a simple specification of the dining philosophers and
     intends to illustrate how one may compose two specifications and derive
     properties of the composed system.

-----------------------------------------------------------------------------*)


load_library{lib = unity_lib, theory = "example01"};
open Rsyntax;

(* Bind names of all definitions and theorems. There's a lot of them.  *)
map add_theory_to_sml ["state_logic","unless","ensures","gen_induct",
                       "leadsto","comp_unity"];

(*
  INTRODUCTION.

  To make the specification taken from the Chandy Misra book, we must define
  a state having the properties as described. In the example the state of the
  system is informally given as a set of variables, every variable representing
  a dining philosopher. A philosophers activity may be asked by the predicates
  u.t, u.h and u.e.

  To reflect this description in our HOL example, a philosopher can be doing
  one of three possible things, defined by the type:

	dine = 	EATING | THINKING | HUNGRY.

  A state of philosopher activities may then be represented as a function from
  some unspecified type of the philosopher to the dine type representing the
  actual activity in a given state:

	s:'a->dine.

  To ask for the activity of a philosopher in a given state, we introduce three
  predicates:

	eating, thinking and hungry.

  Every predicate take a philosopher as argument and returns a state abstracted
  boolean value as result, expressing whether the predicate, say eating, is
  satisfied for philosopher p in any state s. This is written as:

        eating p.

  In this way we abstract the predicates u.e, u.t and u.h as described in the
  book. The quantification is made over all philosophers p.
*)

(*
  Defining the type dine:
*)
val dine_Axiom = Define_type.define_type
                 {name="dine_Axiom",
                  type_spec = `dine = EATING | THINKING | HUNGRY`,
                  fixities = [Prefix,Prefix,Prefix]};

(*
  To prove some properties of this type we need an induction theorem for
  the dine type:
*)
val dine_Induct = prove_induction_thm dine_Axiom;

(*
  Make the induction theorem a tactic:
*)
val dine_INDUCT_TAC = INDUCT_THEN dine_Induct ASSUME_TAC;

(*
  To prove the needed properties, we must have some additionally information
  about the type:
*)
val exists_dine_thm1 = prove_rec_fn_exists dine_Axiom 
      (--`(f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)`--);

val exists_dine_thm2 = prove_rec_fn_exists dine_Axiom 
      (--`(f EATING = F) /\ (f THINKING = T) /\ (f HUNGRY = F)`--);

(*
  Now we are able to prove some trivial theorems about the type dine, which
  are needed to prove the used equalities in the example:
*)
val dine_thm1 = TAC_PROOF
  (([], (--`~(EATING = THINKING)`--)),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC (--`?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)`--)
   THEN ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);

val dine_thm2 = TAC_PROOF
  (([], (--`~(THINKING = EATING)`--)),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC (--`?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)`--)
   THEN ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);

val dine_thm3 = TAC_PROOF
  (([], (--`~(EATING = HUNGRY)`--)),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC (--`?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)`--)
   THEN ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);

val dine_thm4 = TAC_PROOF
  (([], (--`~(HUNGRY = EATING)`--)),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC (--`?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)`--)
   THEN ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);

val dine_thm5 = TAC_PROOF
  (([], (--`~(THINKING = HUNGRY)`--)),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm2 THEN
   UNDISCH_TAC (--`?f. (f EATING = F) /\ (f THINKING = T) /\ (f HUNGRY = F)`--)
   THEN ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);

val dine_thm6 = TAC_PROOF
  (([], (--`~(HUNGRY = THINKING)`--)),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm2 THEN
   UNDISCH_TAC (--`?f. (f EATING = F) /\ (f THINKING = T) /\ (f HUNGRY = F)`--)
   THEN ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);

val dine_thm7 = TAC_PROOF
  (([], (--`!u:dine. ~(u = EATING) = ((u = THINKING) \/ (u = HUNGRY))`--)),
   dine_INDUCT_TAC THENL
     [REWRITE_TAC [DE_MORGAN_THM,dine_thm1,dine_thm3],
      REWRITE_TAC [DE_MORGAN_THM,dine_thm2,dine_thm4],
      REWRITE_TAC [DE_MORGAN_THM,dine_thm4]]);

(*
  Now we define the state predicates for expressing the activity of
  philosophers:
*)
val eating = new_definition
   ("eating",
    (--`eating (p:'a) = (\s:'a->dine. (s p) = EATING)`--));

val thinking = new_definition
   ("thinking",
    (--`thinking (p:'a) = (\s:'a->dine. (s p) = THINKING)`--));

val hungry = new_definition
   ("hungry",
    (--`hungry (p:'a) = (\s:'a->dine. (s p) = HUNGRY)`--));


(*
  Proving the used equalities:
*)
val dine_thm8 = GEN (--`p:'a`--) 
                    (GEN (--`s:'a->dine`--) 
                         (SPEC (--`(s:'a->dine) p`--) dine_thm7));

(*
  Proving the used equality:
	~eating p = thinking p \/ hungry p
*)
val dine_thm9 = TAC_PROOF
  (([], (--`!p:'a. (~* (eating p)) = ((thinking p) \/* (hungry p))`--)),
   REWRITE_TAC [eating,thinking,hungry] THEN
   REWRITE_TAC [~*,\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   GEN_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPEC (--`p:'a`--) dine_thm8)));

val dine_thm10 = TAC_PROOF
  (([], (--`!u:dine. ~(u = THINKING) = ((u = HUNGRY) \/ (u = EATING))`--)),
   dine_INDUCT_TAC THENL
     [REWRITE_TAC [DE_MORGAN_THM,dine_thm1,dine_thm3],
      REWRITE_TAC [DE_MORGAN_THM,dine_thm2,dine_thm4,dine_thm5],
      REWRITE_TAC [DE_MORGAN_THM,dine_thm3,dine_thm5,dine_thm6]]);

val dine_thm11 = GEN (--`p:'a`--) 
                     (GEN (--`s:'a->dine`--)
                          (SPEC (--`(s:'a->dine)p`--) dine_thm10));

(*
  Proving the used equality:
	~thinking p = hungry p \/ eating p
*)
val dine_thm12 = TAC_PROOF
  (([], (--`!p:'a. (~* (thinking p)) = ((hungry p) \/* (eating p))`--)),
   REWRITE_TAC [eating,thinking,hungry] THEN
   REWRITE_TAC [~*,\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   GEN_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPEC (--`p:'a`--) dine_thm11)));

(*
  The Specification.
  ==================

  The method used here is an attempt to bind properties to a certain component.
  This way of specifying may be changed if a better idea turns up.
*)

(*
  Properties given for the user component:
                           ===============
*)
val user_safe1 = new_definition ("user_safe1",
   (--`user_safe1 user = !p:'a. ((thinking p) UNLESS (hungry p)) user`--));

val user_safe2 = new_definition ("user_safe2",
   (--`user_safe2 user = !p:'a. (hungry p) STABLE user`--));

val user_safe3 = new_definition ("user_safe3",
   (--`user_safe3 user = !p:'a. ((eating p) UNLESS (thinking p)) user`--));

(*
  Properties given for the G component:
                           ============
*)
val G_safe1    =  new_definition ("G_safe1",
   (--`G_safe1 G = !p:'a. (thinking p) STABLE G`--));

val G_safe2    =  new_definition ("G_safe2",
   (--`G_safe2 G = !p:'a. (~*(thinking p)) STABLE G`--));

val G_safe3    =  new_definition
  ("G_safe3", (--`G_safe3 G = !p:'a. (eating p) STABLE G`--));

val G_safe4    =  new_definition
  ("G_safe4", (--`G_safe4 G = !p:'a. (~* (eating p)) STABLE G`--));

(*
  Conditional Properties:
*)
val G_cond =  new_definition ("G_cond",
   (--`G_cond G init_cond = 
      !(pi:'a) pj. 
         ~(pi = pj) ==>
         (~*((eating pi) /\* (eating pj))) INVARIANT (init_cond, G)`--));

val user_live1 = new_definition ("user_live1",
   (--`user_live1 user init_cond =
      !(p:'a) (G:(('a->dine)->('a->dine))list).
          G_cond G init_cond ==> ((eating p) LEADSTO (thinking p)) user`--));

(*
  Properties for the composed system mutex:
                     ======================
*)

(*
  Is this the right way of specifying the mutual exclusion property?
*)
val mutex_safe1 = new_definition ("mutex_safe1",
--`mutex_safe1 G user init_cond =
   !(pi:'a) pj. ~(pi = pj) ==>
    (~*(eating pi /\* eating pj)) INVARIANT (init_cond, (APPEND user G))`--);

val mutex_live1 = new_definition ("mutex_live1",
   (--`mutex_live1 G user =
      !p:'a. ((hungry p) LEADSTO (eating p)) (APPEND user G)`--));

(*----------------------------------------------------------------------------
 *									     *
 *			Derived properties				     *
 *									     *
 *---------------------------------------------------------------------------*)

(*
  Due to restricted use of SPEC, SPECL, the type instantiation is needed.
  Strange since REWRITE tactics do not need the instantiation
*)
val theta = [{redex= ==`:'a`==, residue = ==`:'a->dine`==}];
val INSTY = INST_TYPE theta;
val UNLESS_thm8     = INSTY UNLESS_thm8;
val False           = INSTY False;
val COMP_UNITY_cor2 = INSTY COMP_UNITY_cor2;
val UNLESS_thm2     = INSTY UNLESS_thm2;
val UNLESS_thm4     = INSTY UNLESS_thm4;
val OR_COMM_lemma   = INSTY OR_COMM_lemma;
val AND_OR_DISTR_lemma   = INSTY AND_OR_DISTR_lemma;
val UNLESS_thm3     = INSTY UNLESS_thm3;
val AND_COMM_lemma   = INSTY AND_COMM_lemma;
val SYM_AND_IMPLY_WEAK_lemma = INSTY SYM_AND_IMPLY_WEAK_lemma;

(*
  Derived property:

     Given properties user_safe1, user_safe2, user_safe3, prove that all users
     satisfy:

	!user p. user_safe1 user /\ user_safe2 user /\ user_safe3 user ==>
            ~eating p is stable in user
*)
val user_thm1 = TAC_PROOF
  (([], (--`!user (p:'a).
           user_safe1 user /\ user_safe2 user /\ user_safe3 user ==>
               (~* (eating p)) STABLE user`--)),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [user_safe1,user_safe2,user_safe3] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC (--`p:'a`--) 
                    (ASSUME (--`!p:'a. (hungry p) STABLE user`--))) THEN
   ASSUME_TAC
       (SPEC (--`p:'a`--) 
             (ASSUME(--`!p:'a. ((thinking p) UNLESS (hungry p)) user`--))) THEN
   UNDISCH_TAC (--`(hungry (p:'a)) STABLE user`--) THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`((thinking (p:'a)) UNLESS (hungry p))user`--),
         (--`((hungry (p:'a)) UNLESS False)user`--)]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`thinking (p:'a)`--),(--`hungry (p:'a)`--),
         (--`False:('a->dine)->bool`--),
         (--`user:(('a->dine)->('a->dine))list`--)]
         UNLESS_thm8)) THEN
   UNDISCH_TAC (--`((thinking (p:'a) \/* (hungry p)) UNLESS False)user`--)
   THEN REWRITE_TAC [SYM (SPEC_ALL dine_thm9)]);

(*
  Derived property:

     Given properties user_safe1 and G_safe1, prove that all users and Gs
     satisfy:

	!user G p. user_safe1 user /\ G_safe1 G ==>
            (thinking p) unless (hungry p) in (user [] G)

     in the composed system mutex.
*)
val mutex_thm1 = TAC_PROOF
  (([], (--`!user G (p:'a). user_safe1 user /\ G_safe1 G ==>
               ((thinking p) UNLESS (hungry p)) (APPEND user G)`--)),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [user_safe1,G_safe1] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (ASSUME
        (--`!p:'a. ((thinking p) UNLESS (hungry p))user`--))) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME (--`!p:'a. (thinking p) STABLE G`--))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
       [(--`((thinking (p:'a)) UNLESS (hungry p))user`--),
        (--`(thinking (p:'a)) STABLE G`--)]
        AND_INTRO_THM)) THEN
   REWRITE_TAC [UNDISCH_ALL (SPECL
       [(--`thinking (p:'a)`--),(--`hungry (p:'a)`--),
        (--`user:(('a->dine)->('a->dine))list`--),
        (--`G:(('a->dine)->('a->dine))list`--)] COMP_UNITY_cor2)]);

(*
  Derived property:

     Given properties user_safe2 and G_safe2, prove that all users and Gs
     satisfy:

	!user G p. user_safe2 user /\ G_safe2 G ==>
            (hungry p) unless (eating p) in (user [] G)

     in the composed system mutex.

  The rewriting of boolean expressions are tedious, need to invent something
  better.
*)
val mutex_thm2 = TAC_PROOF
  (([], (--`!(p:'a) user G. user_safe2 user /\ G_safe2 G ==>
                     ((hungry p) UNLESS (eating p)) (APPEND G user)`--)),
   REWRITE_TAC [user_safe2,G_safe2] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (ASSUME (--`!p:'a. (~*(thinking p)) STABLE G`--))) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME (--`!p:'a. (hungry p) STABLE user`--))) THEN
   UNDISCH_TAC (--`(~*(thinking (p:'a))) STABLE G`--) THEN
   REWRITE_TAC [dine_thm12] THEN
   ASSUME_TAC (SPECL
        [(--`hungry (p:'a)`--),
         (--`G:(('a->dine)->('a->dine))list`--)] UNLESS_thm2) THEN
   REWRITE_TAC [STABLE] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`((hungry (p:'a)) UNLESS (~*(hungry p)))G`--),
         (--`(((eating (p:'a)) \/* (hungry p)) UNLESS False)G`--)]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`hungry (p:'a)`--),(--`~* (hungry (p:'a))`--),
         (--`(eating (p:'a)) \/* (hungry p)`--),
         (--`False:('a->dine)->bool`--),
         (--`G:(('a->dine)->('a->dine))list`--)] UNLESS_thm4)) THEN
   UNDISCH_TAC
         (--`(((hungry p) /\* ((eating p) \/* (hungry p))) UNLESS
           ((((hungry (p:'a)) /\* False) \/*
            (((eating p) \/* (hungry p)) /\* (~*(hungry p)))) \/*
           ((~*(hungry p)) /\* False))) G`--) THEN
   REWRITE_TAC [AND_False_lemma] THEN
   REWRITE_TAC [OR_False_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        [(--`False:('a->dine)->bool`--),
         (--`((eating (p:'a)) \/* (hungry p)) /\* (~*(hungry p))`--)]
         OR_COMM_lemma] THEN
   REWRITE_TAC [OR_False_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        [(--`hungry (p:'a)`--),(--`eating (p:'a)`--),(--`hungry (p:'a)`--)]
         AND_OR_DISTR_lemma] THEN
   REWRITE_TAC [AND_AND_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        [(--`hungry (p:'a)`--),(--`eating (p:'a)`--)] AND_COMM_lemma] THEN
   REWRITE_TAC [P_AND_Q_OR_Q_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        [(--`~* (hungry (p:'a))`--),(--`eating (p:'a)`--),
         (--`hungry (p:'a)`--)] AND_OR_DISTR_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [P_AND_NOT_P_lemma] THEN
   REWRITE_TAC [OR_False_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL
        [(--`eating (p:'a)`--),(--`~* (hungry (p:'a))`--)]
         SYM_AND_IMPLY_WEAK_lemma) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`((hungry (p:'a)) UNLESS ((eating p) /\* (~*(hungry p))))G`--),
         (--`!s:'a->dine. ((eating p) /\* (~*(hungry p)))s ==> eating p s`--)]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`hungry (p:'a)`--),(--`(eating (p:'a)) /\* (~*(hungry p))`--),
         (--`eating (p:'a)`--),(--`G:(('a->dine)->('a->dine))list`--)]
         UNLESS_thm3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`((hungry (p:'a)) UNLESS (eating p))G`--),
         (--`(hungry (p:'a)) STABLE user`--)]
         AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`hungry (p:'a)`--),(--`eating (p:'a)`--),
         (--`G:(('a->dine)->('a->dine))list`--),
         (--`user:(('a->dine)->('a->dine))list`--)] COMP_UNITY_cor2)));

(*
  Derived property:

     Given properties user_safe3 and G_safe3, prove that all users and Gs
     satisfy:

	!user G p. user_safe3 user /\ G_safe3 G ==>
            (eating p) unless (thinking p) in (user [] G)

     in the composed system mutex.
*)
val mutex_thm3 = TAC_PROOF
  (([], (--`!user G (p:'a). user_safe3 user /\ G_safe3 G ==>
                  ((eating p) UNLESS (thinking p)) (APPEND user G)`--)),
   REWRITE_TAC [user_safe3,G_safe3] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (ASSUME (--`!p:'a. (eating p) STABLE G`--))) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME
        (--`!p:'a. ((eating p) UNLESS (thinking p))user`--))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`((eating (p:'a)) UNLESS (thinking p))user`--),
         (--`(eating (p:'a)) STABLE G`--)]
         AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
        [(--`eating (p:'a)`--),(--`thinking (p:'a)`--),
         (--`user:(('a->dine)->('a->dine))list`--),
         (--`G:(('a->dine)->('a->dine))list`--)] COMP_UNITY_cor2)));

(*
  End of example
*)

export_theory();
