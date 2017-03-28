(*===========================================================================*)
(* LIBRARY:     wellorder                                                    *)
(*                                                                           *)
(* DESCRIPTION: (1) Versions of the Axiom of Choice                          *)
(*              (2) Theorems about wosets, including recursion theorem       *)
(*                                                                           *)
(* AUTHOR:      John Harrison                                                *)
(*              University of Cambridge Computer Laboratory                  *)
(*              New Museums Site                                             *)
(*              Pembroke Street                                              *)
(*              Cambridge CB2 3QG                                            *)
(*              England.                                                     *)
(*                                                                           *)
(*              jrh@cl.cam.ac.uk                                             *)
(*                                                                           *)
(* DATE:        30th May 1992    [Original version written]                  *)
(* REVISED:     31st Mar 1993    [Recursion theorem added]                   *)
(*                                                                           *)
(* DETAILS:     The versions of the axiom of choice proved here are:         *)
(*                                                                           *)
(*              1. Kuratowski's Lemma:                                       *)
(*                 Every chain is a poset can be extended to a maximal       *)
(*                 chain.                                                    *)
(*                                                                           *)
(*              2. Hausdorff Maximum Principle:                              *)
(*                 Every poset has a maximal chain.                          *)
(*                                                                           *)
(*              3. Zorn's Lemma:                                             *)
(*                 A poset where every chain has an upper bound, has a       *)
(*                 maximal element.                                          *)
(*                                                                           *)
(*              4. Cantor-Zermelo well-ordering theorem:                     *)
(*                 Every set can be wellordered.                             *)
(*                                                                           *)
(*              Proofs follow quite closely those in "R.R. Stoll - Set       *)
(*              Theory and Logic - Dover 1979"                               *)
(*                                                                           *)
(*              The recursion theorem justifies arbitrary recursive          *)
(*              definitions:                                                 *)
(*                                                                           *)
(*                ?!f. f a = h f a                                           *)
(*                                                                           *)
(*              provided one can prove that for some wellfounded             *)
(*              "measure" function, the value of |h f a| depends             *)
(*              only on the values of |f| at values of lower measure         *)
(*              than |a|.                                                    *)
(*===========================================================================*)

(* Set the path when building library theories *)
local
val path = (!HOLdir)^"library/wellorder/theories/"^Globals.theory_file_type^"/"
in
val _ = theory_path := path :: (!Globals.theory_path)
end;

new_theory "WELLORDER";

val ty = ty_antiq(==`:'a#'a->bool`==);

(*---------------------------------------------------------------------------*)
(* For compatibility                                                         *)
(*---------------------------------------------------------------------------*)

load_library{lib = hol88_lib, theory = "-"};

open Psyntax Compat;

val PAIR = theorem "pair" "PAIR";;

val LESS_EQ_REFL = theorem "arithmetic" "LESS_EQ_REFL";

val WOP = theorem "arithmetic" "WOP";

val NOT_LESS_EQUAL = theorem "arithmetic" "NOT_LESS_EQUAL";

val LESS_EQUAL_ANTISYM = theorem "arithmetic" "LESS_EQUAL_ANTISYM";

val LESS_NOT_EQ = theorem "prim_rec" "LESS_NOT_EQ";

val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";

(*---------------------------------------------------------------------------*)
(* Some useful tactics etc.                                                  *)
(*---------------------------------------------------------------------------*)

val LAND_CONV = RATOR_CONV o RAND_CONV;

val TAUT_CONV =
  let fun vl w t = type_of t = (==`:bool`==) andalso
  can (find_term is_var) t andalso free_in t w in
  C (curry prove)
  (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
   (C (curry op THEN) (REWRITE_TAC[]) o BOOL_CASES_TAC o hd o
   sort free_in o
    W(find_terms o vl) o snd)) end;

val GEN_PAIR_TAC =
  W(curry op THEN GEN_TAC o SUBST1_TAC o SYM o
    C ISPEC PAIR o fst o dest_forall o snd);

val PBETA_TAC = CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV);

fun ABBREV_TAC tm =
  let val (v,t) = dest_eq tm in
  CHOOSE_THEN (fn th =>  SUBST_ALL_TAC th THEN ASSUME_TAC th)
              (EXISTS(mk_exists(v,mk_eq(t,v)),t) (REFL t)) end;

fun EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  assert(curry op = s o fst o dest_var o rhs o concl)) THEN BETA_TAC;

(*===========================================================================*)
(* (0) Firstly, some definitions concerned with orders                       *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Subset                                                                    *)
(*---------------------------------------------------------------------------*)

val wo_subset = new_infix_definition("wo_subset",
  (--`wo_subset P Q = !x:'a. P x ==> Q x`--), 450);

(*---------------------------------------------------------------------------*)
(* wo_Union                                                                  *)
(*---------------------------------------------------------------------------*)

val wo_Union = new_definition("wo_Union",
  (--`wo_Union P = \x:'a. ?p. P p /\ p x`--));

(*---------------------------------------------------------------------------*)
(* Field of an uncurried binary relation                                     *)
(*---------------------------------------------------------------------------*)

val wo_fl = new_definition("wo_fl",
  (--`wo_fl(l:^ty) x = ?y:'a. l(x,y) \/ l(y,x)`--));

(*---------------------------------------------------------------------------*)
(* Partial order (we infer the domain from the field of the relation)        *)
(*---------------------------------------------------------------------------*)

val wo_poset = new_definition("wo_poset",
  (--`wo_poset (l:^ty) =
       (!x. wo_fl(l) x ==> l(x,x)) /\
       (!x y z. l(x,y) /\ l(y,z) ==> l(x,z)) /\
       (!x y. l(x,y) /\ l(y,x) ==> (x = y))`--));

(*---------------------------------------------------------------------------*)
(* Chain in a poset (Defined as a subset of the field, not the ordering)     *)
(*---------------------------------------------------------------------------*)

val wo_chain = new_definition("wo_chain",
  (--`wo_chain(l:^ty) P = (!x y. P x /\ P y ==> l(x,y) \/ l(y,x))`--));

(*---------------------------------------------------------------------------*)
(* Wellorder                                                                 *)
(*---------------------------------------------------------------------------*)

val wo_woset = new_definition("wo_woset",
 (--`wo_woset (l:^ty) =
       (!x. wo_fl(l) x ==> l(x,x)) /\
       (!x y z. l(x,y) /\ l(y,z) ==> l(x,z)) /\
       (!x y. l(x,y) /\ l(y,x) ==> (x = y)) /\
       (!x y. wo_fl(l) x /\ wo_fl(l) y ==> l(x,y) \/ l(y,x)) /\
       (!P. (!x. P x ==> wo_fl(l) x) /\ (?x. P x) ==>
            (?y. P y /\ (!z. P z ==> l(y,z))))`--));

(*---------------------------------------------------------------------------*)
(* Initial segment                                                           *)
(*---------------------------------------------------------------------------*)

val wo_inseg = new_definition("wo_inseg",
  (--`wo_inseg (l:^ty,m) =
        wo_woset l /\ wo_woset m /\ (!x y. l(x,y) = wo_fl(l) y /\ m(x,y))`--));

(*---------------------------------------------------------------------------*)
(* A definition of "less than" is convenient.                                *)
(*---------------------------------------------------------------------------*)

val wo_less = new_definition("wo_less",
  (--`(wo_less l)(x,y) = (l:^ty)(x,y) /\ ~(x = y)`--));

(*---------------------------------------------------------------------------*)
(* Derive useful properties of subset                                        *)
(*---------------------------------------------------------------------------*)

val SUBSET_REFL = prove_thm("SUBSET_REFL",
  (--`!P:'a->bool. P wo_subset P`--),
  REWRITE_TAC[wo_subset]);

val SUBSET_ANTISYM = prove_thm("SUBSET_ANTISYM",
  (--`!(P:'a->bool) Q. P wo_subset Q /\ Q wo_subset P ==> (P = Q)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[wo_subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  CONV_TAC(RAND_CONV FUN_EQ_CONV) THEN
  REWRITE_TAC[TAUT_CONV (--`(a ==> b) /\ (b ==> a) = (a = b)`--)]);

val SUBSET_TRANS = prove_thm("SUBSET_TRANS",
  (--`!(P:'a->bool) Q R. P wo_subset Q /\ Q wo_subset R ==> P wo_subset R`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[wo_subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC (--`x:'a`--)) o MP_TAC o 
                            SPEC (--`x:'a`--)) THEN
  MATCH_ACCEPT_TAC(TAUT_CONV (--`(a ==> b) /\ (b ==> c) ==> (a ==> c)`--)));

(*---------------------------------------------------------------------------*)
(* Now useful things about the orderings                                     *)
(*---------------------------------------------------------------------------*)

val [POSET_REFL, POSET_TRANS, POSET_ANTISYM] = 
  map (GEN (--`l:^ty`--) o DISCH_ALL)
      (CONJUNCTS(PURE_ONCE_REWRITE_RULE[wo_poset] 
                                       (ASSUME (--`wo_poset (l:^ty)`--))));

val POSET_FLEQ = prove_thm("POSET_FLEQ",
  (--`!l:^ty. wo_poset l ==> (!x. wo_fl(l) x = l(x,x))`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP POSET_REFL),
    DISCH_TAC THEN REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`x:'a`--) THEN
    ASM_REWRITE_TAC[]]);

val CHAIN_SUBSET = prove_thm("CHAIN_SUBSET",
  (--`!(l:^ty) P Q. wo_chain(l) P /\ Q wo_subset P ==> wo_chain(l) Q`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[wo_chain, wo_subset] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);

val [WOSET_REFL, WOSET_TRANS, WOSET_ANTISYM, WOSET_TOTAL, WOSET_WELL] =
  map (GEN (--`l:^ty`--) o DISCH_ALL)
      (CONJUNCTS(PURE_ONCE_REWRITE_RULE[wo_woset] 
                                       (ASSUME (--`wo_woset (l:^ty)`--))));

val WOSET_POSET = prove_thm("WOSET_POSET",
  (--`!l:^ty. wo_woset l ==> wo_poset l`--),
  GEN_TAC THEN REWRITE_TAC[wo_woset, wo_poset] THEN
  DISCH_THEN(fn th =>  REWRITE_TAC[th]));

val WOSET_FLEQ = prove_thm("WOSET_FLEQ",
  (--`!l:^ty. wo_woset l ==> (!x. wo_fl(l) x = l(x,x))`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP WOSET_POSET) THEN
  MATCH_ACCEPT_TAC POSET_FLEQ);

val WOSET_TRANS_LESS = prove_thm("WOSET_TRANS_LESS",
  (--`!l:^ty. wo_woset l ==>
       !x y z. (wo_less l)(x,y) /\ l(y,z) ==> (wo_less l)(x,z)`--),
  REWRITE_TAC[wo_less] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS) THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[],
    UNDISCH_TAC (--`x:'a = z`--) THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC (--`~(z:'a = y)`--) THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Antisymmetry and wellfoundedness are sufficient for a wellorder           *)
(*---------------------------------------------------------------------------*)

val WOSET = prove_thm("WOSET",
  (--`!l:^ty. wo_woset l =
        (!x y. l(x,y) /\ l(y,x) ==> (x = y)) /\
        (!P. (!x. P x ==> wo_fl(l) x) /\ (?x. P x) ==>
             (?y. P y /\ (!z. P z ==> l(y,z))))`--),
  GEN_TAC THEN REWRITE_TAC[wo_woset] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (--`!x y. wo_fl(l:^ty) x /\ wo_fl(l) y 
                         ==> l(x,y) \/ l(y,x)`--) MP_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_ASSUM(MP_TAC 
    o SPEC (--`\z:'a. (z = x) \/ (z = y)`--)) THEN BETA_TAC THEN
    W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
        FIRST_ASSUM ACCEPT_TAC,
        EXISTS_TAC (--`x:'a`--) THEN REWRITE_TAC[]], ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`z:'a`--) 
                             (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THENL
     [DISCH_THEN(MP_TAC o SPEC (--`y:'a`--)), 
      DISCH_THEN(MP_TAC o SPEC (--`x:'a`--))] THEN
    REWRITE_TAC[] THEN DISCH_THEN(fn th =>  REWRITE_TAC[th]),
    DISCH_THEN(fn th =>  ASSUME_TAC th THEN REWRITE_TAC[th] THEN
      MP_TAC(GEN (--`x:'a`--) (SPECL [(--`x:'a`--), (--`x:'a`--)] th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fn th =>  REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[TAUT_CONV (--`a = ~~a`--)] THEN
    CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV) THEN
    REWRITE_TAC[NOT_IMP] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN (--`wo_fl(l:^ty) x /\ wo_fl(l) y /\ wo_fl(l) z`--) 
                 STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[wo_fl] THEN REPEAT CONJ_TAC THENL
       [EXISTS_TAC (--`y:'a`--), EXISTS_TAC (--`x:'a`--), 
        EXISTS_TAC (--`y:'a`--)] THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    UNDISCH_TAC (--`!x y. wo_fl(l:^ty) x /\ wo_fl(l) y 
                          ==> l(x,y) \/ l(y,x)`--) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`z:'a`--), (--`x:'a`--)]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC 
                o SPEC (--`\w:'a. (w = x) \/ (w = y) \/ (w = z)`--)) THEN
    BETA_TAC THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
        FIRST_ASSUM ACCEPT_TAC,
        EXISTS_TAC (--`x:'a`--) THEN REWRITE_TAC[]],
      DISCH_THEN(fn th =>  REWRITE_TAC[th])] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`w:'a`--) 
                             (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(DISJ_CASES_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THENL
     map (fn t =>  DISCH_THEN(MP_TAC o SPEC t)) 
                         [(--`z:'a`--), (--`x:'a`--), (--`y:'a`--)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC (--`!x y. l(x,y) /\ l(y,x) ==> (x:'a = y)`--) THENL
     [DISCH_THEN(MP_TAC o SPECL [(--`x:'a`--), (--`y:'a`--)]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (--`(l:^ty)(y,z)`--) THEN ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o SPECL [(--`y:'a`--), (--`z:'a`--)]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (--`(l:^ty)(x,z)`--) THEN ASM_REWRITE_TAC[]]]);

(*===========================================================================*)
(* (1) Major lemma: expanding function on a CPO has a fixpoint (Bourbaki)    *)
(*===========================================================================*)

val CPO_FIX = prove_thm("CPO_FIX",
  (--`!l:^ty. wo_poset l /\
      (!A. wo_chain(l) A ==>
          ?m. wo_fl(l) m /\ (!x. A x ==> l(x,m)) /\
              (!m'. wo_fl(l) m' /\ (!x. A x ==> l(x,m')) ==> l(m,m'))) /\
      (!x. wo_fl(l) x ==> l(x,f(x))) ==>
    ?y. wo_fl(l) y /\ (f(y) = y)`--),
  let fun ADM_THEN s ttac =
         MP_TAC(ASSUME (mk_comb((--`adm:('a->bool)->bool`--),
                                mk_var(s,(==`:'a->bool`==))))) THEN
         EXPAND_TAC "adm" THEN DISCH_THEN ttac
  and P_THEN s ttac =
         MP_TAC(ASSUME (mk_comb((--`P:'a->bool`--),
                                mk_var(s,(==`:'a`==))))) THEN
         EXPAND_TAC "P" THEN DISCH_THEN ttac 
  in
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o CONV_RULE(ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV)) THEN
  DISCH_THEN(X_CHOOSE_TAC (--`lub:('a->bool)->'a`--) 
             o CONV_RULE SKOLEM_CONV) THEN
  SUBGOAL_THEN (--`wo_chain(l:^ty) (\x. F)`--) MP_TAC THENL
   [REWRITE_TAC[wo_chain], ALL_TAC] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  ABBREV_TAC (--`b:'a = lub(\x:'a. F)`--) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE(GEN_ALPHA_CONV (--`x:'a`--))) THEN
  ABBREV_TAC (--`adm 
     = \A. A wo_subset (wo_fl l) /\
           A b /\
           (!x. A x ==> A(f x)) /\
           (!C. wo_chain(l:^ty) C /\ C wo_subset A ==> A(lub C))`--) THEN
  ABBREV_TAC (--`M = \x:'a. !A. adm A ==> A x`--) THEN
  SUBGOAL_THEN (--`!A:'a->bool. adm A ==> M wo_subset A`--) ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[wo_subset] THEN BETA_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  SUBGOAL_THEN (--`!R. adm(\x:'a. M x /\ R x) ==> !x. M x ==> R x`--) 
               ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM wo_subset] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (--`\x:'a. M x /\ R x`--) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      REWRITE_TAC[wo_subset] THEN BETA_TAC THEN GEN_TAC THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT2)], ALL_TAC] THEN
  SUBGOAL_THEN (--`(adm:('a->bool)->bool)(wo_fl(l:^ty))`--) ASSUME_TAC THENL
   [EXPAND_TAC "adm" THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    CONJ_TAC THENL
     [X_GEN_TAC (--`x:'a`--) THEN DISCH_TAC THEN REWRITE_TAC[wo_fl] THEN
      EXISTS_TAC (--`x:'a`--) THEN DISJ2_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
      GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)], ALL_TAC] THEN
  SUBGOAL_THEN (--`(adm:('a->bool)->bool) M`--) ASSUME_TAC THENL
   [EXPAND_TAC "adm" THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      EXPAND_TAC "M" THEN GEN_TAC THEN EXPAND_TAC "adm" THEN
      DISCH_THEN(ACCEPT_TAC o el 2 o CONJUNCTS),
      GEN_TAC THEN EXPAND_TAC "M" THEN
      DISCH_THEN(fn th1 => X_GEN_TAC (--`A:'a->bool`--) THEN
        DISCH_THEN(fn th2 => MP_TAC(MATCH_MP th1 th2) THEN MP_TAC th2)) THEN
      EXPAND_TAC "adm" THEN DISCH_THEN(MATCH_ACCEPT_TAC o el 3 o CONJUNCTS),
      X_GEN_TAC (--`C:'a->bool`--) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      EXPAND_TAC "M" THEN REWRITE_TAC[wo_subset] THEN BETA_TAC THEN
      DISCH_THEN(curry op THEN (X_GEN_TAC (--`A:'a->bool`--) THEN DISCH_TAC) 
                               o MP_TAC) THEN
      DISCH_THEN(MP_TAC o GEN (--`x:'a`--) o DISCH (--`(C:'a->bool) x`--) o
        SPEC (--`A:'a->bool`--) o UNDISCH o SPEC (--`x:'a`--)) THEN
      ASM_REWRITE_TAC[GSYM wo_subset] THEN
      DISCH_THEN(MP_TAC o CONJ(ASSUME (--`wo_chain(l:^ty) C`--))) THEN
      UNDISCH_TAC (--`(adm:('a->bool)->bool) A`--) THEN EXPAND_TAC "adm" THEN
      DISCH_THEN(MATCH_ACCEPT_TAC o last o CONJUNCTS)],
    ALL_TAC] THEN
  ABBREV_TAC (--`P = \x:'a. !y. M y /\ l(y,x) /\ ~(y = x) ==> l(f y,x)`--) THEN
  SUBGOAL_THEN (--`!x:'a. M x /\ P x ==>
                   !z. M z ==> (\z. l(z,x) \/ l(f x,z)) z`--) MP_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    BETA_TAC THEN EXPAND_TAC "adm" THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[wo_subset] THEN BETA_TAC THEN X_GEN_TAC (--`z:'a`--) THEN
      REWRITE_TAC[wo_fl] THEN DISCH_THEN(DISJ_CASES_TAC o CONJUNCT2) THENL
       [EXISTS_TAC (--`x:'a`--), EXISTS_TAC (--`(f:'a->'a) x`--)] THEN 
       ASM_REWRITE_TAC[],

      ADM_THEN "M" (ACCEPT_TAC o el 2 o CONJUNCTS),

      DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ADM_THEN "M" (MP_TAC o CONJUNCT1) THEN REWRITE_TAC[wo_subset] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,

      X_GEN_TAC (--`z:'a`--) THEN 
      DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
       [DISCH_THEN(MP_TAC o CONJUNCT1) THEN
        ADM_THEN "M" (MATCH_ACCEPT_TAC o el 3 o CONJUNCTS),
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
         [ASM_CASES_TAC (--`z:'a = x`--) THENL
           [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
            FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_REFL) THEN
            ADM_THEN "M" (MP_TAC o CONJUNCT1) THEN REWRITE_TAC[wo_subset] THEN
            DISCH_THEN MATCH_MP_TAC THEN
            ADM_THEN "M" (MATCH_MP_TAC o el 3 o CONJUNCTS) THEN
            FIRST_ASSUM ACCEPT_TAC,
            DISJ1_TAC THEN P_THEN "x" (MP_TAC o SPEC (--`z:'a`--)) THEN
            ASM_REWRITE_TAC[]],
          DISJ2_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
          EXISTS_TAC (--`z:'a`--) THEN ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[wo_fl] THEN
          EXISTS_TAC (--`(f:'a->'a) x`--) THEN ASM_REWRITE_TAC[]]],

      X_GEN_TAC (--`C:'a->bool`--) THEN 
      DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
       [DISCH_TAC THEN ADM_THEN "M" (MATCH_MP_TAC o last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
        REWRITE_TAC[wo_subset] THEN
        DISCH_THEN(fn th => GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
        BETA_TAC THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1),
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[wo_subset] THEN BETA_TAC THEN
        ASM_CASES_TAC (--`!z. C z ==> (l:^ty)(z,x)`--) THENL
         [FIRST_ASSUM(MP_TAC o 
                      C MATCH_MP (ASSUME (--`wo_chain(l:^ty) C`--))) THEN
          DISCH_THEN(MP_TAC o SPEC (--`x:'a`--) o last o CONJUNCTS) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
          DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          ADM_THEN "M" (MP_TAC o CONJUNCT1) THEN REWRITE_TAC[wo_subset] THEN
          DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
          DISCH_THEN(curry op THEN DISJ2_TAC o MP_TAC) THEN
          FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
          DISCH_THEN(MP_TAC o CONV_RULE NOT_FORALL_CONV) THEN
          REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_TAC (--`z:'a`--)) THEN
          DISCH_THEN(MP_TAC o SPEC (--`z:'a`--)) THEN ASM_REWRITE_TAC[] THEN
          DISCH_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
          EXISTS_TAC (--`z:'a`--) THEN ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM(MP_TAC o 
                      C MATCH_MP (ASSUME (--`wo_chain(l:^ty) C`--))) THEN
          DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
          ASM_REWRITE_TAC[]]]],

    BETA_TAC THEN DISCH_TAC] THEN
  SUBGOAL_THEN (--`!x:'a. M x ==> P x`--) ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "adm" THEN BETA_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN 
      EXISTS_TAC (--`M:'a->bool`--) THEN CONJ_TAC THENL
       [REWRITE_TAC[wo_subset] THEN GEN_TAC THEN BETA_TAC THEN
        DISCH_THEN(ACCEPT_TAC o CONJUNCT1),
        ADM_THEN "M" (ACCEPT_TAC o CONJUNCT1)],

      ADM_THEN "M" (ACCEPT_TAC o el 2 o CONJUNCTS),

      EXPAND_TAC "P" THEN X_GEN_TAC (--`x:'a`--) THEN STRIP_TAC THEN
      UNDISCH_TAC (--`!x. wo_fl(l:^ty) x ==> l(b,x)`--) THEN
      DISCH_THEN(MP_TAC o SPEC (--`x:'a`--)) THEN REWRITE_TAC[wo_fl] THEN
      CONV_TAC(ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
      DISCH_THEN(MP_TAC o SPEC (--`b:'a`--)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP POSET_ANTISYM) THEN
      DISCH_THEN(MP_TAC o SPECL [(--`x:'a`--), (--`b:'a`--)]) THEN
      ASM_REWRITE_TAC[],

      X_GEN_TAC (--`x:'a`--) THEN 
      DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
       [DISCH_TAC THEN ADM_THEN "M" (MATCH_MP_TAC o el 3 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[],
        DISCH_THEN(fn th => ASSUME_TAC(CONJUNCT2 th) THEN
          FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
        EXPAND_TAC "P" THEN X_GEN_TAC (--`y:'a`--) THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        DISCH_THEN(fn th => FIRST_ASSUM(DISJ_CASES_TAC o C MATCH_MP th) THEN
              ASSUME_TAC th) THENL
         [ALL_TAC, FIRST_ASSUM(MP_TAC o MATCH_MP POSET_ANTISYM) THEN
          DISCH_THEN(MP_TAC o SPECL [(--`y:'a`--), (--`(f:'a->'a) x`--)]) THEN
          ASM_REWRITE_TAC[]] THEN
        ASM_CASES_TAC (--`y:'a = x`--) THENL
         [ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_REFL) THEN
          REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`y:'a`--) THEN 
          ASM_REWRITE_TAC[],
          ALL_TAC] THEN
        P_THEN "x" (MP_TAC o SPEC (--`y:'a`--)) THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
        EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[wo_fl] THEN
        EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[]],

      X_GEN_TAC (--`C:'a->bool`--) THEN 
      DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
       [DISCH_TAC THEN ADM_THEN "M" (MATCH_MP_TAC o last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC (--`\x:'a. M x /\ P x`--) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[wo_subset] THEN GEN_TAC THEN BETA_TAC THEN
        DISCH_THEN(ACCEPT_TAC o CONJUNCT1), ALL_TAC] THEN
      STRIP_TAC THEN EXPAND_TAC "P" THEN 
      X_GEN_TAC (--`y:'a`--) THEN STRIP_TAC THEN
      SUBGOAL_THEN (--`?y1. C y1 /\ (l:^ty)(y,y1)`--) MP_TAC THENL
       [GEN_REWRITE_TAC I [] [TAUT_CONV(--`a = ~~a`--)] THEN
        CONV_TAC(RAND_CONV NOT_EXISTS_CONV) THEN
        REWRITE_TAC[TAUT_CONV (--`~(a /\ b) = a ==> ~b`--)] THEN DISCH_TAC THEN
        SUBGOAL_THEN (--`!y1. C y1 ==> (l:^ty)(y1,y)`--) ASSUME_TAC THENL
         [GEN_TAC THEN DISCH_TAC THEN
          FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
          EXISTS_TAC (--`(f:'a->'a) y1`--) THEN CONJ_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN 
            UNDISCH_TAC (--`wo_chain(l:^ty) C`--) THEN
            REWRITE_TAC[wo_chain] THEN
            DISCH_THEN(MP_TAC o SPECL [(--`y1:'a`--), (--`y1:'a`--)]) THEN
            ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[wo_fl] THEN
            EXISTS_TAC (--`y1:'a`--) THEN ASM_REWRITE_TAC[],
            SUBGOAL_THEN (--`M y1 /\ P(y1:'a)`--) MP_TAC THENL
             [UNDISCH_TAC (--`C wo_subset (\x:'a. M x /\ P x)`--) THEN
              REWRITE_TAC[wo_subset] THEN BETA_TAC THEN
              DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
            DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
            DISCH_THEN(MP_TAC o SPEC (--`y:'a`--)) THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC (TAUT_CONV (--`~a ==> a \/ b ==> b`--)) THEN
            FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC],
        ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o 
                    C MATCH_MP (ASSUME (--`wo_chain(l:^ty) C`--))) THEN
        DISCH_THEN(MP_TAC o SPEC (--`y:'a`--) o el 3 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
         [REWRITE_TAC[wo_fl] THEN 
          EXISTS_TAC (--`(lub:('a->bool)->'a) C`--) THEN
          ASM_REWRITE_TAC[],
          DISCH_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP POSET_ANTISYM) THEN
          DISCH_THEN(MP_TAC o 
                     SPECL [(--`y:'a`--), (--`(lub:('a->bool)->'a) C`--)]) THEN
          ASM_REWRITE_TAC[]], ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN (--`y1:'a`--) STRIP_ASSUME_TAC) THEN
      MP_TAC(ASSUME (--`C wo_subset (\x:'a. M x /\ P x)`--)) THEN
      REWRITE_TAC[wo_subset] THEN BETA_TAC THEN
      DISCH_THEN(MP_TAC o SPEC (--`y1:'a`--)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_CASES_TAC (--`y:'a = y1`--) THENL
       [DISCH_THEN(MP_TAC o CONJ(ASSUME (--`(M:'a->bool) y1`--))) THEN
        DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN(MP_TAC o SPEC (--`(lub:('a->bool)->'a) C`--)) THEN
        UNDISCH_TAC (--`y:'a = y1`--) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        MATCH_MP_TAC(TAUT_CONV (--`a /\ ~b ==> (a ==> b \/ c) ==> c`--)) THEN
        CONJ_TAC THENL
         [ADM_THEN "M" (MATCH_MP_TAC o last o CONJUNCTS) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC (--`\x:'a. M x /\ P x`--) THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[wo_subset] THEN GEN_TAC THEN BETA_TAC THEN
          DISCH_THEN(ACCEPT_TAC o CONJUNCT1),
          DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP POSET_ANTISYM) THEN
          DISCH_THEN(MP_TAC o SPECL [(--`y:'a`--), 
                                     (--`(lub:('a->bool)->'a) C`--)]) THEN
          ASM_REWRITE_TAC[]],
        EXPAND_TAC "P" THEN DISCH_THEN(MP_TAC o SPEC (--`y:'a`--)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
        EXISTS_TAC (--`y1:'a`--) THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP(ASSUME (--`wo_chain(l:^ty) C`--))) THEN
        DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
        FIRST_ASSUM ACCEPT_TAC]], ALL_TAC] THEN
  SUBGOAL_THEN (--`wo_chain(l:^ty) M`--) ASSUME_TAC THENL
   [REWRITE_TAC[wo_chain] THEN 
    MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y:'a`--)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (fn th => ASSUME_TAC th THEN
      FIRST_ASSUM(MP_TAC o CONJ th o C MATCH_MP th)) ASSUME_TAC) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(MP_TAC o SPEC (--`y:'a`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
    EXISTS_TAC (--`(f:'a->'a) x`--) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ADM_THEN "M" (MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[wo_subset] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  EXISTS_TAC (--`(lub:('a->bool)->'a) M`--) THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME (--`wo_chain(l:^ty) M`--))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1),
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_ANTISYM) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME (--`wo_chain(l:^ty) M`--))) THEN
      DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
      ADM_THEN "M" (MATCH_MP_TAC o el 3 o CONJUNCTS) THEN
      ADM_THEN "M" (MATCH_MP_TAC o last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[SUBSET_REFL],
      FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME (--`wo_chain(l:^ty) M`--))) THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]] end);

(*===========================================================================*)
(* (2) HILBERT EPSILON AXIOM ==> KURATOWSKI'S LEMMA                          *)
(*===========================================================================*)

val ord = (--`\(U,V). P wo_subset U /\ U wo_subset V /\ wo_chain(l:^ty) V`--);

(*---------------------------------------------------------------------------*)
(* Show that "subset" on chains containing P is a partial order              *)
(*---------------------------------------------------------------------------*)

val POSET_ORD = prove_thm("POSET_ORD",
  (--`wo_poset ^ord`--),
  let val TRY_EXISTS_TAC =
    FIRST_ASSUM(fn th => EXISTS_TAC(rand(concl th)) THEN
                     ASM_REWRITE_TAC[] THEN NO_TAC) in
  REWRITE_TAC[wo_poset] THEN PBETA_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[wo_fl, SUBSET_REFL] THEN PBETA_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC CHAIN_SUBSET THEN TRY_EXISTS_TAC,
      MATCH_MP_TAC SUBSET_TRANS THEN TRY_EXISTS_TAC],
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN TRY_EXISTS_TAC,
    STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[]] end);

(*---------------------------------------------------------------------------*)
(* Apply CPO_FIX to an increasing chain of chains                            *)
(*---------------------------------------------------------------------------*)

val KL = prove_thm("KL",
  (--`!l:^ty. wo_poset l ==>
        !Q. wo_chain(l) Q ==>
            ?P. (wo_chain(l) P /\ Q wo_subset P) /\
                (!R. wo_chain(l) R /\ P wo_subset R ==> (R = P))`--),
  GEN_REWRITE_TAC I [] [TAUT_CONV (--`a = ~~a`--)] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`l:^ty`--) MP_TAC 
             o CONV_RULE NOT_FORALL_CONV) THEN
  PURE_REWRITE_TAC[NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`P:'a->bool`--) MP_TAC 
             o CONV_RULE NOT_FORALL_CONV) THEN
  PURE_REWRITE_TAC[NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  DISCH_TAC THEN C SUBGOAL_THEN MP_TAC
    (--`!Q. wo_chain(l:^ty) Q /\ P wo_subset Q ==>
        ?R. wo_chain(l) R /\ Q wo_subset R /\ ~(R = Q)`--) THENL
   [GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC (--`Q:'a->bool`--)) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
    REWRITE_TAC[NOT_IMP, CONJ_ASSOC], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV SKOLEM_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC (--`f:('a->bool)->('a->bool)`--)) THEN
  MP_TAC(ISPEC ord CPO_FIX) THEN REWRITE_TAC[POSET_ORD] THEN
  REWRITE_TAC[MATCH_MP POSET_FLEQ POSET_ORD, SUBSET_REFL] THEN PBETA_TAC THEN
  W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o rand o snd) THENL
   [ALL_TAC, DISCH_THEN(fn th => REWRITE_TAC[th, SUBSET_REFL]) THEN
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    PURE_ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
   [ALL_TAC, X_GEN_TAC (--`Q:'a->bool`--) THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(fn th => FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th) THEN
                    ASSUME_TAC (CONJUNCT2 th)) THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC (--`U:('a->bool)->bool`--) THEN DISCH_TAC THEN
  ASM_CASES_TAC (--`!X:'a->bool. ~(U X)`--) THENL
   [EXISTS_TAC (--`P:'a->bool`--) THEN 
    ASM_REWRITE_TAC[SUBSET_REFL], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC (--`R:'a->bool`--)) THEN
  EXISTS_TAC (--`(wo_Union U) :'a->bool`--) THEN MP_TAC
    (ASSUME (--`wo_chain(\(U,V). P wo_subset U /\ 
                                 U wo_subset V /\ 
                                 wo_chain(l:^ty) V)U`--)) THEN
  GEN_REWRITE_TAC(RATOR_CONV o RAND_CONV) [] [wo_chain] THEN
  PBETA_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN (--`X:'a->bool`--) 
              o SPECL [(--`X:'a->bool`--), (--`X:'a->bool`--)]) THEN
  REWRITE_TAC[SUBSET_REFL] THEN
  SUBGOAL_THEN (--`wo_chain(l:^ty) (wo_Union U)`--) ASSUME_TAC THENL
   [REWRITE_TAC[wo_Union, wo_chain] THEN BETA_TAC THEN
    MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y:'a`--)] THEN 
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN (--`X:'a->bool`--) STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN (--`Y:'a->bool`--) STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert
     (is_forall o snd o dest_forall) o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`X:'a->bool`--), (--`Y:'a->bool`--)]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC (--`(X:'a->bool) wo_subset Y`--) THEN 
      REWRITE_TAC[wo_subset] THEN
      DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o MATCH_MP th)) THEN
      UNDISCH_TAC (--`wo_chain(l:^ty) Y`--) THEN REWRITE_TAC[wo_chain] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      UNDISCH_TAC (--`(Y:'a->bool) wo_subset X`--) THEN 
      REWRITE_TAC[wo_subset] THEN
      DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o MATCH_MP th)) THEN
      UNDISCH_TAC (--`wo_chain(l:^ty) X`--) THEN REWRITE_TAC[wo_chain] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN 
  GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) []
                  [TAUT_CONV (--`(a ==> b /\ c) = (a ==> b) /\ (a ==> c)`--)] 
  THEN CONV_TAC(ONCE_DEPTH_CONV FORALL_AND_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`!X:'a->bool. U X ==> X wo_subset(wo_Union U)`--) 
               ASSUME_TAC
   THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wo_subset, wo_Union] THEN
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN 
    EXISTS_TAC (--`X:'a->bool`--) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`(P:'a->bool) wo_subset (wo_Union U)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (--`R:'a->bool`--) THEN 
   CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  X_GEN_TAC (--`Q:'a->bool`--) THEN 
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[wo_subset, wo_Union] THEN BETA_TAC THEN
  DISCH_THEN(curry op THEN (GEN_TAC THEN DISCH_THEN
   (X_CHOOSE_TAC (--`M:'a->bool`--))) o MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC (--`M:'a->bool`--)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);

(*===========================================================================*)
(* (3) KURATOWSKI'S LEMMA ==> HAUSDORFF MAXIMAL PRINCIPLE                    *)
(*===========================================================================*)

val HP = prove_thm("HP",
  (--`!l:^ty. wo_poset l ==>
        ?P. wo_chain(l) P /\ !Q. wo_chain(l) Q  /\ P wo_subset Q 
            ==> (Q = P)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC (--`\x:'a. F`--) o MATCH_MP KL) THEN
  REWRITE_TAC[wo_chain, wo_subset]);

(*===========================================================================*)
(* (4) HAUSDORFF MAXIMAL PRINCIPLE ==> ZORN'S LEMMA                          *)
(*===========================================================================*)

val ZL = prove_thm("ZL",
  (--`!l:^ty. wo_poset l /\
           (!P. wo_chain(l) P ==> (?y. wo_fl(l) y /\ !x. P x ==> l(x,y))) ==>
        ?y. wo_fl(l) y /\ !x. l(y,x) ==> (y = x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN (--`M:'a->bool`--) 
                            STRIP_ASSUME_TAC o MATCH_MP HP) THEN
  UNDISCH_TAC (--`!P. wo_chain(l:^ty) P ==> 
                     (?y. wo_fl(l) y /\ !x. P x ==> l(x,y))`--) THEN
  DISCH_THEN(MP_TAC o SPEC (--`M:'a->bool`--)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`m:'a`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`m:'a`--) THEN ASM_REWRITE_TAC[] THEN 
  X_GEN_TAC (--`z:'a`--) THEN
  DISCH_TAC THEN GEN_REWRITE_TAC I [] 
                               [TAUT_CONV (--`a = ~~a`--)] THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`wo_chain(l) (\x:'a. M x \/ (x = z))`--) MP_TAC THENL
   [REWRITE_TAC[wo_chain] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
    ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC (--`wo_chain(l:^ty) M`--) THEN REWRITE_TAC[wo_chain] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      DISJ1_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC (--`m:'a`--) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      DISJ2_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC (--`m:'a`--) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_REFL) THEN
      REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`m:'a`--) THEN ASM_REWRITE_TAC[]],
    ALL_TAC] THEN
  SUBGOAL_THEN (--`M wo_subset (\x:'a. M x \/ (x = z))`--) MP_TAC THENL
   [REWRITE_TAC[wo_subset] THEN GEN_TAC THEN BETA_TAC THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]), ALL_TAC] THEN
  GEN_REWRITE_TAC I [] 
                 [TAUT_CONV (--`(a ==> b ==> c) = (b /\ a ==> c)`--)] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[] THEN CONV_TAC(RAND_CONV FUN_EQ_CONV) THEN
  DISCH_THEN(MP_TAC o SPEC (--`z:'a`--)) THEN 
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [(--`m:'a`--), (--`z:'a`--)] 
              o MATCH_MP POSET_ANTISYM) THEN
  ASM_REWRITE_TAC[]);

(*===========================================================================*)
(* (5) ZORN'S LEMMA ==> WELL-ORDERING PRINCIPLE                              *)
(*===========================================================================*)

val INSEG_WOSET = prove_thm("INSEG_WOSET",
  (--`!(l:^ty) m. wo_inseg(l,m) ==> wo_woset l /\ wo_woset m`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[wo_inseg] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val INSEG_FL = prove_thm("INSEG_FL",
  (--`!l:^ty. wo_fl(wo_inseg) l = wo_woset l`--),
  GEN_TAC THEN REWRITE_TAC[wo_fl, wo_inseg] THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (DISJ_CASES_THEN (fn th => REWRITE_TAC[th]))),
    DISCH_TAC THEN EXISTS_TAC (--`l:^ty`--) THEN ASM_REWRITE_TAC[wo_inseg] THEN
    MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y:'a`--)] THEN
    GEN_REWRITE_TAC I []
                    [TAUT_CONV (--`(b = a /\ b) = (b ==> a)`--)] THEN
    DISCH_THEN(curry op THEN (EXISTS_TAC (--`x:'a`--)) 
               o (fn th => REWRITE_TAC[th]))]);

val INSEG_SUBSET = prove_thm("INSEG_SUBSET",
  (--`!(l:^ty) m. wo_inseg(l,m) ==> !x y. l(x,y) ==> m(x,y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[wo_inseg] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

(*---------------------------------------------------------------------------*)
(* Initial segment defines a partial order                                   *)
(*---------------------------------------------------------------------------*)
val INSEG_POSET = prove_thm("INSEG_POSET",
  (--`wo_poset (wo_inseg:^ty#^ty->bool)`--),
  REWRITE_TAC[wo_poset, wo_inseg] THEN REPEAT CONJ_TAC THEN
  MAP_EVERY (TRY o X_GEN_TAC) [(--`X:^ty`--), (--`Y:^ty`--),(--`Z:^ty`--)] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INSEG_FL]) THEN
    ASM_REWRITE_TAC[] THEN 
    MAP_EVERY X_GEN_TAC [(--`x:'a`--),(--`y:'a`--)] THEN
    GEN_REWRITE_TAC I []
                   [TAUT_CONV (--`(b = a /\ b) = (b ==> a)`--)] THEN
    DISCH_TAC THEN REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`x:'a`--) THEN
    ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a ==> b) ==> (a /\ b /\ c = a /\ c)`--)) THEN
    MAP_EVERY (fn th => REWRITE_TAC[MATCH_MP WOSET_FLEQ th])
     [ASSUME (--`wo_woset(X:^ty)`--), ASSUME (--`wo_woset(Y:^ty)`--)] THEN
    FIRST_ASSUM(fn th => GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [] [th]) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2),
    CONV_TAC(X_FUN_EQ_CONV (--`p:'a#'a`--)) THEN GEN_PAIR_TAC THEN EQ_TAC THEN
    FIRST_ASSUM(fn th => GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [] [th]) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2)]);;


(* Original 
 * val INSEG_POSET = prove_thm("INSEG_POSET",
 *   (--`wo_poset (wo_inseg:^ty#^ty->bool)`--),
 *   REWRITE_TAC[wo_poset, wo_inseg] THEN REPEAT CONJ_TAC THEN
 *   MAP_EVERY(TRY o X_GEN_TAC)[(--`X:^ty`--),(--`Y:^ty`--),(--`Z:^ty`--)] THEN
 *   DISCH_THEN STRIP_ASSUME_TAC THENL
 *    [RULE_ASSUM_TAC(REWRITE_RULE[INSEG_FL]) THEN
 *     ASM_REWRITE_TAC[] THEN
 *     MAP_EVERY X_GEN_TAC[(--`x:'a`--),(--`y:'a`--)] THEN
 *     GEN_REWRITE_TAC I Rewrite.empty_rewrites 
 *                    [TAUT_CONV (--`(b = a /\ b) = (b ==> a)`--)] THEN
 *     DISCH_TAC THEN REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`x:'a`--) THEN
 *     ASM_REWRITE_TAC[],
 *     ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
 *     MATCH_MP_TAC(TAUT_CONV(--`(a ==> b) ==> (a /\ b /\ c = a /\ c)`--)) THEN
 *     MAP_EVERY (fn th => REWRITE_TAC[MATCH_MP WOSET_FLEQ th])
 *      [ASSUME (--`wo_woset(X:^ty)`--), ASSUME (--`wo_woset(Y:^ty)`--)] THEN
 *     FIRST_ASSUM(fn th => GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) 
 *                                          Rewrite.empty_rewrites [th]) THEN
 *     DISCH_THEN(ACCEPT_TAC o CONJUNCT2),
 *     CONV_TAC(X_FUN_EQ_CONV (--`p:'a#'a`--)) THEN GEN_PAIR_TAC THEN
 *     PURE_ASM_REWRITE_TAC[TAUT_CONV (--`(a /\ b = b) = b ==> a`--)] THEN
 *     FIRST_ASSUM(fn th => DISCH_THEN(MP_TAC o
 *       MATCH_MP (MATCH_MP INSEG_SUBSET th))) THEN
 *     DISCH_TAC THEN REWRITE_TAC[wo_fl] THEN
 *     EXISTS_TAC (--`FST(p:'a#'a)`--) THEN
 *     DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
 *****)
(*---------------------------------------------------------------------------*)
(* Field of a union of relations is the union of the fields                  *)
(*---------------------------------------------------------------------------*)

val FL_UNION = prove_thm("FL_UNION",
  (--`!P x. wo_fl(wo_Union P) x = ?l:^ty. P l /\ wo_fl(l) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[wo_Union, wo_fl] THEN BETA_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV OR_EXISTS_CONV) THEN
  REWRITE_TAC[GSYM LEFT_AND_OVER_OR] THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_AND_EXISTS_CONV) THEN
  CONV_TAC(RAND_CONV SWAP_EXISTS_CONV) THEN REFL_TAC);

(*---------------------------------------------------------------------------*)
(* The union of a *chain* of wosets is a woset                               *)
(*---------------------------------------------------------------------------*)

val WOSET_UNION = prove_thm("INSEG_WOSET_UNION",
  (--`!P:^ty->bool. wo_chain(wo_inseg) P ==> wo_woset(wo_Union P)`--),
  GEN_TAC THEN REWRITE_TAC[wo_chain] THEN DISCH_TAC THEN
  REWRITE_TAC[WOSET] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y:'a`--)] THEN 
    REWRITE_TAC[wo_Union] THEN
    BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN (--`l:^ty`--) STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN (--`m:^ty`--) STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`l:^ty`--), (--`m:^ty`--)]) THEN 
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN 
                (fn th => ASSUME_TAC(MATCH_MP INSEG_SUBSET th) THEN
      STRIP_ASSUME_TAC(MATCH_MP INSEG_WOSET th))) THENL
    map (MP_TAC o C SPEC WOSET_ANTISYM) [(--`m:^ty`--), (--`l:^ty`--)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
    X_GEN_TAC (--`Q:'a->bool`--) THEN REWRITE_TAC[FL_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC (--`w:'a`--))) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o MATCH_MP th) 
                                   THEN ASSUME_TAC th) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`l:^ty`--) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPECL [(--`l:^ty`--), (--`l:^ty`--)]) THEN
    REWRITE_TAC[ASSUME (--`(P:^ty->bool) l`--)] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1 o MATCH_MP INSEG_WOSET) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
    DISCH_THEN(MP_TAC o SPEC (--`\x:'a. Q x /\ wo_fl(l) x`--)) THEN 
    BETA_TAC THEN REWRITE_TAC[TAUT_CONV (--`a /\ b ==> b`--)] THEN
    CONV_TAC(RATOR_CONV(RAND_CONV(LEFT_IMP_EXISTS_CONV))) THEN
    DISCH_THEN(MP_TAC o SPEC (--`w:'a`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`y:'a`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN 
    X_GEN_TAC (--`z:'a`--) THEN
    ASM_CASES_TAC (--`wo_fl(l:^ty) z`--) THENL
     [DISCH_THEN(MP_TAC o C CONJ (ASSUME (--`wo_fl(l:^ty) z`--))) THEN
      DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[wo_Union] THEN BETA_TAC THEN EXISTS_TAC (--`l:^ty`--) THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(X_CHOOSE_THEN (--`m:^ty`--) STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[wo_Union] THEN BETA_TAC THEN EXISTS_TAC (--`m:^ty`--) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPECL [(--`m:^ty`--), (--`l:^ty`--)]) THEN
      REWRITE_TAC[ASSUME (--`(P:^ty->bool) l`--), 
                  ASSUME (--`(P:^ty->bool) m`--)] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL

       [REWRITE_TAC[wo_inseg, CONJ_ASSOC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        DISCH_THEN(MP_TAC o SPECL [(--`z:'a`--), (--`z:'a`--)]) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY (fn th => ASM_REWRITE_TAC[GSYM(MATCH_MP WOSET_FLEQ th)])
         [ASSUME (--`wo_woset(l:^ty)`--), ASSUME (--`wo_woset(m:^ty)`--)],
        REWRITE_TAC[wo_inseg, CONJ_ASSOC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        DISCH_THEN(fn th => MP_TAC th THEN 
                            MP_TAC(SPECL [(--`y:'a`--), (--`y:'a`--)] th)) THEN
        MAP_EVERY (fn th => ASM_REWRITE_TAC[GSYM(MATCH_MP WOSET_FLEQ th)])
         [ASSUME (--`wo_woset(l:^ty)`--), 
          ASSUME (--`wo_woset(m:^ty)`--)] THEN DISCH_TAC THEN
        DISCH_THEN(MP_TAC o SPECL [(--`z:'a`--), (--`y:'a`--)]) THEN 
        ASM_REWRITE_TAC[] THEN
        CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
        MP_TAC(MATCH_MP WOSET_TOTAL (ASSUME (--`wo_woset(m:^ty)`--))) THEN
        DISCH_THEN(MP_TAC o SPECL [(--`y:'a`--), (--`z:'a`--)]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN UNDISCH_TAC (--`~wo_fl(l:^ty) z`--) THEN 
        REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`y:'a`--) THEN 
        ASM_REWRITE_TAC[]]]]);

(*---------------------------------------------------------------------------*)
(* There is a maximal woset                                                  *)
(*---------------------------------------------------------------------------*)

val WOSET_MAXIMAL = prove_thm("WOSET_MAXIMAL",
  (--`?l:^ty. wo_fl(wo_inseg) l /\ (!m. wo_inseg(l,m) ==> (l = m))`--),
  MATCH_MP_TAC ZL THEN REWRITE_TAC[INSEG_POSET] THEN
  X_GEN_TAC (--`P:^ty->bool`--) THEN DISCH_TAC THEN
  EXISTS_TAC (--`wo_Union(P:^ty->bool)`--) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WOSET_UNION) THEN
  ASM_REWRITE_TAC[INSEG_FL] THEN
  X_GEN_TAC (--`l:^ty`--) THEN DISCH_TAC THEN REWRITE_TAC[wo_inseg] THEN
  SUBGOAL_THEN (--`wo_woset(l:^ty)`--) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONV_RULE(REWR_CONV wo_chain)) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`l:^ty`--), (--`l:^ty`--)]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[wo_inseg] THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]), ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN 
  MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y:'a`--)] THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[wo_Union] THEN BETA_TAC THEN EXISTS_TAC (--`l:^ty`--) THEN
      ASM_REWRITE_TAC[]],
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[wo_Union] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN (--`m:^ty`--) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o CONV_RULE(REWR_CONV wo_chain)) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`m:^ty`--), (--`l:^ty`--)]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(MATCH_MP_TAC o MATCH_MP INSEG_SUBSET) THEN
      FIRST_ASSUM ACCEPT_TAC,
      REWRITE_TAC[wo_inseg] THEN DISCH_THEN(fn th => ASM_REWRITE_TAC[th])]]);

(*---------------------------------------------------------------------------*)
(* The field of the maximal wellorder covers the entire type                 *)
(*---------------------------------------------------------------------------*)

val tm = (--`\(x,y). l(x,y) \/ (wo_fl(l:^ty) x \/ (x = m)) /\ (y = m)`--);

val WO_EXFL = prove_thm("WO_EXFL",
  (--`!x. wo_fl(^tm) x = wo_fl(l) x \/ (x = m)`--),
  GEN_TAC THEN REWRITE_TAC[wo_fl] THEN PBETA_TAC THEN
  ASM_CASES_TAC (--`x:'a = m`--) THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC (--`m:'a`--) THEN ASM_REWRITE_TAC[],
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN (--`y:'a`--) MP_TAC) THENL
     [DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[],
      DISCH_THEN DISJ_CASES_TAC THEN EXISTS_TAC (--`y:'a`--) THEN
      ASM_REWRITE_TAC[]]]);

val WO_TYPE = prove_thm("WO_TYPE",
  (--`?l:^ty. wo_woset l /\ (!x. wo_fl(l) x)`--),
  X_CHOOSE_THEN (--`l:^ty`--) STRIP_ASSUME_TAC WOSET_MAXIMAL THEN
  EXISTS_TAC (--`l:^ty`--) THEN ASM_REWRITE_TAC[GSYM INSEG_FL] THEN
  GEN_REWRITE_TAC I [] [TAUT_CONV (--`a = ~~a`--)] THEN
  CONV_TAC(RAND_CONV NOT_FORALL_CONV) THEN 
  DISCH_THEN(X_CHOOSE_TAC (--`m:'a`--)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INSEG_FL]) THEN
  SUBGOAL_THEN (--`wo_inseg(l,^tm)`--) 
               (fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THENL
   [ALL_TAC, DISCH_THEN(MP_TAC o C AP_THM (--`(m:'a,m)`--)) THEN
    PBETA_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fn th => ASM_REWRITE_TAC[GSYM(MATCH_MP WOSET_FLEQ th)])] THEN
  ASM_REWRITE_TAC[wo_inseg] THEN PBETA_TAC THEN CONJ_TAC THENL
   [ALL_TAC, MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y:'a`--)] THEN
    ASM_CASES_TAC (--`(l:^ty)(x,y)`--) THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC[]]] THEN
  REWRITE_TAC[WOSET] THEN PBETA_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y:'a`--)] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
      ASM_REWRITE_TAC[],
      UNDISCH_TAC (--`~wo_fl(l:^ty) m`--) THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[wo_fl] THEN
      EXISTS_TAC (--`y:'a`--) THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
      DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      FIRST_ASSUM SUBST_ALL_TAC THEN UNDISCH_TAC (--`~wo_fl(l:^ty) m`--) THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`x:'a`--) THEN
      DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN
  X_GEN_TAC (--`P:'a->bool`--) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC (--`w:'a`--))) THEN
  REWRITE_TAC[WO_EXFL] THEN FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
  DISCH_THEN(MP_TAC o SPEC (--`\x:'a. P x /\ wo_fl(l) x`--)) THEN
  BETA_TAC THEN REWRITE_TAC[TAUT_CONV (--`a /\ b ==> b`--)] THEN
  ASM_CASES_TAC (--`?x:'a. P x /\ wo_fl(l) x`--) THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN (--`y:'a`--) STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN 
    X_GEN_TAC (--`z:'a`--) THEN DISCH_THEN(fn th => ASSUME_TAC th THEN
      FIRST_ASSUM(DISJ_CASES_TAC o C MATCH_MP th)) THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(MP_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
    REWRITE_TAC[TAUT_CONV (--`(a ==> b ==> c) = (a /\ b ==> c)`--)] THEN
    CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
    DISCH_THEN(MP_TAC o GEN_ALL o MATCH_MP (TAUT_CONV
      (--`~(a /\ b) /\ (a ==> b \/ c) ==> (a ==> c)`--)) o SPEC_ALL) THEN
    DISCH_TAC THEN EXISTS_TAC (--`m:'a`--) THEN
    SUBGOAL_THEN (--`w:'a = m`--) SUBST_ALL_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    DISJ2_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Now the restriction to an arbitrary set P                                 *)
(*---------------------------------------------------------------------------*)

val WO_RESTFL = prove_thm("WO_RESTFL",
  (--`!l. wo_woset l ==>
       !P. wo_fl(\(x:'a,y). P x /\ P y /\ l(x,y)) x = P x /\ wo_fl(l) x`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN 
  REWRITE_TAC[wo_fl] THEN PBETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN (--`y:'a`--) DISJ_CASES_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN (--`y:'a`--) DISJ_CASES_TAC)) THEN
    EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[GSYM(MATCH_MP WOSET_FLEQ th)]) THEN
    REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[]]);

val WO = prove_thm("WO",
  (--`!P. ?l:^ty. wo_woset l /\ (wo_fl(l) = P)`--),
  GEN_TAC THEN X_CHOOSE_THEN (--`l:^ty`--) STRIP_ASSUME_TAC WO_TYPE THEN
  EXISTS_TAC (--`\(x:'a,y). P x /\ P y /\ l(x,y)`--) THEN
  REWRITE_TAC[WOSET] THEN PBETA_TAC THEN 
  CONV_TAC(RAND_CONV(X_FUN_EQ_CONV (--`x:'a`--))) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP WO_RESTFL th]) THEN PBETA_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[],
    X_GEN_TAC (--`Q:'a->bool`--) THEN 
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
    DISCH_THEN(MP_TAC o SPEC (--`Q:'a->bool`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`y:'a`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN 
    GEN_TAC THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);


(*===========================================================================*)
(* (6) Proof of recursion theorem                                            *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Induction on a wellorder                                                  *)
(*---------------------------------------------------------------------------*)

val WO_INDUCT = prove_thm("WO_INDUCT",
  (--`!P l. wo_woset l /\
         (!x:'a. wo_fl(l) x /\ (!y. (wo_less l)(y,x) ==> P(y)) ==> P(x))
        ==> !x. wo_fl(l) x ==> P(x)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
  DISCH_THEN(MP_TAC o SPEC (--`\x:'a. wo_fl(l) x /\ ~P(x)`--)) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[TAUT_CONV (--`a /\ b ==> a`--)] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`x:'a`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE
    [TAUT_CONV (--`(a /\ ~b ==> c) = (a /\ ~c ==> b)`--)]) THEN
  X_GEN_TAC (--`y:'a`--) THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[wo_less]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`y:'a`--), (--`x:'a`--)]) THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Tactic to apply the above                                                 *)
(*---------------------------------------------------------------------------*)

val WO_INDUCT_TAC =
  let val thm = CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) WO_INDUCT in
  fn (asl,w) =>
    let val qv = fst(dest_forall w)
        val bod = (snd o dest_imp o snd o dest_forall) w
        val pred = mk_abs(qv,bod)
        val thi = ISPEC pred thm
        val thf = CONV_RULE
      (ONCE_DEPTH_CONV(BETA_CONV o assert (curry op = pred o rator))) thi in
    MATCH_MP_TAC thf (asl,w) end end;

(*---------------------------------------------------------------------------*)
(* Functions satisfying recursion eqn must agree on their common "domain"    *)
(*---------------------------------------------------------------------------*)

val AGREE_LEMMA = prove_thm("AGREE_LEMMA",
  (--`!l h (ms:'a->'c) m n f g z.
        wo_woset l /\
        (!x. wo_fl(l)(ms(x))) /\
        (!f f' x. (!y. (wo_less l)(ms y,ms x) ==> (f(y) = f'(y))) ==>
                        (h f x = h f' x)) /\
        (!x. l(ms x,m) ==> (f x = h f x)) /\
        (!x. l(ms x,n) ==> (g x = h g x)) /\
        l(ms z,m) /\
        l(ms z,n) ==> (f z :'b = g z)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`!p (x:'a). (l:'c#'c->bool)(p,m) /\ l(p,n) /\ (ms(x) = p)
                           ==> (f x :'b= g x)`--) MATCH_MP_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC (--`wo_fl(l:'c#'c->bool) p`--) THENL
     [UNDISCH_TAC (--`wo_fl(l:'c#'c->bool) p`--) THEN
      MAP_EVERY (W (curry SPEC_TAC)) [(--`x:'a`--), (--`p:'c`--)],
      STRIP_TAC THEN UNDISCH_TAC (--`~wo_fl(l:'c#'c->bool) p`--) THEN
      REWRITE_TAC[wo_fl] THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
      EXISTS_TAC (--`n:'c`--) THEN ASM_REWRITE_TAC[]],
    EXISTS_TAC (--`(ms:'a->'c) z`--) THEN ASM_REWRITE_TAC[]] THEN
  CONV_TAC(ONCE_DEPTH_CONV FORALL_IMP_CONV) THEN
  WO_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`r:'c`--) THEN STRIP_TAC THEN
  X_GEN_TAC (--`x:'a`--) THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RES_THEN(fn th => REWRITE_TAC[th]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC (--`y:'a`--) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAUT_CONV (--`a ==> b ==> c = a /\ b ==> c`--)])
  THEN FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (--`(ms:'a->'c) y`--) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS) THEN
  EXISTS_TAC (--`(ms:'a->'c) x`--) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wo_less]) THEN
  ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Transfinite recursion *below a given value of the domain*                 *)
(*---------------------------------------------------------------------------*)

val WO_RECURSE_LOCAL = prove_thm("WO_RECURSE_LOCAL",
  (--`!l h (ms:'a->'c).
        wo_woset l /\
        (!x. wo_fl(l)(ms(x))) /\
        (!f f' x. (!y. (wo_less l)(ms y,ms x) ==> (f(y) = f'(y))) ==>
                        (h f x = h f' x))
            ==> !n. ?f:'a->'b. !x. l(ms x,n) ==> (f x = h f x)`--),
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC (--`wo_fl(l:'c#'c->bool) n`--) THENL
   [UNDISCH_TAC (--`wo_fl(l:'c#'c->bool) n`--) THEN 
    SPEC_TAC((--`n:'c`--),(--`n:'c`--)),
    EXISTS_TAC (--`f:'a->'b`--) THEN X_GEN_TAC (--`x:'a`--) THEN
    DISCH_TAC THEN UNDISCH_TAC (--`~wo_fl(l:'c#'c->bool) n`--) THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[wo_fl] THEN EXISTS_TAC (--`(ms:'a->'c) x`--) THEN
    ASM_REWRITE_TAC[]] THEN
  WO_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`m:'c`--) THEN 
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC(RATOR_CONV(ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV SKOLEM_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC (--`Fn:'c->'a->'b`--)) THEN
  EXISTS_TAC (--`\x:'a. h(\y. (Fn:'c->'a->'b)(ms y) y) x :'b`--) THEN
  X_GEN_TAC (--`x:'a`--) THEN DISCH_TAC THEN BETA_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC (--`y:'a`--) THEN
  DISCH_TAC THEN BETA_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAUT_CONV (--`a ==> b ==> c = a /\ b ==> c`--)])
  THEN SUBGOAL_THEN (--`(Fn:'c->'a->'b) (ms y) y = h (Fn(ms y)) y`--) 
                    SUBST1_TAC 
  THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS_LESS) THEN
      EXISTS_TAC (--`(ms:'a->'c) x`--) THEN ASM_REWRITE_TAC[],
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL) THEN
      ASM_REWRITE_TAC[]],
    FIRST_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC (--`z:'a`--) THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC AGREE_LEMMA THEN
    MAP_EVERY EXISTS_TAC [(--`l:'c#'c->bool`--), 
                          (--`h:('a->'b)->'a->'b`--), (--`ms:'a->'c`--),
      (--`(ms:'a->'c) y`--), (--`(ms:'a->'c) z`--)] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (--`(l:'c#'c->bool)(ms(z:'a),ms(z))`--) ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL), ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EVERY_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[wo_less] th]) THEN
    SUBGOAL_THEN (--`(wo_less l)(ms(y:'a),(m:'c))`--) ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS_LESS) THEN
      EXISTS_TAC (--`(ms:'a->'c) x`--), ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC (--`w:'a`--) THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS_LESS) THEN
    EXISTS_TAC (--`(ms:'a->'c) y`--) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS) THEN
    EXISTS_TAC (--`(ms:'a->'c) x`--) THEN
    EVERY_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[wo_less] th])]);

(*---------------------------------------------------------------------------*)
(* Finally, an overall function                                              *)
(*---------------------------------------------------------------------------*)

val WO_RECURSE_EXISTS = prove_thm("WO_RECURSE_EXISTS",
  (--`!l h (ms:'a->'c).
        wo_woset l /\
        (!x. wo_fl(l)(ms(x))) /\
        (!f f' x. (!y. (wo_less l)(ms y,ms x) ==> (f(y) = f'(y))) ==>
                        (h f x = h f' x))
            ==> ?f:'a->'b. !x. f x = h f x`--),
  REPEAT GEN_TAC THEN DISCH_THEN(fn th =>
    STRIP_ASSUME_TAC th THEN MP_TAC(MATCH_MP WO_RECURSE_LOCAL th)) THEN
  DISCH_THEN(MP_TAC o CONV_RULE SKOLEM_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC (--`Fn:'c->'a->'b`--)) THEN
  EXISTS_TAC (--`\x. (Fn:'c->'a->'b) (ms x) x`--) THEN GEN_TAC THEN 
  BETA_TAC THEN SUBGOAL_THEN (--`(Fn:'c->'a->'b) (ms x) x = h (Fn(ms x)) x`--) 
                             SUBST1_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL) THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC (--`y:'a`--) THEN
    DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC AGREE_LEMMA THEN
    MAP_EVERY EXISTS_TAC [(--`l:'c#'c->bool`--), (--`h:('a->'b)->'a->'b`--),
               (--`ms:'a->'c`--),(--`(ms:'a->'c) x`--), (--`(ms:'a->'c) y`--)] 
    THEN ASM_REWRITE_TAC[] THEN
    EVERY_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[wo_less] th]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL) THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Now the final version including uniqueness                                *)
(*---------------------------------------------------------------------------*)

val WO_RECURSE = prove_thm("WO_RECURSE ",
  (--`!l h (ms:'a->'c).
        wo_woset l /\
        (!x. wo_fl(l)(ms(x))) /\
        (!f g x. (!y. (wo_less l)(ms y,ms x) ==> (f(y) = g(y)))
                 ==> (h f x = h g x))
        ==> ?!f:'a->'b. !x. f x = h f x`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXISTS_UNIQUE_CONV THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP WO_RECURSE_EXISTS th]) THEN
  MAP_EVERY X_GEN_TAC [(--`f1:'a->'b`--), (--`f2:'a->'b`--)] THEN 
  STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`z:'a`--) THEN
  MATCH_MP_TAC AGREE_LEMMA THEN
  MAP_EVERY EXISTS_TAC 
         [(--`l:'c#'c->bool`--), (--`h:('a->'b)->'a->'b`--), (--`ms:'a->'c`--),
          (--`(ms:'a->'c) z`--), (--`(ms:'a->'c) z`--)] THEN 
  ASM_REWRITE_TAC[] THEN 
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL o el 1 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Now the special case of natural number measure                            *)
(*---------------------------------------------------------------------------*)

val FL_NUM = prove_thm("FL_NUM",
  (--`!n. wo_fl(\(m,n). m <= n) n`--),
  GEN_TAC THEN REWRITE_TAC[wo_fl] THEN
  EXISTS_TAC (--`n:num`--) THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  REWRITE_TAC[LESS_EQ_REFL]);

val WOSET_NUM = prove_thm("WOSET_NUM",
  (--`wo_woset(\(m,n). m <= n)`--),
  REWRITE_TAC[WOSET] THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  REWRITE_TAC[LESS_EQUAL_ANTISYM, FL_NUM] THEN
  GEN_TAC THEN CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV CONTRAPOS_CONV)) THEN
  REWRITE_TAC[NOT_LESS_EQUAL, WOP]);

val WO_RECURSE_NUM = prove_thm("WO_RECURSE_NUM",
  (--`!h ms.
     (!f g x. (!y. ms y < ms x ==> (f(y) = g(y))) ==> (h f x = h g x))
            ==> ?!f:'a->'b. !x. f x = h f x`--),
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC (--`\(m,n). m <= n`--) WO_RECURSE) THEN
  EXISTS_TAC (--`ms:'a->num`--) THEN REWRITE_TAC[FL_NUM, WOSET_NUM] THEN
  REWRITE_TAC[wo_less] THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  REWRITE_TAC[LESS_OR_EQ, TAUT_CONV (--`(a \/ b) /\ ~b = a /\ ~b`--)] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_NOT_EQ THEN
  ASM_REWRITE_TAC[]);

export_theory();
