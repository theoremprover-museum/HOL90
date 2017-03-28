(* ==================================================================== *)
(* FILE		: mk_koenig.sml						*)
(* DESCRIPTION  : Derivation of Koenig's lemma				*)
(* AUTHOR       : Paul Loewenstein (paul.loewenstein@eng.sun.com)       *)
(* DATE		: 19 February 1993                                      *)
(* ==================================================================== *)

new_theory "koenig";

val Bounded = new_definition ("Bounded", (--`Bounded b P =
 (?f. (!x:'a. P x ==> (?n. n < b /\ (x = f n))))`--));

val Finite = new_definition ("Finite",
  (--`Finite (P:'a->bool) = (?b. Bounded b P)`--));

(* Finite can be expressed as an equality - useful for rewriting *)

val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";

val Finite_EQ = TAC_PROOF (([],
  (--`!P. Finite P = (?b f. (!x:'a. P x = (?n. n < b /\ (x = f n))))`--)),
 GEN_TAC THEN
 REWRITE_TAC[Finite,Bounded] THEN
 EQ_TAC THEN
 STRIP_TAC THENL
 [
  ASM_CASES_TAC (--`?x:'a.P x`--) THENL
  [
   POP_ASSUM STRIP_ASSUME_TAC THEN
   EXISTS_TAC (--`b:num`--) THEN
   EXISTS_TAC (--`\n:num. P (f n) => f n | x:'a`--) THEN
   BETA_TAC THEN
   GEN_TAC THEN
   EQ_TAC THENL
   [
    DISCH_THEN
     (fn x => ASSUME_TAC x THEN ANTE_RES_THEN STRIP_ASSUME_TAC x) THEN
    EXISTS_TAC (--`n:num`--) THEN
    POP_ASSUM (ASSUME_TAC o SYM) THEN
    ASM_REWRITE_TAC[]
   ,
    STRIP_TAC THEN
    ASM_CASES_TAC (--`P ((f:num->'a) n):bool`--) THEN
    ASM_REWRITE_TAC[]
   ]
  ,
   EXISTS_TAC (--`0`--) THEN
   POP_ASSUM (ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
   ASM_REWRITE_TAC[NOT_LESS_0]
  ]
 ,
  EXISTS_TAC (--`b:num`--) THEN
  EXISTS_TAC (--`f:num->'a`--) THEN
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  EXISTS_TAC (--`n:num`--) THEN
  CONJ_TAC THEN
  FIRST_ASSUM ACCEPT_TAC
 ]);

(*

 A directed graph connecting vertices in set represented by type
 :'a can be represented by a relation X:'a->'a->bool. X v v' is true
 iff there is an edge from v to v'.

 The graph is finitely branching if !v. Finite X v.

*)

(* There exists an infinite path from vertex x in Digraph X *)

val Infinite_Path = new_definition ("Infinite_Path",
 (--`Infinite_Path x X =
   (?s. (s 0 = (x:'a)) /\ (!d. X (s d) (s (SUC d))))`--));

(* There is no bound on the length of paths from x *)

val Unbounded_Path = new_definition ("Unbounded_Path",
 (--`Unbounded_Path x X =
   (!n. (?s. (s 0 = (x:'a)) /\ (!d. d < n ==> X (s d) (s (SUC d)))))`--));

(* 2 lemmas, a conversion and a tactic for Koenig_Digraph_Lemma *)

val LESS_TRANS = theorem "arithmetic" "LESS_TRANS";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";

val LESS_LEQ_TRANS = TAC_PROOF (([],
  (--`! m n p. m < n /\ n <= p ==> m < p`--)),
 REPEAT STRIP_TAC THEN
 POP_ASSUM (DISJ_CASES_TAC o REWRITE_RULE[LESS_OR_EQ]) THENL
 [
  IMP_RES_TAC LESS_TRANS
 ,
  POP_ASSUM (fn x => POP_ASSUM (fn y => ACCEPT_TAC (SUBS [x] y)))
 ]);

(* |- !m n. m < (SUC n) = m <= n *)

val LESS_THM = theorem "prim_rec" "LESS_THM";

val LESS_SUC_LESS_EQ =
 PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL LESS_OR_EQ)]
  (PURE_ONCE_REWRITE_RULE[DISJ_SYM] LESS_THM);

(* |- (?q. (q = r) /\ P[q]) = P[r] *)

fun EXISTS_PRUNE_CONV tm =
 let val {Bvar = q,Body = c} = dest_exists tm;
     val {conj1 = e, conj2 = p} = dest_conj c;
     val {lhs = _,rhs = r} = dest_eq e in
    IMP_ANTISYM_RULE
     (let val th = ASSUME c in
       DISCH tm (CHOOSE (q,ASSUME tm) (SUBS [CONJUNCT1 th] (CONJUNCT2 th)))
      end)
     (let val pr = subst [{residue = r, redex = q}] p in
       DISCH pr (EXISTS (tm,r) (CONJ (REFL r) (ASSUME pr)))
      end)
 end
 handle _ =>
   raise HOL_ERR {origin_structure = "mk_koenig",
      origin_function = "EXISTS_PRUNE_CONV",
      message = "Some error or other"};

fun CCONTR_TAC (asl, w) =
  ([(mk_neg w :: asl, (--`F`--))], (fn [th] => CCONTR w th));

(* Koenig's Lemma - Digraph Formulation *)

val SIMP_REC_THM = theorem "prim_rec" "SIMP_REC_THM";
val INDUCTION = theorem "num" "INDUCTION";
val LESS_0 = theorem "prim_rec" "LESS_0";
val LESS_SUC = theorem "prim_rec" "LESS_SUC";
val LESS_MONO_EQ = theorem "arithmetic" "LESS_MONO_EQ";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val LESS_MONO = theorem "prim_rec" "LESS_MONO";
val LESS_EQ_REFL = theorem "arithmetic" "LESS_EQ_REFL";
val LESS_REFL = theorem "prim_rec" "LESS_REFL";
val OR_LESS = theorem "arithmetic" "OR_LESS";
val LESS_EQ = theorem "arithmetic" "LESS_EQ";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val LESS_IMP_LESS_OR_EQ = theorem "arithmetic" "LESS_IMP_LESS_OR_EQ";

val Koenig_Digraph_Lemma = TAC_PROOF (([],
  (--`!(x:'a) X.
     (!s. Finite (X s)) ==> Unbounded_Path x X ==> Infinite_Path x X`--)),
 REWRITE_TAC[Finite_EQ,Unbounded_Path,Infinite_Path] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`SIMP_REC (x:'a) (\x. @y. X x y /\ Unbounded_Path y X)`--) THEN
 CONJ_TAC THENL
 [
  REWRITE_TAC[SIMP_REC_THM]
 ,
  SUBGOAL_THEN (--`!d. ?s.
   (!d'. d' <= d ==>
     (SIMP_REC (x:'a) (\x. @y. X x y /\ Unbounded_Path y X) d' = s d')) /\
   (!d'. d' < d ==> X (s d') (s (SUC d'))) /\
   Unbounded_Path (s d) X`--) ASSUME_TAC THENL
  [
(*  Induction on path length *)
   INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THENL
   [
    EXISTS_TAC (--`\d:num. x:'a`--) THEN
    REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0] THEN
    REPEAT STRIP_TAC THENL
    [
     ASM_REWRITE_TAC[SIMP_REC_THM]
    ,
     REWRITE_TAC[Unbounded_Path] THEN
     GEN_TAC THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`n:num`--)) THEN
     EXISTS_TAC (--`s:num->'a`--) THEN
     ASM_REWRITE_TAC[]
    ]
   ,
    EXISTS_TAC (--`\d'. (d' <= d) => s d' |
      (@y:'a. X (s d) y /\ Unbounded_Path y X)`--) THEN
    BETA_TAC THEN
    SUBGOAL_THEN (--`?y:'a. X (s (d:num))y /\ Unbounded_Path y X`--)
     (STRIP_ASSUME_TAC o SELECT_RULE) THENL
    [
     POP_ASSUM (ASSUME_TAC o REWRITE_RULE[Unbounded_Path]) THEN
     REWRITE_TAC[Unbounded_Path] THEN
     SUBGOAL_THEN
      (--`!n. ?c. (c 0 = (s:num->'a) d) /\ (X (s d) (c (SUC 0))) /\
       (!d'. d' < n ==> X (c d') (c(SUC d')))`--) MP_TAC THENL
     [
      GEN_TAC THEN
      POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`SUC n`--)) THEN
      EXISTS_TAC (--`s':num->'a`--) THEN
      REPEAT STRIP_TAC THENL
      [
       FIRST_ASSUM ACCEPT_TAC
      ,
       POP_ASSUM (MP_TAC o SPEC (--`0`--)) THEN
       ASM_REWRITE_TAC[LESS_0]
      ,
       IMP_RES_TAC LESS_SUC THEN
       RES_TAC
      ]
     ,
      STRIP_ASSUME_TAC (SPECL [(--`(s:num->'a) d`--)] (ASSUME
        (--`!(s:'a). ?b f. !x:'a. X s x = (?n. n < b /\ (x = f n))`--))) THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC ((--`b:num`--),(--`b:num`--)) THEN
      INDUCT_THEN INDUCTION ASSUME_TAC THENL
      [
       REWRITE_TAC[NOT_LESS_0]
      ,
       REWRITE_TAC[LESS_THM,RIGHT_AND_OVER_OR] THEN
       CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV THENC
        (ONCE_DEPTH_CONV EXISTS_PRUNE_CONV)) THEN
       DISCH_TAC THEN
       REWRITE_TAC[RIGHT_AND_OVER_OR] THEN
       CONV_TAC
        (EXISTS_OR_CONV THENC (ONCE_DEPTH_CONV EXISTS_PRUNE_CONV)) THEN 
       CCONTR_TAC THEN
       POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
       IMP_RES_THEN (STRIP_ASSUME_TAC o CONV_RULE NOT_FORALL_CONV)
        (CONTRAPOS (ASSUME (--`(!n.
         ?c.
          (c 0 = (s:num->'a) d) /\
          (?n'. n' < b' /\ (c(SUC 0) = f n')) /\
          (!d'. d' < n ==> X(c d')(c(SUC d')))) ==>
       (?y.
         (?n. n < b' /\ (y = f n)) /\
         (!n. ?s. (s 0 = y) /\ (!d. d < n ==> X(s d)(s(SUC d)))))`--))) THEN
       POP_ASSUM (ASSUME_TAC o CONV_RULE (ONCE_DEPTH_CONV EXISTS_IMP_CONV) o
         REWRITE_RULE [DE_MORGAN_THM,SYM(SPEC_ALL IMP_DISJ_THM)] o
        CONV_RULE NOT_EXISTS_CONV) THEN
       ASSUM_LIST (FIRST o (mapfilter (STRIP_ASSUME_TAC o CONV_RULE
        (NOT_FORALL_CONV THENC ONCE_DEPTH_CONV NOT_EXISTS_CONV)))) THEN
       POP_ASSUM (ASSUME_TAC o GEN_ALL o BETA_RULE o
         SPEC (--`\d. c (SUC d):'a`--) o
         REWRITE_RULE [DE_MORGAN_THM,SYM(SPEC_ALL IMP_DISJ_THM)]) THEN
       ASM_CASES_TAC (--`n < SUC n'`--) THENL
       [
        STRIP_ASSUME_TAC (SPEC (--`SUC n'`--) (ASSUME (--`!n.
        ?c.
         (c 0 = (s:num->'a) d) /\
         ((c(SUC 0) = f b') \/ (?n'. n' < b' /\ (c(SUC 0) = f n'))) /\
         (!d'. d' < n ==> X(c d')(c(SUC d')))`--))) THENL
        [
         POP_ASSUM (ASSUME_TAC o GEN_ALL o REWRITE_RULE[LESS_MONO_EQ] o
           SPEC (--`SUC d`--)) THEN
         RES_TAC
        ,
         RES_TAC THEN
         ASSUM_LIST (FIRST o (mapfilter (STRIP_ASSUME_TAC o
          REWRITE_RULE[DE_MORGAN_THM,IMP_DISJ_THM] o
          CONV_RULE NOT_FORALL_CONV))) THEN
         IMP_RES_TAC LESS_TRANS THEN
         RES_TAC THEN
         RES_TAC
        ]
       ,
        POP_ASSUM (ASSUME_TAC o REWRITE_RULE[NOT_LESS]) THEN
        STRIP_ASSUME_TAC (SPEC (--`n:num`--) (ASSUME (--`!n.
        ?c.
         (c 0 = (s:num->'a) d) /\
         ((c(SUC 0) = f b') \/ (?n'. n' < b' /\ (c(SUC 0) = f n'))) /\
         (!d'. d' < n ==> X(c d')(c(SUC d')))`--))) THENL
        [
         POP_ASSUM (ASSUME_TAC o GEN_ALL o SPEC (--`SUC d'`--)) THEN
         ANTE_RES_THEN (STRIP_ASSUME_TAC o
          REWRITE_RULE[DE_MORGAN_THM,IMP_DISJ_THM] o
          CONV_RULE NOT_FORALL_CONV)
           (ASSUME (--`c(SUC 0):'a = f (b':num)`--)) THEN
         IMP_RES_TAC LESS_MONO THEN
         IMP_RES_TAC LESS_LEQ_TRANS THEN
         RES_TAC THEN
         RES_TAC
        ,
         RES_TAC
        ]
       ]
      ]
     ]
    ,
     REPEAT STRIP_TAC THENL
     [
      POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[LESS_OR_EQ]) THENL
      [
       POP_ASSUM (ASSUME_TAC o REWRITE_RULE[LESS_SUC_LESS_EQ]) THEN
       RES_TAC THEN
       ASM_REWRITE_TAC[]
      ,
       ANTE_RES_THEN ASSUME_TAC (SPEC (--`d:num`--) LESS_EQ_REFL) THEN
       ASM_REWRITE_TAC
        [REWRITE_RULE[LESS_REFL] (SPECL [(--`n:num`--),(--`n:num`--)] OR_LESS),
         SIMP_REC_THM] THEN
       BETA_TAC THEN
       REFL_TAC
      ]
     ,
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[LESS_SUC_LESS_EQ]) THEN
      ASM_REWRITE_TAC[] THEN
      POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[LESS_OR_EQ]) THENL
      [
       RES_TAC THEN
       ASM_REWRITE_TAC[SYM (SPEC_ALL LESS_EQ)]
      ,
       ASM_REWRITE_TAC
        [REWRITE_RULE[LESS_REFL] (SPECL [(--`n:num`--),(--`n:num`--)] OR_LESS)]
      ]
     ,
      ASM_REWRITE_TAC
       [REWRITE_RULE[LESS_REFL] (SPECL [(--`n:num`--),(--`n:num`--)] OR_LESS)]
     ]
    ]
   ]
  ,
   GEN_TAC THEN
   POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`SUC d`--)) THEN
   ANTE_RES_THEN ASSUME_TAC (SPEC (--`d:num`--) LESS_SUC_REFL) THEN
   ANTE_RES_THEN ASSUME_TAC (SPEC (--`SUC d`--) LESS_EQ_REFL) THEN
   ANTE_RES_THEN ASSUME_TAC
    (MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC (--`d:num`--) LESS_SUC_REFL)) THEN
   ASM_REWRITE_TAC[]
  ]
 ]);

(* Original formulation of Koenig's lemma (minus a few accents)

Fundamenta Mathematicae, Vol 8 1926 Page 120:

Soit E_1, E_2, E_3,... une suite denombrable d'ensembles finis, non
vides, et soit R une relation telle qu'a chaque element x_{n+1} de
chaque ensemble E_{n+1} corresponde au moins un element x_n de E_n,
lie a x_{n+1} par la relation R, c'est ce que nous ecrivons sous la
forme x_n R x_{n+1} (n = 1,2,3,...). Alors on peut choisir dans chaque
ensemble E_n un element a_n de sorte que, pour la suite infinie
a_1,a_2,a_3,..., on ait a_n R a_{n+1} (n = 1,2,3,...).

*)

(* In HOL (we shall be deriving it from Koenig_Digraph_Lemma):

  |- !E R.
      (!n.
        Finite(E n) /\
        (?x. E n x) /\
        (!x'. E(SUC n)x' ==> (?x. E n x /\ R x x'))) ==>
      (?a. !n. E n(a n) /\ R(a n)(a(SUC n)))
*)

val Unbounded_Lemma = TAC_PROOF (([], (--`!E R.
   (!n.  (?x:'a. E n x) /\
     (!x'. E (SUC n) x' ==> (?x. E n x /\ R x x'))) ==>
    (!n. (?a. (!m. m < n ==> E m (a m) /\ R (a m) (a (SUC m)))))`--)),
 REPEAT GEN_TAC THEN
 STRIP_TAC THEN
 SUBGOAL_THEN (--`!n (x:'a). E n x ==>
   (?a. (a n = x) /\ (!m. m < n ==> E m (a m) /\ R (a m) (a (SUC m))))`--)
  ASSUME_TAC THENL
 [
  POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE FORALL_AND_CONV) THEN
  INDUCT_THEN INDUCTION ASSUME_TAC THENL
  [
   REPEAT STRIP_TAC THEN
   EXISTS_TAC (--`\n:num. x:'a`--) THEN
   REWRITE_TAC[NOT_LESS_0]
  ,
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC THEN
   EXISTS_TAC (--`\m. m < SUC n => a m | x:'a`--) THEN
   BETA_TAC THEN
   REWRITE_TAC[LESS_REFL] THEN
   GEN_TAC THEN
   DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE[LESS_THM]) THENL
   [
    ASM_REWRITE_TAC[LESS_SUC_REFL,LESS_REFL]
   ,
    RES_TAC THEN
    IMP_RES_TAC LESS_SUC THEN
    IMP_RES_TAC LESS_MONO THEN
    ASM_REWRITE_TAC[]
   ]
  ]
 ,
  GEN_TAC THEN
  POP_ASSUM_LIST (EVERY o map (STRIP_ASSUME_TAC o SPEC (--`n:num`--))) THEN
  RES_TAC THEN
  EXISTS_TAC (--`a:num->'a`--) THEN
  FIRST_ASSUM ACCEPT_TAC
 ]);

val PRE = theorem "prim_rec" "PRE";
val NOT_SUC = theorem "num" "NOT_SUC";
val num_CASES = theorem "arithmetic" "num_CASES";

val Digraph_Lemma = TAC_PROOF (([],
  (--`!(E:num->'a->bool) R.
    (!n. ?a. !m. m < n ==> E m(a m) /\ R(a m)(a(SUC m))) ==>
     Unbounded_Path (0,(x:'a))
          (\(d,s) (d',s'). E d s' /\ (d' = SUC d) /\ ((d = 0) \/ R s s'))`--)),
 REWRITE_TAC[Unbounded_Path] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`n:num`--)) THEN
 EXISTS_TAC (--`\d. d,((d = 0) => x | a (PRE d):'a)`--) THEN
 BETA_TAC THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 REWRITE_TAC[] THEN
 GEN_TAC THEN
 STRIP_ASSUME_TAC (SPEC (--`d:num`--) num_CASES) THENL
 [
  ASM_REWRITE_TAC[PRE,NOT_SUC] THEN
  DISCH_TAC THEN
  RES_TAC
 ,
  ASM_REWRITE_TAC[PRE,NOT_SUC] THEN
  DISCH_TAC THEN
  RES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASSUME_TAC (SPEC (--`n':num`--) LESS_SUC_REFL) THEN
  IMP_RES_TAC LESS_TRANS THEN
  RES_TAC
 ]);

val PAIR = theorem "pair" "PAIR";
val PAIR_EQ = theorem "pair" "PAIR_EQ";

val Path_Lemma = TAC_PROOF (([],
  (--`!(E:num->'a->bool) R.
    Infinite_Path  (0,(x:'a))
            (\(d,s) (d',s'). E d s' /\ (d' = SUC d) /\ ((d = 0) \/ R s s')) ==>
       (?a. (!n. E n (a n) /\ R (a n) (a (SUC n))))`--)),
 REWRITE_TAC[Infinite_Path] THEN
 PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN
 REWRITE_TAC[] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (--`\t. SND (s (SUC t):num#'a)`--) THEN
 GEN_TAC THEN
 BETA_TAC THEN
 SUBGOAL_THEN (--`!d. FST (s d:num#'a) = d`--)
  (fn x => POP_ASSUM (ASSUME_TAC o REWRITE_RULE[x]))  THENL
 [
  INDUCT_THEN INDUCTION ASSUME_TAC THEN
  ASM_REWRITE_TAC[]
 ,
  CONJ_TAC THENL
  [
   ASM_REWRITE_TAC[]
  ,
   POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`SUC n`--)) THEN
   IMP_RES_TAC NOT_SUC
  ]
 ]);

val Finite_Lemma = TAC_PROOF (([],
  (--`!E:num->'a->bool.
     (!n. Finite (E n)) ==>
     (!s:num#'a.
       Finite
        ((\(d,x) (d',x'). E d x' /\ (d' = SUC d) /\ ((d = 0) \/ R x x'))
        s))`--)),
 REWRITE_TAC[Finite,Bounded] THEN
 PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
 CONV_TAC (REDEPTH_CONV PAIRED_BETA_CONV) THEN
 PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN
 REPEAT STRIP_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`FST (s:num#'a)`--)) THEN
 EXISTS_TAC (--`b:num`--) THEN
 EXISTS_TAC (--`\n:num. SUC (FST (s:num#'a)), (f n:'a)`--) THEN
 BETA_TAC THEN
 REPEAT GEN_TAC THEN
 DISCH_THEN (EVERY o map ASSUME_TAC o CONJUNCTS) THEN
 RES_TAC THEN
 EXISTS_TAC (--`n:num`--) THEN
 ASM_REWRITE_TAC[]);

val Koenig_Original_Lemma = TAC_PROOF (([],
 (--`!(E:num->'a->bool) R.
   (!n. Finite (E n) /\ (?x. E n x) /\
     (!x'. E (SUC n) x' ==> (?x. E n x /\ R x x'))) ==>
   (?a. (!n. E n (a n) /\ R (a n) (a (SUC n))))`--)),
 REPEAT GEN_TAC THEN
 DISCH_THEN (STRIP_ASSUME_TAC o
  CONV_RULE (ONCE_DEPTH_CONV FORALL_AND_CONV)) THEN
 IMP_RES_TAC Unbounded_Lemma THEN
 IMP_RES_TAC Digraph_Lemma THEN
 POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
 IMP_RES_TAC Finite_Lemma THEN
 POP_ASSUM (ASSUME_TAC o GEN (--`s'':num#'a`--) o
  SPECL [(--`s'':num#'a`--),(--`R:'a->'a->bool`--)]) THEN
 IMP_RES_TAC Koenig_Digraph_Lemma THEN
 IMP_RES_TAC Path_Lemma  THEN
 EXISTS_TAC (--`a:num->'a`--) THEN
 FIRST_ASSUM ACCEPT_TAC);

save_thm ("Finite_EQ",Finite_EQ);
save_thm ("Koenig_Digraph_Lemma",Koenig_Digraph_Lemma);
save_thm ("Koenig_Original_Lemma",Koenig_Original_Lemma);

export_theory();
