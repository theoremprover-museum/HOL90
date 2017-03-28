(* ************************************************************************* *)
(*                                                                           *)
(* FILE          : mk_dijkstra.sml                                           *)
(* DESCRIPTION   : Definition of weakest preconditions in HOL                *)
(*                                                                           *)
(* AUTHOR        : Mike Gordon, University of Cambridge                      *)
(* DATE          : March 1988                                                *)
(*                                                                           *)
(* TRANSLATOR    : Matthew Morley, University of Edinburgh                   *)
(* DATE          : Feb 1993                                                  *)
(*                                                                           *)
(* ************************************************************************* *)

new_theory "dijkstra";

load_library{lib=string_lib,theory="dijkstra"};

load_library{lib=taut_lib,theory="dijkstra"};

new_parent "halts_thms";

Add_to_sml.add_definitions_to_sml "halts_thms";
Add_to_sml.add_definitions_to_sml "semantics";

val HALTS = definition "halts" "HALTS";

val MK_FINITE_WHILE_CLAUSES = theorem "semantics" "MK_FINITE_WHILE_CLAUSES";

val num_Axiom  = theorem "prim_rec" "num_Axiom";
val INV_SUC_EQ = theorem "prim_rec" "INV_SUC_EQ";

val UNCURRY_DEF = definition "pair" "UNCURRY_DEF";

(* ========================================================================= *)
(* 
    A deterministic command is one that is single valued 
    (i.e. a partial function).
                                                                             *)
(* ========================================================================= *)

val DET = new_definition
    ("DET",
     (--`DET (c) = !(s:string ->num) (s':string -> num) s''. 
      c(s,s') /\ c(s,s'') ==> (s' = s'')`--))

(* ========================================================================= *)
(*
    If p and p' are predicates then "p' is weaker then p" if p' is "less 
    constraining", i.e. everything satisfying p also satisfies p', but 
    perhaps there are some things satisfying p' that do not satisfy p.
                                                                             *)
(* ========================================================================= *)

val WEAKER = new_definition
    ("WEAKER",
     (--`WEAKER p' p = !s:'a. p s ==> p' s`--));

val WEAKER_ANTISYM = save_thm("WEAKER_ANTISYM",
 prove
  ((--`!p1 p2 : 'a->bool. WEAKER p1 p2 /\ WEAKER p2 p1 ==> (p1=p2)`--),
   REWRITE_TAC[WEAKER]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC));

(* ========================================================================= *)
(*                    Uniqueness of weakest conditions                       *)
(* ========================================================================= *)

val WEAKEST_UNIQUE_LEMMA = save_thm("WEAKEST_UNIQUE_LEMMA",
 prove
  ((--`!P:('a->bool)->bool. !p1 p2.
     (P p1 /\ !p'. P p' ==> WEAKER p1 p') /\
     (P p2 /\ !p'. P p' ==> WEAKER p2 p') ==>
     (p1 = p2)`--),
   REPEAT STRIP_TAC
    THEN RES_TAC
    THEN IMP_RES_TAC WEAKER_ANTISYM));


(* ========================================================================= *)
(*
    The weakest thing satisfying P is a predicate p satisfying P that is 
    weaker than all other predicated satisfying P.
                                                                             *)
(* ========================================================================= *)

val WEAKEST = new_definition
    ("WEAKEST",
     (--`WEAKEST(P:('a->bool)->bool) =
      @p. P p /\ !p'. P p' ==> WEAKER p p'`--));

(* ========================================================================= *)
(*                           Uniqueness of weakest                           *)
(* ========================================================================= *)

val WEAKEST_UNIQUE = save_thm("WEAKEST_UNIQUE",
 prove
  ((--`!P:('a->bool)->bool. !p.
     (P p /\ !p'. P p' ==> WEAKER p p') ==> (p = WEAKEST P)`--),
   REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN ASSUM_LIST
          (fn [th] => let val t = concl th
			  and p = (--`p:'a->bool`--)
		      in
			  ASSUME_TAC(SELECT_RULE(EXISTS((--`?^p.^t`--),p)th))
		      end)
    THEN ASSUM_LIST (* Why doesn't IMP_RES_TAC work? *)
          (fn [th1,th2] =>
             ASSUME_TAC(MATCH_MP WEAKEST_UNIQUE_LEMMA (CONJ th1 th2)))
    THEN ASM_REWRITE_TAC[WEAKEST]));

(* ========================================================================= *)
(*		Abstract definition of weakest preconditions                 *)
(* ========================================================================= *)

val WP = new_definition
    ("WP",
     (--`WP (c,q) = WEAKEST(\p. T_SPEC(p,c,q))`--));

val WLP = new_definition
    ("WLP",
     (--`WLP (c,q) = WEAKEST(\p. MK_SPEC(p,c,q))`--));

(* ========================================================================= *)
(*
    Alternative definitions (corresponds to the definition on page 88 of
    Backhouse's book or page 108 of Gries' book).
                                                                             *)
(* ========================================================================= *)

val WP1 = new_definition
    ("WP1",
     (--`WP1 (c,q) (s:string->num) =
      (?s':string->num. c(s,s')) /\ (!s'. c(s,s') ==> q s')`--));

val WLP1 = new_definition
    ("WLP1",
     (--`WLP1 (c,q) (s:string->num) = !s':string->num. c(s,s') ==> q s'`--));

val WP1_T_SPEC = save_thm("WP1_T_SPEC",
 prove
  ((--`!c q. T_SPEC(WP1(c,q),c,q)`--),
   REWRITE_TAC[WP1,T_SPEC,HALTS,MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN EXISTS_TAC (--`s':string->num`--)
    THEN ASM_REWRITE_TAC[]));

val WLP1_MK_SPEC = save_thm("WLP1_MK_SPEC",
 prove
  ((--`!c q. MK_SPEC(WLP1(c,q),c,q)`--),
   REWRITE_TAC[WLP1,MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC));

val WP1_WEAKEST = save_thm("WP1_WEAKEST",
 prove
  ((--`!p c q. T_SPEC(p,c,q) ==> WEAKER (WP1(c,q)) p`--),
   REWRITE_TAC[WEAKER,WP1,T_SPEC,HALTS,MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC,RES_TAC]));

val WLP1_WEAKEST = save_thm("WLP1_WEAKEST",
 prove
  ((--`!p c q. MK_SPEC(p,c,q) ==> WEAKER (WLP1(c,q)) p`--),
   REWRITE_TAC[WEAKER,WLP1,MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC));

val WP1_LEMMA =
 MATCH_MP
  (BETA_RULE
    (SPEC (--`\p. T_SPEC(p,c,q)`--) 
      (INST_TYPE [{residue=(==`:string->num`==), redex=(==`:'a`==)}] 
        WEAKEST_UNIQUE)))
  (CONJ (SPEC_ALL WP1_T_SPEC) (GEN (--`p:(string->num)->bool`--) 
    (SPEC_ALL WP1_WEAKEST)));

val WLP1_LEMMA =
 MATCH_MP
  (BETA_RULE
    (SPEC (--`\p. MK_SPEC(p,c,q)`--) 
      (INST_TYPE [{residue=(==`:string->num`==), redex=(==`:'a`==)}] 
        WEAKEST_UNIQUE)))
  (CONJ (SPEC_ALL WLP1_MK_SPEC) (GEN (--`p:(string->num)->bool`--) 
    (SPEC_ALL WLP1_WEAKEST)));

val WP_WP1 = save_thm("WP_WP1",
 prove
  ((--`!c q. WP (c,q) = WP1 (c,q)`--),
   REWRITE_TAC[WP1_LEMMA,WP]));

val WLP_WLP1 = save_thm("WLP_WLP1",
 prove
  ((--`!c q. WLP (c,q) = WLP1 (c,q)`--),
   REWRITE_TAC[WLP1_LEMMA,WLP]));

val WP_THM = save_thm("WP_THM",
 prove
  ((--`!c q. WP (c,q) = \s. (?s':string->num. c(s,s')) /\ 
        (!s'. c(s,s') ==> q s')`--),
    REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REWRITE_TAC[WP_WP1,WP1]));

val WLP_THM = save_thm("WLP_THM",
 prove
  ((--`!c q. WLP (c,q) = \s.!s'. c(s,s') ==> q s'`--),
   REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REWRITE_TAC[WLP_WLP1,WLP1]));

val WP_T_SPEC = save_thm("WP_T_SPEC",
 prove
  ((--`!c q. (?s. WP(c,q)s) ==> T_SPEC(WP(c,q),c,q)`--),
   REWRITE_TAC[WP_WP1,WP1_T_SPEC]));

val WLP_MK_SPEC = save_thm("WLP_MK_SPEC",
 prove
  ((--`!c q. (?s. WLP(c,q)s) ==> MK_SPEC(WLP(c,q),c,q)`--),
   REWRITE_TAC[WLP_WLP1,WLP1_MK_SPEC]));

val WP_WEAKEST = save_thm("WP_WEAKEST",
 prove
  ((--`!p c q. T_SPEC(p,c,q) ==> WEAKER (WP(c,q)) p`--),
   REWRITE_TAC[WP_WP1,WP1_WEAKEST]));

val WLP_WEAKEST = save_thm("WLP_WEAKEST",
 prove
  ((--`!p c q. MK_SPEC(p,c,q) ==> WEAKER (WLP(c,q)) p`--),
   REWRITE_TAC[WLP_WLP1,WLP1_WEAKEST]));

val T_SPEC_WP = save_thm("T_SPEC_WP",
 prove
  ((--`!p c q. T_SPEC(p,c,q) = !s. (p s ==> WP(c,q)s)`--),
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC 
    THENL
      [IMP_RES_TAC WP_WEAKEST 
        THEN IMP_RES_TAC WEAKER,
       REWRITE_TAC[WP_THM,T_SPEC,MK_SPEC,HALTS]
        THEN POP_ASSUM(ASSUME_TAC o BETA_RULE o REWRITE_RULE[WP_THM]) 
        THEN REPEAT STRIP_TAC 
        THENL
          [RES_TAC, RES_THEN MATCH_ACCEPT_TAC]]));

val MK_SPEC_WLP = save_thm("MK_SPEC_WLP",
 prove
  ((--`!p c q. MK_SPEC(p,c,q) = !s. (p s ==> WLP(c,q)s)`--),
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC WLP_WEAKEST
    THEN POP_ASSUM(ASSUME_TAC o REWRITE_RULE[WEAKER])
    THEN RES_TAC
    THEN REWRITE_TAC[WLP_THM,MK_SPEC]
    THEN POP_ASSUM(ASSUME_TAC o BETA_RULE o REWRITE_RULE[WLP_THM])
    THEN REPEAT STRIP_TAC
    THEN RES_TAC));

(* ========================================================================= *)
(*	   Dijkstra's properties 1 -- 4 (see pp 18-19 of his book).          *)
(* ========================================================================= *)

val WP_PROP1 = save_thm("WP_PROP1",
 prove
  ((--`!c. WP(c, \s.F) = \s.F`--),
   REWRITE_TAC[WP_THM]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC));

val WLP_PROP1 = save_thm("WLP_PROP1",
 prove
  ((--`!c. WLP(c, \s.F) = \s. ~?s'. c(s,s')`--),
   REWRITE_TAC[WLP_THM]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[]));

val WP_PROP2 = save_thm("WP_PROP2",
 prove
  ((--`!p q c. (!s. p s ==> q s) ==> !s. WP(c,p)s ==> WP(c,q)s`--),
   REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC 
    THENL
      [EXISTS_TAC (--`s':string->num`--) 
        THEN ASM_REWRITE_TAC[],
       RES_TAC 
        THEN RES_TAC]));

val WLP_PROP2 = save_thm("WLP_PROP2",
 prove
  ((--`!p q c. (!s. p s ==> q s) ==> !s. WLP(c,p)s ==> WLP(c,q)s`--),
   REWRITE_TAC[WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC THEN RES_TAC));

val WP_PROP3 = save_thm("WP_PROP3",
 prove
  ((--`!p q c s. WP(c,p)s /\ WP(c,q)s = WP(c, \s. p s /\ q s)s`--),
   REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN EXISTS_TAC (--`s':string->num`--)
    THEN ASM_REWRITE_TAC[]));

val WLP_PROP3 = save_thm("WLP_PROP3",
 prove
  ((--`!p q c s. WLP(c,p)s /\ WLP(c,q)s = WLP(c, \s. p s /\ q s)s`--),
   REWRITE_TAC[WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC));

val WP_PROP4 = save_thm("WP_PROP4",
 prove
  ((--`!p q c s. WP(c,p)s \/ WP(c,q)s ==> WP(c, \s. p s \/ q s)s`--),
   REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN (EXISTS_TAC (--`s':string->num`--) ORELSE ALL_TAC)
    THEN ASM_REWRITE_TAC[]));

val WLP_PROP4 = save_thm("WLP_PROP4",
 prove
  ((--`!p q c s. WLP(c,p)s \/ WLP(c,q)s ==> WLP(c, \s. p s \/ q s)s`--),
   REWRITE_TAC[WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]));

(* ========================================================================= *)
(*
                   u \/ v                             u \/ v
    DISJ1_TAC      ======              DISJ2_TAC      ======
                      u                                  v
                                                                             *)
(* ========================================================================= *)

val WP_PROP4' = save_thm("WP_PROP4'",
 prove
  ((--`!p q c. DET c ==> !s:string->num. WP (c,p) s \/ WP (c,q) s = 
                                         WP (c, \s. p s \/ q s) s`--),
   REWRITE_TAC[DET] 
    THEN  REPEAT STRIP_TAC 
    THEN  EQ_TAC 
    THEN  REWRITE_TAC[WP_PROP4,WP_THM] 
    THEN  CONV_TAC (DEPTH_CONV BETA_CONV) 
    THEN  REPEAT STRIP_TAC 
    THEN  RES_TAC 
    THENL
      [DISJ1_TAC THEN CONJ_TAC 
        THENL
          [EXISTS_TAC (--`s':string->num`--) 
            THEN FIRST_ASSUM ACCEPT_TAC,
           REPEAT STRIP_TAC 
            THEN  RES_THEN (REPEAT_GTCL IMP_RES_THEN (TRY o SUBST1_TAC)) 
            THEN  FIRST_ASSUM ACCEPT_TAC],
           DISJ2_TAC 
            THEN CONJ_TAC 
            THENL
              [EXISTS_TAC (--`s':string->num`--) 
                THEN FIRST_ASSUM ACCEPT_TAC,
               REPEAT STRIP_TAC 
                THEN  RES_THEN (REPEAT_GTCL IMP_RES_THEN (TRY o SUBST1_TAC)) 
                THEN  FIRST_ASSUM ACCEPT_TAC]]));

val DISJ_IMP_LEMMA = 
    Taut.TAUT_PROVE (--`!t1 t2. (t1 \/ t2) = (~t2 ==> t1)`--);

val NOT_IMP_LEMMA = 
    Taut.TAUT_PROVE (--`!t1 t2. ~(t1 ==> t2) = (t1 /\ ~t2)`--);

val WLP_PROP4' = save_thm("WLP_PROP4'",
 prove
  ((--`!p q c. DET c ==> !s. WLP(c,p)s \/ WLP(c,q)s = 
                             WLP(c, \s. p s \/ q s)s`--),
   REWRITE_TAC[DET]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[WLP_PROP4,WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[DISJ_IMP_LEMMA]
    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
    THEN REWRITE_TAC[NOT_IMP_LEMMA]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(fn thl => REWRITE_TAC[el 3 thl])
    THENL[ASM_REWRITE_TAC[],RES_TAC]));


(* ========================================================================= *)
(* 	  Now we prove properties about particular command types             *)
(* ========================================================================= *)

val SKIP_WP = save_thm("SKIP_WP",
 prove
  ((--`!p. WP(MK_SKIP,p) = p`--),
   REWRITE_TAC[WP_THM,MK_SKIP]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o mapfilter SYM)
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC (--`f:string->num`--)
    THEN REWRITE_TAC[]));

val SKIP_WLP = save_thm("SKIP_WLP",
 prove
  ((--`!p. WLP(MK_SKIP,p) = p`--),
   REWRITE_TAC[WLP_THM,MK_SKIP]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL[ASSUME_TAC(REFL (--`f:string->num`--)), ALL_TAC]
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o mapfilter SYM)
    THEN ASM_REWRITE_TAC[]));

val ABORT_WP = save_thm("ABORT_WP",
 prove
  ((--`!p. WP(MK_ABORT,p) = \s.F`--),
   REWRITE_TAC[WP_THM,MK_ABORT]
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC));

val ABORT_WLP = save_thm("ABORT_WLP",
 prove
  ((--`!p. WLP(MK_ABORT,p) = \s.T`--),
   REWRITE_TAC[WLP_THM,MK_ABORT]
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC));

val ASSIGN_WP = save_thm("ASSIGN_WP",
 prove
  ((--`!x f p. WP(MK_ASSIGN(x,f),p) = \s. p (BND x (f s) s)`--),
   REWRITE_TAC[WP_THM,MK_ASSIGN]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(fn thl => REWRITE_TAC(mapfilter SYM thl))
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM(fn th =>EXISTS_TAC(rand(concl th)))
    THEN REWRITE_TAC[]));

val ASSIGN_WLP = save_thm("ASSIGN_WLP",
 prove
  ((--`!x f p. WLP(MK_ASSIGN(x,f),p) = \s. p (BND x (f s) s)`--),
   REWRITE_TAC[WLP_THM,MK_ASSIGN]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(fn thl => REWRITE_TAC(mapfilter SYM thl))
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM
          (fn th => 
	   let val t = (rhs o #ant o dest_imp o #Body o dest_forall o concl) th
	   in
	       REWRITE_TAC[REWRITE_RULE[](SPEC t th)]
	   end)));

val SEQ_WP = save_thm("SEQ_WP",
 prove
  ((--`!c c' p.  DET c ==> !s. (WP(MK_SEQ(c,c'),p)s = WP(c,WP(c',p))s)`--),
   REWRITE_TAC[WP_THM,MK_SEQ,DET] 
    THEN  CONV_TAC (DEPTH_CONV BETA_CONV) 
    THEN  REPEAT (EQ_TAC ORELSE STRIP_TAC) 
    THENL
      [EXISTS_TAC (--`s'':string->num`--) 
        THEN  FIRST_ASSUM ACCEPT_TAC,
       EXISTS_TAC (--`s':string->num`--) 
        THEN  RES_TAC 
        THEN  SUBST1_TAC (ASSUME (--`s''':string->num = s''`--)) 
        THEN  FIRST_ASSUM ACCEPT_TAC,
       RES_TAC,
       RES_TAC 
        THEN  MAP_EVERY EXISTS_TAC [(--`s'':string->num`--),
                                    (--`s':string->num`--)] 
        THEN  CONJ_TAC 
        THEN  FIRST_ASSUM ACCEPT_TAC,
       RES_TAC]));

(* ========================================================================= *)
(*
   The material below shows that without the assumption that DET c it is not 
   the case that WP(MK_SEQ(c,c'),p)s = WP(c,WP(c',p))s
                                                                             *)
(* ========================================================================= *)
(* ========================================================================= *)
(* One long example...

Add_to_sml.add_definitions_to_sml "semantics";
Add_to_sml.add_definitions_to_sml "dijkstra";
Add_to_sml.add_theorems_to_sml "dijkstra";

val S1 = new_definition("S1", (--`(S1:string->num) str = 0`--));
val S2 = new_definition("S2", (--`(S2:string->num) str = 1`--));

val NOT_SUC = theorem "num" "NOT_SUC";

val S1_NOT_S2 = save_thm("S1_NOT_S2",
 prove
  ((--`~(S1 = S2)`--),
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   THEN CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV)
   THEN REWRITE_TAC[S1,S2,num_CONV (--`1`--),NOT_EQ_SYM(SPEC_ALL NOT_SUC)]));

val C1 = new_definition("C1",
         (--`C1((s:string->num),s') = (s' = S1) \/ (s' = S2)`--));

val C2 = new_definition("C2",(--`C2(s,s') = (s = S1)  /\ (s' = S1)`--));

val C1_C2 = save_thm("C1_C2",
 prove
  ((--`MK_SEQ(C1,C2)(s,s') = (s' = S1)`--),
   REWRITE_TAC[MK_SEQ,C1,C2]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (--`S1`--)
    THEN ASM_REWRITE_TAC[]));

val WP_C1_C2 = save_thm("WP_C1_C2",
 prove
  ((--`WP(MK_SEQ(C1,C2),p)s = p S1`--),
   REWRITE_TAC[WP_THM,MK_SEQ,C1,C2]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN (POP_ASSUM(MAP_EVERY(ASSUME_TAC o GEN_ALL) o IMP_CANON)
          ORELSE ALL_TAC)
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC (--`S1`--)
    THEN EXISTS_TAC (--`S1`--)
    THEN REWRITE_TAC[]));

val WP_C2 = save_thm("WP_C2",
 prove
  ((--`WP(C2,p)s = (s=S1) /\ p S1`--),
   REWRITE_TAC[WP_THM,C2]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC (--`S1`--)
    THEN REWRITE_TAC[]));

val WP_C1_WP_C2 = save_thm("WP_C1_WP_C2",
 prove
  ((--`WP(C1,WP(C2,p))s = F`--),
   REWRITE_TAC[WP_C2,WP_THM,C1,C2]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM(
           ASSUME_TAC o REWRITE_RULE[NOT_EQ_SYM S1_NOT_S2] o SPEC (--`S2`--))
    THEN ASM_REWRITE_TAC[]));

val NOT_SEQ_WP = save_thm("NOT_SEQ_WP",
 prove
  ((--`~!c c' p s. (WP(MK_SEQ(c,c'),p)s = WP(c,WP(c',p))s)`--),
   CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV)
    THEN EXISTS_TAC (--`C1`--)
    THEN EXISTS_TAC (--`C2`--)
    THEN REWRITE_TAC[WP_C1_C2,WP_C1_WP_C2]
    THEN EXISTS_TAC (--`\p:string->num.T`--)
    THEN BETA_TAC));

                                                                             *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(*        Determinacy is not needed with weakest liberal preconditions       *)
(* ************************************************************************* *)

val SEQ_WLP = save_thm("SEQ_WLP",
 prove
  ((--`!c c' p s. (WLP(MK_SEQ(c,c'),p)s = WLP(c,WLP(c',p))s)`--),
   REWRITE_TAC[WLP_THM,MK_SEQ]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(ASSUME_TAC o GEN_ALL o hd o IMP_CANON o (el 3))
    THEN POP_ASSUM(
           ASSUME_TAC o SPECL[(--`s':string->num`--),(--`s'':string->num`--)])
    THEN RES_TAC));

val IF1_WP = save_thm("IF1_WP",
 prove
  ((--`!c b p s. WP(MK_IF1(b,c),p)s = (b s => WP(c,p)s | p s)`--),
   REWRITE_TAC[WP_THM,MK_IF1]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC (--`(b:(string->num)->bool)s`--)
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THENL
     [EXISTS_TAC (--`s:string->num`--),
      POP_ASSUM(fn th => REWRITE_TAC[SYM th])]
    THEN ASM_REWRITE_TAC[]));

val IF1_WLP = save_thm("IF1_WLP",
 prove
  ((--`!c b p s. WLP(MK_IF1(b,c),p)s = (b s => WLP(c,p)s | p s)`--),
   REWRITE_TAC[WLP_THM,MK_IF1]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC (--`(b:(string->num)->bool)s`--)
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THENL
     [ASSUME_TAC(REFL (--`s:string->num`--))
       THEN RES_TAC,
      POP_ASSUM(fn th => REWRITE_TAC[SYM th])]
    THEN ASM_REWRITE_TAC[]));

val IF2_WP = save_thm("IF2_WP",
 prove
  ((--`!c c' p s. WP(MK_IF2(b,c,c'),p)s = (b s => WP(c,p)s | WP(c',p)s)`--),
   REWRITE_TAC[WP_THM,MK_IF2]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC (--`(b:(string->num)->bool)s`--)
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC));

val IF2_WLP = save_thm("IF2_WLP",
 prove
  ((--`!c c' p s. WLP(MK_IF2(b,c,c'),p)s = (b s => WLP(c,p)s | WLP(c',p)s)`--),
   REWRITE_TAC[WLP_THM,MK_IF2]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC (--`(b:(string->num)->bool)s`--)
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC));

(* ************************************************************************* *)
(*
   ITER : num -> (string->num->bool) # command -> command

   ITER 0 (b,c) (s,s')        =  ~(b s) /\ (s = s')

   ITER (SUC n) (b,c) (s,s')  =   b s /\ MK_SEQ(c, ITER n (b,c))(s,s')
                                                                             *)
(* ************************************************************************* *)

val ITER = new_recursive_definition{
    name= "ITER",
    def= (--`(ITER 0       = \(b,c) (s,s'). ~(b s) /\ (s = s')) /\
             (ITER (SUC n) = \(b,c) (s,s'). b s /\ 
                MK_SEQ(c, ITER n (b,c)) (s,s'))`--),
    fixity=Prefix,
    rec_axiom= num_Axiom};

val ITER_CLAUSES = save_thm("ITER_CLAUSES",
 prove
  ((--`(ITER 0       (b,c) (s,s')  =  ~(b s) /\ (s = s')) /\
       (ITER (SUC n) (b,c) (s,s')  =  b s /\ 
          MK_SEQ(c, ITER n (b,c))(s,s'))`--),
   PURE_REWRITE_TAC[ITER]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[]));

val COND_LEMMA = 
    (Taut.TAUT_PROVE 
     (--`!b t1 t2. (b => t1 | t2) = (b ==> t1) /\ (~b ==> t2)`--))
    handle _ =>
	TAC_PROOF
	(([],
	  (--`!b t1 t2. (b => t1 | t2) = (b ==> t1) /\ (~b ==> t2)`--)),
	 REPEAT STRIP_TAC
	 THEN  COND_CASES_TAC
	 THENL [REWRITE_TAC[],REWRITE_TAC[]]);

val WHILE_ITER1 = save_thm("WHILE_ITER1",
 prove
  ((--`MK_WHILE(b,c)(s,s') ==> ?n. ITER n (b,c) (s,s')`--),
   REWRITE_TAC[MK_WHILE]
    THEN STRIP_TAC
    THEN ASSUM_LIST(fn [th] => UNDISCH_TAC(concl th))
    THEN SPEC_TAC((--`s':string->num`--),(--`s':string->num`--))
    THEN SPEC_TAC((--`s:string->num`--),(--`s:string->num`--))
    THEN SPEC_TAC((--`n:num`--),(--`n:num`--))
    THEN INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[MK_FINITE_WHILE_CLAUSES,MK_IF1,MK_SEQ,COND_LEMMA]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC (--`(b:(string->num)->bool)s`--)
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THENL
     [POP_ASSUM STRIP_ASSUME_TAC
       THEN RES_TAC
       THEN POP_ASSUM STRIP_ASSUME_TAC
       THEN EXISTS_TAC (--`SUC n'`--)
       THEN ASM_REWRITE_TAC[ITER_CLAUSES,MK_SEQ]
       THEN EXISTS_TAC (--`s'':string->num`--)
       THEN ASM_REWRITE_TAC[],
      EXISTS_TAC (--`0`--)
       THEN ASM_REWRITE_TAC[ITER_CLAUSES,MK_SEQ]]));

val WHILE_ITER2 = save_thm("WHILE_ITER2",
 prove
  ((--`!n s s'. ITER n (b,c) (s,s') ==> MK_WHILE(b,c)(s,s')`--),
   REWRITE_TAC[MK_WHILE]
    THEN INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[ITER_CLAUSES,MK_SEQ]
    THEN REPEAT STRIP_TAC
    THENL
     [EXISTS_TAC (--`SUC 0`--)
       THEN ASM_REWRITE_TAC[MK_FINITE_WHILE_CLAUSES,MK_IF1,MK_SEQ],
      RES_TAC
       THEN POP_ASSUM STRIP_ASSUME_TAC
       THEN EXISTS_TAC (--`SUC n'`--)
       THEN ASM_REWRITE_TAC[MK_FINITE_WHILE_CLAUSES,MK_IF1,MK_SEQ]
       THEN EXISTS_TAC (--`s'':string->num`--)
       THEN ASM_REWRITE_TAC[]]));

val WHILE_ITER = save_thm("WHILE_ITER",
 prove
  ((--`MK_WHILE(b,c)(s,s') = ?n. ITER n (b,c) (s,s')`--),
   EQ_TAC
    THENL
     [ACCEPT_TAC WHILE_ITER1,
      REPEAT STRIP_TAC
       THEN IMP_RES_TAC WHILE_ITER2]));

val ITER_UNIQUE = save_thm("ITER_UNIQUE",
 prove
  ((--`DET c ==>
     !n s s'. ITER n(b,c)(s,s') ==>
               !n' s''. ITER n'(b,c)(s,s'') ==> (n = n')`--),
   DISCH_TAC 
    THEN  INDUCT_TAC 
    THEN  REPEAT GEN_TAC 
    THEN  REWRITE_TAC[ITER_CLAUSES,MK_SEQ] 
    THEN  STRIP_TAC 
    THENL
      [INDUCT_TAC 
        THEN GEN_TAC 
        THENL
          [REWRITE_TAC[ITER_CLAUSES],ASM_REWRITE_TAC[ITER_CLAUSES]],
       INDUCT_TAC 
        THEN  GEN_TAC 
        THEN  ASM_REWRITE_TAC[ITER_CLAUSES,MK_SEQ,INV_SUC_EQ] 
        THEN  REPEAT STRIP_TAC 
        THEN  IMP_RES_THEN IMP_RES_TAC DET 
        THEN  ASSUM_LIST(fn thl => ASSUME_TAC(SUBS[el 3 thl](el 5 thl))) 
        THEN  RES_TAC]));

val ITER_WP = new_recursive_definition{
  name= "ITER_WP",
  def= (--`(ITER_WP 0       b c p s = ~(b s) /\ p s) /\
           (ITER_WP (SUC n) b c p s = b s /\ WP(c,ITER_WP n b c p) s)`--),
  fixity=Prefix,
  rec_axiom=num_Axiom};

val DET_ITER = save_thm("DET_ITER",
 prove
  ((--`DET c ==> !n. DET(ITER n (b,c))`--),
   REWRITE_TAC[DET]
    THEN DISCH_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[ITER_CLAUSES,MK_SEQ]
    THEN REPEAT STRIP_TAC
    THENL
     [ASSUM_LIST(REWRITE_TAC o (mapfilter SYM)),
      RES_TAC THEN
      SUBST_ALL_TAC (ASSUME (--`(s'''':string->num) = s'''`--)) THEN
      RES_TAC]));

val WP_ITER = save_thm("WP_ITER",
 prove
  ((--`DET c ==> !n. !s. WP(ITER n (b,c),p) s =  ITER_WP n b c p s`--),
   DISCH_TAC
    THEN INDUCT_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[ITER_CLAUSES,ITER_WP,WP_THM]
    THEN BETA_TAC
    THENL
     [EQ_TAC
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
       THEN ASM_REWRITE_TAC[]
       THEN EXISTS_TAC (--`s:string->num`--)
       THEN REWRITE_TAC[],
      ALL_TAC]
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter(SYM o SPEC_ALL)))
    THEN REWRITE_TAC[WP_THM,MK_SEQ]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC []
    THENL
     [EXISTS_TAC (--`s'':string->num`--) THEN FIRST_ASSUM ACCEPT_TAC,
      IMP_RES_THEN IMP_RES_TAC DET THEN
      EXISTS_TAC (--`s':string->num`--) THEN
      SUBST1_TAC (ASSUME (--`s''':string->num = s''`--)) THEN
      FIRST_ASSUM ACCEPT_TAC,
      EXISTS_TAC (--`s'':string->num`--) THEN
      EXISTS_TAC (--`s':string->num`--) THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]));

val WHILE_WP = save_thm("WHILE_WP",
 prove
  ((--`!c. DET c ==> !b p s. WP(MK_WHILE(b,c),p)s = ?n. ITER_WP n b c p s`--),
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[WHILE_ITER,WP_THM]
    THEN BETA_TAC
    THEN REWRITE_TAC [SYM(SPEC_ALL(UNDISCH WP_ITER))]
    THEN REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [EXISTS_TAC (--`n:num`--) THEN CONJ_TAC THENL
      [EXISTS_TAC (--`s':string->num`--) THEN FIRST_ASSUM ACCEPT_TAC,
       REPEAT STRIP_TAC THEN RES_TAC],
      EXISTS_TAC (--`s':string->num`--)
      THEN EXISTS_TAC (--`n:num`--)
      THEN ASM_REWRITE_TAC[],
      IMP_RES_TAC DET_ITER
       THEN ASSUM_LIST(IMP_RES_TAC o REWRITE_RULE[DET] o hd)
       THEN IMP_RES_TAC ITER_UNIQUE
       THEN FIRST_ASSUM MATCH_MP_TAC
       THEN SUBST1_TAC (ASSUME (--`n:num = n'`--))
       THEN FIRST_ASSUM ACCEPT_TAC]));


val FINITE_WHILE_WP_0 = save_thm("FINITE_WHILE_WP_0",
 prove
  ((--`WP(MK_FINITE_WHILE 0 (b,c),p)s =  F`--),
   REWRITE_TAC[MK_FINITE_WHILE_CLAUSES,ITER_WP,WP_THM]));

val LEMMA1 =
 TAC_PROOF
  (([], (--`(?(s':string->num). s = s') /\ (!s'. (s = s') ==> p s') = p s`--)),
   EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC (--`s:string->num`--)
    THEN ASM_REWRITE_TAC[]);

val FINITE_WHILE_WP_SUC = save_thm("FINITE_WHILE_WP_SUC",
 prove
  ((--`WP(MK_FINITE_WHILE (SUC n) (b,c),p)s =
    (b s => WP(MK_SEQ(c,MK_FINITE_WHILE n(b,c)),p) s | p s)`--),
   REWRITE_TAC[MK_FINITE_WHILE_CLAUSES,ITER_WP,WP_THM]
    THEN BETA_TAC
    THEN REWRITE_TAC[MK_FINITE_WHILE_CLAUSES]
    THEN ASM_CASES_TAC (--`(b:(string->num)->bool)s`--)
    THEN ASM_REWRITE_TAC[MK_SEQ,MK_IF1,LEMMA1]));

val ITER_WLP = new_recursive_definition{
  name= "ITER_WLP",
  def= (--`(ITER_WLP 0       b c p s = ~(b s) ==> p s) /\
           (ITER_WLP (SUC n) b c p s = b s ==> WLP(c,ITER_WLP n b c p) s)`--),
  fixity=Prefix,
  rec_axiom=num_Axiom};

val WLP_ITER = save_thm("WLP_ITER",
 prove
  ((--`!n. !s. WLP(ITER n (b,c),p) s =  ITER_WLP n b c p s`--),
   INDUCT_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[ITER_CLAUSES,ITER_WLP,WLP_THM]
    THEN BETA_TAC
    THENL
     [EQ_TAC
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
       THEN ASM_REWRITE_TAC[]
       THEN ASSUM_LIST
             (fn [th1,th2,th3] => 
                ASSUME_TAC(REWRITE_RULE[](SPEC (--`s:string->num`--) th3)))
       THEN RES_TAC,
      ALL_TAC]
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter(SYM o SPEC_ALL)))
    THEN REWRITE_TAC[WLP_THM,MK_SEQ]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(fn thl => 
           ASSUME_TAC(SPEC (--`s'':string->num`--) (el 5 thl)))
    THEN POP_ASSUM(fn th => 
           ASSUME_TAC(GEN (--`s''':string->num`--) (hd(IMP_CANON th))))
    THEN RES_TAC));

val WHILE_WLP = save_thm("WHILE_WLP",
 prove
  ((--`!c b p s. WLP(MK_WHILE(b,c),p)s = !n. ITER_WLP n b c p s`--),
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[WHILE_ITER,WLP_THM,SYM(SPEC_ALL WLP_ITER)]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(GEN_ALL(hd( IMP_CANON(el 2 thl)))))
    THEN RES_TAC));

close_theory();

export_theory();

