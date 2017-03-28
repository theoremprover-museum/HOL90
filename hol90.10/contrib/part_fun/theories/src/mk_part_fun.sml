(* ===================================================================== *)
(* FILE          : mk_part_fun.sml                                       *)
(* DESCRIPTION   : Theory of partial functions.                          *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 92.08.21                                              *)
(*                                                                       *)
(* ===================================================================== *)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

load_library {lib = utils_lib, theory = "-"};
open ExtraGeneralFunctions;

val _ = new_theory "partial_functions";

local
    val path = (!HOLdir)^"contrib/part_fun/theories/"^
	       SysParams.theory_file_type^"/"
in
    val _ = theory_path := path :: (!theory_path)
end;

val _ = new_parent "lift";
val _ = add_theory_to_sml "lift";

val empty_part_fun_DEF = new_definition ("empty_part_fun_DEF",
(--`empty_part_fun = \y:'b.(undefined: 'a lift)`--));

(*
val empty_part_fun_DEF = |- empty_part_fun = (\y. undefined) : thm
*)


val singleton_part_fun_DEF = new_definition ("singleton_part_fun_DEF",
(--`singleton_part_fun (x:'a) (s:'b) = 
      \y:'a. (x = y => lift s | undefined)`--));

(*
val singleton_part_fun_DEF =
  |- !x s. singleton_part_fun x s = (\y. (x = y) => (lift s) | undefined) : thm
*)

    
val update_fun_DEF = new_definition ("update_fun_DEF",
(--`update_fun f (x:'a) (y:'b) = \z. ((x = z) => y | f z)`--));

(*
val update_fun_DEF =
  |- !f x y. update_fun f x y = (\z. (x = z) => y | (f z)) : thm
*)

val modify_part_fun_DEF = new_definition ("modify_part_fun_DEF",
(--`modify_part_fun f (g:'a -> 'b lift) =
      \x.((g x = undefined) => f x | g x)`--));

(*
val modify_part_fun_DEF =
  |- !f g. modify_part_fun f g = (\x. (g x = undefined) => (f x) | (g x)) : thm
*)


val modify_ID = store_thm("modify_ID",
(--`!(f:'a -> 'b lift). (modify_part_fun empty_part_fun f = f) /\
 (modify_part_fun f empty_part_fun = f)`--),
GEN_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN 
REWRITE_TAC[modify_part_fun_DEF,empty_part_fun_DEF,ETA_AX] THEN
GEN_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);

(*
val modify_ID =
  |- !f.
       (modify_part_fun empty_part_fun f = f) /\
       (modify_part_fun f empty_part_fun = f) : thm
*)


val part_fun_range_DEF =
    new_definition("part_fun_range_DEF",
(--`!f:'a -> 'b lift. part_fun_range f = \y. ?x.f x = lift y`--));

(*
val part_fun_range_DEF = |- !f. part_fun_range f = (\y. ?x. f x = lift y) : thm
*)


val part_fun_range_lemma = store_thm("part_fun_range_lemma",
(--`!(f:'a -> 'b lift) x. is_defined (f x) ==>
                               part_fun_range f (lower (f x))`--),
REPEAT STRIP_TAC THEN
PURE_ONCE_REWRITE_TAC[part_fun_range_DEF] THEN BETA_TAC THEN
EXISTS_TAC (--`x:'a`--) THEN CONV_TAC SYM_CONV THEN
PURE_ONCE_REWRITE_TAC[lift_lower_THM] THEN FIRST_ASSUM ACCEPT_TAC);

(*
val part_fun_range_lemma =
  |- !f x. is_defined (f x) ==> part_fun_range f (lower (f x)) : thm
*)


val part_fun_domain_DEF =
    new_definition("part_fun_domain_DEF",
(--`!f:'a -> 'b lift. part_fun_domain f = \x.is_defined (f x)`--));

(*
val part_fun_domain_DEF = |- !f. part_fun_domain f = (\x. is_defined (f x))
  : thm
*)


val part_fun_domain_lemma = save_thm("part_fun_domain_lemma",
BETA_RULE(CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) part_fun_domain_DEF));

(*
val part_fun_domain_lemma = |- !f x. part_fun_domain f x = is_defined (f x)
  : thm
*)


val part_fun_domain_undef_lemma = store_thm("part_fun_domain_undef_lemma",
(--`!x:'b. ~(part_fun_domain (\x. (undefined:'a lift)) x)`--),
GEN_TAC THEN PURE_ONCE_REWRITE_TAC [part_fun_domain_lemma] THEN
BETA_TAC THEN REWRITE_TAC [is_defined_lemma]);

(*
val part_fun_domain_undef_lemma = |- !x. ~(part_fun_domain (\x. undefined) x)
  : thm
*)


val disjoint_domains_DEF = new_definition ("disjoint_domains_DEF",
    (--`!(f:'b -> 'a lift) (g:'b -> 'a lift).
        disjoint_domains f g =
             ~?x. part_fun_domain f x = part_fun_domain g x`--));

(*
val disjoint_domains_DEF =
  |- !f g.
       disjoint_domains f g = ~(?x. part_fun_domain f x = part_fun_domain g x)
  : thm
*)


val disjoint_domians_modify_commute =
store_thm("disjoint_domians_modify_commute",
(--`!f (g:'a -> 'b lift). disjoint_domains f g ==>
    ((modify_part_fun f g) = (modify_part_fun g f))`--),
REPEAT GEN_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC[disjoint_domains_DEF,modify_part_fun_DEF,part_fun_domain_DEF] THEN
BETA_TAC THEN CONV_TAC RIGHT_IMP_FORALL_CONV THEN GEN_TAC THEN
CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV THENC LEFT_IMP_FORALL_CONV) THEN
EXISTS_TAC (--`x:'a`--)  THEN
(REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [is_defined_lemma]) THEN
ASM_REWRITE_TAC [is_defined_is_not_undefined]);

(*
val disjoint_domians_modify_commute =
  |- !f g. disjoint_domains f g ==> (modify_part_fun f g = modify_part_fun g f)
  : thm
*)


val lift_fun_DEF =
    new_definition("lift_fun_DEF",
		   (--`!(f:'a -> 'b). lift_fun f = \x. lift (f x)`--));

(*
val lift_fun_DEF = |- !f. lift_fun f = (\x. lift (f x)) :thm
*)


val lift_fun_ASSOC_THM = store_thm("lift_fun_ASSOC_THM",
(--`!(g:'b -> 'c) (f:'a -> 'b) x. lift_fun g (f x) = lift_fun (g o f) x`--),
REPEAT GEN_TAC THEN
REWRITE_TAC[lift_fun_DEF,definition "combin" "o_DEF"] THEN
BETA_TAC THEN REFL_TAC);

(*
val lift_fun_ASSOC_THM = |- !g f x. lift_fun g (f x) = lift_fun (g o f) x :thm
*)


val lift_fun_domain_TOTAL = store_thm("lift_fun_domain_TOTAL",
(--`!f:'a -> 'b.part_fun_domain (lift_fun f) = \x.T`--),
GEN_TAC THEN REWRITE_TAC[lift_fun_DEF, part_fun_domain_DEF] THEN
CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
REWRITE_TAC[is_defined_lemma]);

(*
val lift_fun_domain_TOTAL = |- !f. part_fun_domain (lift_fun f) = (\x. T) : thm
*)


val lift_compose_DEF =
    new_definition("lift_compose_DEF",
		   (--`!(g:'b -> 'c lift) (f:'a -> 'b lift) x.
		       lift_compose g f x =
		       (is_defined(f x) =>  g (lower (f x)) | undefined)`--));

(*
val lift_compose_DEF =
  |- !g f x.
       lift_compose g f x =
       ((is_defined (f x)) => (g (lower (f x))) | undefined) : thm
*)


val lift_compose_ASSOC = store_thm("lift_compose_ASSOC",
(--`!(h:'c -> 'd lift) (g:'b -> 'c lift) (f:'a -> 'b lift).
  lift_compose h (lift_compose g f) = lift_compose (lift_compose h g) f`--),
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
REWRITE_TAC[lift_compose_DEF] THEN
STRIP_ASSUME_TAC (ISPEC (--`(f:'a -> 'b lift) x`--) lift_CASES) THEN
ASM_REWRITE_TAC [is_defined_lemma,lower_DEF]);

(*
val lift_compose_ASSOC =
  |- !h g f.
       lift_compose h (lift_compose g f) = lift_compose (lift_compose h g) f
  : thm
*)


val lift_compose_lift_THM = store_thm ("lift_compose_lift_THM",
(--`!(g:'b -> 'c lift) (f:'a -> 'b) x.
      lift_compose g (lift_fun f) x = g (f x)`--),
REPEAT GEN_TAC THEN
PURE_REWRITE_TAC[lift_compose_DEF,lift_fun_DEF] THEN
BETA_TAC THEN REWRITE_TAC[is_defined_lemma,lower_DEF]);

(*
val lift_compose_lift_THM =
  |- !g f x. lift_compose g (lift_fun f) x = g (f x) :thm
*)


val lift_compose_lemma = store_thm ("lift_compose_lemma",
(--`!(g:'b -> 'c lift) f:'a -> 'b lift.
       lift_compose g f =
       \x.(is_defined(f x) => g (lower (f x)) | undefined)`--),
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN
MATCH_ACCEPT_TAC lift_compose_DEF);

(*
val lift_compose_lemma =
  |- !g f.
       lift_compose g f =
       (\x. (is_defined (f x)) => (g (lower (f x))) | undefined) : thm
*)

val lift_compose_ID = store_thm("lift_compose_ID",
(--`!f:'a -> 'b lift. (lift_compose f (lift_fun \x.x) = f) /\
                      (lift_compose (lift_fun \x.x) f = f)`--),
GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
PURE_ONCE_REWRITE_TAC[lift_compose_lift_THM] THEN BETA_TAC THEN
REWRITE_TAC[lift_compose_lemma,lift_fun_DEF] THEN BETA_TAC THEN GEN_TAC THEN
COND_CASES_TAC  THENL
[ASM_REWRITE_TAC[lift_lower_THM],
 CONV_TAC SYM_CONV THEN
 ASM_REWRITE_TAC[undefined_not_exists_THM,SYM(SPEC_ALL is_defined_DEF)]]);

(*
val lift_compose_ID =
  |- !f.
       (lift_compose f (lift_fun (\x. x)) = f) /\
       (lift_compose (lift_fun (\x. x)) f = f) : thm
*)


val lift_fun_compose_COMMUTE = store_thm ("lift_fun_compose_COMMUTE",
(--`!(g:'b -> 'c) (f:'a -> 'b).
     lift_compose (lift_fun g) (lift_fun f) = lift_fun (g o f)`--),
REPEAT GEN_TAC THEN
CONV_TAC FUN_EQ_CONV THEN
REWRITE_TAC[SYM(SPEC_ALL lift_fun_ASSOC_THM),lift_compose_lift_THM]);

(*
val lift_fun_compose_COMMUTE =
  |- !g f. lift_compose (lift_fun g) (lift_fun f) = lift_fun (g o f) :thm
*)


val range_compose = store_thm("range_compose",
(--`!(f:'a -> 'b lift) (g:'b -> 'c) t. part_fun_range f t ==>
      part_fun_range (lift_compose (lift_fun g) f) (g t)`--),
REPEAT GEN_TAC THEN
PURE_REWRITE_TAC [part_fun_range_DEF,lift_compose_DEF,lift_fun_DEF] THEN
BETA_TAC THEN STRIP_TAC THEN EXISTS_TAC (--`x:'a`--) THEN
ASM_REWRITE_TAC [is_defined_lemma,lift_ONE_ONE,lower_DEF]);

(*
val range_compose =
  |- !f g t.
       part_fun_range f t ==>
       part_fun_range (lift_compose (lift_fun g) f) (g t) : thm
*)


val lift_fun_of_graph_DEF =
    new_specification
      {name = "lift_fun_of_graph_DEF",
       consts = [{const_name = "lift_fun_of_graph", fixity = Prefix}],
       sat_thm =
       prove
       ((--`?p. !(g:'a -> 'b -> bool) x.
	 (?y.g x y) => (is_defined(p g x) /\ g x (lower (p g x)))
	   | (p g x = undefined)`--),
	EXISTS_TAC (--`\g (x:'a).(?y.g x y) => lift (@y:'b. g x y)
			                    | undefined `--) THEN
	REPEAT STRIP_TAC THEN
	BETA_TAC THEN
	COND_CASES_TAC THEN  (* Why does it leave the T and F behind? *)
	ASM_REWRITE_TAC[is_defined_lemma,lower_DEF] THEN
	CONV_TAC SELECT_CONV THEN
	FIRST_ASSUM ACCEPT_TAC)};

(*
val lift_fun_of_graph_DEF =
  |- !g x.
       (?y. g x y)
       => (is_defined (lift_fun_of_graph g x) /\
           g x (lower (lift_fun_of_graph g x)))
       | (lift_fun_of_graph g x = undefined) : thm
*)


val lift_fun_of_graph_lemma = store_thm("lift_fun_of_graph_lemma",
(--`!(g:'a -> 'b -> bool) x.
      ((lift_fun_of_graph g x = undefined) = (!y.~(g x y))) /\
      (is_defined (lift_fun_of_graph g x) =
       g x (lower(lift_fun_of_graph g x))) /\
      ((?y.g x y) = g x (lower(lift_fun_of_graph g x)))`--),
GEN_TAC THEN GEN_TAC THEN ASM_CONJ1_TAC THENL
[(EQ_TAC THENL
  [(DISCH_TAC THEN
    ASSUM_LIST (fn thl => ASSUME_TAC
		(REWRITE_RULE thl 
		 (SPECL [(--`g:'a -> 'b -> bool`--),(--`x:'a`--)]
		        lift_fun_of_graph_DEF))) THEN
    FIRST_ASSUM (UNDISCH_TAC o concl) THEN REWRITE_TAC[is_defined_lemma] THEN
    (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST_ASSUM (UNDISCH_TAC o concl) THEN
    CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
    DISCH_THEN ACCEPT_TAC),
   (PURE_ONCE_REWRITE_TAC[undefined_not_exists_THM] THEN
    CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN DISCH_TAC THEN
    STRIP_TAC THEN
    ASSUM_LIST (fn thl => ASSUME_TAC
		(REWRITE_RULE thl 
		 (SPECL [(--`g:'a -> 'b -> bool`--),(--`x:'a`--)]
		        lift_fun_of_graph_DEF))) THEN
    ASM_REWRITE_TAC[undef_not_lift])]),
 (REWRITE_TAC[is_defined_DEF] THEN
  ASM_REWRITE_TAC
    [REWRITE_RULE[](AP_TERM (--`~`--)
		    (SYM(SPEC_ALL undefined_not_exists_THM)))] THEN
  CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN REWRITE_TAC [] THEN
  EQ_TAC THENL
  [(DISCH_TAC THEN
    ASSUM_LIST (fn thl => STRIP_ASSUME_TAC
		(REWRITE_RULE thl 
		 (SPECL [(--`g:'a -> 'b -> bool`--),(--`x:'a`--)]
		        lift_fun_of_graph_DEF)))),
   (DISCH_THEN (fn th => EXISTS_TAC (rand(concl th)) THEN ACCEPT_TAC th))])]);

(*
val lift_fun_of_graph_lemma =
  |- !g x.
       ((lift_fun_of_graph g x = undefined) = (!y. ~(g x y))) /\
       (is_defined (lift_fun_of_graph g x) =
        g x (lower (lift_fun_of_graph g x))) /\
       ((?y. g x y) = g x (lower (lift_fun_of_graph g x))) : thm
*)


(*
Define the predicate is_part_fun_graph:('a -> 'b -> bool) -> bool which
describes those relations that are the graphs of partial functions.
*)

val is_part_fun_graph_DEF = new_definition("is_part_fun_graph_DEF",
(--`!g:'a -> 'b -> bool.is_part_fun_graph g =
      !x y1 y2. ((g x y1) /\ (g x y2)) ==> (y1 = y2)`--));

(*
val is_part_fun_graph_DEF =
  |- !g.
       is_part_fun_graph g =
       (!x y1 y2. g x y1 /\ g x y2 ==> (y1 = y2)) :thm
*)


(*
Define the function mk_part_fun_graph:('a -> 'b lift) -> 'a -> 'b -> bool
which returns the graph of a partial function.
*)

val mk_part_fun_graph_DEF = new_definition("mk_part_fun_graph_DEF",
(--`!f:'a -> 'b lift.mk_part_fun_graph f = \x y.f x = lift y`--));

(*
val mk_part_fun_graph_DEF =
  |- !f. mk_part_fun_graph f = (\x y. f x = lift y) :thm
*)


val fun_graph_fun_THM = store_thm("fun_graph_fun_THM",
(--`!f:'a -> 'b lift. lift_fun_of_graph(mk_part_fun_graph f) = f`--),
GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
PURE_ONCE_REWRITE_TAC[mk_part_fun_graph_DEF] THEN BETA_TAC THEN
ASM_CASES_TAC (--`?y:'b.f (x:'a) = lift y`--) THEN
FIRST_ASSUM
  (fn thm =>
    STRIP_ASSUME_TAC
     (REWRITE_RULE[thm,SYM(SPEC_ALL lift_lower_THM)]
      (BETA_RULE
       (SPECL [(--`\ (x:'a) (y:'b). f x = lift y`--),(--`x:'a`--)]
	lift_fun_of_graph_DEF)))) THENL
[ACCEPT_TAC(SYM(TRANS
  (ASSUME(--`f x =
     lift (lower (lift_fun_of_graph (\ (x:'a) (y:'b). f x = lift y) x))`--))
  (ASSUME(--`lift (lower (lift_fun_of_graph (\x y. f x = lift y) x)) =
    lift_fun_of_graph (\ (x:'a) (y:'b). f x = lift y) x`--)))),
 PURE_ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
 ASM_REWRITE_TAC[undefined_not_exists_THM]]);


(*
val fun_graph_fun_THM =
  |- !f. lift_fun_of_graph (mk_part_fun_graph f) = f :thm
*)


val fun_fun_graph_THM = store_thm("fun_fun_graph_THM",
(--`!g:'a -> 'b -> bool.(mk_part_fun_graph(lift_fun_of_graph g) = g) =
                     (is_part_fun_graph g)`--),
GEN_TAC THEN
PURE_ONCE_REWRITE_TAC[mk_part_fun_graph_DEF,is_part_fun_graph_DEF] THEN
CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
EQ_TAC THENL
[CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV))) THEN
 STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
 CONV_TAC (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV SYM_CONV)))) THEN
 STRIP_TAC THEN
 PURE_ONCE_REWRITE_TAC[SYM(SPEC_ALL lift_ONE_ONE)] THEN
 ASM_REWRITE_TAC[],
 REPEAT STRIP_TAC THEN
 (ASM_CASES_TAC (--`?y. g (x:'a) (y:'b)`--) THENL
  [ALL_TAC, POP_ASSUM (ASSUME_TAC o (CONV_RULE NOT_EXISTS_CONV))]) THEN
 ASSUM_LIST (fn thl => STRIP_ASSUME_TAC
 (CONV_RULE (NOT_EXISTS_CONV ORELSEC ALL_CONV)
  (REWRITE_RULE (undefined_not_exists_THM :: is_defined_DEF :: thl)
   (SPECL [(--`g:'a -> 'b -> bool`--),(--`x:'a`--)]
    lift_fun_of_graph_DEF)))) THENL
 [POP_ASSUM
  (fn th =>
   ASSUM_LIST
   (fn thl => ASSUME_TAC (REWRITE_RULE(lower_DEF :: thl) th))) THEN
  ASM_REWRITE_TAC[lift_ONE_ONE] THEN
  CONV_TAC (RATOR_CONV (RAND_CONV SYM_CONV)) THEN
  EQ_TAC THEN DISCH_TAC THENL
  [ASM_REWRITE_TAC[], RES_TAC],
  ASM_REWRITE_TAC[]]]);

(*
val fun_fun_graph_THM =
  |- !g.
       (mk_part_fun_graph (lift_fun_of_graph g) = g) =
       is_part_fun_graph g :thm
*)


val graph_compose_DEF = new_definition("graph_compose_DEF",
(--`!g h. graph_compose g h = \(x:'a) (z:'c). ?y:'b. h x y /\ g y z`--));

(*
val graph_compose_DEF = |- !g h. graph_compose g h = (\x z. ?y. h x y /\ g y z)
  : thm
*)



val graph_lift_compose_COMMUTE = store_thm("graph_lift_compose_COMMUTE",
(--`!(g:'b -> 'c lift)(f:'a -> 'b lift).
       graph_compose (mk_part_fun_graph g) (mk_part_fun_graph f) =
       mk_part_fun_graph(lift_compose g f)`--),
GEN_TAC THEN GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
PURE_REWRITE_TAC[graph_compose_DEF,
		 mk_part_fun_graph_DEF,
		 lift_compose_DEF] THEN BETA_TAC THEN
(STRIP_ASSUME_TAC (ISPEC (--`(f:'a -> 'b lift)x`--)lift_CASES) THEN
 ASM_REWRITE_TAC[is_defined_lemma,undef_not_lift,lower_DEF,lift_ONE_ONE]) THEN
EQ_TAC THENL
[(STRIP_TAC THEN ASM_REWRITE_TAC[]),
 (DISCH_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
  EXISTS_TAC (--`x'':'b`--) THEN (CONJ_TAC THEN REFL_TAC))]);


(*
val graph_lift_compose_COMMUTE =
  |- !g f.
       graph_compose (mk_part_fun_graph g) (mk_part_fun_graph f) =
       mk_part_fun_graph (lift_compose g f) : thm
*)


val lift_graph_compose_is_lift_compose_graph =
store_thm("lift_graph_compose_is_lift_compose_graph",
(--`!(h:'b -> 'c -> bool)(g:'a -> 'b -> bool).
      ((is_part_fun_graph h) /\ (is_part_fun_graph g)) ==>
      (lift_fun_of_graph(graph_compose h g) =
       lift_compose(lift_fun_of_graph h)(lift_fun_of_graph g))`--),
GEN_TAC THEN GEN_TAC THEN
PURE_REWRITE_TAC[is_part_fun_graph_DEF,lift_compose_lemma] THEN STRIP_TAC THEN
CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN GEN_TAC THEN
PURE_ONCE_REWRITE_TAC[lift_fun_of_graph_lemma] THEN
(COND_CASES_TAC THEN
 ASM_REWRITE_TAC[lift_fun_of_graph_lemma,graph_compose_DEF]) THENL
[(ASM_CASES_TAC
    (--`lift_fun_of_graph (h:'b -> 'c -> bool)
                          (lower (lift_fun_of_graph g (x:'a))) =
         undefined`--) THENL
  [(FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM (UNDISCH_TAC o concl) THEN
    PURE_ONCE_REWRITE_TAC[lift_fun_of_graph_lemma] THEN
    BETA_TAC THEN CONV_TAC CONTRAPOS_CONV THEN 
    CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN REWRITE_TAC[] THEN
    STRIP_TAC THEN EXISTS_TAC (--`y:'c`--) THEN
    (fn gl as (asl,g) =>
       SUPPOSE_TAC(mk_eq{lhs = rand(rator g),
			 rhs = rand(rator(hd asl))})gl) THENL
    [(FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC),
     (FIRST_ASSUM (fn th => MATCH_MP_IMP_TAC th THEN STRIP_TAC THEN
                   FIRST_ASSUM ACCEPT_TAC))]),
   (POP_ASSUM (fn th =>
               let val th1 = REWRITE_RULE
	            [SYM(SPEC_ALL is_defined_is_not_undefined)] th
               in ASSUME_TAC th1 THEN
                  ASSUME_TAC (REWRITE_RULE [lift_fun_of_graph_lemma] th1)
               end) THEN
    (fn gl as (_,g) =>
     let val {lhs=l,rhs=r} = dest_eq g
	 val graph = rand(rator l)
	 val lower = (--`lower:'c lift -> 'c`--)
	 val graph_at_x = mk_comb{Rator=graph,Rand =(--`x:'a`--)}
	 val asm1 = mk_comb{Rator = graph_at_x,
			    Rand = mk_comb{Rator=lower, Rand =l}}
	 val asm2 = mk_comb{Rator = graph_at_x,
			    Rand = mk_comb{Rator=lower, Rand = r}}
	 val z1 = (--`z1:'c`--)
	 val z2 = (--`z2:'c`--)
	 val asm3 =
	     list_mk_forall
	     ([z1,z2],
	      mk_imp{ant=mk_conj{conj1=mk_comb{Rator=graph_at_x,Rand =z1},
				 conj2=mk_comb{Rator=graph_at_x,Rand =z2}},
		     conseq=mk_eq{lhs=z1,rhs=z2}})
     in
	 SUPPOSE_TAC asm1 THENL
	 [SUPPOSE_TAC asm2 THENL [SUPPOSE_TAC asm3, ALL_TAC],ALL_TAC]
     end  gl) THENL
    [(SUBST_MATCH_TAC (SYM(UNDISCH(SPEC_ALL lower_ONE_ONE))) THENL
      [(FIRST_ASSUM MATCH_MP_IMP_TAC THEN
	(CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)),
       (CONJ_TAC THENL
	[ASM_REWRITE_TAC[lift_fun_of_graph_lemma],
         FIRST_ASSUM ACCEPT_TAC])]),
     (BETA_TAC THEN REPEAT STRIP_TAC THEN
      PURE_ONCE_REWRITE_TAC[SYM(SPEC_ALL is_defined_DEF)] THEN
      FIRST_ASSUM (MATCH_MP_IMP_TAC o (SPEC (--`y:'b`--))) THEN
      (CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC]) THEN
      (SUPPOSE_TAC (--`(y:'b) = y'`--) THENL [ASM_REWRITE_TAC[],ALL_TAC]) THEN
      FIRST_ASSUM (MATCH_MP_IMP_TAC o (SPEC (--`x:'a`--))) THEN
      (CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)),
     (BETA_TAC THEN
      EXISTS_TAC (--`(lower (lift_fun_of_graph g (x:'a))):'b`--) THEN
      (CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)),
     (PURE_ONCE_REWRITE_TAC[SYM(CONJUNCT2(CONJUNCT2
			      (SPEC_ALL lift_fun_of_graph_lemma)))] THEN
      BETA_TAC THEN FIRST_ASSUM (EXISTS_TAC o rand o concl) THEN
      EXISTS_TAC (--`(lower (lift_fun_of_graph g (x:'a))):'b`--) THEN
      (CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC))])]),
 (BETA_TAC THEN GEN_TAC THEN FIRST_ASSUM (UNDISCH_TAC o concl) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[SYM(CONJUNCT2(CONJUNCT2(SPEC_ALL lift_fun_of_graph_lemma)))]THEN
  STRIP_TAC THEN EXISTS_TAC (--`y':'b`--) THEN FIRST_ASSUM ACCEPT_TAC)]);


(*
val lift_graph_compose_is_lift_compose_graph =
  |- !h g.
       is_part_fun_graph h /\ is_part_fun_graph g ==>
       (lift_fun_of_graph (graph_compose h g) =
        lift_compose (lift_fun_of_graph h) (lift_fun_of_graph g)) : thm
val it = () : unit
*)


val _ = export_theory();
