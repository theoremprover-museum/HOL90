(*---------------------------------------------------------------------------
 * McCarthy's function for computing the fringe of a binary tree. 
 * It's a nested function, but a nested primitive recursion, and therefore
 * trivial to prove termination for. In fact, it should be automatic!
 *---------------------------------------------------------------------------*)

new_theory"fringe";

val _ = cons_path"../" theory_path;
val _ = new_parent"kls_list";
val APPEND = theorem"kls_list" "APPEND";



(*---------------------------------------------------------------------------
 *     Define btrees.
 *---------------------------------------------------------------------------*)
local open Hol_datatype
in
val btree_facts = hol_datatype
                        `btree = LEAF of 'a
                               | NODE of 'a => btree => btree`
end;


(*---------------------------------------------------------------------------
 * The size of a btree 
 *---------------------------------------------------------------------------*)
val Weight_eqns = 
define Prefix
   `(Weight (LEAF x) = 1) /\
    (Weight (NODE (v:'a) p q) = SUC(Weight q + Weight p))`;


(*---------------------------------------------------------------------------
 * The fringe of a btree is the elements at the leaves, from left-to-right.
 *---------------------------------------------------------------------------*)
val fringe_def = Rfunction
`measure (Weight o FST)`
   `(fringe(LEAF x, Acc) = x::Acc) /\
    (fringe(NODE (v:'a) b1 b2, Acc) = fringe(b1, fringe(b2,Acc)))`;


val fringe_terminates = Q.prove
`Weight b2 < Weight (NODE (v:'a) b1 b2) /\ 
 Weight b1 < Weight (NODE v b1 b2)`
(RW_TAC[Weight_eqns] THEN REPEAT CONJ_TAC 
 THEN REPEAT GEN_TAC 
 THEN CONV_TAC ARITH_CONV);


val fringe_eqns = save_thm("fringe_eqns", 
  RW_RULE [fringe_terminates] (#rules fringe_def));

val fringe_induction = save_thm("fringe_induction", 
   RW_RULE[fringe_terminates] (DISCH_ALL(#induction fringe_def)));


(*---------------------------------------------------------------------------
 * A property (from Boyer&Moore 79) of fringe: the fringe of a btree is
 * equal to the flattened btree. The neat thing about the B&M proof is
 * that it is fully automatic (they begin from our introduced subgoal),
 * including a subsidiary inductive proof that APPEND is associative. 
 *---------------------------------------------------------------------------*)
val flatten_def = 
define Prefix 
  `(flatten (LEAF x) = [x:'a]) /\
   (flatten (NODE v b1 b2) = APPEND (flatten b1) (flatten b2))`;


val flatten_eq_fringe = Q.prove
`!tr:'a btree. flatten tr = fringe(tr,[])`
(Q.SUBGOAL_THEN 
    `!tr (L:'a list). APPEND (flatten tr) L = fringe(tr,L)`
    (fn th => RW_TAC[APPEND,GSYM th]) 
 THEN 
  PROG_TAC{induction=fringe_induction, rules=fringe_eqns}
   THEN RW_TAC[flatten_def,APPEND]
   THEN REPEAT (POP_ASSUM (SUBST_ALL_TAC o SYM))
   THEN RW_TAC[theorem"list" "APPEND_ASSOC"]);


html_theory"-";
