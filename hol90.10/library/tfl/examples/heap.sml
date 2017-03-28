(*---------------------------------------------------------------------------
 * Binary trees and some algorithms
 *---------------------------------------------------------------------------*)

new_theory"heap";

val order = ty_antiq(Type`:'a -> 'a -> bool`);

local open Hol_datatype
in
val btree_facts = hol_datatype
                        `btree = LEAF of 'a
                               | NODE of 'a => btree => btree`
end;


val btree_pred = 
define Prefix
  `btree_pred x y = 
     (?(v:'a) M. y = NODE v M x) \/ (?v N. y = NODE v x N)`;

val WF_DEF = definition "WF" "WF_DEF";
use"../utils.sml";

val WFbtree = Q.prove`WF (btree_pred:'a btree -> 'a btree ->bool)`
(RW_TAC[WF_DEF,btree_pred] THEN BETA_TAC THEN GEN_TAC THEN 
 CONV_TAC(CONTRAPOS_CONV THENC NNF_CONV) THEN DISCH_TAC THEN 
 INDUCT_THEN (#induction(snd btree_facts)) MP_TAC THEN REPEAT STRIP_TAC THEN
 RES_TAC THEN RULE_ASSUM_TAC(RW_RULE[]) THEN ASM_RW_TAC[] THEN 
 POP_ASSUM MP_TAC THEN POP_ASSUM (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS) THEN 
 ASM_RW_TAC[]);


(*---------------------------------------------------------------------------
 * Due to Arthur Norman
 *---------------------------------------------------------------------------*)
val upheap_def = 
Rfunction
`inv_image btree_pred (SND o SND)`

   `(upheap(R:^order, w, LEAF x) = NODE w (LEAF x) (LEAF x)) /\
    (upheap(R, (w:'a), NODE v p q) =
         (R w v => NODE w (upheap(R,v,q)) p
                 | NODE v (upheap(R,w,q)) p))`;

val upheap_terminates = save_thm("upheap_terminates",
prove_termination  upheap_def
(CRW_TAC[theorem"WF" "WF_inv_image", WFbtree,btree_pred] 
  THEN REPEAT STRIP_TAC 
  THEN DISJ1_TAC 
  THEN MAP_EVERY Q.EXISTS_TAC [`v`,`p`]
  THEN RW_TAC[]));

val upheap_eqns = save_thm("upheap_eqns", 
  RW_RULE[upheap_terminates] (DISCH_ALL(#rules upheap_def)));

val upheap_induction = save_thm("upheap_induction", 
  RW_RULE[upheap_terminates] (DISCH_ALL(#induction upheap_def)));


(*---------------------------------------------------------------------------
 * The following prim. rec version accomplishes the same thing, with less
 *   work! The lesson seems to be to use primitive recursion when you can.
 *---------------------------------------------------------------------------*)
val Upheap_eqns = define Prefix
   `(Upheap (LEAF x) (R:^order) w = NODE w (LEAF x) (LEAF x)) /\
    (Upheap (NODE v p q) R (w:'a)  =
          (R w v => NODE w (Upheap q R v) p
                  | NODE v (Upheap q R w) p))`;


(*---------------------------------------------------------------------------
 * But could also just use the "Weight" measure.
 *---------------------------------------------------------------------------*)
val Weight_eqns = 
define Prefix
   `(Weight (LEAF x) = 1) /\
    (Weight (NODE (v:'a) p q) = SUC(Weight q + Weight p))`;

val heap_def = Rfunction `measure (Weight o SND o SND)`
   `(heap(R:^order, w, (LEAF x)) = NODE w (LEAF x) (LEAF x)) /\
    (heap(R,      (w:'a), NODE v p q) =
         (R w v => NODE w (heap(R,v,q)) p
                 | NODE v (heap(R,w,q)) p))`;

val heap_terminates = prove_termination heap_def
(RW_TAC[Weight_eqns] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
 DISCH_TAC THEN CONV_TAC ARITH_CONV);

val heap_eqns = save_thm("heap_eqns", 
  RW_RULE [heap_terminates] (#rules heap_def));

val heap_induction = save_thm("heap_induction", 
  RW_RULE [heap_terminates] (DISCH_ALL(#induction heap_def)));


(*---------------------------------------------------------------------------
 * Merging heaps 
 *---------------------------------------------------------------------------*)
val merge_heap_def = Rfunction
`measure ((\(x,y). Weight x + Weight y) o SND)`
   `(merge_heap(R:^order,LEAF x, b) = b) /\
    (merge_heap(R, NODE v b1 b2, LEAF x) = NODE v b1 b2) /\
    (merge_heap(R, NODE v b1 b2, NODE w c1 c2) = 
         (R v w => NODE v (merge_heap(R,b1,b2)) (NODE w c1 c2)
                |  NODE w (NODE v b1 b2) (merge_heap(R,c1,c2))))`;

val merge_heap_terminates = prove_termination merge_heap_def
(RW_TAC[Weight_eqns] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
 DISCH_TAC THEN CONV_TAC ARITH_CONV);

val merge_heap_eqns = save_thm("merge_heap_eqns", 
  RW_RULE [merge_heap_terminates] (#rules merge_heap_def));

val merge_heap_induction = save_thm("merge_heap_induction", 
  RW_RULE [merge_heap_terminates] (DISCH_ALL(#induction merge_heap_def)));


(* With better pattern matching. *)
val mheap_def = Rfunction
`measure ((\(x,y). Weight x + Weight y) o SND)`
   `(mheap(R, NODE v b1 b2, 
              NODE w c1 c2) = 
           (R v w => NODE v (mheap(R,b1,b2)) (NODE w c1 c2)
                  |  NODE w (NODE v b1 b2) (mheap(R,c1,c2)))) /\
    (mheap(R:^order,LEAF x, b) = b) /\
    (mheap(R, n, y) = n)`;

val mheap_terminates = prove_termination mheap_def
(RW_TAC[Weight_eqns] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
 DISCH_TAC THEN CONV_TAC ARITH_CONV);

val mheap_eqns = save_thm("mheap_eqns", 
  RW_RULE [mheap_terminates] (#rules mheap_def));

val mheap_induction = save_thm("mheap_induction", 
  RW_RULE [mheap_terminates] (DISCH_ALL(#induction mheap_def)));

html_theory"-";
