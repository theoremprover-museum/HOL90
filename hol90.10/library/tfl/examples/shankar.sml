new_theory "shankar";

local open Hol_datatype
in
val btree_info = 
          hol_datatype    `btree = LEAF | NODE of btree => 'a => btree`


val fold_def = 
   define Prefix
       `(fold LEAF (v:'a) (f:'a->'b->'a->'a)  = v) /\
        (fold (NODE t1 M t2) v f = f (fold t1 v f) M (fold t2 v f))`
end;


val th1 = Q.ASSUME`WF(R:'a ->'a->bool)`;
val th2 = Q.ASSUME`(f:'a -> 'a#'b#'a) = WFREC R M`;
val unfoldf = Prim.mk_functional (Term
    `unfold(P:'a->bool,(f:'a -> 'a#'b#'a),x) = 
        (P x => let (y,a,z) = f x
                in 
                NODE (unfold(P,f,y)) a (unfold(P,f,z))
         | LEAF)`);

val unfold_def = 
  function
   `unfold(P:'a->bool,(f:'a -> 'a#'b#'a),x) = 
        (P x => let (y,a,z) = f x
                in 
                NODE (unfold(P,f,y)) a (unfold(P,f,z))
         | LEAF)`;

val fusion_def = 
 function
   `fusion(P:'a->bool,
          (f:'a -> 'a#'b#'a),
          (c:'c),
          (g:'c ->'b ->'c ->'c),
          (x:'a))
     = (P x => let (y,a,z) = f x
               in 
               g (fusion(P,f,c,g,y))  a  (fusion(P,f,c,g,z))
        | c)`;

(* Prove that unfolding and then reducing is the same as doing a fusion. *)
g`!(P:'a->bool) (f:'a->'a#'b#'a) x (c:'b) g.
  fold c g (unfold(P,f,x)) = fusion(P,f,c,g,x)`;

val ef = expandf;

ef(REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[unfold_def] THEN 
   ONCE_REWRITE_TAC[fusion_def]);
