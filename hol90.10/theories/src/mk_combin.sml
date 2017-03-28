(* ===================================================================== *)
(* FILE          : mk_combin.sml                                         *)
(* DESCRIPTION   : Basic combinator definitions and some theorems about  *)
(*                 them. Translated from hol88.                          *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.02.26                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


new_theory "combin";

(* Definition of function composition.          *)

val o_DEF = new_infix_definition("o_DEF", 
   --`o (f:'b->'c) (g:'a->'b) = \x:'a.f(g(x))`--,
   800);

val K_DEF = new_definition("K_DEF",
   --`K = \(x:'a) (y:'b). x`--);

val S_DEF = new_definition("S_DEF", 
   --`S = \(f:'a->'b->'c) (g:'a->'b) (x:'a). f x (g x)`--);

val I_DEF = new_definition("I_DEF", --`I:'a->'a = S K (K: 'a -> 'a -> 'a)`--);

close_theory ();


(* Theorem about application of composed functions.      *)

val o_THM = store_thm("o_THM",
   --`! (f:'b->'c) (g:'a->'b) (x:'a). (f o g) x = f(g(x))`--,
   REPEAT GEN_TAC 
   THEN PURE_REWRITE_TAC [ o_DEF ] 
   THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
   THEN REFL_TAC);

(* This theorem states that function composition is associative.  
*)
val o_ASSOC = store_thm("o_ASSOC",
   --`!(f:'c->'d) (g:'b->'c) (h:'a->'b). f o (g o h) = (f o g) o h`--,
   REPEAT GEN_TAC 
   THEN REWRITE_TAC [ o_DEF ] 
   THEN CONV_TAC (REDEPTH_CONV BETA_CONV) 
   THEN REFL_TAC);

(* Theorem about application of K.          *)
val K_THM = store_thm("K_THM",
    --`!(x:'a) (y:'b). K x y = x`--,
    REPEAT GEN_TAC
    THEN PURE_REWRITE_TAC [ K_DEF ] 
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN REFL_TAC);

(* Theorem about application of S.          *)
val S_THM = store_thm("S_THM",
   --`!(f:'a->'b->'c) (g:'a->'b) (x:'a). S f g x = (f x)(g x)`--,
   REPEAT GEN_TAC 
   THEN PURE_REWRITE_TAC [ S_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

(* Theorem about application of I.          *)
val I_THM = store_thm("I_THM",
   --`!x:'a. I x = x`--,
   REPEAT GEN_TAC 
   THEN PURE_REWRITE_TAC [ I_DEF, S_THM, K_THM ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

(* I is the identity for function composition.        *) 
store_thm("I_o_ID",
   --`!(f:'a->'b). ((I o f) = f) /\ ((f o I) = f)`--,
   REPEAT STRIP_TAC 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN REWRITE_TAC [ o_DEF ] 
   THEN CONV_TAC (REDEPTH_CONV BETA_CONV) 
   THEN REWRITE_TAC [ I_THM ]);

export_theory();
