(* ===================================================================== *)
(* FILE          : mk_pair.sml                                           *)
(* DESCRIPTION   : The (non-definitional) theory of pairs. Translated    *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


new_theory "pair";

val MK_PAIR_DEF = new_definition("MK_PAIR_DEF", 
                --`MK_PAIR (x:'a)(y:'b) = \a b.(a=x)/\(b=y)`--);
val IS_PAIR_DEF = new_definition("IS_PAIR_DEF",
                --`IS_PAIR p = ?(x:'a) (y:'b). p = MK_PAIR x y`--);

val PAIR_EXISTS = prove(
   --`?p. IS_PAIR (p:'a->'b->bool)`--,
   EXISTS_TAC (--`MK_PAIR (x:'a) (y:'b)`--)
   THEN REWRITE_TAC[MK_PAIR_DEF,IS_PAIR_DEF]
   THEN EXISTS_TAC (--`x:'a`--)
   THEN EXISTS_TAC (--`y:'b`--)
   THEN REWRITE_TAC[]);

new_type_definition{name = "prod",
                    pred = --`IS_PAIR:('a->'b->bool)->bool`--, 
                    inhab_thm = PAIR_EXISTS};

(* Added TFM 88.03.31							*)
(*									*)
(* needs to be added because new_type_definition now does not define 	*)
(* REP_prod.								*)
new_definition("REP_prod",
   --`REP_prod  = 
       @rep:('a,'b)prod->('a->'b->bool). 
            (!p' p''. (rep p' = rep p'') ==> (p' = p'')) /\ 
            (!p. IS_PAIR (p:'a->'b->bool)  = (?p'. p = rep p'))`--);

val COMMA_DEF = new_infix_definition("COMMA_DEF", 
              --`, (x:'a) (y:'b) = @p. REP_prod p = MK_PAIR x y`--, 50);
val FST_DEF = new_definition ("FST_DEF",
              --`FST(p:'a#'b) = @x. ?y. MK_PAIR x y = REP_prod p`--);
val SND_DEF = new_definition("SND_DEF", 
              --`SND(p:'a#'b) = @y. ?x. MK_PAIR x y = REP_prod p`--);

(* The following can be proved, but out of laziness we make them axioms *)
val PAIR = save_thm ("PAIR", mk_thm([], --`!(x:'a#'b). (FST x, SND x) = x`--));
val FST = save_thm ("FST", mk_thm([], --`!(x:'a)(y:'b). FST(x,y) = x`--));
val SND = save_thm ("SND", mk_thm([], --`!(x:'a)(y:'b). SND(x,y) = y`--));

val PAIR_EQ = store_thm("PAIR_EQ",
   --`((x:'a, (y:'b)) = (a,b)) = ((x=a) /\ (y=b))`--,
   EQ_TAC THENL
   [DISCH_THEN (fn th =>
    REWRITE_TAC [REWRITE_RULE [FST] (AP_TERM (--`FST:('a#'b)->'a`--) th),
                 REWRITE_RULE [SND] (AP_TERM (--`SND:('a#'b)->'b`--) th)]),
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);


(* UNCURRY is needed for terms of the form `\(x,y).t`   *)

val UNCURRY_DEF = new_definition("UNCURRY_DEF",
 --`UNCURRY(f:'a->'b->'c) (x,y) = f x y`--);
val CURRY_DEF = new_definition("CURRY_DEF", 
 --`CURRY (f:('a#'b)->'c) x y = f(x,y)`--);

close_theory();

export_theory();
