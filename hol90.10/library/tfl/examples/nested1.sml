(*---------------------------------------------------------------------------
 * This example refers to the one in "nested.sml". The question asked
 * at the Munich Types Club Meeting was 
 *
 *    "what about if you take   g 0 = 1?"
 *
 *---------------------------------------------------------------------------*)

new_theory"nested1" handle _ => ();

val Gdef = 
Rfunction `$<`  `(G 0 = 1) /\ 
                 (G(SUC x) = G(G x))`;


(*---------------------------------------------------------------------------
val Gdef =
  {induction= |- !P.
                  P 0 /\
                  (!x. (G x < SUC x ==> P (G x)) /\ P x ==> P (SUC x)) ==>
                  (!v. P v),
   rules=|- (G 0 = 1) /\ 
            (G (SUC x) = ((G x < SUC x) => (G (G x)) | (@v. T))),
   tcs=[`!x. G x < SUC x`]}
----------------------------------------------------------------------------*)

tgoal Gdef;

(*---------------------------------------------------------------------------
val it =
  Status: 1 proof.
  1. Incomplete:
       Initial goal:
       `!x. G x < SUC x`
-----------------------------------------------------------------------------*)

REC_INDUCT_TAC (#induction Gdef);
(*---------------------------------------------------------------------------
  `G 0 < SUC 0 /\
   (!x.
     (G x < SUC x ==> G (G x) < SUC (G x)) /\ G x < SUC x ==>
     G (SUC x) < SUC (SUC x))`
  
Now the first conjunct can be rewritten with G 0 = 1 to get
an unsolvable goal. Termination can't be proved. So, what are we left with,
then? We've defined a function - what is it?

    G 0 = 1

    G 1 = (G 0 < 1) => G(G 0) | Arb
        = (1 < 1) => G(G 0) | Arb
        = Arb

    G 2 = (G 1 < 2) => G(G 1) | Arb
        = (Arb < 2) => G(G 1) | Arb
        = no known way to proceed.

The lesson is not to believe you really have the originally specified 
function until you have eliminated all the termination conditions.
-----------------------------------------------------------------------------*)
