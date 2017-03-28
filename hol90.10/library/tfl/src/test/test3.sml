(* From Peter Sestoft's 1996 Dagstuhl paper 
 * 
 *     "ML pattern match compilation and partial evaluation"
 *
 *---------------------------------------------------------------------------*)
new_theory"test3";

(*---------------------------------------------------------------------------
 * Define a type of lambda terms, plus "let" expressions.
 *---------------------------------------------------------------------------*)
val ty_info = 
Hol_datatype.hol_datatype `lambda = Var of num
                                  | Lamb of num => lambda
                                  | App of lambda => lambda
                                  | Let of num => lambda => lambda`;


(*---------------------------------------------------------------------------
 * Last pattern inaccessible. Notice that this will generate more clauses
 * than the def'n for H1. Why? Because, at the time of processing the 
 * patterns for H, we take into account all given rows, and only detect 
 * non-reachability at the end of processing. During processing, the last
 * row (10) overlaps with row 6 and causes 6 to be expanded. The moral is
 * to go back and do the definition properly.
 *---------------------------------------------------------------------------*)
function `(H (Var m)               = 111) /\
          (H (Lamb m (Var n))      = 222) /\
          (H (Lamb m (Lamb n M))   = 333) /\
          (H (Lamb m (App M N))    = 444) /\
          (H (App (Lamb m M) N)    = 555) /\
          (H (App (App M N) P)     = 666) /\
          (H (Let m (Let n M N) P) = 777) /\
          (H (Lamb m (Let n M N))  = 888) /\
          (H (Let m M (App N P))   = 999) /\
          (H (App (App (Lamb m (Lamb n M)) N) P) = 1010)`;


function `(H1 (Var m)               = 111) /\
          (H1 (Lamb m (Var n))      = 222) /\
          (H1 (Lamb m (Lamb n M))   = 333) /\
          (H1 (Lamb m (App M N))    = 444) /\
          (H1 (App (Lamb m M) N)    = 555) /\
          (H1 (App (App M N) P)     = 666) /\
          (H1 (Let m (Let n M N) P) = 777) /\
          (H1 (Lamb m (Let n M N))  = 888) /\
          (H1 (Let m M (App N P))   = 999)`;


