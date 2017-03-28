(*---------------------------------------------------------------------------
 * Expression evaluation
 *
 * A datatype of arithmetic expressions and the equivalence of two
 * different evaluation mechanisms.
 *---------------------------------------------------------------------------*)
new_theory"expression" handle _ => ();

use "../utils.sml";

(*---------------------------------------------------------------------------
 * Datatype of expressions
 *---------------------------------------------------------------------------*)
local open Hol_datatype
in
val expression_ty_def = 
  hol_datatype `expression = VAR of 'a
                           | CONST of num
                           | ADD of expression => expression
                           | APPLY of expression => 'a => expression`
end;


(* Association lists *)
val assoc_def = Rfunction 
  `inv_image (\L1 L2. ?h. L2 = h::L1) (FST o SND)`
     `(assoc(k1,[],d) = (d:'b)) /\
      (assoc(k1:'a, (k,y)::t, d) = ((k=k1) => y | assoc(k1, t, d)))`;

(* Compare the ML style for readability. *)
 fun assoc (k1,[],d) = d
   | assoc (k1, (k,y)::t, d) = if (k=k1) then y else assoc(k1, t, d);

