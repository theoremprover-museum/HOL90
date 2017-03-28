(*---------------------------------------------------------------------------
 * Propositional logic
 *
 * A simple presentation of the Wang algorithm found in the LISP 1.5 book.
 * Adapted from Cambridge University's "Foundations of Computer Science" 
 * lecture notes by M. Richards.
 *---------------------------------------------------------------------------*)
new_theory"prop" handle _ => ();
new_parent"kls_list";


(*---------------------------------------------------------------------------
 * Datatype of propositions.
 *---------------------------------------------------------------------------*)
local open Hol_datatype
in
val prop_ty_def = 
     hol_datatype `prop = VAR of 'a
                        | NOT of prop
                        | AND of prop => prop
                        | OR of  prop => prop`
end;


val add_def = 
Q.new_definition("add_def",   `add(x:'a,s) = (mem x s => s | x::s)`);

val Prv = function
`(Prv(al,NOT x::cl, ar,cr)   = Prv(al,cl,ar,x::cr))                          /\
 (Prv(al,AND x y::cl, ar,cr) = Prv(al,x::y::cl,ar,cr))                       /\
 (Prv(al,OR x  y::cl,ar,cr)  = Prv(al,x::cl,ar,cr) /\ Prv(al,y::cl,ar,cr))   /\
 (Prv(al,VAR v::cl,ar,cr)    = mem v ar \/ Prv(add(v,al),cl,ar,cr))          /\
 (Prv(al,[],ar,NOT x::cr)    = Prv(al,[],ar,cr))                             /\
 (Prv(al,[],ar,AND x y::cr)  = Prv(al,[],ar,x::cr) /\ Prv(al,[],ar,y::cr))   /\
 (Prv(al,[],ar,OR x y::cr)   = Prv(al,[],ar,x::y::cr))                       /\
 (Prv(al,[],ar,VAR v::cr)    = mem v al \/ Prv(al,[],add(v,ar),cr))          /\
 (Prv(al,[],ar,([]:'a prop list)) = F)`;


(*---------------------------------------------------------------------------
 * Disjunctive normal form. Note that the recursion can't be structural, 
 * because of examples like
 *
 *   Dnf (a /\ (b \/ c)) /\ d 
 *     = ((a /\ b) \/ (a /\ c)) /\ d
 *     = (a /\ b /\ d) \/ (a /\ c /\ d)
 *---------------------------------------------------------------------------*)


infixr 5 /\ 
infixr 4 \/;

datatype prop = /\ of prop * prop
              | \/ of prop * prop
              | NOT of prop
              | VAR of string;


local fun D(x /\ (y \/ z)) = D(x /\ y) \/ D(x /\ z)
        | D((y \/ z) /\ x) = D(y /\ x) \/ D(z /\ x)
        | D x = x
in
fun Dnf (A /\ B) = D(Dnf A /\ Dnf B)
  | Dnf (A \/ B) = Dnf A \/ Dnf B
  | Dnf x = x
end;


(* Alternative? Which is faster/more correct? *)
fun Disj(A /\ B) = H(Disj A /\ Disj B)
  | Disj (A \/ B) = Disj A \/ Disj B
  | Disj x = x
and H(x /\ (y \/ z)) = Disj(x /\ y) \/ Disj(x /\ z)
  | H((y \/ z) /\ x) = Disj(y /\ x) \/ Disj(z /\ x)
  | H x = x;

val A = VAR"A";
val B = VAR"B"
val B1 = VAR"B1"
val B2 = VAR"B2"
val B3 = VAR"B3"
val C = VAR"C";
val D = VAR"D";

Dnf (VAR"a" /\ VAR"b");
Dnf ((VAR"a" /\ (VAR"b" \/ VAR"c")) /\ VAR"d");
Dnf (A /\ (B1 /\ (B2 \/ B3) \/ C) /\ D);
Disj (A /\ (B1 /\ (B2 \/ B3) \/ C) /\ D);

(*----------------------------------------------------------------------------
 *
 * val which_ty_def = Hol_datatype.hol_datatype `which = ONE | TWO`
 * 
 * Rfunction ??
 * `(DDnf(ONE,AND x y) = DDnf(TWO, AND (DDnf(ONE,x)) (DDnf(ONE,y)))) /\
 *  (DDnf(ONE,OR x y) = OR (DDnf(ONE,x)) (DDnf(ONE,y))) /\
 *  (DDnf(ONE,NOT x) = NOT(DDnf(ONE,x))) /\
 *  (DDnf(ONE,VAR v) = VAR (v:'a)) /\
 *  (DDnf(TWO,AND x(OR y z)) = DDnf(TWO,OR (DDnf(ONE,AND x y))
 *                                         (DDnf(ONE,AND x z)))) /\
 *  (DDnf(TWO,AND (OR y z)x) = DDnf(TWO,OR (DDnf(ONE,AND y x)) 
 *                                         (DDnf(ONE,AND z x)))) /\
 *  (DDnf(TWO, x) = x)`;
 * 
 *---------------------------------------------------------------------------*)
