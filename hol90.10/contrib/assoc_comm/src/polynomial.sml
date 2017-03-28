signature Polynomial_sig =
  sig
    val all_solutions : (int array * int) -> 
                        (int array * int) -> int array list
  end;


functor POLYNOMIAL (Ac_lib : Ac_lib_sig) : Polynomial_sig =
struct

open Rsyntax;
infix 9 sub; open Array;
val length = List.length;

fun new_int_array s = array(s, 0);
val decr = Ac_lib.decr
val incr = Ac_lib.incr;

local 
fun e_d A B sA sB i j =
   let val Ai = A sub i
       and Bj = B sub j
       and soln = new_int_array (sA+sB)
       val lcm_Ai_Bj = Ac_lib.lcm Ai Bj
       val d = lcm_Ai_Bj div Ai
       and e = lcm_Ai_Bj div Bj
   in
     update (soln,i,d);
     update (soln,(sA+j),e);
     soln
   end
in
(* Huet's special solutions, referred to in lemma 2 of his IPL note. *)
fun special_solns (p1:int array) (p2:int array) = 
   let val sp1 = Array.length p1
       and sp2 = Array.length p2
   in
   Ac_lib.for2D (decr sp1) (decr sp2) (e_d p1 p2 sp1 sp2)
   end
end;


(* s1 is the lhs coefficients, s2 the rhs. A is the candidate solution.
   Example:
      is_solution (arrayoflist [2,1,1]) 
                  (arrayoflist [1,1,2])
                  (arrayoflist [1,0,0,1,1,0]);
      - val it = true : bool
*)
fun is_solution s1 s2 A = 
   (Ac_lib.sigma_prod A s1 0 0 (Array.length s1) = 
    Ac_lib.sigma_prod A s2 (Array.length s1) 0 (Array.length s2));



(* Simple backtrack over an array A of natural numbers. A is the state of the
 * solution, p is the predicate that tells if a fully-filled out solution is
 * OK, and i is the index into A that separates the filled in portion (the left
 * hand side) and the to-be filled out portions (the rhs). The list (a::b) is
 * the limit indices of each element of the solution and the list (c::d) is the
 * current values at each index.
 *
 * fun baktrack [] [] p A i = 
 *       if (p A) 
 *       then [Ac_lib.copy_int_arr A] 
 *       else []
 *   | baktrack (a::b) (c::d) p A i =
 *       if (c <= a) 
 *       then ((Ac_lib.cupdate A i c);
 *             (baktrack b d p A (i+1))@(baktrack (a::b) ((c+1)::d) p A i))
 *       else []
 *   | baktrack _ _ p A i = raise Ac_IMP_ERR;
 **)



(*---------------------------------------------------------------------------
 * Huet's examples. Size of solutions: AB - 7, CD - 29, EF - 65
 * val A = arrayoflist [2,1]
 * and B = arrayoflist [1,1,2]
 * and C = arrayoflist [15,2,1]
 * and D = arrayoflist [3,5,10]
 * and E = arrayoflist [9,5,2]
 * and F = arrayoflist [3,7,8];
 * 
 * all_solutions(A,2) (B,2);
 * all_solutions(C,15) (D,10);
 * all_solutions(E,9) (F,8);
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Maxa is the limit on values of the lhs, maxb the limit on values of 
 * the rhs.
 *---------------------------------------------------------------------------*)
fun all_solutions ((lhs_coeff:int array),maxa)
                  ((rhs_coeff:int array),maxb) =
   let
   val len = (Array.length lhs_coeff)+(Array.length rhs_coeff)
   and ssolns = special_solns lhs_coeff rhs_coeff
   and rhs_base = (Array.length lhs_coeff)
   and lhs_top = decr(Array.length lhs_coeff)
   and rhs_size = Array.length rhs_coeff
   and lhs_size = Array.length lhs_coeff
   and solutionp = is_solution lhs_coeff rhs_coeff
   and count = ref 0 
   and is_allzero = ref true
   and lhs_sum = ref 0
   and rhs_sum = ref 0
   val MAX = Portable.Array.fromList (Ac_lib.replicate maxa lhs_size @
                          Ac_lib.replicate maxb rhs_size)
   and S = (curry array) len 0
   and SS = (Portable.Array.fromList o (map Portable.Array.fromList)) ssolns
   and Slist = ref (flatten ssolns)
   and maxy_arr = (curry array) rhs_size maxb
   and maxy_arr_copy = (curry array) rhs_size maxb
   fun rhs_max () = Ac_lib.sigma_prod rhs_coeff maxy_arr 0 0 rhs_size
   and maxy k = 
       let val j = ref 0
       in while (!j < rhs_size)
          do let val i = ref 0 
             in Ac_lib.cupdate maxy_arr (!j) maxb
                ;
                while (!i <= k)
                do ( let val sij = SS sub (!i) sub (!j)
                     in if (((S sub (!i)) >= (sij sub (!i))) andalso
                            ((sij sub (rhs_base+(!j))) <= (maxy_arr sub (!j))))
                        then Ac_lib.cupdate maxy_arr (!j)
                                            ((sij sub (rhs_base+(!j)))-1)
                        else ()
                     end;
                     i := !i + 1)
                ;
                j := !j + 1
             end
       end
   in
   let fun backtrack i = 
      (if ((i+2) = len) 
       then let val d = !lhs_sum - (!rhs_sum)
                val q = d div (rhs_coeff sub (i-rhs_base+1))
            in
            if ((q * (rhs_coeff sub (i-rhs_base+1))) = d) 
            then ( Ac_lib.cupdate S (i+1) q;
                   if (!is_allzero) then is_allzero := false
                   else if ((solutionp S) andalso 
                            (all (fn x => not (Ac_lib.comp_gteq S x))
                                 (!Slist)))
                        then Slist := (Ac_lib.copy_int_arr S)::(!Slist)
                        else ())
            else ()
            end
       else  backtrack (i+1);

      if (((S sub i)+1) > (MAX sub i))
      then(if (i < rhs_base) 
           then lhs_sum := !lhs_sum - ((lhs_coeff sub i)*(MAX sub i))
           else rhs_sum := !rhs_sum-((rhs_coeff sub (i-rhs_base))*(MAX sub i));
           Ac_lib.cupdate S i 0)
      else
      ( Ac_lib.cupdate S i ((S sub i)+1);
        if (i < rhs_base)   (* working on lhs soln *)
        then ( maxy i; 
               lhs_sum := !lhs_sum + (lhs_coeff sub i);
               if (!lhs_sum > (rhs_max()))
               then ( lhs_sum := !lhs_sum - ((lhs_coeff sub i)*(S sub i));
                      Ac_lib.cupdate S i 0)
               else backtrack i)
        else  (* lhs set, working on partial rhs soln *)
        let val rhs_index = i-rhs_base
        in
          rhs_sum := !rhs_sum + (rhs_coeff sub rhs_index);
          if ((S sub i) > (maxy_arr sub rhs_index))
          then ( rhs_sum := !rhs_sum - ((rhs_coeff sub rhs_index)*(S sub i));
                 Ac_lib.cupdate S i 0)
          else if (!rhs_sum > !lhs_sum)
               then (rhs_sum := !rhs_sum-((rhs_coeff sub rhs_index)*(S sub i));
                     Ac_lib.cupdate S i 0)
               else backtrack i
         end))
   in
     backtrack 0; 
     !Slist
   end
end;

end; (* Polynomial *)
