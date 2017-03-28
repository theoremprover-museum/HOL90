signature Ac_lib_sig = 
  sig
    val allzero : int array -> bool
    val arr_max : int array -> int
    val cart_prod : 'a list -> 'b list -> ('a * 'b) list
    val comp_gteq : int array -> int array -> bool
    val copy_int_arr : int array -> int array
    val cross_prod : 'a list list -> 'a list list
    val cupdate : 'a array -> int -> 'a -> unit
    val decr : int -> int
    val divided_by : int -> int -> bool
    val exp : int -> int -> int
    val extract : ('a -> bool) -> 'a list -> 'a * 'a list
    val for2D : int -> int -> (int -> int -> 'a) -> 'a list list
    val for2D_se : int -> int -> (int -> int -> 'a) -> unit
    val inc_2Darr : int array array -> unit
    val incr : int -> int
    val iota : int -> int -> int list
    val is_prime : int -> bool
    val it_min : int list -> int
    val largest_el : int list -> int
    val lcm : int -> int -> int
    val multiset_diff : ''a list -> ''a list -> ''a list
    val multiset_eq : ''a list -> ''a list -> bool
    val multiset_intersect : ''a list -> ''a list -> ''a list
    val multiset_union : 'a list -> 'a list -> 'a list
    val op_U : ('a -> 'a -> bool) -> 'a list list -> 'a list
    val op_disjoint : ('a -> 'a -> bool) -> 'a list list -> bool
    val op_intersect : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
    val op_is_subset : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val op_lex_gt : ('a -> 'b -> bool)
                    -> ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val op_mem : ('a -> 'b -> bool) -> 'a -> 'b list -> bool
    val op_multiset_diff : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
    val op_multiset_eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val op_multiset_gt : ('a -> 'a -> bool)
                         -> ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
    val op_multiset_intersect : ('a -> 'b -> bool)
                                -> 'a list -> 'b list -> 'a list
    val op_multiset_union : 'a list -> 'a list -> 'a list
    val op_nodupify : ('a -> 'a -> bool) -> 'a list -> 'a list
    val op_nodups : ('a -> 'a -> bool) -> 'a list -> bool
    val op_null_intersection : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val op_remove_all : ('a -> 'b -> bool) -> 'a -> 'b list -> 'b list
    val op_remove_once : ('a -> 'b -> bool) -> 'a -> 'b list -> 'b list
    val op_set_diff : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
    val op_set_eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val op_union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
    val partition : ('a -> 'a -> bool) -> 'a list -> 'a list list
    val perm : 'a list -> 'a list list
    val permute : 'a list -> 'a list list
    val powerset : 'a list -> 'a list list
    val remove_once : ''a -> ''a list -> ''a list
    val replicate : 'a -> int -> 'a list
    val rotate : 'a list -> 'a list list
    val sigma : (int -> int -> int)
                -> int array -> int array -> int -> int -> int -> int
    val sigma_prod : int array -> int array -> int -> int -> int -> int
    val split : ('a -> bool) -> 'a list -> 'a list * 'a list
    val subsets : ('a list -> bool) -> 'a list -> 'a list list
    val sum : int list -> int
    val transpose : 'a list list -> 'a list list
  end;

structure Ac_lib :Ac_lib_sig =
struct

fun AC_LIB_ERR{function,message} = HOL_ERR{origin_structure = "Ac_lib",
                                           origin_function = function,
                                           message = message}
open Rsyntax;
infix 9 sub; open Array;
val length = List.length;

(* So what is 0^0, anyway? *)
fun exp 0 m = 0
  | exp n 0 = 1
  | exp n m = n*(exp n (m-1));

fun decr x = x-1
and incr x = x+1;

fun it_min alist = 
   itlist (fn (x:int) => fn y => if (x <= y) then x else y) 
          alist (hd alist);

fun sum alist = itlist (curry (op+):int->int->int) alist 0

val split = Lib.partition  (* Naming clash with hol90 Lib *)

(* Partitions a list on the basis of a two-place predicate, which is moved
 * through the list. 
 * 
 *     - partition (uncurry (op =)) [1,2,3,1,1,2,2,3,4,5,4,4,3,2,1];
 *     val it = [[1,1,1,1],[2,2,2,2],[3,3,3],[4,4,4],[5]] : int list list
 ***)
fun partition p =
   let fun break [] = []
         | break (a::b) = 
             let val (class,rst) = split (p a) b
             in (a::class)::(break rst) 
             end
   in break
   end;


(* Takes a list, m long, of n-length lists, i.e., an m by n array, and
 * turns it into an n by m array by changing the ith column into the ith
 * row. 
 ***)
fun transpose a =  
   if (all null a) 
   then [] 
   else (itlist (curry (op ::)) (map hd a) []) :: (transpose (map tl a));

fun iota bot top = 
   let fun iot i =
         if (i > top) 
         then []
         else i::(iot (i+1))
   in iot bot
   end;

(* Might be generally useful.
 * fun itvector f v b =
 *    let fun it (i,x) = 
 *          if (i<0)
 *          then x
 *          else it (i-1, f (Vector.sub(v,i)) x)
 *    in it(Vector.length v - 1, b)
 *    end;
 * 
 * fun rev_itvector f v b =
 *    let val len = Vector.length v
 *        fun rev_it (i,x) = 
 *          if (i>=len)
 *          then x
 *          else rev_it (i+1, f (Vector.sub(v,i)) x)
 *    in rev_it(0, b)
 *    end;
 ***)

(* Just plain wrong. Not easy to see how to modify this to generate and 
 * test in a subset-by-subset manner. The problem is that you can't filter 
 * without destroying other subsets that may meet the predicate.
 *
 * local 
 * fun cons x L = x::L
 * in
 * fun subsets_r p =
 *    let val filt = filter p
 *        fun f [] = filt [[]]
 *          | f (a::rst) = 
 *             let val ss = f rst
 *             in filt (map (cons a) ss)@(filt ss)
 *             end
 *    in f
 *    end
 * end;
 ***)

(* In SML/NJ, the following is no faster than the commented out 
 * implementation of subsets.
 ***)
local
(* powers of 2 from 0 to MAX_BASIS_SIZE *)
val MAX_BASIS_SIZE = 29
val powers_of_two = Vector.vector (map (exp 2) (iota 0 MAX_BASIS_SIZE))
in
fun subsets p (s:'a list) =
   let val svect = Vector.vector s
       val sze = Vector.length svect
       val two_exp_sze = exp 2 sze
                         handle Overflow => raise AC_LIB_ERR
                                             {function="subsets",
                                              message ="too many"}
       fun word_to_subset w =
          let fun is_bit_set i = 
                 (Bits.andb(w, Vector.sub(powers_of_two,i)) <> 0)
              fun loop i = 
                if (i>=sze)
                then []
                else case (is_bit_set i)
                       of false => loop(i+1)
                        | true => Vector.sub(svect,i)::loop(i+1)
          in loop 0
          end
        fun loop i =
           if (i>=two_exp_sze)
           then []
           else let val sset = word_to_subset i
                in if (p sset)
                   then sset::loop(i+1)
                   else loop(i+1)
                end
   in loop 0
   end
end;

val powerset = subsets (fn _ => true);

(*
 * exception INSUFFICIENT_BITS;
 * 
 * (* - bit_pattern 4 3;   val it = [0,0,1,1] : int list *)
 * fun bit_pattern bits n =
 *    if (n < exp 2 bits)
 *    then let fun bpat n 0 = []
 *               | bpat n bits = 
 *                   let val divisor = exp 2 (bits-1)
 *                       val (quo,r) = ((n div divisor),(n mod divisor))
 *                   in quo::(bpat r (bits-1))
 *                   end
 *         in bpat n bits
 *         end
 *    else raise INSUFFICIENT_BITS;
 * 
 * 
 * fun subsets p (s:'a list) =
 *    let val size = length s
 *        fun sset bpat = 
 *           itlist2 (fn x => fn y => fn z => if (x=1) then (y::z) else z) 
 *                   bpat s
 *    in
 *    itlist (fn x => fn y => let val sbset = sset (bit_pattern size x) []
 *                            in if (p sbset) then (sbset::y) else y
 *                            end)
 *           (iota 0 ((exp 2 size)-1)) []
 *    end;
 ***)


fun remove_once item =
   let fun remv [] = []
         | remv (a::b) = 
             if (item=a) 
             then b
             else (a::remv b)
   in remv
   end;


(* Opaque type operations *)

fun op_mem eq_func i =
   let val eqi = eq_func i
       fun mem [] = false
         | mem (a::b) = eqi a orelse mem b
   in mem
   end;

fun op_nodups eq_func =
   let val mem = op_mem eq_func
       fun ndup [] = true
         | ndup (a::b) = 
               if (mem a b)
               then false 
               else ndup b
   in ndup
   end;

fun op_nodupify eq_func =
   let val mem = op_mem eq_func
       fun ndup [] = []
         | ndup (a::b) = 
               if (mem a b) 
               then ndup b
               else a::ndup b
   in ndup
   end;

fun op_union eq_func =
   let val mem = op_mem eq_func
       fun un [] [] = []
         | un a []  = a
         | un [] a  = a
         | un (a::b) c = 
             if (mem a c) 
             then (un b c)
             else (a::(un b c))
   in un
   end;

(* Union of a family of sets *)
fun op_U eq_func set_o_sets = itlist (op_union eq_func) set_o_sets [];

(* All the elements in the first set that are not also in the  second set. *)
fun op_set_diff eq_func a b = 
   let val mem = C (op_mem eq_func) b
   in gather (not o mem) a
   end;

fun op_remove_once eq_func item =
   let val eq_item = eq_func item
       fun remv [] = []
         | remv (a::rst) = 
               if (eq_item a) 
               then rst
               else (a::remv rst)
   in remv
   end;

fun op_remove_all eq_func item =
   let val eq_item = eq_func item
       fun remv [] = []
         | remv (a::rst) = 
               if (eq_item a) 
               then remv rst
               else (a::remv rst)
   in remv
   end;

fun op_intersect eq_func a b = 
   let val in_b = C (op_mem eq_func) b
   in gather in_b a
   end;

fun op_null_intersection eq_func =
   let val mem = op_mem eq_func
       fun null_int _  [] = true
         | null_int [] _ = true
         | null_int (a::b) c = 
            if (mem a c) 
            then false
            else null_int b c
   in null_int
   end;

fun op_disjoint eq_func =
   let fun disj [] = true
         | disj (a::b) = 
            (all null (map (op_intersect eq_func a) b))
            andalso (disj b)
   in disj
   end;

fun op_is_subset eq_func a b = 
   let val memb = C (op_mem eq_func) b
   in all memb a
   end;

fun op_set_eq eq_func =
   let val mem = op_mem eq_func
       val remove = op_remove_once eq_func
       fun seteq [] [] = true
         | seteq [] _ = false
         | seteq _ [] = false
         | seteq (a::b) c = 
             if (mem a c) 
             then seteq b (remove a c)
             else false
   in seteq
   end;

(* Extends an ordering on elements of a type to a lexicographic ordering on
 * lists of elements of that type. Right now, we require the lists to be the
 * same length.
 ***)
fun op_lex_gt eq_func order =
   let fun gt [] [] = false
         | gt (t1::rst1) (t2::rst2) =
              if (order t1 t2) 
              then true
              else if (eq_func t1 t2) 
                   then gt rst1 rst2
                   else false
         | gt  _ _  = raise AC_LIB_ERR{function = "op_lex_gt", 
                                       message = "inequal length lists"}
   in gt 
   end;



(* Multiset operations *)
val multiset_union = append;

fun multiset_intersect [] _ = []
  | multiset_intersect _ [] = []
  | multiset_intersect (a::b) c = 
      if (mem a c) 
      then (a::multiset_intersect b (remove_once a c))
      else multiset_intersect b c;

fun multiset_diff a [] = a 
  | multiset_diff [] a = []
  | multiset_diff (a::b) c = 
      if (mem a c)
      then (multiset_diff b (remove_once a c))
      else a::(multiset_diff b c);

val multiset_eq = set_eq;
val op_multiset_union = multiset_union;

fun op_multiset_intersect eq_func =
   let val mem = op_mem eq_func
       and remove = op_remove_once eq_func
       fun mint [] _ = []
         | mint _ [] = []
         | mint (a::b) c = 
            if (mem a c) 
            then (a::mint b (remove a c))
       else mint b c
   in mint
   end;

fun op_multiset_diff eq_func =
   let val mem = op_mem eq_func
       val remove = op_remove_once eq_func
       fun mdiff a [] = a 
         | mdiff [] _ = []
         | mdiff (a::b) c = 
             if (mem a c) 
             then mdiff b (remove a c)
             else a::mdiff b c
   in mdiff
   end;

val op_multiset_eq = op_set_eq;

(* Extends an ordering on elements of a type to multisets of elements of that
 * type.
 ***)
fun op_multiset_gt el_eq el_order m1 m2 =
   let val mdiff = op_multiset_diff el_eq
       val m1' = mdiff m1 m2
       and m2' = mdiff m2 m1
   in
   if (null m1') 
   then false
   else if (null m2') 
        then true
        else exists (fn x => all (el_order x) m2') m1'
   end;


local 
fun rot 0 _ = []
  | rot n [] = raise AC_LIB_ERR{function = "rotate.rot", 
                                message = "Can't rotate an empty list"}
  | rot n (al as (a::b)) = al :: (rot (n-1) (b@[a]))
in
fun rotate alist = rot (length alist) alist 
end;

(* Generate all n! permutations of a list with permute *)
fun perm [] = []
  | perm [a] = [[a]]
  | perm (a::b) = map (curry (op ::) a) (permute b)
and
    permute al = flatten (map perm (rotate al));


fun divided_by n1 n2 = 
   let val quotient = n1 div n2
   in n1 = quotient*n2
   end;

fun is_prime num = 
   (num = 2) 
   orelse
   all (not o (divided_by num)) (iota 2 ((num div 2)+1));

fun lcm n1 (n2:int) = 
   let val (large,small) = (if (n1 > n2) then (n1,n2) else (n2,n1))
       fun find_lcm i j =
          if (i = small) 
          then small*large
          else  let val smj = small*j
                    and lgi = large*i
                in if (smj = lgi) 
                   then smj
                   else if (smj > lgi) 
                        then find_lcm (i+1) j 
                        else find_lcm i (j+1)
                end

   in find_lcm 1 1
   end;

(* f needs to be a function with first arg corresponding to row and
   second to column. Notice how this gets inverted in the nested call. *)
fun for2D row_bound col_bound f =
    map (for 0 col_bound)
        (for 0 row_bound f);

fun for2D_se row_bound col_bound f =
    (map (for_se 0 col_bound) (for 0 row_bound f); ());

fun cart_prod s1 s2 = flatten (map (fn x => (map (fn y => (x,y)) s2)) s1);


(* Should generalize to other data types, as with sorting *)
fun largest_el alist = itlist (curry max) alist 0;

fun replicate x =
   let fun repl 0 = []
         | repl n = x::repl (n-1)
   in repl
   end;

(* - cross_prod [[1,2],[3,4,5],[6]];
 * val it = [[1,3,6],[1,4,6],[1,5,6],[2,3,6],[2,4,6],[2,5,6]] : int list list
 ***)
fun cross_prod lol =
   itlist (fn w => fn v => flatten (map (fn x => map (fn y => x::y) v) w))
          lol [[]];

fun extract p alist =
   let fun fnr ((a::rst),L) = 
             if (p a) 
             then (a, (rev L)@rst)
             else fnr (rst, a::L)
         | fnr ([],_) = raise AC_LIB_ERR{function = "extract",
                                         message = "unsatisfied predicate"}
   in fnr (alist,[])
   end;

(* This was for compatibility between PolyML and SML/NJ -- they used
 *    to differ on whether they had empty arrays.
 ****)
(*
 * abstype 'a ARRAY = ZERO_LEN_ARR | ARR of 'a Array.array
 * with
 * val arrayoflist = (fn [] => ZERO_LEN_ARR |
 *                       L => ARR (arrayoflist L));
 * 
 * val array = fn (0,_) => ZERO_LEN_ARR |
 *                (s,init_val) => ARR(Array.array(s,init_val));
 * 
 * val ARR_length = fn ZERO_LEN_ARR => 0 |
 *                 ARR A => Array.length A;
 * 
 * infix sub;
 * val sub = fn (ZERO_LEN_ARR,_) => raise Array.Subscript |
 *              (ARR A,i) => (op Array.sub)(A,i);
 * 
 * val update = fn (ZERO_LEN_ARR,_,_) => raise Array.Subscript |
 *                 (ARR A,i,v) => update(A,i,v);
 * end;
 ****)

fun cupdate x y z = update(x,y,z);

fun inc_2Darr (arr: int array array) =
   let val rows = (Array.length arr)
       and cols = decr(Array.length (arr sub 0))
       fun inc_el ar x y = cupdate (ar sub x) y (incr ((ar sub x) sub y))
   in
   for2D_se rows cols (inc_el arr)
   end;


fun copy_int_arr (A:int array) = 
    let val B = array((Array.length A),0)
    in 
       for 0 (decr(Array.length A)) (fn x => cupdate B x (A sub x));
       B
    end;

fun arr_max (A: int array) =
   let val max = ref 0
   in
      for_se 0 (decr(Array.length A)) 
               (fn x => if ((A sub x) > !max) 
                        then max := (A sub x) 
                        else ());
      !max
   end;


(* Sum of "products" from A1 and A2. Base indices are lbA1 and lbA2, number of
   products is n. f is the function applied index-wise.
*)
fun sigma f (A1:int array) (A2: int array) lbA1 lbA2 n =
   let fun sum_f i =
          if (i = n) 
          then 0
          else (f (A1 sub (lbA1+i)) (A2 sub (lbA2+i))) + (sum_f (i+1))
   in sum_f 0
end;

val sigma_prod = sigma (curry (op * :int*int->int));


(* Component-wise greater-than-or-equal-to (big conjunction) 
   Could be generalized by having an ordering predicate argument. *)
fun comp_gteq (A:int array) (B:int array) =
   let val n = Array.length A
       fun gt i =
          if (i=n) 
          then true
          else ((A sub i) >= (B sub i)) andalso gt (i+1)
   in gt 0
   end;

fun allzero (A:int array) = 
   let val n = Array.length A
       fun zerop i =
         if (i=n) 
         then true
         else ((A sub i) = 0) andalso zerop (i+1)
   in zerop 0
   end;

end; (* Ac_lib *)
