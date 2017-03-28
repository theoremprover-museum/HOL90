structure KBlib :KBlib_sig =
struct 
open Rsyntax;

fun KB_LIB_ERR s = 
       HOL_ERR{origin_structure = "KBlib",
               origin_function = s,
               message = ""};

fun cons x l = x::l;

(* Split around a predicate.
  Example.
  split (curry $= 3) [1;2;3;4;5;4;3;2;1;3];;
  ([3; 3; 3], [1; 2; 4; 5; 4; 2; 1]) : (int list # int list)
*)
fun split p alist = 
   let fun split [] L R = (L,R)
         | split (a::rst) L R = 
             if (p a)
             then split rst (a::L) R
             else split rst L (a::R)
   in
   split alist [] []
   end;


local fun rot 0 _ = [] |
      rot n [] = raise KB_LIB_ERR "rotate" |
      rot n (al as (a::b)) = al :: (rot (n-1) (b@[a]))
in
fun rotate alist = rot (length alist) alist
end;

(* Generate all n! permutations of a list with permute *)
fun perm [] = [] |
    perm [a] = [[a]] |
    perm (a::b) = map (cons a) (permute b)
and
    permute al = flatten (map perm (rotate al));

fun remove_once a [] = []
  | remove_once a (b::rst) = 
          if (a = b) 
          then rst
          else b::(remove_once a rst);
fun is_subset [] _ = true
  | is_subset (a::rst) S = (mem a S) andalso (is_subset rst S);

fun multiset_diff a [] = a |
    multiset_diff [] a = [] |
    multiset_diff (a::b) c = 
       if (mem a c) 
       then (multiset_diff b (remove_once a c))
       else a::(multiset_diff b c);

fun multiset_gt order m1 m2 =
   let val m1' = multiset_diff m1 m2
       and m2' = multiset_diff m2 m1
   in
   if (null m1') then false
   else
   if (null m2') then true
   else
   exists (fn x => all (order x) m2') m1'
   end;


(* Extends an ordering on elements of a type to a lexicographic ordering on
  lists of elements of that type.
*)
fun lex_gt order [] [] = false |
    lex_gt order _ []  = raise KB_LIB_ERR "lex_gt" |
    lex_gt order [] _  = raise KB_LIB_ERR "lex_gt"|
    lex_gt order (t1::rst1) (t2::rst2) =
          if (order t1 t2) then true
          else if (t1=t2) 
          then lex_gt order rst1 rst2
          else false;


fun merge_sort p = 
   let fun merge [] [] = [] |
           merge a [] = a |
           merge [] a = a |
           merge (one as (a::b)) 
                 (two as (c::d)) = 
                     if (p a c) 
                     then (a::merge b two)
                     else (c::merge one d)
       fun pass [] = [] |
           pass [a] = [a] |
           pass (a::b::c) = (merge a b)::(pass c)
       fun sort [] = [] |
           sort [a] = a |
           sort a = sort (pass a)
   in
   sort o (map (fn x => [x]))
   end;

fun iota bot top =
   if bot > top
   then []
   else bot::(iota (bot+1) top);

end;  (* KBlib *)
