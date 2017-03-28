(* ===================================================================== *)
(* FILE          : lib.sml                                               *)
(* DESCRIPTION   : library of useful SML functions.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


functor LIB(Exception : Exception_sig) : Lib_sig =
struct

fun LIB_ERR {function,message} =
	  Exception.HOL_ERR{origin_structure="Lib",
                            origin_function=function,
                            message=message};

(* Support routines of general utility *)

fun curry f x y = f(x,y)
fun uncurry f (x,y) = f x y

val append = curry (op @)
val concat = curry (op ^)
val equal = curry (op =)

(* The same as Cambridge ML's infix # *)
infix 3 ##
val op ## = (fn (f,g) => (fn (x,y) => (f x, g y)))

fun A f x = f x
fun B f g x = f (g x)
fun C f x y = f y x
fun I x = x
fun K x y = x
fun S x y z = x z (y z)

fun fst (x,_) = x
and snd (_,y) = y

fun can f x = (f x; true) handle _ => false

fun assert p x = 
   if (p x) 
   then x
   else raise LIB_ERR{function = "assert", message = "predicate not true"}

fun tryfind f = 
   let fun F (h::t) = (f h handle _ => F t)
         | F [] = raise LIB_ERR{function = "tryfind", 
                                message = "all applications failed"}
   in F
   end;

fun el _ [] = raise LIB_ERR{function = "el", message = "empty list"}
  | el 1 (a::_) = a
  | el n (_::rst) = 
      if (n<1)
      then raise LIB_ERR{function = "el",message = "negative index"}
      else el (n-1) rst

fun map2 f L1 L2 =
   let fun mp2 [] [] L = rev L
         | mp2 (a1::rst1) (a2::rst2) L = mp2 rst1 rst2 (f a1 a2::L)
         | mp2 _ _ _ = raise LIB_ERR{function = "map2",
                                     message = "different length lists"}
   in mp2 L1 L2 []
   end;

fun all p =
   let fun every [] = true
         | every (a::rst) = (p a) andalso every rst       
   in every 
   end;

fun all2 p  =
   let fun every2 [] [] = true
         | every2 (a1::rst1) (a2::rst2) = (p a1 a2) andalso (every2 rst1 rst2)
         | every2  _  [] = raise LIB_ERR{function = "all2",
                                         message = "different length lists"}
   in every2
   end;

fun first p =
   let fun oneth [] = raise LIB_ERR{function = "first",
                                    message = "unsatisfied predicate"}
         | oneth (a::rst) = 
             if (p a) 
             then a 
             else oneth rst
   in oneth
   end;

fun split_after n alist = 
   if (n >= 0)
   then let fun spa 0 (L,R) = (rev L,R)
              | spa _ (_,[]) = raise LIB_ERR{function = "split_after",
                                     message = "index bigger than list length"}
              | spa n (L,(a::rst)) = spa (n-1) (a::L, rst)
        in spa n ([],alist)
        end
   else raise LIB_ERR{function = "split_after",message = "negative index"};


fun itlist f L base_value =
   let fun it [] = base_value
         | it (a::rst) = f a (it rst)
   in it L 
   end;

fun itlist2 f L1 L2 base_value =
   let fun it ([],[]) = base_value
         | it ((a::rst1),(b::rst2)) = f a b (it (rst1,rst2))
         | it _ = raise LIB_ERR{function="itlist2",
                                message="lists of different length"}
   in  it (L1,L2)
   end;

fun rev_itlist f =
   let fun rev_it [] base = base
         | rev_it (a::rst) base = rev_it rst (f a base)
   in
   rev_it
   end;

fun rev_itlist2 f L1 L2 =
   let fun rev_it2 ([],[]) base = base
         | rev_it2 ((a::rst1),(b::rst2)) base = rev_it2 (rst1,rst2) 
                                                        (f a b base)
         | rev_it2 _ _ = raise LIB_ERR{function="rev_itlist2",
                                       message="lists of different length"}
   in rev_it2 (L1,L2)
   end;

fun end_itlist f =
   let fun endit [] = raise LIB_ERR{function = "end_itlist",
                                    message = "list too short"}
         | endit alist = 
            let val (base::ralist) = rev alist
            in itlist f (rev ralist) base
            end
   in endit
   end;

fun gather p L = itlist (fn x => fn y => if (p x) then x::y else y) L []

val filter = gather

fun partition p alist = 
   itlist (fn x => fn (L,R) => if (p x) then (x::L, R) else (L, x::R))
          alist ([],[]);

fun zip [] [] = []
  | zip (a::b) (c::d) = (a,c)::(zip b d)
  | zip _ _ = raise LIB_ERR{function = "zip",
			    message = "different length lists"}

val combine = uncurry zip

fun unzip L = itlist (fn (x,y) => fn (l1,l2) =>((x::l1),(y::l2))) L ([],[]);

val split = unzip

fun mapfilter f alist = 
   itlist (fn i => fn L => ((f i)::L) handle _ => L) alist [];

(* Remove one level of bracketing from a list. Isn't this just flat? *)
fun flatten alist = itlist append alist [];

exception NOT_FOUND
exception NO_CHANGE
fun assoc item =
   let fun assc ((key,ob)::rst) = 
             if (item = key)
             then ob
             else assc rst
         | assc [] = raise NOT_FOUND
   in assc
   end

fun assoc1 item =
   let fun assc ((entry as (key,_))::rst) = 
             if (item = key)
             then SOME entry
             else assc rst
         | assc [] = NONE
    in assc
    end;

fun assoc2 item =
   let fun assc((entry as (_,key))::rst) =
            if (item = key)
            then SOME entry
            else assc rst
         | assc [] = NONE
   in assc
   end;


type 'a subst = {redex:'a, residue:'a} list

fun subst_assoc test =
   let fun assc [] = NONE
         | assc ({redex,residue}::rst) = 
               if (test redex) 
               then SOME(residue)
               else assc rst
   in assc
   end;

infix 5 |->
fun (r1 |-> r2) = {redex=r1, residue=r2};

(* Some set operations *)

fun mem i =
   let fun it (a::rst) = (i=a) orelse it rst
         | it [] = false
   in it
   end;
    
fun mk_set [] = []
  | mk_set (a::rst) =
      if (mem a rst) 
      then mk_set rst
      else a::(mk_set rst);

fun union [] S = S
  | union S [] = S
  | union (a::rst) S2 = 
       if (mem a S2) 
       then (union rst S2)
       else union rst (a::S2);

(* Union of a family of sets *)
fun U set_o_sets = itlist union set_o_sets []

(* All the elements in the first set that are not also in the second set. *)
fun set_diff a b = gather (fn x => not (mem x b)) a
val subtract = set_diff

fun intersect [] _ = []
  | intersect _ [] = []
  | intersect S1 S2 = mk_set(gather (C mem S2) S1)

fun null_intersection _  [] = true
  | null_intersection [] _ = true
  | null_intersection (a::rst) S = 
        if (mem a S) 
        then false
        else (null_intersection rst S)

fun set_eq S1 S2 = (set_diff S1 S2 = []) andalso (set_diff S2 S1 = []);

(* Opaque type set operations *)
fun op_mem eq_func i =
   let val eqi = eq_func i
       fun mem [] = false
         | mem (a::b) = eqi a orelse mem b
   in mem
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
fun op_U eq_func set_o_sets = itlist (op_union eq_func) set_o_sets []

fun op_intersect eq_func a b = 
   let val mem = op_mem eq_func
       val in_b = C mem b
       fun mk_set [] = []
         | mk_set (a::rst) =
           if (mem a rst) 
           then mk_set rst
           else a::(mk_set rst)
   in mk_set(gather in_b a)
   end;


fun for base top f =
   let fun fer i = 
          if (i>top)
          then []
          else f i :: fer(i+1)
   in fer base
   end;

fun for_se base top f =
   let fun fer_se i =
         if (i>top)
         then ()
         else (f i; fer_se(i+1))
   in fer_se base
   end;

(* Strings and ints *)
local
fun nts 0 = []
  | nts n = chr((n mod 10)+48)::nts (n div 10)
in
fun int_to_string 0 = "0"
  | int_to_string n = 
      let val n' = abs n
      in implode((if (n'<> n) then "~" else "")::rev (nts n'))
      end
end;

fun string_to_int str =
   let val neg = ord"~"
       val accum = ref 0
       fun loop i = 
         (case ordof(str,i)
            of 48 => accum := (!accum) * 10
             | 49 => accum := (!accum) * 10 + 1
             | 50 => accum := (!accum) * 10 + 2
             | 51 => accum := (!accum) * 10 + 3
             | 52 => accum := (!accum) * 10 + 4
             | 53 => accum := (!accum) * 10 + 5
             | 54 => accum := (!accum) * 10 + 6
             | 55 => accum := (!accum) * 10 + 7
             | 56 => accum := (!accum) * 10 + 8
             | 57 => accum := (!accum) * 10 + 9
             | _  => raise LIB_ERR{function = "string_to_int",
                                   message = "not all numeric"};
          loop (i+1))
          handle Ord => !accum
   in 
   if (ordof(str,0) = neg) 
   then ~(loop 1) 
   else loop 0
   end;

local
infix 9 sub
open Array
in
fun list_of_array A =
   let val n = Array.length A
   in
   for 0 (n-1) (fn i => Array.sub(A,i))
   end
end;

(* A naive merge sort. *)
fun sort p = 
   let fun merge [] [] = []
         | merge a [] = a
         | merge [] a = a
         | merge (one as (a::rst1)) (two as (b::rst2)) = 
                if (p a b) 
                then (a::merge rst1 two)
                else (b::merge one rst2)
       fun pass [] = []
         | pass [a] = [a]
         | pass (a::b::rst) = (merge a b)::(pass rst)
       fun srt [] = []
         | srt [a] = a
         | srt L = srt (pass L)
   in
   srt o (map (fn x => [x]))
   end

val int_sort = sort (curry (op <= :int*int->bool))

(*  ( close_in(open_in s); true ) handle _ => false         *)
fun file_exists_for_reading s =
   System.Unsafe.SysIO.access(s,[System.Unsafe.SysIO.A_READ])
   handle System.Unsafe.CInterface.SystemCall _ => false


fun find_path (path::rst) fstr = 
      let val path' = path^fstr
      in if (file_exists_for_reading path')
         then path'
         else find_path rst fstr
      end
  | find_path [] s = raise LIB_ERR{function = "find_path",
				   message = "Can't find "^s^"."}


(* Try to keep empty string first in path. This is so that one can
   get around masking effects, e.g., one might be looking for a particular 
   "z.th" on the theory_path, but a "z.th" occurs "earlier" that hides the
   particular "z.th" being searched for. Helpful for developing local 
   versions of system {theories,help,libraries}.
*)
fun cons_path s L =
   if (mem s (!L))
   then ()
   else case L
          of (ref (alist as (""::rst))) => L := (""::s::rst)
           | _ => L := s::(!L)

fun append_path s L = 
   if (mem s (!L))
   then ()
   else L := (!L)@[s]


type time = System.Timer.time
val timestamp : unit -> System.Timer.time =
      System.Unsafe.CInterface.c_function "timeofday"

fun time_eq (t1:System.Timer.time) t2 = (t1 = t2)
fun time_lt (t1:System.Timer.time) t2 = System.Timer.earlier(t1,t2)


(* sml/nj 93 **********************
 * (* From Elsa Gunter *)
 * fun exit() = System.Unsafe.CInterface.exit 0;
 * 
 * (* From Elsa Gunter *)
 * fun compile file =
 *     let
 *         val old_interp = !System.Control.interp
 *     in
 *         System.Control.interp := false;
 *         use file handle e => Raise e;
 *         System.Control.interp := old_interp
 *     end
 * 
 * (* From Elsa Gunter *)
 * fun load file =
 *     let
 *         val old_interp = !System.Control.interp
 *     in
 *         System.Control.interp := true;
 *         use file handle e => Raise e;
 *         System.Control.interp := old_interp
 *     end
 * 
 * (* From Elsa Gunter *)
 * local
 *     fun all_dot_files [] = true
 *       | all_dot_files (file::files) =
 * 	  (ord file = ord ".") andalso all_dot_files files
 * in
 *     fun clean_directory directory =
 * 	if all_dot_files (System.Directory.listDir directory) then ()
 * 	else (case System.system ("/bin/rm "^directory^"/*")
 * 		of 0 => ()
 * 		 | _ => raise LIB_ERR{function = "clean_directory",
 * 				      message = "can't remove files."})
 * end
 * 
 ******************************)

(* sml/nj 102 **********************
 * (* From Elsa Gunter *)
 * fun exit() = System.Unix.exit 0;
 * 
 * (* From Elsa Gunter *)
 * fun compile file =
 *     let
 *         val old_interp = !Globals.interp
 *     in
 *         Globals.interp := false;
 *         use file handle e => Raise e;
 *         Globals.interp := old_interp
 *     end
 * 
 * (* From Elsa Gunter *)
 * fun load file =
 *     let
 *         val old_interp = !Globals.interp
 *     in
 *         Globals.interp := true;
 *         use file handle e => Raise e;
 *         Globals.interp := old_interp
 *     end
 * 
 * (* From Elsa Gunter *)
 * local
 *     fun all_dot_files [] = true
 *       | all_dot_files (file::files) =
 * 	  (ord file = ord ".") andalso all_dot_files files
 * in
 *     fun clean_directory directory =
 * 	if all_dot_files (System.Directory.listDir directory) then ()
 * 	else (case System.system ("/bin/rm "^directory^"/*")
 * 		of 0 => ()
 * 		 | _ => raise LIB_ERR{function = "clean_directory",
 * 				      message = "can't remove files."})
 * end
 ********************************************)

(* From Elsa Gunter *)
fun exit() = System.Unsafe.CInterface.exit 0;
 
 (* From Elsa Gunter *)
fun compile file =
   let val old_interp = !System.Control.interp
   in System.Control.interp := false;
      use file handle e => (System.Control.interp := old_interp; Raise e);
      System.Control.interp := old_interp
   end
 
 (* From Elsa Gunter *)
fun interpret file =
   let val old_interp = !System.Control.interp
   in System.Control.interp := true;
      use file handle e => (System.Control.interp := old_interp; Raise e);
      System.Control.interp := old_interp
   end
 

 (* From Elsa Gunter *)
local
fun all_dot_files [] = true
  | all_dot_files (file::files) =
 	  (ord file = ord ".") andalso all_dot_files files
in
fun clean_directory directory =
   if all_dot_files (System.Directory.listDir directory) 
   then ()
   else (case System.system ("/bin/rm "^directory^"/*")
           of 0 => ()
            | _ => raise LIB_ERR{function = "clean_directory",
                                 message = "can't remove files."})
end;
 
fun fresh_name s = 
   let val n = ref 0
   in   fn () => (n := !n + 1; s^(int_to_string (!n)))
   end;

(* sml/nj 93
 * fun use_string s = System.Compile.use_stream (open_string s)
 *                    handle e => Exception.Raise e
 ****)
(* sml/nj 102
 * fun use_string s = Compiler.Interact.use_stream (open_string s)
 *                    handle e => Exception.Raise e
 ****)

fun use_string s = System.Compile.use_stream (open_string s)
                   handle e => Exception.Raise e;

(* sml/nj 93 val say = System.Print.say; *)
(* sml/nj 102 val say = Compiler.Control.Print.say; *)

val say = System.Print.say;

fun quote s = "\""^s^"\"";

(* sml/nj 93 val eval_string = System.Compile.use_stream o open_string *)
(* sml/nj 102 val eval_string = Compiler.Interact.use_stream o open_string *)
val eval_string = System.Compile.use_stream o open_string;

val cd = System.Directory.cd
and pwd = System.Directory.getWD;
fun ls() = System.system "ls";

fun words2 sep string =
    snd (itlist (fn ch => fn (chs,tokl) => 
	           if (ch = sep) 
                   then if (null chs)
                        then ([],tokl)
		        else ([], (implode chs :: tokl))
	           else ((ch::chs), tokl))
                (sep::explode string)
                ([],[]));

fun front_n_back [] = raise LIB_ERR{function = "front_n_back", 
                                    message = "empty list"}
  | front_n_back L = 
       let val (last::rfront) = rev L
       in (rev rfront, last)
       end;

fun funpow n f x =
   let fun it (0,res) = res
         | it (n,res) = it (n-1, f res)
   in it(n,x)
   end;

end (* Lib *)
