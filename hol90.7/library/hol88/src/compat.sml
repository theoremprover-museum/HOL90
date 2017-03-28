(* ===================================================================== *)
(* FILE          : compat.sml                                            *)
(* DESCRIPTION   : Routines that provide compatibility with hol88.       *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


structure Compat : Compat_sig =
struct
fun COMPAT_ERR{function,message} = 
       HOL_ERR{origin_structure = "Compat",
               origin_function = function,
               message = message};

val setify = Lib.mk_set;
val find = Lib.first;
val match = Psyntax.match_term;
val prove_thm = Tactical.store_thm;
val string_of_int = Lib.int_to_string
val int_of_string = Lib.string_to_int;
val save = exportML;

fun assoc i alist = 
   case (Lib.assoc1 i alist)
     of NONE => raise COMPAT_ERR{function = "assoc",
                                 message = ""}
      | (SOME x) => x;
fun rev_assoc i alist = 
   case (Lib.assoc2 i alist)
     of NONE => raise COMPAT_ERR{function = "rev_assoc",
                                 message = ""}
      | (SOME x) => x;


val inst_type = Psyntax.type_subst;

val frees = rev o Term.free_vars;
val freesl = rev o Term.free_varsl;
val tyvars = rev o Term.type_vars_in_term
fun tyvarsl tm_list = itlist (union o tyvars) tm_list [];

fun GEN_ALL th = 
   Lib.itlist Drule.GEN 
              (Lib.set_diff (frees(Thm.concl th)) 
                            (freesl(Thm.hyp th)))
              th;

fun new_axiom(s,tm) = new_open_axiom(s,gen_all tm);

val conjuncts = Dsyntax.strip_conj
val disjuncts = Dsyntax.strip_disj


local
val num_Axiom = theorem "prim_rec" "num_Axiom"
in
fun new_prim_rec_definition (name,tm) =
   Psyntax.new_recursive_definition Prefix num_Axiom name tm

fun new_infix_prim_rec_definition(name,tm,prec) =
   Psyntax.new_recursive_definition (Infix prec) num_Axiom name tm
end;


val PROVE = Tactical.prove;
val prove_thm = Tactical.store_thm
val flat = Lib.flatten
val forall = Lib.all;


(* I really bungled this one! hol88 ancestry has different type than
 * hol90 ancestry. Plus, they return different answers: hol88 includes 
 * current theory, hol90 doesn't.
 ***)
fun ancestry() = Theory.current_theory()::Theory.ancestry"-";

val last = snd o Lib.front_n_back
val butlast = fst o Lib.front_n_back;

fun W f x = f x x;
fun CB f g x = g(f x);
val KI = K I;  (* Dual of K; K and KI are analogs of fst and snd *)
infix 4 oo;
val op oo = fn (f,(g,h)) => fn x => f(g x, h x);
fun Co (f,g) x y = f (g y) x;    (* permutation-composition                *)

fun replicate x =
   let fun repl 0 = []
         | repl n = x::repl (n-1)
   in repl
   end;

fun GEN_REWRITE_RULE F thlist1 thlist2 =
    Rewrite.GEN_REWRITE_RULE F 
        (Rewrite.add_rewrites Rewrite.empty_rewrites thlist1) thlist2;

fun GEN_REWRITE_TAC F thlist1 thlist2 =
    Rewrite.GEN_REWRITE_TAC F 
        (Rewrite.add_rewrites Rewrite.empty_rewrites thlist1) thlist2;

fun variant L tm =
   if is_var tm
   then Term.variant L tm
   else if is_const tm
        then Term.variant L (mk_var (dest_const tm))
        else raise COMPAT_ERR{function = "variant", 
                              message = "not a variable or a constant"};
end; (* Compat *)
