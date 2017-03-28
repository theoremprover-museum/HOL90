signature Ac_subst_sig =
  sig
    structure Ac_term : Ac_term_sig
    val mk_ident_binding : 'a -> {redex:'a, residue:'a}
    val is_ident_binding : {redex:''a, residue:''a} -> bool
    val identity_subst : 'a subst
    val redex_assoc : ''a -> ''a subst -> ''a option
    val apply_subst : Ac_term.ac_term subst 
                      -> Ac_term.ac_term -> Ac_term.ac_term
    val apply_subst_to_binding : Ac_term.ac_term subst
                                 -> {redex:'a, residue:Ac_term.ac_term}
                                 -> {redex:'a, residue:Ac_term.ac_term}
    val redexes : 'a subst -> 'a list
    val residues : 'a subst -> 'a list
    val compose : Ac_term.ac_term subst
                  -> Ac_term.ac_term subst -> Ac_term.ac_term subst
    exception MK_IDEMPOTENT
    val mk_idempotent : Ac_term.ac_term subst -> Ac_term.ac_term subst
    val compose_subst_sets : Ac_term.ac_term subst list
                             -> Ac_term.ac_term subst list
                             -> Ac_term.ac_term subst list
    val apply_substs : Ac_term.ac_term subst list 
                       -> Ac_term.ac_term -> Ac_term.ac_term list
    val apply_substs_to_terms : Ac_term.ac_term subst list 
                                -> Ac_term.ac_term list -> Ac_term.ac_term list
    val restrict : ''a subst -> ''a list -> ''a subst
  end;



functor AC_SUBST(structure Ac_lib: Ac_lib_sig
                 structure Ac_term : Ac_term_sig) : Ac_subst_sig =
struct
structure Ac_term = Ac_term;
open Rsyntax;
fun mk_ident_binding v = {redex = v, residue = v};
fun is_ident_binding {redex,residue} = redex = residue
val identity_subst = [];

fun redex_assoc item =
   let fun assc [] = NONE
         | assc ({redex,residue}::rst) = 
               if (item = redex) 
               then (SOME residue)
               else assc rst
   in assc
   end;



(* Go through a term and only operate on the leaves. *)
local 
fun endo f =
   let fun operate (Ac_term.Ac_app(g,args)) = 
                    Ac_term.Ac_app(g, map operate args)
         | operate atom = f atom
   in operate
   end
in
fun apply_subst s = 
   endo (fn atm => case (redex_assoc atm s)
                     of NONE => atm
                      | SOME replacement => replacement)
end;

fun apply_subst_to_binding s {redex,residue} = 
   {redex=redex, residue = apply_subst s residue};

fun redexes (s:'a subst) = map #redex s;
fun residues (s:'a subst) = map #residue s;

(* s2 o s1 *)
fun compose s2 s1 =
   let val c = map (apply_subst_to_binding s2) s1
       val c' = gather (not o is_ident_binding) c
       val s1redexes = redexes s1
       val c'' = gather (fn {redex,residue} => not (mem redex s1redexes)) s2
   in
   (c'@c'')
   end;


exception MK_IDEMPOTENT;

fun mk_idempotent s = 
   let fun find_free_binding theta vset =
          Ac_lib.extract (fn {redex,residue} => all (fn x => not (mem x vset))
                                                    (Ac_term.ac_vars residue))
                         theta
          handle e => raise MK_IDEMPOTENT
       fun mk_idem [] [] = identity_subst
         | mk_idem _  [] = raise MK_IDEMPOTENT
         | mk_idem []  _ = raise MK_IDEMPOTENT
         | mk_idem s vset =
             let val ((bnd as {redex,...}),rst) = find_free_binding s vset
             in compose [bnd] (mk_idem rst (Ac_lib.remove_once redex vset))
             end
   in mk_idem s (map #redex s)
   end;

fun compose_subst_sets subst_set1 subst_set2 =
   itlist (fn x => fn y => (map (compose x) subst_set2)@y) subst_set1 [];

fun apply_substs slist tm = map (fn s => apply_subst s tm) slist;

fun apply_substs_to_terms slist tmlist =
   itlist (fn x => fn y => (map (apply_subst x) tmlist)@y) slist [];

fun restrict s vlist = gather (fn {redex,residue} => mem redex vlist) s;

end; (* AC_SUBST *)
