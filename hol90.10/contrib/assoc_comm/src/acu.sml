signature Acu_sig = 
  sig
    structure Ac_term : Ac_term_sig
    val ac_unify : term list -> Ac_term.ac_term
                   -> Ac_term.ac_term -> Ac_term.ac_term subst list
    val hol_ac_unify : term list -> term -> term -> term subst list
    val hol_ac_match : term list -> term -> term -> term subst list
  end;

functor ACU (structure Ac_lib : Ac_lib_sig
             structure Ac_subst : Ac_subst_sig
             structure Polynomial : Polynomial_sig) : Acu_sig =
struct
structure Ac_term = Ac_subst.Ac_term;
open Ac_term;
open Rsyntax;

fun ACU_ERR s = 
    HOL_ERR{origin_structure = "ACU",
            origin_function = s,
            message = ""};

infix 9 sub; open Array;
val length = List.length;

val arrayoflist = Portable.Array.fromList;


local 
val termlist_diff = Ac_lib.op_multiset_diff ac_term_eq
in
fun remove_common_terms (Ac_app(f,args1)) (Ac_app(g,args2)) =
     let val args1' = termlist_diff args1 args2
         and args2' = termlist_diff args2 args1
     in
     (Ac_app(f,args1'),Ac_app(g,args2'))
     end
  | remove_common_terms _ _ = raise ACU_ERR "remove_common_terms"
end;

fun mk_term_poly (Ac_app(f,args)) = 
     let val classes = Ac_lib.partition ac_term_eq args
         val reps = map hd classes
         and multiplicities = map length classes
     in
     zip reps multiplicities
     end
  | mk_term_poly _ = raise ACU_ERR "mk_term_poly";


local
val term_poly_sort_decr = sort (fn (_,(x:int)) => (fn (_,y) => x > y))
in
fun convert t1 t2 = 
   let val tpoly1 = term_poly_sort_decr (mk_term_poly t1)
       and tpoly2 = term_poly_sort_decr (mk_term_poly t2)
       val max_tpoly1 = snd (hd tpoly1)
       and max_tpoly2 = snd (hd tpoly2)
   in
   if (max_tpoly1 >= max_tpoly2)
   then ((arrayoflist (map snd tpoly1)),max_tpoly2,
         (arrayoflist (rev (map snd tpoly2))),max_tpoly1, 
         arrayoflist(tpoly1@(rev tpoly2)))
   else ((arrayoflist (map snd tpoly2)),max_tpoly1,
         (arrayoflist (rev (map snd tpoly1))),max_tpoly2, 
         arrayoflist(tpoly2@(rev tpoly1)))
   end
end;


fun gen_basis t1 t2 =
   let val (lp,ml,rp,mr,tpoly) = convert t1 t2
   in (tpoly, Polynomial.all_solutions(lp,ml) (rp,mr))
   end;


fun var_indices tpoly = 
   flatten (for 0 ((Array.length tpoly)-1) 
              (fn x => let val tm = fst (tpoly sub x)
                       in if (is_ac_var tm) then [x] else [] 
                       end));

fun gen_subst the_uniform_type tpoly c ss =
   let val vi = var_indices tpoly
       fun Qj soln =
          flatten (for 0 ((Array.length tpoly)-1)
                      (fn x => let val tm = fst (tpoly sub x)
                                   and sx = soln sub x
                               in if (sx = 1) andalso (not (is_ac_var tm))
                                  then [x] 
                                  else [] 
                               end))
       val qj = map (fn s => let val temp = Qj s
                             in if ((length temp) = 0) 
                                then (s, Ac_var(genvar the_uniform_type))
                                else (s,(fst(tpoly sub (Ac_lib.it_min temp))))
                             end)
                    ss
       fun find_tpart col =
          itlist (fn (s,q) => fn y =>
                    if (s sub col = 0) 
                    then y
                    else (Ac_lib.replicate q (s sub col))@y)
                 qj []
       val tparts = map find_tpart vi
   in
   Ac_subst.mk_idempotent
      (map2 (fn tp => fn x =>
               {redex = fst(tpoly sub x),
                residue = if (length tp = 1) then (hd tp) else Ac_app(c, tp)})
           tparts vi)
   end;


fun const_or_app_indices tpoly = 
   flatten (for 0 ((Array.length tpoly)-1) 
               (fn x => let val tm = fst (tpoly sub x)
                        in if (is_ac_var tm) 
                           then [] 
                           else [x]
                        end));

fun pair_subst s (t1,t2) = 
   (Ac_subst.apply_subst s t1, Ac_subst.apply_subst s t2);

val subst_in_subst:ac_term subst -> ac_term subst -> ac_term subst =
   map o Ac_subst.apply_subst_to_binding;


fun occurs (v as Ac_var _) =
     let fun occ (w as Ac_var _) = (v = w)
           | occ (Ac_const _) = false
           | occ (Ac_app(_,args)) = exists occ args
     in occ
     end
  | occurs _ = raise ACU_ERR "occurs";


(* Unbelievably complicated algorithm
 *
 *    term list -> ac_term -> ac_term -> ac_term subst list 
 *
 ***)

fun ac_unify ac_consts t1 t2 = 
let 
fun unif t1 t2 = uni[(t1,t2)] [Ac_subst.identity_subst]
and
uni [] subs = subs
| uni ((l,r)::rst) subs = 
   if (l = r) 
   then uni rst subs
   else if (is_ac_var l) 
        then if (occurs l r) 
             then []  (* Empty list of unifiers means failure *)
             else let val new_addition = [{redex=l, residue = r}]
                  in uni (map (pair_subst new_addition) rst)
                         (map (Ac_subst.compose new_addition) subs)
                  end
        else 
        if (is_ac_var r)
        then if (occurs r l) 
             then []
             else let val new_addition = [{redex=r, residue=l}]
                  in uni (map (pair_subst new_addition) rst)
                         (map (Ac_subst.compose new_addition) subs)
                  end
        else 
        if ((is_ac_const l) orelse (is_ac_const r)) 
        then []
        else let val (Ac_app(f,arg1)) = l
                 and (Ac_app(g,arg2)) = r
             in 
             if (f <> g)
             then []
             else if (mem f ac_consts)
                  then let val {Tyop="fun",Args=[ty,_]} = dest_type(type_of f)
                           val thetas = ACU ty l r
                       in
                       itlist (fn th => fn A =>
                                (uni (map (pair_subst th) rst)
                                     (map (Ac_subst.compose th) subs))@A)
                              thetas []
                       end
                  else uni ((zip arg1 arg2)@rst) subs
             end
and
unify_set tmlist = 
   let fun unif_set [] subs = subs
         | unif_set [a] subs = subs
         | unif_set (a::b::c) subs =
              let val thetas = unif a b
              in itlist (fn th => fn accum =>
                           (unif_set (map (Ac_subst.apply_subst th) (b::c))
                                     (map (Ac_subst.compose th) subs))@accum)
                        thetas []
              end
   in unif_set tmlist [Ac_subst.identity_subst]
   end
and
ACU ty t1 t2 = 
   if (ac_term_eq t1 t2) 
   then [Ac_subst.identity_subst]
   else 
   let val (t1' as Ac_app(f,args1), 
            t2' as Ac_app(g,args2)) = remove_common_terms t1 t2
   in if ((f <> g) orelse (length args1 = 0) orelse (length args2 = 0))
      then []
      else let val (tpoly,B) = gen_basis t1' t2'
               val subsets_n_substs = gather_subsets tpoly B
           in itlist(fn (ss,gammas) => fn accum =>
                       let val sigma = gen_subst ty tpoly f ss
                       in (restore_sub sigma gammas)@accum
                       end)
                    subsets_n_substs []
           end 
   end 
and
merge set_o_subst_sets =
   let 
   fun merge_subst_set subst_set =
      let fun resolve_conflicts [] subs = subs
            | resolve_conflicts (ambig::rst) subs =
                let val thetas = unify_set (Ac_subst.residues ambig)
                    and bnd = hd ambig
                    val new_conflicts = 
                       itlist (fn x => fn y => (map (subst_in_subst x) rst)@y)
                              thetas []
                    and new_subs = 
                       itlist (fn x => fn y =>
                                 let val new_subst = Ac_subst.compose x [bnd]
                                 in (map (Ac_subst.compose new_subst) subs)@y 
                                 end)
                              thetas []
                in
                resolve_conflicts new_conflicts new_subs
                end
          val parted = Ac_lib.partition
                          (fn bnd1 => fn bnd2 => (#redex bnd1 = #redex bnd2))
                          (flatten subst_set:ac_term subst)
          val (sb,groups) = (flatten##I) 
                            (Ac_lib.split (fn x => (length x) = 1) parted)
      in map Ac_subst.mk_idempotent 
             (if (length groups = 0) 
              then [sb] 
              else resolve_conflicts groups [sb])
      end
   val prospects = Ac_lib.cross_prod set_o_subst_sets
   in
   itlist (fn x => fn y => (merge_subst_set x)@y) prospects []
   end
and
restore_sub first others = 
let 
fun resolve_substs [] theta = 
      ([Ac_subst.mk_idempotent theta] handle MK_IDEMPOTENT => [])
  | resolve_substs ((b1 as {redex=v1,residue=t1})::sigma')
                   (theta:ac_term subst) =
     let val (same_pertainer_bind_set,theta') = 
                    Ac_lib.split (fn bnd => (#redex bnd = v1)) theta
     in if ((length same_pertainer_bind_set)=0) 
        then resolve_substs sigma' (Ac_subst.compose [b1] theta)
        else let val (b2 as {redex=v2,residue=t2}) = hd same_pertainer_bind_set
                 val deltas = unif t1 t2
             in 
             itlist(fn delta => fn accum => 
                      let val t1' = Ac_subst.apply_subst delta t1
                      in itlist(fn x => fn y => (resolve_substs delta x)@y)
                               (resolve_substs sigma' 
                                              ({redex=v1,residue=t1'}::theta'))
                               []
                      end)
                   deltas []
             end
     end
in itlist (fn x => fn y => (resolve_substs first x)@y) others []
end

(* Gather subsets of the basis subject to some constraints.
 *
 * Rule 4 of Fortenbacher implies that there can be no column of the
 * basis with a 2 or greater, when the term polynomial at that column is
 * a constant term or an application term.
 *
 * Rule 5 says that, within a row of the basis, all non-variable entries
 * must be unifiable (AC-unifiable).
 ***)
and 
gather_subsets tpoly B =
let val non_var_indices = const_or_app_indices tpoly
    fun rule4 soln = not(exists (fn x => (soln sub x) > 1) non_var_indices)
    fun rule5 soln = 
      (soln, unify_set 
             (itlist(fn x => fn y => 
                      if ((soln sub x) >= 1) 
                      then (fst(tpoly sub x))::y 
                      else y)
              non_var_indices []))
    val B' = gather rule4 B
    val further_reduction = 
         itlist (fn soln => fn y => 
                   let val (thing as (_,substs)) = rule5 soln
                   in if ((length substs) = 0)  (*???????????*)
                      then y 
                      else (thing::y)
                   end)
                B' []
    val (B'',basis_subst_sets) = (arrayoflist##arrayoflist) 
                                 (unzip further_reduction)
    fun col_sum soln_indices i = Ac_lib.sum (map (fn x => B'' sub x sub i)
                                                 soln_indices)
    fun OK_subset ss = 
       (not ((length ss) = 0))
       andalso
       (all I (for 0 ((Array.length tpoly)-1)
                   (fn x => let val cs = col_sum ss x
                            in ((cs >= 1) andalso
                               (is_ac_var (fst(tpoly sub x)) orelse (cs = 1)))
                            end)))
in
itlist (fn indices => fn accum =>
          let val thetas = merge (map (fn x => basis_subst_sets sub x) indices)
          in ((map (fn y => B'' sub y) indices),thetas)::accum
          end)
       (Ac_lib.subsets OK_subset (Ac_lib.iota 0 ((Array.length B'')-1)))  []
end
in
unif t1 t2
end;

fun hol_ac_unify ac_consts t1 t2 =
   let val mk_ac = mk_ac ac_consts
       val un_ac = un_ac ac_consts
       fun % {redex,residue} = {redex=un_ac redex, residue=un_ac residue}
       val theta = ac_unify ac_consts (mk_ac t1) (mk_ac t2)
   in map (map %) theta
   end;

fun hol_ac_match ac_consts t1 t2 =
   let val mk_ac = Ac_term.mk_ac ac_consts
       val mk_rigid_ac = Ac_term.mk_rigid_ac ac_consts
       val un_ac = Ac_term.un_ac ac_consts
       fun % {redex,residue} = {redex=un_ac redex, residue=un_ac residue}
   in
   case (ac_unify ac_consts (mk_ac t1) (mk_rigid_ac t2))
     of [] => raise ACU_ERR "hol_ac_match"
      | theta => map (map %) theta
   end;


end; (* ACU *)
