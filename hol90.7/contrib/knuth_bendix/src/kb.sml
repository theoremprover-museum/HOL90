structure KB : KB_sig = 
struct

open Psyntax;

exception NOT_UNIFORM_TYPE and NOT_FUNCTION_TYPE and NOT_FIRST_ORDER_EQN and
          FIND_MATCH_ERR and OCCURS_CHECK and TERM_SIZE_ERR and 
          NON_VAR_SUBSTITUTION and NO_UNIFIER and EXCESS_VARS_IN_RHS and 
          LHS_CANNOT_BE_A_VARIABLE and RULE_ALREADY_MARKED and
          GET_UNMARKED and KB_NO_MATCH and EQN_NOT_ORIENTABLE;

exception TERM_MATCH
exception TERM_CLASH;
exception KB_IMP_ERR of string;

(* Warning. None of the functions that deal with terms in this file 
  check types, e.g., a substitution returned from the unification algo.
  may not actually be a match. These functions depend on input terms 
  having passed the "first order test" coded below.
*)

(* First some functions that tell if a term is first order
*)
fun is_uniform_var ty tm = (is_var tm) andalso (ty = type_of tm);
fun is_uniform_const ty tm = (is_const tm) andalso (ty = type_of tm);

fun strip_uniform_curried_functype ty fun_type =
   let val ("fun",[ty1,ty2]) = dest_type fun_type
   in
   if (ty = ty1)
   then if (ty = ty2)
        then [ty1 , ty2]
        else (ty1 :: strip_uniform_curried_functype ty ty2)
   else raise NOT_UNIFORM_TYPE
   end;


(* Actually, terms have to be recursively first order and of a
  uniform curried type.
*)
fun first_order ty tm = 
     (type_of tm = ty) andalso
     ((is_uniform_var ty tm) orelse
      (is_uniform_const ty tm) orelse
      (if (is_comb tm)
       then let val (c,args) = strip_comb tm
            in
            (all (first_order ty) args) andalso
            (is_const c) andalso
            ((length args)+1 = length (strip_uniform_curried_functype ty 
                                                                  (type_of c)))
            end
       else false))
       handle _ => false;


fun first_order_eqn ty tm =
   let val (tm1,tm2) = dest_eq tm
   in
   if (ty = type_of tm1)
   then (first_order ty tm1) andalso (first_order ty tm2)
   else false
   end;


(* Slightly adapted from the system "find_match" function
  so that it keeps an occurrence list (really just a director 
  string in which 0 means "go left" and 1 means "go right").
*)
fun kb_match pat =
   let fun find_mt occ ob =
      ((match_term pat ob, occ)
      handle _ =>
      find_mt (0::occ) (rator ob)
      handle _ => 
      find_mt (1::occ) (rand  ob)
      handle _ => 
      raise FIND_MATCH_ERR)
   in
   (I##rev) o (find_mt [])
   end;

(*
fun fot_occurs (v1 as Var _) v2 = (v1=v2) |
    fot_occurs _ (Const _) = false |
    fot_occurs v (c as Comb _) = exists (fn a => fot_occurs v a) 
                                    (snd (strip_comb c)) |
    fot_occurs _ _ = raise OCCURS_CHECK;
*)
exception FOT_OCCURS_ERR;
fun fot_occurs tm1 tm2 =
   if (is_var tm1)
   then (tm1 = tm2)
   else if (is_const tm2)
        then false
        else if (is_comb tm2)
             then exists (fn a => fot_occurs tm1 a)
                         (snd (strip_comb tm2))
             else raise FOT_OCCURS_ERR;

(*
fun term_size (Var _) = 0 |
    term_size (Const _) = 1 |
    term_size (c as Comb  _) = 1 + (itlist (fn x => fn y => (term_size x) + y)
                                           (snd (strip_comb c))
                                           0) |
    term_size _ = raise TERM_SIZE_ERR;
*)
fun term_size tm = 
   if (is_var tm)
   then 0
   else if (is_const tm) 
        then 1
        else if (is_comb tm)
             then 1 + (itlist (fn x => fn y => (term_size x) + y)
                              (snd (strip_comb tm))
                              0)
             else raise TERM_SIZE_ERR;

local
fun subst_in_subst_binding s (tm1,tm2) = ((subst s tm1), tm2)
fun is_ident_binding (t1,t2) = (t1=t2)
in
(* s2 o s1. For HOL-style substitutions, we require t/v bindings,
  i.e., the variable being substituted for is second.
*)
fun fot_compose s2 s1 =
   if ((all is_var (map snd s2)) andalso (all is_var (map snd s1)))
   then let val c = map (subst_in_subst_binding s2) s1
            val c' = gather (not o is_ident_binding) c
            val c'' = gather (fn (a,b) => not (mem b (map snd s1))) s2
        in
        (c'@c'')
        end
   else raise NON_VAR_SUBSTITUTION
end;

fun fot_app_sub s binding_list = map ((subst s)##(subst s)) binding_list;

(* First order unification example, from Martelli andalso Montanari paper.
  new_theory "gaz";
  new_constant("f", `:bool -> bool -> bool -> bool -> bool`);
  new_constant("g",`bool->bool->bool`);
  new_constant("h",`bool->bool->bool`);

  #fot_unify `f x (g y z) y F` `f (g (h T w) y) x (h T u) u`;
  [(`g(h T F)(h T F)`, `x`);
   (`h T F`, `y`);
   (`h T F`, `z`);
   (`F`, `w`);
   (`F`, `u`)]
   : (term # term) list
*)

(* There are faster ways of doing this.
*)
fun fot_unify t1 t2 =
   let fun unif [] s = s |
           unif ((l,r)::rst) s = 
             if (l = r) 
             then unif rst s
             else if (is_var l) 
                  then if (fot_occurs l r) 
                       then raise NO_UNIFIER
                       else let val new_addition = [(r,l)]
                            in unif (fot_app_sub new_addition rst) 
                                    (fot_compose new_addition s)
                            end
                  else if (is_var r)
                       then unif ((r,l) :: rst) s
                       else if ((is_const l) orelse (is_const r)) 
                            then raise NO_UNIFIER
                            else unif((rator l,rator r)::(rand l,rand r)::rst)s
   in
   unif [(t1,t2)] []
   end;

(* Change to eliminate redundancy *)
fun thm_eq th1 th2 = 
   let val (h1,c1) = dest_thm th1
       and (h2,c2) = dest_thm th2
   in (aconv c1 c2) andalso (set_eq h1 h2)
   end;


val global_rule_count = ref 0;
fun reset_rule_count() = global_rule_count := 0;

abstype rule = rule of (int*thm*bool)
with
  fun number (rule(n,_,_)) = n
  fun rule_thm (rule(_,th,_)) = th
  fun marked (rule(_,_,m)) = m
  fun dest_rule (rule r) = r
  fun rule_lhs (rule(_,th,_)) = fst (dest_eq (concl th))
  fun rule_rhs (rule(_,th,_)) = snd (dest_eq (concl th))

  fun mk_rule n th m = 
     let val t1 = (fst o dest_eq o concl) th
         and t2 = (snd o dest_eq o concl) th
     in
     if (not (KBlib.is_subset (all_vars t2) (all_vars t1)))
     then raise EXCESS_VARS_IN_RHS
     else if (is_var t1) 
          then raise LHS_CANNOT_BE_A_VARIABLE
          else rule(n,th,m)
     end;

  (* This is a bit dodgy. I should do the checks of mk_rule,
   *  but I only call mk_new_rule on oriented critical pairs, 
   *  which are guaranteed to pass the tests in mk_rule.
   ********************************************************************)
  fun mk_new_rule th = (inc global_rule_count; 
                        rule(!global_rule_count,th,false));

  fun mark (rule(n,th,mrked)) = 
     if mrked
     then raise RULE_ALREADY_MARKED
     else rule(n,th,true);

  fun pp_rule ppstrm (rule(n,th,c)) = 
     let val {add_string,add_break,begin_block, end_block, add_newline, ...} =
                PP.with_ppstream ppstrm
         val pp_term = Hol_pp.pp_term ppstrm
         val (l,r) = dest_eq (concl th)
     in
       begin_block PP.CONSISTENT 0;
       add_string (int_to_string n^". "^(if c then "*" else ""));
       begin_block PP.CONSISTENT 2;
       pp_term l;
       add_string " -->";
       add_break(2,0);
       pp_term r;
       end_block();
       add_newline();
       end_block() 
     end;

  fun rule_eq (rule(_,th1,_)) (rule(_,th2,_)) = thm_eq th1 th2;

  fun order_thm order th = 
     let val {lhs,rhs} = Dsyntax.dest_eq(concl th)
     in if order lhs rhs
        then mk_new_rule th
        else if order rhs lhs
             then mk_new_rule (SYM th)
             else raise EQN_NOT_ORIENTABLE
     end;
end; (* abstype rule *)

(* fun print_rules R = (map print_rule R;()); *)

val rule_sort = 
   KBlib.merge_sort 
    (fn x => fn y =>
       let val (lhs1,lhs2) = (rule_lhs##rule_lhs) (x,y)
       in not (term_size lhs1 > term_size lhs2)
       end);


fun get_unmarked R = 
   let val (m,unm) = KBlib.split marked R
   in
   if (length unm = 0) 
   then raise GET_UNMARKED
   else let val sorted_unmarked = rule_sort unm
        in (hd sorted_unmarked,(tl sorted_unmarked@m))
        end
   end;

fun kb_match_rule_with_term r t = kb_match (rule_lhs r) t;

fun find_kb_match t [] =  raise KB_NO_MATCH |
    find_kb_match t (r::rst) = ((kb_match_rule_with_term r t),r)
                             handle _ (* TERM_MATCH *) => find_kb_match t rst;

fun replace in_tm =
   let fun repl tm [] = in_tm |
           repl tm (dir::rst) =
               let val (t1,t2) = dest_comb tm
               in
               mk_comb (if (dir=0)
                        then (repl t1 rst, t2)
                        else (t1, repl t2 rst))
               end
               handle _ => raise KB_IMP_ERR "repl"
   in 
   repl
   end;


fun apply_subst_to_rule s r = 
    mk_rule (number r) (INST s (rule_thm r))  (marked r);


fun normalize_rule r = 
   let fun normal_subst trm = 
      let val trm_vars = all_vars trm
          and ty = type_of trm
          val new_var_names = map ((concat "x") o int_to_string)
                                  (KBlib.iota 1 (length trm_vars))
          val new_vars = map (fn n => mk_var(n,ty)) new_var_names
      in
      zip new_vars trm_vars
      end
   in
   apply_subst_to_rule (normal_subst (rule_lhs r)) r
   end;


(* Specialize a closed theorem to all new variables, and remember
  which old variables got replaced by which new new ones, i.e., an
  inverse substitution.
*)
fun gspec_w_mem th blist =
   let val c = concl th
   in if (is_forall c)
      then let val (x,body) = dest_forall c
               val v = genvar (type_of x)
           in gspec_w_mem (SPEC v th) ((x,v)::blist)
           end
      else (th,blist)
   end;

(*************************************************************************
 * Close the thm up, then specialize all variables to new ones, keeping
 * track of the inverse substitution. Thus the following should be
 * true (in SML-ese):
 *
 *     - let val (th1,s1) = RENAME_APART th
 *      in
 *      (concl (INST s1 th1)) = (concl (SPEC_ALL th)
 *      end;
 *************************************************************************)
fun RENAME_APART rle = 
   let val (new_th,s) = gspec_w_mem (GEN_ALL (rule_thm rle)) []
   in
   ((mk_rule (number rle) new_th (marked rle)),s)
   end;


(**************************************************************************
 * Computes overlaps. We have to check, right at the start, that subt and 
 * supert are not the same. If they are, then we don't attempt to fot_unify 
 * them. Overlaps are computed throughout supert.
 ****************************************************************************)
fun superpose teq subt supert occ =
   if (is_var supert)
   then []  (* [] stands for no superposition *)
   else if (is_const supert)
        then if (subt = supert)
             then [([],occ)]
             else []
        else let val top_overlap = 
                      if teq
                      then [] 
                      else ([((fot_unify subt supert),occ)] handle _ => [])
                 and (t1,t2) = dest_comb supert
             in
             top_overlap@(superpose false subt t1 (0::occ))@
                         (superpose false subt t2 (1::occ))
             end;


(* Does some pre-processing before calling superpose.  *)
fun overlap r1 r2 inv_sub = 
   let val lhs1 = rule_lhs r1
       and lhs2 = rule_lhs r2
       (* If rules equal before renaming, then superpose needs to ignore 
        * the top_overlap
        *****************************************************************)
       and same_rule = rule_eq r1 (apply_subst_to_rule inv_sub r2)
   in
   map (I##rev) (superpose same_rule lhs2 lhs1 [])
   end;


fun mk_template th occ =
   let val (left,right) = dest_eq(concl th)
       val v = genvar (type_of left)
   in
   (v, mk_eq (replace v left occ, right))
   end;


(* **********************************************************************
 * This is the heart of the Knuth-Bendix procedure. The call to 
 * overlap computes the overlaps between r1 and r2. From those,
 * we infer the critical pairs with SUBST.
 ************************************************************************)
fun crits r1 r2 = 
   let val (r2',inv_sub) = RENAME_APART r2
   in
   if (rule_eq r1 r2')  (* Possible if no vars in r2 *)
   then []
   else map (fn (theta,occ) =>
               let val inst_r1 = INST theta (rule_thm r1)
                   and inst_r2' = INST theta (rule_thm r2')
                   val (v,template) = mk_template inst_r1 occ
               in
               SUBST [(inst_r2',v)] template inst_r1
               end)
            (overlap r1 r2' inv_sub)
   end;


fun critical_pairs rule1 rule2 = (crits rule1 rule2)@(crits rule2 rule1);

fun all_cp r R = op_U thm_eq (map (critical_pairs r) R);

fun print_cp th = print_thm th;

val rule_union = op_union rule_eq
and eqn_U = op_U thm_eq;

local
val rc = SPEC_ALL REFL_CLAUSE
val ty = ==`:'a`==
in
fun reduce_eqn_fully R th = 
   KB_rewrite.PSUB_ALL 
      ((INST_TYPE[(type_of(lhs(concl th)),ty)] rc)::(map rule_thm R))
            th
end;

fun lhs_reducible reducer prospect = 
   can (kb_match_rule_with_term reducer) (rule_lhs prospect);

fun lhs_reduce reducer = KB_rewrite.RW_LHS_FULLY [rule_thm reducer];

fun rhs_reduce reducers reducee =
   let val (n,th,m) = dest_rule reducee
   in mk_rule n (KB_rewrite.RW_RHS_FULLY (map rule_thm reducers) th) m
   end;

fun show_list _ [] =  output(std_out, "none\n") |
    show_list pfun alist = ( output(std_out, "\n"); 
                             map pfun alist; 
                             output(std_out,"\n"));

fun unorderable th orderp = not ((orderp th) orelse (orderp (SYM th)));

fun reflexive th = thm_eq TRUTH th;
fun print_newline() = output(std_out,"\n");
fun print_string s = output(std_out,s);

(* *************************************************************************
 * The functions "assess" and "transfer" define a state machine. "assess"
 * passes control to "transfer", which moves orderable equations from E to 
 * R until E is empty. Then control returns to "assess", whereupon we find 
 * all critical pairs in R and move them into E. Then we go back to the 
 * initial state. This terminates when a prospective rule is not orderable, 
 * or when we succeed in completing the system. The program can loop forever.
 ****************************************************************************)


fun kb order E = 
   let val E' = map SPEC_ALL E
       val ty = type_of (lhs (concl (hd E')))
       val order_eqn = order_thm order
       exception HOP
       fun transfer [] [] R = R
         | transfer [] unorderableE R = 
             ( print_newline();
               print_string "Unorderable equations:";
               show_list print_thm (map (reduce_eqn_fully R) unorderableE);
               raise EQN_NOT_ORIENTABLE)
         | transfer (e::rst) unorderableE R =
            let val e' = reduce_eqn_fully R e
            in if (reflexive e')
               then transfer rst unorderableE R
               else let val rle = order_eqn e' handle EQN_NOT_ORIENTABLE
                                  => raise HOP
                        val (lr,nlr) = (KBlib.split o lhs_reducible) rle R
                    in
                    transfer(eqn_U [rst, unorderableE, map (lhs_reduce rle)
                                                           (map rule_thm lr)])
                            []
                            (rule_union(map(rhs_reduce(rule_union[rle] R))nlr)
                                           [rle])
                    end 
                    handle HOP => transfer rst (e::unorderableE) R
            end

       fun assess E R =
          let val R' = if (length E = 0)  then R  else transfer E [] R
          in if (all marked R')
             then map (rule_thm o normalize_rule) R'
             else let val (r,R'') = get_unmarked R'
                      val crit_pairs = 
                         all_cp r (gather (fn x => not (number x>number r)) R')
                  in assess crit_pairs (R''@[mark r])
                  end
          end
   in
   if (Lib.all (first_order_eqn ty o concl) E')
   then assess E' []
   else raise NOT_FIRST_ORDER_EQN
   end;

(*
fun kb order_pred E = 
   let val E' = map SPEC_ALL E
       val ty = type_of (lhs (concl (hd E')))
       val order = Lib.uncurry order_pred o dest_eq o concl
       fun unorderable th = not (order th orelse order (SYM th));
       fun transfer [] [] R = R
         | transfer [] unorderableE R = 
             ( print_newline();
               print_string "Unorderable equations:";
               show_list print_thm (map (reduce_eqn_fully R) unorderableE);
               raise EQN_NOT_ORIENTABLE)
         | transfer (e::rst) unorderableE R =
            let val e' = reduce_eqn_fully R e
            in if (reflexive e')
               then transfer rst unorderableE R
               else if (unorderable e') 
                    then transfer rst (e :: unorderableE) R
                    else let val rle = mk_new_rule 
                               (if (order e') then e' 
                                else if (order (SYM e')) then SYM e'
                                     else raise EQN_NOT_ORIENTABLE)
                             val (lr,nlr) = (KBlib.split o lhs_reducible) rle R
                         in
                         transfer(eqn_U [rst, unorderableE, 
                                         map(lhs_reduce rle)(map rule_thm lr)])
                                 []
                                 (rule_union (map (rhs_reduce 
                                                     (rule_union [rle] R)) nlr)
                                             [rle])
                         end
            end

       fun assess E R =
          let val R' = if (length E = 0)  then R  else transfer E [] R
          in if (all marked R')
             then map (rule_thm o normalize_rule) R'
             else let val (r,R'') = get_unmarked R'
                      val crit_pairs = 
                         all_cp r (gather (fn x => not (number x>number r)) R')
                  in assess crit_pairs (R''@[mark r])
                  end
          end
   in
   if (Lib.all (first_order_eqn ty o concl) E')
   then assess E' []
   else raise NOT_FIRST_ORDER_EQN
   end;
*)


(* Tracing version  *)

fun show_transfer_args E =
   (print_string "........................................... Transferring equations: ";
    show_list (fn x => (print_thm x; print_newline())) E);

fun print_rule rle = PP.with_pp (PP.defaultConsumer()) (Lib.C pp_rule rle);
fun pp_rules ppstrm R = 
  (PP.begin_block ppstrm PP.CONSISTENT 0;
   PP.pr_list (pp_rule ppstrm) (fn () => ()) 
              (fn () => PP.add_newline ppstrm) R; 
   PP.end_block ppstrm);
fun print_rules R = PP.with_pp (PP.defaultConsumer()) (Lib.C pp_rules R);
fun pp_thms ppstrm R = 
  (PP.begin_block ppstrm PP.CONSISTENT 0;
   PP.pr_list (pp_thm ppstrm) (fn () => ()) 
              (fn () => PP.add_newline ppstrm) R; 
   PP.end_block ppstrm);
fun print_thms R = PP.with_pp (PP.defaultConsumer()) (Lib.C pp_thms R);

fun transfer_trace [] [] R orderp = R
  | transfer_trace [] unorderableE R _ = 
     ( print_newline();
       print_string "Unorderable equations:";
       show_list print_thm (map (reduce_eqn_fully R) unorderableE);
       raise EQN_NOT_ORIENTABLE)
  | transfer_trace (e::rst) unorderableE R orderp =
       ( print_string "Selected equation: ";
         print_thm e;
         let val e' = reduce_eqn_fully R e
         in
         ( print_newline();
           print_string "Reduced equation: ";
           print_thm e';
           if (reflexive e')
           then ( print_newline();
                  print_string "Reduced to identity.";
                  print_newline();
                  transfer_trace rst unorderableE R orderp)
           else if (unorderable e' orderp) 
                then ( print_newline();
                       print_string "shifting equation:";
                       print_newline();
                       print_thm e; print_newline();
                       print_string "to unorderableE because reduced form:";
                       print_newline();
                       print_thm e';
                       print_string " is unorderable.";
                       print_newline();
                       transfer_trace rst (e :: unorderableE) R orderp)
                else let val rle = mk_new_rule 
                                    (if (orderp e') 
                                     then e' 
                                     else if (orderp (SYM e'))
                                          then SYM e'
                                          else raise EQN_NOT_ORIENTABLE)
                     in
                     ( print_newline();
                       print_string "New rule: ";
                       PP.with_pp (PP.defaultConsumer())
                                  (Lib.C pp_rule rle);
                       let val (lr,nlr) = (KBlib.split o lhs_reducible) rle R
                       in
                       transfer_trace 
                         (eqn_U [ rst, unorderableE, map (lhs_reduce rle) 
                                                         (map rule_thm lr)])
                         []
                         (rule_union (map (rhs_reduce (rule_union[rle] R))nlr) 
                                     [rle])
                         orderp
                       end)
                     end
         )
         end
       );




fun assess_trace E R orderp =
   ( show_transfer_args E;
     let val R' = if (length E = 0) 
                  then R 
                  else transfer_trace E [] R orderp
     in
     ( print_string "...................................... \
                  \ transferred all equations";
       print_newline();
       print_string "rule set is: ";
       print_rules R';
       if (all marked R')
       then let val finalR = map (rule_thm o normalize_rule) R'
            in
            ( print_string "Completion successful. Final rule set is: ";
              show_list print_thm finalR; 
              print_newline();print_newline();print_newline();
              finalR)
            end
       else let val (r,R'') = get_unmarked R'
            in
            ( print_newline(); print_newline();
              print_string "Computing critical pairs between "; 
              print_newline();
              print_rule r;
              print_string "and";
              print_rules(gather (fn x => not ((number x) > (number r))) R');
              let val crit_pairs = 
                   all_cp r (gather (fn x => not ((number x) > (number r))) R')
              in
              ( print_string "Critical pairs: "; print_newline();
                print_thms crit_pairs; 
                print_newline();
                assess_trace crit_pairs (R''@[(mark r)]) orderp)
              end)
            end
     )
     end
   );

fun kb_trace order_pred E = 
   let val E' = map SPEC_ALL E
       val ty = type_of (lhs (concl (hd E')))
   in
   if (all ((first_order_eqn ty) o concl) E')
   then assess_trace E' [] (fn th => (uncurry order_pred) (dest_eq (concl th)))
   else raise NOT_FIRST_ORDER_EQN
   end;

end; (*KB*)
