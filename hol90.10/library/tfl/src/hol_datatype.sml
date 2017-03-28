(*---------------------------------------------------------------------------
 * Agglomerates a bunch of tools stemming from a datatype definition. 
 * Yet to be done: define a notion of size for a datatype.
 *---------------------------------------------------------------------------*)


structure Hol_datatype : Hol_datatype_sig =
struct

open WFTheoryLoaded;

type term = CoreHol.Term.term
type fixity = CoreHol.Term.fixity
type thm = CoreHol.Thm.thm
type tactic = Abbrev.tactic;

structure Rules = Rules;
structure RW = RW;
structure HOL = HOL;   (* Need theories of pairs, nums, and lists. *)

open Lib Exception CoreHol;
open Type Term Dsyntax Thm Theory Drule Tactical Tactic Conv Induct_then
     Prim_rec Rec_type_support;

infix ##;
infix THEN;

fun HOL_DATATYPE_ERR{func,mesg} = 
    HOL_ERR{origin_structure = "Hol_datatype",
            origin_function = func,
            message = mesg};

fun strip_type ty =
   let val {Tyop = "fun", Args = [ty1,ty2]} = dest_type ty
       val (D,r) = strip_type ty2
   in (ty1::D, r)
   end
   handle _ => ([],ty);

infixr 3 -->;
fun (ty1 --> ty2) = mk_type{Tyop="fun",Args =[ty1,ty2]};

fun num_variant vlist v =
  let val counter = ref 0
      val {Name,Ty} = dest_var v
      val slist = ref (map (#Name o dest_var) vlist)
      fun pass str = 
         if (mem str (!slist)) 
         then ( counter := !counter + 1;
                pass (Lib.concat Name (Lib.int_to_string(!counter))))
         else (slist := str :: !slist; str)
  in 
  mk_var{Name=pass Name,  Ty=Ty}
  end;

(*---------------------------------------------------------------------------
 * Defining and proving case congruence:
 *
 *    |- (M = M') /\
 *       (!x1,...,xk. (M' = C1 x1..xk) ==> (f1 x1..xk = f1' x1..xk)) 
 *        /\ ... /\
 *       (!x1,...,xj. (M' = Cn x1..xj) ==> (fn x1..xj = fn' x1..xj)) 
 *       ==>
 *      (ty_case f1..fn M = ty_case f1'..fn' m')
 *
 *---------------------------------------------------------------------------*)
fun case_cong_term case_def =
 let val clauses = (strip_conj o concl) case_def
     val clause1 = hd clauses
     val left = (#lhs o dest_eq o #2 o strip_forall) clause1
     val ty = type_of (rand left)
     val allvars = all_varsl clauses
     val M = variant allvars (mk_var{Name = "M", Ty = ty})
     val M' = variant (M::allvars) (mk_var{Name = "M", Ty = ty})
     fun mk_clause clause =
       let val {lhs,rhs} = (dest_eq o #2 o strip_forall) clause
           val func = (#1 o strip_comb) rhs
           val (constr,xbar) = strip_comb(rand lhs)
           val {Name,Ty} = dest_var func
           val func' = variant allvars (mk_var{Name=Name^"'", Ty=Ty})
       in (func',
           list_mk_forall
           (xbar, mk_imp{ant = mk_eq{lhs=M',rhs=list_mk_comb(constr,xbar)},
                         conseq = mk_eq{lhs=list_mk_comb(func,xbar),
                                        rhs=list_mk_comb(func',xbar)}}))
       end
     val (funcs',clauses') = unzip (map mk_clause clauses)
     val lhsM = mk_comb{Rator=rator left, Rand=M}
     val c = #1(strip_comb left)
 in
 mk_imp{ant = list_mk_conj(mk_eq{lhs=M, rhs=M'}::clauses'),
        conseq = mk_eq{lhs=lhsM, rhs=list_mk_comb(c,(funcs'@[M']))}}
 end;
  
(*---------------------------------------------------------------------------
 *
 *        A, v = M[x1,...,xn] |- N
 *  ------------------------------------------
 *     A, ?x1...xn. v = M[x1,...,xn] |- N
 *
 *---------------------------------------------------------------------------*)
fun EQ_EXISTS_LINTRO (thm,(vlist,theta)) = 
  let val [veq] = filter (can dest_eq) (hyp thm)
      fun CHOOSER v (tm,thm) = 
        let val w = (case (subst_assoc (fn w => v=w) theta)
                      of SOME w => w
                       | NONE => v)
            val ex_tm = mk_exists{Bvar=w, Body=tm}
        in (ex_tm, CHOOSE(w, ASSUME ex_tm) thm)
        end
  in snd(itlist CHOOSER vlist (veq,thm))
  end;

fun case_cong_thm nchotomy case_def =
 let val gl = case_cong_term case_def
     val {ant,conseq} = dest_imp gl
     val imps = CONJUNCTS (ASSUME ant)
     val M_eq_M' = hd imps
     val {lhs=M, rhs=M'} = dest_eq (concl M_eq_M')
     fun get_asm tm = (#ant o dest_imp o #2 o strip_forall) tm handle _ => tm
     val case_assms = map (ASSUME o get_asm o concl) imps
     val {lhs=lconseq, rhs=rconseq} = dest_eq conseq
     val lconseq_thm = SUBST_CONV[{var=M, thm = M_eq_M'}] lconseq lconseq
     val lconseqM' = rhs(concl lconseq_thm)
     val nchotomy' = ISPEC M' nchotomy
     val disjrl = map ((I##rhs) o strip_exists)	(strip_disj (concl nchotomy'))
     fun zot icase_thm (iimp,(vlist,disjrhs)) =
       let val lth = Rewrite.REWRITE_CONV[icase_thm, case_def] lconseqM'
           val rth = Rewrite.REWRITE_CONV[icase_thm, case_def] rconseq
           val theta = Match.match_term disjrhs
                     ((rhs o #ant o dest_imp o #2 o strip_forall o concl) iimp)
           val th = MATCH_MP iimp icase_thm
           val th1 = TRANS lth th
       in (TRANS th1 (SYM rth), (vlist, #1 theta))
       end
     val thm_substs = map2 zot (tl case_assms) (zip (tl imps) disjrl)
     val aag = map (TRANS lconseq_thm o EQ_EXISTS_LINTRO) thm_substs
 in
 GEN_ALL(DISCH_ALL(Rules.DISJ_CASESL nchotomy' aag))
 end;


fun define_case ax =
   let val exu = snd(strip_forall(concl ax))
       val {Rator,Rand} = dest_comb exu
       val {Name = "?!",...} = dest_const Rator
       val {Bvar,Body} = dest_abs Rand
       val ty = type_of Bvar
       val {Tyop="fun",Args=[dty,rty]} = dest_type ty
       val {Tyop,Args} = dest_type dty
       val clist = map (rand o lhs o #2 o strip_forall) (strip_conj Body)
       fun mk_cfun ctm (nv,away) =
          let val (c,args) = strip_comb ctm
              val fty = itlist (curry (op -->)) (map type_of args) rty
              val vname = if (length args = 0) then "v" else "f"
              val v = num_variant away (mk_var{Name = vname, Ty = fty})
          in (v::nv, v::away)
          end
      val arg_list = rev(fst(rev_itlist mk_cfun clist ([],free_varsl clist)))
      val v = mk_var{Name = Tyop^"_case",
                     Ty = itlist (curry (op -->)) (map type_of arg_list) ty}
      val preamble = list_mk_comb(v,arg_list)
      fun clause (a,c) = mk_eq{lhs = mk_comb{Rator=preamble,Rand=c},
                               rhs = list_mk_comb(a, rev(free_vars c))}
   in
    new_recursive_definition
        {name=Tyop^"_case_def", fixity=Prefix, rec_axiom=ax,
         def = list_mk_conj (map clause (zip arg_list clist))}
   end;

(*---------------------------------------------------------------------------
 * Returns the datatype name and the constructors. A copy of the beginning
 * of "define_case".
 *---------------------------------------------------------------------------*)
fun ax_info ax = 
  let val exu = snd(strip_forall(concl ax))
      val {Rator,Rand} = dest_comb exu
      val {Name = "?!",...} = dest_const Rator
      val {Bvar,Body} = dest_abs Rand
      val ty = type_of Bvar
      val {Tyop="fun",Args=[dty,rty]} = dest_type ty
      val {Tyop,Args} = dest_type dty
      val clist = map (rand o lhs o #2 o strip_forall) (strip_conj Body)
  in
   (Tyop,  map (fst o strip_comb) clist)
  end;


fun hol_datatype_tools datatype_ax case_def =
  let val induct_thm = prove_induction_thm datatype_ax
      val one_one = [prove_constructors_one_one datatype_ax] handle _ => []
      val D = CONJUNCTS(prove_constructors_distinct datatype_ax)
              handle _ => []
      val distincts = D@map GSYM D
      val (ty_name,constructors) = ax_info  datatype_ax
      val case_const = (#1 o strip_comb o lhs o #2 
                        o strip_forall o hd o strip_conj o concl) case_def
      val simpls = RW.add_rws RW.empty_simpls(case_def::(distincts@one_one))
      val nchotomy = prove_cases_thm induct_thm
      fun definer {def,fixity, name} = 
                 new_recursive_definition{name=name, def=def,fixity=fixity,
                                          rec_axiom=datatype_ax}
  in
   (ty_name,
   {constructors = constructors,
    case_const = case_const,
    case_def   = case_def,
    case_cong  = case_cong_thm nchotomy case_def,
    induction  = induct_thm,
    induct_tac = INDUCT_THEN induct_thm ASSUME_TAC,
    nchotomy   = nchotomy, 
    one_one    = one_one,
    distinct   = distincts,
    simpls     = simpls,
    definer    = definer,
    axiom      = datatype_ax})
  end;


(*---------------------------------------------------------------------------
 * The following 2 should be in "pair". Then we wouldn't need a 
 * "basic_datatypes" theory, but can merely load the "HOL" theory and
 * initialize "the_info". (We would also need to define case_constants
 * for nums, lists, and pairs somewhere (maybe in the original theories).)
 *---------------------------------------------------------------------------*)

val pair_ax = Lib.try (theorem "pair") "pair_Axiom";
val num_ax = Lib.try (theorem "prim_rec") "num_Axiom";
val list_ax = Lib.try (theorem "list") "list_Axiom";

(* val pair_case_def = Lib.try (definition"pair") "UNCURRY_DEF"; *)
(* val pair_case_def = Lib.try (definition"pair") "PAIR_CASE_DEF"; *)
val pair_case_def = Lib.try (definition"WF") "PAIR_CASE_DEF";
val num_case_def = Lib.try (definition "arithmetic") "num_case_def";
val list_case_def = Lib.try (definition "list") "list_case_def";

val prod_info = hol_datatype_tools pair_ax pair_case_def;
val num_info =  hol_datatype_tools num_ax num_case_def
val list_info = hol_datatype_tools list_ax list_case_def;

(*---------------------------------------------------------------------------
 * The reference cell, used to provide a central site for datatype facts.
 * It will not interact well with a HOL having reloadable theories! It is
 * somewhat redundant in its information, as well.
 *
 * If one wanted to do a "load_theory" on a theory that had datatypes
 * defined in it, or in its ancestry, then the information about those
 * datatypes needs to be added to "the_info" by the user. Hopefully, a
 * future version of HOL will remedy this. Another implementation note:
 * this should probably be a hash table.
 *---------------------------------------------------------------------------*)
val the_info = 
ref ([]: (string * {axiom:thm, 
                   case_const:term, case_cong:thm,
                   case_def:thm, constructors:term list,
                   definer:{def:term, fixity:fixity, name:string} -> thm,
                   distinct:thm list, induct_tac:tactic, induction:thm,
                   nchotomy:thm, one_one:thm list, simpls:RW.simpls}) list);

fun add_info (info as (ty_name, {simpls, ...})) =
  ( RW.Implicit.add_simpls simpls;
    the_info := (!the_info)@[info]);

fun current() = !the_info;

val _ = (add_info prod_info; 
         add_info num_info; 
         add_info list_info);

(*---------------------------------------------------------------------------
 * Examples of use:
 * 
 *   local open Hol_datatype
 *   in
 *   val term_ty_def = 
 *       hol_datatype `term = Var of 'a
 *                          | Const of 'a
 *                          | App of term => term`
 *
 *   val subst_ty_def =
 *       hol_datatype  `subst = Fail | Subst of ('a#'a term) list`
 *   end;
 *
 *
 * Returns a great deal of information about the datatype: theorems, 
 * definition of case-constant, induction tactics, etc.
 *
 * Side-effects: it adds this information to a list maintained with a 
 * reference cell.
 *
 *---------------------------------------------------------------------------*)
fun hol_datatype q = 
let val {ty_name, clauses} = Parse.type_spec_parser q
    fun prefix{constructor,args} = {constructor = constructor,
                                    args = args, fixity = Prefix}
    val clauses' = map prefix clauses
    open Define_type
    fun def() = 
       let val ax = dtype{clauses=clauses',save_name=ty_name,ty_name=ty_name}
       in hol_datatype_tools ax (define_case ax)
       end
    val entry = Theory.perform_atomic_theory_op def
    val _ = add_info entry
in 
  entry  
end handle e => Raise e;


(*---------------------------------------------------------------------------
 * Do case analysis on leading universally quantified variable. The var must
 * be of a known datatype.
 *---------------------------------------------------------------------------*)
fun CASES_TAC (g as (_,w)) =
 let val {Bvar, ...} = dest_forall w
     val {Tyop, ...} = Type.dest_type(Term.type_of Bvar)
     val case_thm = #nchotomy(Lib.assoc Tyop (!the_info))
 in 
   (GEN_TAC THEN STRUCT_CASES_TAC (ISPEC Bvar case_thm)) g
 end;

(*---------------------------------------------------------------------------
 val bool_cases = 
   new_definition
      ("bool_case",Term `bool_case (x:'a) y v = COND v x y`);

  local val def = ISPECL[Term`x:bool`,Term`y:bool`] bool_cases
  in 
  val bool_case_thm = save_thm("bool_case_thm",
  REWRITE_RULE[COND_CLAUSES]
      (CONJ (GEN(Term`x:bool`)(GEN(Term`y:bool`)(ISPECL[Term`T`] def)))
            (GEN(Term`x:bool`)(GEN(Term`y:bool`)(ISPECL[Term`F`] def)))))
  end;
----------------------------------------------------------------------------*)

val _ = delete_cache();

end;
