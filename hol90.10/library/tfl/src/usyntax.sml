structure USyntax : USyntax_sig =
struct

structure Utils = Utils;
open Utils;
open Mask;
infix 3 |->;

type Type = CoreHol.Type.hol_type
type Term = CoreHol.Term.term
type Preterm = CoreHol.Term.term

open CoreHol;
type hol_type = Type.hol_type;
type term = Term.term

fun USYNTAX_ERR{func,mesg} = Utils.ERR{module = "Usyntax",func=func,mesg=mesg};

(*---------------------------------------------------------------------------
 * This can be more pretty in SML97 with a datatype replication.
 *---------------------------------------------------------------------------*)
structure SmallTerm: 
sig
  datatype lambda = VAR   of {Name : string, Ty : hol_type}
                  | CONST of {Name : string, Ty : hol_type}
                  | COMB  of {Rator: term, Rand : term}
                  | LAMB  of {Bvar : term, Body : term}
end = struct 
        open CoreHol.Term 
      end; 

open SmallTerm;

local fun mk_bind (A |-> B) = {redex = A, residue = B}
in
  fun mk_hol_subst L = map mk_bind L
end;

local fun mk_bind {redex,residue} = (redex |-> residue)
in
  fun mk_tfp_subst L = map mk_bind L
end;


val type_subst   = Type.type_subst o mk_hol_subst
val type_vars    = Type.type_vars
val type_varsl   = Type.type_varsl
val mk_type      = Type.mk_type
val dest_type    = Type.dest_type
val mk_vartype   = Type.mk_vartype
val dest_vartype = Type.dest_vartype
val is_vartype   = Type.is_vartype
val type_lt      = Type.type_lt

val alpha = Type.mk_vartype"'a";
val bool  = Type.mk_type{Tyop = "bool", Args = []};

infix 3 -->;
fun (ty1 --> ty2) = Type.mk_type{Tyop="fun",Args =[ty1,ty2]};

(* hol_type -> hol_type list * hol_type *)
fun strip_type ty =
   let val {Tyop = "fun", Args = [ty1,ty2]} = Type.dest_type ty
       val (D,r) = strip_type ty2
   in (ty1::D, r)
   end
   handle _ => ([],ty);

(* hol_type -> hol_type list *)
fun strip_prod_type ty =
   let val {Tyop = "prod", Args = [ty1,ty2]} = Type.dest_type ty
   in strip_prod_type ty1 @ strip_prod_type ty2
   end handle _ => [ty];

fun match_type ty1 ty2 = mk_tfp_subst(Match.match_type ty1 ty2);


(* Terms *)
val free_vars  = Term.free_vars

(* Free variables, in order of occurrence, from left to right in the 
 * syntax tree. I should actually write my own here, to have full control.
 *)
val free_vars_lr = rev o free_vars;

val free_varsl = Term.free_varsl
val free_in    = Term.free_in   (* ? *)
val all_vars   = Term.all_vars  (* ? *)
val all_varsl  = Term.all_varsl  (* ? *)
val term_lt    = Term.term_lt
val genvar     = Term.genvar
val genvars    = Term.genvars
val variant    = Term.variant
val type_of    = Term.type_of
val type_vars_in_term = Term.type_vars_in_term
val dest_term = Term.dest_term;
  
  (* Prelogic *)
val aconv     = Term.aconv
val subst     = Term.subst o mk_hol_subst
val inst      = Term.inst o mk_hol_subst
val beta_conv = Term.beta_conv


  (* Construction routines *)
val mk_var        = Rsyntax.mk_var
val mk_const      = Rsyntax.mk_const
val mk_primed_var = Rsyntax.mk_primed_var
val mk_comb       = Rsyntax.mk_comb
val mk_abs        = Rsyntax.mk_abs

val mk_prop   = Utils.I    (* Needed for Isabelle  - drops into meta-logic *)
val mk_eq     = Rsyntax.mk_eq
val mk_imp    = Rsyntax.mk_imp
val mk_select = Rsyntax.mk_select
val mk_forall = Rsyntax.mk_forall
val mk_exists = Rsyntax.mk_exists
val mk_neg    = Dsyntax.mk_neg
val mk_conj   = Rsyntax.mk_conj
val mk_disj   = Rsyntax.mk_disj
val mk_cond   = Rsyntax.mk_cond
val mk_pair   = Rsyntax.mk_pair
val mk_let    = Rsyntax.mk_let
val mk_cons   = Rsyntax.mk_cons
val mk_list   = Rsyntax.mk_list
val mk_pabs   = Rsyntax.mk_pabs

  (* Destruction routines *)
val dest_var    = Rsyntax.dest_var
val dest_const  = Rsyntax.dest_const
val dest_comb   = Rsyntax.dest_comb
val dest_abs    = Rsyntax.dest_abs
val dest_eq     = Rsyntax.dest_eq
val dest_imp    = Rsyntax.dest_imp
val dest_select = Rsyntax.dest_select
val dest_forall = Rsyntax.dest_forall
val dest_exists = Rsyntax.dest_exists
val dest_neg    = Dsyntax.dest_neg
val dest_conj   = Rsyntax.dest_conj
val dest_disj   = Rsyntax.dest_disj
val dest_cond   = Rsyntax.dest_cond
val dest_pair   = Rsyntax.dest_pair
val dest_let    = Rsyntax.dest_let
val dest_cons   = Rsyntax.dest_cons
val dest_list   = Rsyntax.dest_list
val dest_pabs   = Rsyntax.dest_pabs

val lhs   = Dsyntax.lhs
val rhs   = Dsyntax.rhs
val rator = Term.rator
val rand  = Term.rand
val bvar  = Term.bvar
val body  = Term.body


  (* Query routines *)
val is_var     = Term.is_var
val is_const   = Term.is_const
val is_comb    = Term.is_comb
val is_abs     = Term.is_abs
val const_decl = #const o Term.const_decl
  
val is_eq     = Dsyntax.is_eq
val is_imp    = Dsyntax.is_imp
val is_select = Dsyntax.is_select
val is_forall = Dsyntax.is_forall
val is_exists = Dsyntax.is_exists
val is_neg    = Dsyntax.is_neg
val is_conj   = Dsyntax.is_conj
val is_disj   = Dsyntax.is_disj
val is_cond   = Dsyntax.is_cond
val is_pair   = Dsyntax.is_pair
val is_let    = Dsyntax.is_let
val is_cons   = Dsyntax.is_cons
val is_list   = Dsyntax.is_list
val is_pabs   = Dsyntax.is_pabs

  (* Construction of a Term from a list of Terms *)
val list_mk_comb   = Term.list_mk_comb
val list_mk_abs    = Dsyntax.list_mk_abs
val list_mk_imp    = Dsyntax.list_mk_imp
val list_mk_forall = Dsyntax.list_mk_forall
val list_mk_exists = Dsyntax.list_mk_exists
val list_mk_conj   = Dsyntax.list_mk_conj
val list_mk_disj   = Dsyntax.list_mk_disj
val list_mk_pair   = Dsyntax.list_mk_pair

  (* Destructing a Term to a list of Terms *)
val strip_comb     = Dsyntax.strip_comb
val strip_abs      = Dsyntax.strip_abs
val strip_imp      = Dsyntax.strip_imp
val strip_forall   = Dsyntax.strip_forall
val strip_exists   = Dsyntax.strip_exists
val strip_conj     = Dsyntax.strip_conj
val strip_disj     = Dsyntax.strip_disj
val strip_pair     = Dsyntax.strip_pair


(* Miscellaneous *)
fun gen_all tm = 
  itlist (fn v => fn M => Dsyntax.mk_forall{Bvar=v,Body=M}) 
        (free_vars_lr tm) tm;

val find_term  = Dsyntax.find_term
val find_terms = Dsyntax.find_terms

fun mk_vstruct ty V =
  let fun follow_prod_type ty vs =
      let val {Tyop = "prod", Args = [ty1,ty2]} = Type.dest_type ty
          val (ltm,vs1) = follow_prod_type ty1 vs
          val (rtm,vs2) = follow_prod_type ty2 vs1
      in (Dsyntax.mk_pair{fst=ltm, snd=rtm}, vs2)
      end handle _ => (hd vs, tl vs)
 in Lib.fst(follow_prod_type ty V)
 end;

(* Prettyprinting *)
val Term_to_string = Hol_pp.term_to_string


  (* Typing *)
val mk_preterm = Lib.I;

val drop_Trueprop = Lib.I;

(*---------------------------------------------------------------------------
 * Different implementations may represent relations as binary predicates
 * or sets of pairs.
 *---------------------------------------------------------------------------*)
local val bool = Type.mk_type{Tyop="bool",Args=[]}
in
fun dest_relation tm =
   if (type_of tm = bool)
   then let val {Rator,Rand = r} = Term.dest_comb tm
            val {Rator,Rand = d} = Term.dest_comb Rator
        in (Rator,d,r)
        end
        handle _ => raise USYNTAX_ERR{func = "dest_relation",
                                      mesg = "unexpected term structure"}
   else raise USYNTAX_ERR{func="dest_relation",mesg="not a boolean term"}
end;

(*---------------------------------------------------------------------------
 * Different implementations may give their own name to the "wellfoundedness"
 * constant. Probably this should be replaced by matching.
 *---------------------------------------------------------------------------*)
fun is_WFR tm = (#Name(Term.dest_const(rator tm)) = "WF") handle _ => false;

fun ARB ty = Rsyntax.mk_const{Name="ARB", Ty=ty};

end; (* USyntax *)
