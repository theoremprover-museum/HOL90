(*************************************************************)
(*                                                           *)
(* abs_theory.sml                                            *)
(*                                                           *)
(* abstract theory package for hol90                         *)
(*                                                           *)
(* David Shepherd    (des@inmos.co.uk)                       *)
(* INMOS Ltd                                                 *)
(* Copyright (C) 1993                                        *)
(*                                                           *)
(* Much of this is inspired (and copied) from Phil Windley's *)
(* hol88 abstract theory package. In this version we specify *)
(* an abstract entity by its characteristic equation, rather *)
(* than the separate representation and obligation sections  *)
(* of the hol88 version. The abstract constants are taken to *)
(* be all the free variables in the predicate.               *)
(*************************************************************)

signature Abs_theory_sig =
sig

  type hol_type 
  type term 
  type thm
  type proofs
  type goal
  type tactic
  type conv
  type thm_tactic

   val theory_obligs:((string*{oblig:thm,rep_defs:thm list})list)ref
   val new_abstract_entity:{Name:string,Predicate:term}->thm
   val abs_convert_term:term->term
   val ag:term frag list -> proofs
   val abs_set_goal:goal -> proofs
   val abs_prove:term * tactic -> thm
   val abs_store_thm:string * term * tactic -> thm
   val EXPAND_THOBS_CONV:conv
   val EXPAND_THOBS_TAC:tactic
   val EXPAND_THOBS_RULE:thm->thm
   val STRIP_THOBS_THEN:thm_tactic->thm_tactic->tactic
   val STRIP_THOBS_TAC:tactic
   val get_obligs:string -> thm list
   val get_abs_reps:string -> thm list
   val add_obligs:string -> unit
   val abs_add_theory_to_sml:string -> unit
   val instantiate_abs_thm:{abs_term:term,rep_term:term,validation:thm}list
                           -> thm -> thm
   val instantiate_abstract_definition:{abs_term:term,rep_term:term}list
                                       -> thm -> thm -> thm
end;

signature Imp_rewrite_sig =
sig
   type hol_type
   type term
   type thm
   type 'a net
   type conv
   type tactic

val mk_imp_conv_net : thm list -> (term list -> conv) net
val IMP_REWRITES_CONV : term list -> (term list -> conv) net -> conv
val basic_imp_rewrites : (term list -> conv) net ref
val GEN_IMP_REWRITE_CONV : (conv -> conv) -> (term list -> conv) net ref
                            -> thm list -> term list -> conv
val PURE_IMP_REWRITE_CONV : thm list -> term list -> conv
val IMP_REWRITE_CONV : thm list -> term list -> conv
val PURE_ONCE_IMP_REWRITE_CONV : thm list -> term list -> conv
val ONCE_IMP_REWRITE_CONV : thm list -> term list -> conv
val GEN_IMP_REWRITE_RULE : (conv -> conv) -> (term list -> conv) net ref
                            ->  thm list -> thm -> thm
val GEN_IMP_REWRITE_TAC : (conv -> conv) -> (term list -> conv) net ref
                            -> thm list -> tactic
val PURE_IMP_REWRITE_RULE : thm list -> thm -> thm
val IMP_REWRITE_RULE : thm list -> thm -> thm
val PURE_ONCE_IMP_REWRITE_RULE : thm list -> thm -> thm
val ONCE_IMP_REWRITE_RULE : thm list -> thm -> thm
val PURE_ASM_IMP_REWRITE_RULE : thm list -> thm -> thm
val ASM_IMP_REWRITE_RULE : thm list -> thm -> thm
val PURE_ONCE_ASM_IMP_REWRITE_RULE : thm list -> thm -> thm
val ONCE_ASM_IMP_REWRITE_RULE : thm list -> thm -> thm
val PURE_IMP_REWRITE_TAC : thm list -> tactic
val IMP_REWRITE_TAC : thm list -> tactic
val PURE_ONCE_IMP_REWRITE_TAC : thm list -> tactic
val ONCE_IMP_REWRITE_TAC : thm list -> tactic
val PURE_ASM_IMP_REWRITE_TAC : thm list -> tactic
val ASM_IMP_REWRITE_TAC : thm list -> tactic
val PURE_ONCE_ASM_IMP_REWRITE_TAC : thm list -> tactic
val ONCE_ASM_IMP_REWRITE_TAC : thm list -> tactic
val FILTER_PURE_ASM_IMP_REWRITE_RULE :(term -> bool) -> thm list -> thm -> thm
val FILTER_ASM_IMP_REWRITE_RULE :(term -> bool) -> thm list -> thm -> thm
val FILTER_PURE_ONCE_ASM_IMP_REWRITE_RULE :(term -> bool) -> thm list 
                                            -> thm -> thm
val FILTER_ONCE_ASM_IMP_REWRITE_RULE :(term -> bool)
                                       -> thm list -> thm -> thm
val FILTER_PURE_ASM_IMP_REWRITE_TAC :(term -> bool) -> thm list -> tactic
val FILTER_ASM_IMP_REWRITE_TAC :(term -> bool) -> thm list -> tactic
val FILTER_PURE_ONCE_ASM_IMP_REWRITE_TAC :(term -> bool) 
                                            -> thm list -> tactic
val FILTER_ONCE_ASM_IMP_REWRITE_TAC :(term -> bool) -> thm list -> tactic

end;


structure Abs_theory :Abs_theory_sig =
struct

type hol_type = CoreHol.Type.hol_type
type term = CoreHol.Term.term
type thm = CoreHol.Thm.thm
type 'a net = 'a CoreHol.Net.net
type conv = Abbrev.conv;
type tactic = Abbrev.tactic;
type thm_tactic = Abbrev.thm_tactic;
type goal = Abbrev.goal;

open Rsyntax;
open Exception;
open Lib;
open CoreHol.Term;
open CoreHol.Type;
open CoreHol.Thm;
open CoreHol.Theory;
open CoreHol.Dsyntax;
open CoreHol.Net;
open CoreHol.Const_def;
open Drule;
open Define_type;
open Tactic;
   infix THEN;
open Conv;
   infix THENC;
open Parse;
open Goalstack;
open Rewrite;
open Tactical;
open Thm_cont;
open Add_to_sml;


fun ABS_THRY_ERR{function,message} =
         HOL_ERR{origin_structure="abstract_theory",
	         origin_function=function,
		 message=message};
    
    
val theory_obligs = ref([]:(string*{oblig:thm,rep_defs:thm list})list);
    
fun push x rf = rf := x::(!rf);
fun pop rf = 
    let val h = hd(!rf)
    in
	rf := tl(!rf);
	h
    end;
    
fun new_abstract_entity {Name=name,Predicate=pred} =
    let val ops = free_vars pred
	val rep_type = dtype
                {save_name = name,
                 ty_name = name,
                 clauses = [{constructor = name, 
                             args = map (Parse_support.Hty o type_of) ops,
                             fixity = Prefix}]}


	val rep_tm = list_mk_comb((fst o strip_comb o rand o lhs o snd 
                                   o strip_forall o body o rand o body 
                                   o rand o concl)rep_type,ops)
	fun mk_rep_def v = 
	    let val name = (#Name o dest_var)v
		val f = mk_var{Name=name,
			       Ty=mk_type{Tyop="fun",
                                          Args=[type_of rep_tm,type_of v]}}
		val def = mk_eq{lhs=mk_comb{Rator=f,Rand=rep_tm},
				rhs=v}
	    in
		new_recursive_definition{def=def,fixity=Prefix,
					 name=name^"_abs_rep",
                                         rec_axiom=rep_type}
	    end
	val rep_defs = map (fn v => mk_rep_def v) ops
	val rep_var = mk_var{Name=String.str
                                 (hd (Portable.String.explode name)),
                             Ty=type_of rep_tm}
	val pred' = 
	    subst(map(fn(x,y)=>{residue=y,redex=x})
		  (combine(ops,
			   map(fn th =>mk_comb{Rand=rep_var,
					       Rator=(#Rator o dest_comb o lhs 
						      o snd o strip_forall 
                                                      o concl)th})
			   rep_defs)))pred
	val rep_oblig = 
	    mk_forall{Bvar=rep_var,
		      Body=mk_eq
                      {lhs=mk_comb{Rator=mk_var
                                     {Name=name^"_oblig",
			              Ty=mk_type{Tyop="fun",
					         Args=[type_of rep_var,
						       ==`:bool`==]}},
				   Rand=rep_var},
	               rhs=pred'}}
	val oblig_thm = new_definition(name^"_oblig",rep_oblig)
    in		      
	push ((#Tyop o dest_type o type_of)rep_var,
	      {oblig=oblig_thm,
	       rep_defs=rep_defs}) theory_obligs;
	rep_type
    end
handle Exception.HOL_ERR sss => 
   (Exception.print_HOL_ERR(Exception.HOL_ERR sss);
    raise(Exception.HOL_ERR sss));

fun repeat f t =
    let val t' = f t 
    in
	repeat f t'
    end
handle _ => t;
    
fun abs_goal(g:goal as (asl,t)) =
    let fun abs_once (fvs,(asl,t)) =
	let val {Bvar,Body} = dest_forall t
	    val {Tyop,...} = (dest_type o type_of)Bvar
	    val {oblig, ...} = assoc Tyop (!theory_obligs)
	    val var = variant fvs Bvar
	in
	    (var::fvs,
	     ((strip_conj o rhs o concl o ISPEC var)oblig @ asl,
	      subst[{residue=var,redex=Bvar}]Body))
	end
    in
	(snd(repeat abs_once (free_varsl asl,g))):goal
    end;

fun ABS_TAC_PROOF (g,tac) = TAC_PROOF(abs_goal g,tac);

    
fun abs_convert_term t =
    let fun cnvt_once (l,t) =
	let val {Bvar,Body} = dest_forall t
	    val {Tyop,...} = (dest_type o type_of)Bvar
	    val {oblig,...} = assoc Tyop (!theory_obligs)
	in
	    ((Bvar,(lhs o concl o ISPEC Bvar)oblig)::l, Body)
	end
	val (obligl,body) = repeat cnvt_once ([],t)
	    val obligl = rev obligl
    in
	list_mk_forall(map fst obligl,
		       mk_imp{ant=list_mk_conj(map snd obligl),
			      conseq=body})
    end
handle HOL_ERR sss => (print_HOL_ERR(HOL_ERR sss);
		       raise(HOL_ERR sss));

fun ag t = 
   Goalstack.Implicit.set_goal([],abs_convert_term(Parse.term_parser t));
    
fun abs_set_goal (g:goal as (asl,t)) = 
   Goalstack.Implicit.set_goal(asl,abs_convert_term t);

fun suffix s n =
    let val nlen = size n
	and slen = size s
    in
	((nlen > slen) andalso
	 (String.substring(n,(nlen-slen),slen) = s))
    end;

fun EXPAND_THOBS_CONV t = 
    let val {Rator=oblig,Rand=rep} = dest_comb t
    in
	if (not((is_const oblig) andalso
		suffix"_oblig"((#Name o dest_const)oblig)))
	    then raise ABS_THRY_ERR{function="EXPAND_THOBS_TAC",
				    message="not an obligation"}
	else
	    let val tyop = (#Tyop o dest_type o type_of)rep
		val {oblig,rep_defs} = assoc tyop (!theory_obligs)
	    in
		(REWR_CONV oblig THENC ONCE_REWRITE_CONV rep_defs)t
	    end
	handle NOT_FOUND => raise ABS_THRY_ERR{function="EXPAND_THOBS_TAC",
				    message="obligation definition not loaded"}
    end;

val EXPAND_THOBS_TAC = CONV_TAC EXPAND_THOBS_CONV
and EXPAND_THOBS_RULE = CONV_RULE EXPAND_THOBS_CONV;
    
fun STRIP_THOBS_THEN ttac1 ttac2 (g:goal as (asl,t)) =
    let fun cnvt_once (l,t) =
	let val {Bvar,Body} = dest_forall t
	    val {Tyop,...} = (dest_type o type_of)Bvar
	    val {oblig,...} = assoc Tyop (!theory_obligs)
	in
	    ((Bvar,(ISPEC Bvar)oblig)::l, Body)
	end
	val (obligl,body) = repeat cnvt_once ([],t)
	val obligl = rev obligl
	val conjtm = (list_mk_conj o map(lhs o concl o snd))obligl
	val thm = LIST_CONJ(map (uncurry EQ_MP)
			    (combine(map snd obligl,CONJUNCTS(ASSUME conjtm))))
	fun tac(asl,g) =
	    ([(asl,mk_imp{ant=conjtm,
			  conseq=mk_imp{ant=concl thm,
					conseq=(#conseq o dest_imp)body}})],
	     fn [th] => (GENL(map fst obligl) o DISCH conjtm o MP (UNDISCH th))
                        thm)
    in
	(tac THEN DISCH_THEN ttac1 THEN DISCH_THEN ttac2)g
    end;

val STRIP_THOBS_TAC = STRIP_THOBS_THEN STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

fun abs_prove(t,tac) = prove(abs_convert_term t,tac);

fun abs_store_thm(n,t,tac) = store_thm(n,abs_convert_term t,tac);
    
fun get_obligs name =
    let val defs = definitions name
    in
	(map snd o filter(fn (n,th) => suffix "_oblig" n))defs
    end;
    
fun get_abs_reps name =
    let val defs = definitions name
    in
	(map snd o filter(fn (n,th) => suffix "_abs_rep" n))defs
    end;

(* makes use of fact that currently the key identifies the rest *)

fun add_obligs name =
    let val obligs = 
           map(fn th => ((#Tyop o dest_type o type_of o #Bvar o dest_forall 
		          o concl)th, th))
	                (get_obligs name)
	val abs_reps = map(fn th => ((#Tyop o dest_type o type_of o rand o lhs
				      o snd o strip_forall o concl)th, th))
	                (get_abs_reps name)
    in
	theory_obligs 
	:= op_union (fn p1 => fn p2 => (fst p1 = fst p2))
	            (map (fn (key,oblig)
		       => (key,{oblig=oblig,
				rep_defs = (map snd o filter(fn(k,d) => k=key))
                                           abs_reps}))
		      obligs)
	         (!theory_obligs)
    end;

val abs_add_definitions_to_sml 
    = add_to_sml 
    o filter(fn (n,th) => not(exists (Lib.C suffix n)
                                     ["_DEF","abs_rep","oblig"]))
    o definitions;

fun abs_add_theory_to_sml str =
   ( add_axioms_to_sml str;
     abs_add_definitions_to_sml str;
     add_theorems_to_sml str
   );
   
fun instantiate_abs_thm (instantiations:({abs_term:term,rep_term:term,
                                          validation:thm}list)) th = 
    let fun form_instantiation {abs_term:term,rep_term:term,validation:thm} =
	let val val_rep = (rand o snd o strip_imp o snd o strip_forall o concl)
                          validation
	    val (tm_subs,ty_subs) = match_term val_rep rep_term
	    val validity = (ISPECL (map #residue tm_subs)
			    o GENL (map #redex tm_subs)
			    o SPEC_ALL)validation
	    val abs_name = (#Tyop o dest_type o type_of)abs_term
	    val rep_defs = (#rep_defs(assoc(abs_name)
				      (!theory_obligs))
			    handle NOT_FOUND =>
			    raise ABS_THRY_ERR
			    {function="instantiate_abs_thm",
			     message="cannot find obligations for "^abs_name})
	in
	    ((#Name o dest_var)abs_term,
	     {rep_term=rep_term,validity=validity,rep_defs=rep_defs})
	end
	val instant_list = map form_instantiation instantiations
	fun local_spec (vall,th) =
	    let val {Bvar,...} = (dest_forall o concl)th 
		val (vall',th') =
		    let val {rep_term,validity,...} = 
                                    assoc((#Name o dest_var)Bvar)instant_list
		    in
			(validity::vall,ISPEC rep_term th)
		    end
		handle NOT_FOUND => (vall,SPEC Bvar th)
	    in
		(vall',th')
	    end
	val (vall,expth) = repeat local_spec ([],th)
	val implk = map(fn th => ((#conseq o dest_imp o concl)th
				  handle _ => concl th,th))vall
        val conjs = (strip_conj o #ant o dest_imp o concl)expth
        val thl = map(fn t=>assoc t implk
		      handle NOT_FOUND => (DISCH t o ASSUME)t)conjs
        val conjtm = (list_mk_conj o map(fn th => (#ant o dest_imp o concl)th
					 handle _ => (--`T`--)))thl
        val conjsimp =  (snd o EQ_IMP_RULE o REWRITE_CONV[]) conjtm
        val refth = (LIST_CONJ o map(fn(th1,th2) => MP th1 th2 handle _ =>th1))
	            (combine(thl,(CONJUNCTS o ASSUME)conjtm))
	val refth2 = (IMP_TRANS conjsimp
                    o DISCH conjtm 
                  o ONCE_REWRITE_RULE(itlist union 
                                             (map(#rep_defs o snd)instant_list)
                                             [])
              o MP expth) refth
    in
        if ((#ant o dest_imp o concl)conjsimp = (--`T`--))
	    then (MP refth2 TRUTH)
        else GENL(free_vars conjtm) refth2
    end;

fun instantiate_abstract_definition (instantiation:{abs_term:term,
                                                    rep_term:term}list)
                                    def defn2 =
    let val abs_defs = flatten(map (#rep_defs o snd)(!theory_obligs))
        val inst_list = map (fn {abs_term,rep_term} => 
                                      match_term abs_term rep_term)
	                    instantiation
        fun inst [] th = th
	  | inst (m::ms) th = inst ms (INST_TY_TERM m th)
	val inst_def =
	GEN_ALL(BETA_RULE(REWRITE_RULE (abs_defs) 
			  (inst inst_list(SPEC_ALL def)))) 
	val new_def =
        GEN_ALL(BETA_RULE(REWRITE_RULE (abs_defs) 
			  (inst inst_list
			   (SPEC_ALL defn2))))
    in
	BETA_RULE (ONCE_REWRITE_RULE [inst_def] new_def)
    end;

end;

(*STRUCTSTART*)

structure Imp_rewrite: Imp_rewrite_sig =
struct

type hol_type = CoreHol.Type.hol_type;
type term = CoreHol.Term.term
type thm = CoreHol.Thm.thm
type 'a net = 'a CoreHol.Net.net
type goal = Abbrev.goal
type conv = Abbrev.conv
type tactic = Abbrev.tactic;

open Exception;
open Lib;
open CoreHol.Thm;
open CoreHol.Dsyntax;
open CoreHol.Match;
open CoreHol.Term;
open CoreHol.Type;
open CoreHol.Net;
open Drule;
open Tactic;
   infix THEN;
open Conv;
   infix THENC;

fun IMP_REWR_ERR{function,message} = 
         HOL_ERR{origin_structure="abstract_theory",
		 origin_function=function,
		 message=message}

local fun COUNT_UNDISCH 0 thm = thm
	| COUNT_UNDISCH n thm = COUNT_UNDISCH (n -1) (UNDISCH thm)
in
fun INST_ALL_TY_TERM (tm_subst,type_subst) th =
    let val num_hyp = length (hyp th)
    in
       COUNT_UNDISCH num_hyp(INST tm_subst(INST_TYPE type_subst(DISCH_ALL th)))
    end
end;
    
    
(* Match a given part of "th" to a term, instantiating "th".
   The part should be free in the theorem, except for outer bound variables.
*)
fun PART_MATCH_ALL partfn th =
   let val pth = GSPEC (GEN_ALL th)
       val pat = partfn(concl pth)
       val matchfn = match_term pat 
   in
   fn tm => INST_ALL_TY_TERM (matchfn tm) pth
   end;

local exception NOT_AN_EQ
in
fun IMP_REWR_CONV th =
   let val instth = PART_MATCH_ALL lhs th 
                    handle _ => raise NOT_AN_EQ
   in
   fn asl => fn tm => 
     let val eqn = instth tm
         val l = lhs(concl eqn)
         val th' = 
            if (l = tm) 
            then eqn 
            else TRANS (ALPHA tm l) eqn
                 handle _
                 => raise IMP_REWR_ERR{function = "IMP_REWR_CONV",
                                 message = "lhs of theorem doesn't match term"}
     in
     if (all (fn t => mem t asl)(hyp th'))
     then th'
     else raise IMP_REWR_ERR{function = "IMP_REWR_CONV",
                             message = "introduces new assumptions"}
     end		    
   end
   handle NOT_AN_EQ => raise IMP_REWR_ERR{function = "IMP_REWR_CONV",
                            message = "bad theorem argument (not an equation)"}
        | (e as HOL_ERR _) => raise e
end;

fun mk_imp_rewrites th =
   let val th = Drule.SPEC_ALL th
       val t = Thm.concl th 
   in 
   if (is_imp t)
   then mk_imp_rewrites(UNDISCH th)
   else
   if (is_eq t)
   then [th]
   else if (is_conj t)
        then let val (c1,c2) = Drule.CONJ_PAIR th
             in
             ((mk_imp_rewrites c1)@(mk_imp_rewrites c2))
             end
        else if (is_neg t)
             then [Drule.EQF_INTRO th]
             else [Drule.EQT_INTRO th]
   end
   handle _ => raise IMP_REWR_ERR{function = "mk_imp_rewrites",message = ""};

(* [th1; ... ; thn]  --> (mk_rewrites th1) @ ... @ (mk_rewrites thn)   *)
fun mk_imp_rewritesl thl = itlist (append o mk_imp_rewrites) thl [];

(* Augment a conversion net with a list of equality theorems *)
fun add_to_imp_net thl net =
   itlist enter
          (map (fn th => (lhs(concl th), IMP_REWR_CONV th))
               (mk_imp_rewritesl thl))
          net;

fun mk_imp_conv_net thl = add_to_imp_net thl empty_net;

(* Create a conversion from a net *)
fun IMP_REWRITES_CONV asl net tm 
    = FIRST_CONV(map (fn f=>f asl)(lookup tm net)) tm;

    
(* List of basic rewrites (made assignable to enable us to add extra
 * rewrite rules later e.g., those for the theory of pairs).
*)
val basic_imp_rewrites = ref 
   (mk_imp_conv_net (mk_imp_rewritesl [REFL_CLAUSE,
				       EQ_CLAUSES,
				       NOT_CLAUSES,
				       AND_CLAUSES,
				       OR_CLAUSES,
				       IMP_CLAUSES,
				       COND_CLAUSES,
				       FORALL_SIMP,
				       EXISTS_SIMP,
				       ABS_SIMP]));

(* =====================================================================*)
(* Main rewriting conversion                         			*)
(* =====================================================================*)

fun GEN_IMP_REWRITE_CONV (rw_func:conv->conv) basic_net thl asl = 
   rw_func (IMP_REWRITES_CONV asl (add_to_imp_net (mk_imp_rewritesl thl) 
                                                  (!basic_net)));

(* ---------------------------------------------------------------------*)
(* Rewriting conversions.                        			*)
(* ---------------------------------------------------------------------*)

val PURE_IMP_REWRITE_CONV = GEN_IMP_REWRITE_CONV Conv.TOP_DEPTH_CONV
                                                 (ref empty_net)
and IMP_REWRITE_CONV = GEN_IMP_REWRITE_CONV Conv.TOP_DEPTH_CONV 
                                            basic_imp_rewrites
and PURE_ONCE_IMP_REWRITE_CONV = GEN_IMP_REWRITE_CONV Conv.ONCE_DEPTH_CONV
                                                      (ref empty_net)
and ONCE_IMP_REWRITE_CONV = GEN_IMP_REWRITE_CONV Conv.ONCE_DEPTH_CONV
                                                 basic_imp_rewrites;

(* Main rewriting rule *)
fun GEN_IMP_REWRITE_RULE f n thl th 
    = Conv.CONV_RULE(GEN_IMP_REWRITE_CONV f n thl (hyp th))th;

val PURE_IMP_REWRITE_RULE = GEN_IMP_REWRITE_RULE Conv.TOP_DEPTH_CONV
                                                 (ref empty_net)
and IMP_REWRITE_RULE = GEN_IMP_REWRITE_RULE Conv.TOP_DEPTH_CONV
                                            basic_imp_rewrites
and PURE_ONCE_IMP_REWRITE_RULE = GEN_IMP_REWRITE_RULE Conv.ONCE_DEPTH_CONV 
                                                      (ref empty_net)
and ONCE_IMP_REWRITE_RULE = GEN_IMP_REWRITE_RULE Conv.ONCE_DEPTH_CONV 
                                                 basic_imp_rewrites;

(* Rewrite a theorem with the help of its assumptions *)

fun PURE_ASM_IMP_REWRITE_RULE thl th =
   PURE_IMP_REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and ASM_IMP_REWRITE_RULE thl th = 
   IMP_REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and PURE_ONCE_ASM_IMP_REWRITE_RULE thl th =
   PURE_ONCE_IMP_REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and ONCE_ASM_IMP_REWRITE_RULE thl th = 
   ONCE_IMP_REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th;



fun GEN_IMP_REWRITE_TAC f n thl (g:goal as (asl,t)) 
    = Conv.CONV_TAC(GEN_IMP_REWRITE_CONV f n thl asl)g;
      

val (PURE_IMP_REWRITE_TAC: Thm.thm list -> tactic) =
   GEN_IMP_REWRITE_TAC Conv.TOP_DEPTH_CONV (ref empty_net)
and (IMP_REWRITE_TAC: Thm.thm list -> tactic) =
   GEN_IMP_REWRITE_TAC Conv.TOP_DEPTH_CONV basic_imp_rewrites
and (PURE_ONCE_IMP_REWRITE_TAC: Thm.thm list -> tactic) =
   GEN_IMP_REWRITE_TAC Conv.ONCE_DEPTH_CONV (ref empty_net)
and (ONCE_IMP_REWRITE_TAC: Thm.thm list -> tactic) = 
   GEN_IMP_REWRITE_TAC Conv.ONCE_DEPTH_CONV basic_imp_rewrites;


(* Rewrite a goal with the help of its assumptions *)

fun PURE_ASM_IMP_REWRITE_TAC thl :tactic = 
   Tactical.ASSUM_LIST (fn asl => PURE_IMP_REWRITE_TAC (asl @ thl))
and ASM_IMP_REWRITE_TAC thl :tactic      = 
   Tactical.ASSUM_LIST (fn asl => IMP_REWRITE_TAC (asl @ thl))
and PURE_ONCE_ASM_IMP_REWRITE_TAC thl :tactic = 
   Tactical.ASSUM_LIST (fn asl => PURE_ONCE_IMP_REWRITE_TAC (asl @ thl))
and ONCE_ASM_IMP_REWRITE_TAC thl :tactic      = 
   Tactical.ASSUM_LIST (fn asl => ONCE_IMP_REWRITE_TAC (asl @ thl));


(* Rewriting using equations that satisfy a predicate  *)
fun FILTER_PURE_ASM_IMP_REWRITE_RULE f thl th =
    PURE_IMP_REWRITE_RULE ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th
and FILTER_ASM_IMP_REWRITE_RULE f thl th = 
    IMP_REWRITE_RULE ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th
and FILTER_PURE_ONCE_ASM_IMP_REWRITE_RULE f thl th =
    PURE_ONCE_IMP_REWRITE_RULE((map Thm.ASSUME (filter f (Thm.hyp th)))@thl) th
and FILTER_ONCE_ASM_IMP_REWRITE_RULE f thl th = 
    ONCE_IMP_REWRITE_RULE ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th;;

fun FILTER_PURE_ASM_IMP_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST 
          (fn asl => PURE_IMP_REWRITE_TAC ((filter (f o Thm.concl) asl)@thl))
and FILTER_ASM_IMP_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
          (fn asl => IMP_REWRITE_TAC ((filter (f o Thm.concl) asl) @ thl))
and FILTER_PURE_ONCE_ASM_IMP_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
     (fn asl => PURE_ONCE_IMP_REWRITE_TAC ((filter (f o Thm.concl) asl) @ thl))
and FILTER_ONCE_ASM_IMP_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST 
         (fn asl => ONCE_IMP_REWRITE_TAC ((filter (f o Thm.concl) asl) @ thl));

end;
 (*STRUCTEND*)
