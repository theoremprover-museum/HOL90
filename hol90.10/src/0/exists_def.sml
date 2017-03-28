(* ===================================================================== *)
(* FILE          : exists_def.sml                                        *)
(* DESCRIPTION   : An embarrassment, somewhat hidden in hol88, made      *)
(*                 public in hol90. There is an attempt to reduce the    *)
(*                 principle of definition to the principle of constant  *)
(*                 specification. This falls down when trying to define  *)
(*                 the existential quantifier with a constant spec.,     *)
(*                 which requires an existence theorem. I could do as    *)
(*                 in hol88 - just grandfather in "?" as a definition -  *)
(*                 but I provide a separate principle of definition, that*)
(*                 just gets used once, to define "?".                   *)
(*                                                                       *)
(*                 Uses the "pre-constant spec" principle of definition  *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge, for hol88   *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


(*---------------------------------------------------------------------------
 A reiteration.

   There are actually two principles of definition operating in the system:

       1. The one used here to define ?.
       2. The one used everywhere else. It is a special version
          of the principle of constant specification. 

   It is not possible to use the principle of constant specification
   to define ?, for the PCS uses mk_exists, which will fail since we
   have not defined the existential quantifier yet.
 *---------------------------------------------------------------------------*)

functor EXISTS_DEF(structure Theory : Theory_sig
                   structure Dsyntax : Dsyntax_sig
                   sharing 
                     Theory.Thm.Term = Dsyntax.Term) : Exists_def_sig  =
struct
structure Theory = Theory
open Dsyntax;
open Theory.Thm.Term;

val |-> = Lib.|->
infix 5 |->

fun EXISTS_DEF_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Exists_def",
		      origin_function = function,
		      message = message}

(*---------------------------------------------------------------------------
 * Check that tm is a <lhs> where:
 *
 *   <lhs> ::= <var> | <lhs> <var> 
 *
 * and that no variables are repeated. Return list of variables.
 *---------------------------------------------------------------------------*)
fun check_lhs tm =
   if (is_var tm)
   then [tm]
   else if (is_const tm)
        then raise EXISTS_DEF_ERR{function = "check_lhs",
                                  message = "attempt_to_redefine_constant"}
        else if (is_comb tm)
             then let val {Rator,Rand} = dest_comb tm
                      val l1 = check_lhs Rator
                      and l2 = [Rand]
                  in
                  if (Lib.null_intersection l1 l2)
                  then (l1@l2)
                  else raise EXISTS_DEF_ERR{function = "check_lhs",
					    message = "bad lhs in def"}
                  end
             else raise EXISTS_DEF_ERR{function = "check_lhs",
				       message = "bad lhs in def"};


(*---------------------------------------------------------------------------
 * if "C ... = (...:ty)" then  (get_type "C ..." ty) gives the
 *   type of C.
 *
 * fun get_type (Fv _) rightty = rightty
 *   | get_type (Comb{Rator, Rand}) rightty = 
 *       get_type Rator (Type.Tyapp{Tyop = "fun", 
 *                                  Args = [type_of Rand,rightty]})
 *   | get_type _ _ = raise EXISTS_DEF_ERR{function = "get_type",
 *                                         message = "bad lhs in def"};
 *---------------------------------------------------------------------------*)
fun get_type tm rightty = 
   if (is_var tm)
   then rightty
   else if (is_comb tm)
        then let val {Rator,Rand} = dest_comb tm
             in
             get_type Rator (Type.mk_type{Tyop ="fun", 
                                          Args = [type_of Rand,rightty]})
             end
        else raise EXISTS_DEF_ERR{function = "get_type",
				  message = "bad lhs in def"};

fun new_binder_definition(tok,tm) =
 let val (vars,tm') = strip_forall tm
     val {lhs,rhs}  = dest_eq tm'
     val leftvars   = check_lhs lhs
     and ty         = get_type lhs (type_of rhs)
     and rightvars  = free_vars rhs
 in
 if not(Lib.set_eq(Lib.intersect leftvars rightvars)rightvars)
 then raise EXISTS_DEF_ERR{function = "new_binder_definition",
			   message = "unbound var in rhs"}
 else if (Lib.mem (Portable.List.hd leftvars) rightvars)
      then raise EXISTS_DEF_ERR{function = "new_binder_definition",
                                message = "def would be recursive"}
      else let val v = Portable.List.hd leftvars
               val c = {Name = #Name(dest_var v), Ty=ty}
           in
             Theory.new_binder c;
             Theory.store_definition(tok, 
             list_mk_forall(vars, mk_eq{lhs = subst [v |-> mk_const c] lhs, 
                                        rhs = rhs}))
           end
 end;

end; (* EXISTS_DEF *)
