(* ===================================================================== *)
(* FILE          : type_def.sml                                          *)
(* DESCRIPTION   : Implements the principle of type definition. Ported   *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


functor TYPE_DEF (structure Theory : Theory_sig
                  structure Dsyntax : Dsyntax_sig
                  sharing 
                    Theory.Thm.Term = Dsyntax.Term) : Type_def_sig =
struct
structure Theory = Theory;
open Theory;
open Thm;
open Term;
open Dsyntax;

(* ===================================================================== *)
(* new_type_definition: define a new logical type.                       *)
(*                                                                       *)
(* USAGE: new_type_definition(name, pred, thm)  (DRAFT MODE ONLY)        *)
(*                                                                       *)
(* ARGUMENTS: name --- a string giving the name of the new type or       *)
(*                     type operator that is to be defined.              *)
(*                                                                       *)
(*            pred --- a term denoting a predicate which is to           *)
(*                     define a subset of an existing type (ty say)      *)
(*                     that is to represent the new type.  The type      *)
(*                     of pred must be "ty -> bool" and pred must        *)
(*                     must contain no free variables.                   *)
(*                                                                       *)
(*            thm  --- a theorem asserting the existence of some         *)
(*                     object of type ty that satisfies pred.  The       *)
(*                     theorem must be of the form "|- ?x. pred x" for   *)
(*                     some variable x. The theorem must have no         *)
(*                     assumptions.                                      *)
(*                                                                       *)
(* SIDE EFFECTS: 1) Introduces a new type (type operator) with the       *)
(*                  given name. The arity of the new type operator       *)
(*                  is the same as the number of type variables in the   *)
(*                  predicate pred. Fails if name is already the name of *)
(*                  an existing type.                                    *)
(*                                                                       *)
(*               2) Asserts an axiom stating that there is an isomorphism*)
(*                  from the new type to the subset of ty defined by the *)
(*                  predicate pred.  The name of this axiom will be      *)
(*                  form `name_TY_DEF`.  If an axiom (or definition)     *)
(*                  with this name already exists, then the call fails.  *)
(*                                                                       *)
(*                  The form of the axiom asserted will be as follows:   *)
(*                                                                       *)
(*                     new_type_definition(`ty`, "P", |- ?x. P x)        *)
(*                                                                       *)
(*                  yields the axiom:                                    *)
(*                                                                       *)
(*                     ty_TY_DEF = |- ?rep. TYPE_DEFINITION P rep        *)
(*                                                                       *)
(*                  I.e. there is a function rep from the new type to    *)
(*                  the representing type ty that is one to one and onto *)
(*                  the subset defined by P.                             *)
(*                                                                       *)
(* RETURNS: the axiom as a theorem.                                      *)
(*                                                                       *)
(* IMPLEMENTATION NOTE: the dml'ed ML function is_axiom here tests if an *)
(* axiom, OR definition is already in the current theory.                *)
(* ===================================================================== *)

fun TYPE_DEF_ERR s = HOL_ERR{origin_structure = "Type_def",
			     origin_function = "new_type_definition",
			     message = s};

infix 3 -->
fun (X --> Y) = Type.mk_type{Tyop = "fun", Args = [X,Y]};

local
fun is_axiom str = 
   case (assoc1 str (Theory.axioms (Theory.current_theory())))
     of NONE => false
      | (SOME _) => true
fun is_definition str = 
   case (assoc1 str (Theory.definitions (Theory.current_theory())))
     of NONE => false
      | (SOME _) => true

fun is_type str = 
   let fun f ([]:{Name:string,Arity: int} list) = false
         | f ({Name,...}::rst) = (str = Name) orelse f rst

   in
   f (Theory.types (Theory.current_theory()))
   end
in
fun new_type_definition {name,pred,inhab_thm} =
   let val generated_name = name^"_TY_DEF"
       val bool = Type.mk_type{Tyop="bool",Args=[]}
   in
     if (not(Theory.draft_mode()))
     then raise(TYPE_DEF_ERR "not in draft mode")
     else if ((is_axiom generated_name) orelse (is_definition generated_name))
          then raise TYPE_DEF_ERR
                      ("\""^generated_name^"\" already an axiom or definition")
          else if not(null(Term.free_vars pred)) 
               then raise TYPE_DEF_ERR "subset predicate must be a closed term"
               else if (not (case (Type.dest_type(Term.type_of pred))
                                of {Tyop="fun",Args=[_,ty]} => (ty=bool)
                                 | _ => false))
                    then raise TYPE_DEF_ERR
                               "subset predicate has the wrong type"
                    else 
            if not(null(hyp inhab_thm)) 
            then raise TYPE_DEF_ERR"existence theorem must have no assumptions"
            else if not((pred = rator(#Body(dest_exists(concl inhab_thm))))
                        handle _ => false)
                 then raise TYPE_DEF_ERR
                                "existence theorem must match subset predicate"
                 else if (is_type name) 
                      then raise TYPE_DEF_ERR
                       (name^" is already the name of a type or type operator")
            else let val {Args = [ty,_],...} = Type.dest_type(type_of pred) 
                     and evar = #Bvar(dest_exists(concl inhab_thm))
                     val tyvarsl = Term.type_vars_in_term pred 
                 in
                   Theory.new_type{Name = name, Arity = length tyvarsl};
                   let val newty  = Type.mk_type{Tyop = name,Args = tyvarsl}
                       val repty  = newty --> ty
                       val rep    = Term.mk_primed_var{Name="rep", Ty=repty}
                       val TYDEF = mk_const{Name = "TYPE_DEFINITION",
                                           Ty = (ty-->bool) --> (repty-->bool)}
                       val ax = mk_exists
                          {Bvar = rep, 
                           Body = mk_comb{Rator=mk_comb{Rator=TYDEF,Rand=pred},
                                          Rand = rep}}
                   in 
                   Theory.store_definition (generated_name, ax)
                   end
                 end
   end
end;

end; (* TYPE_DEF *)
