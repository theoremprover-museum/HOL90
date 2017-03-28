(****************************************************************************)
(* FILE          : extract.sml                                              *)
(* DESCRIPTION   : Extracting information from HOL types and terms.         *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 1989                                                     *)
(*                                                                          *)
(* TRANSLATED BY : D.R.Syme                                                 *)
(* DATE          : 1995                                                     *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 29th September 1995                                      *)
(****************************************************************************)

structure RetrieveExtract : RETRIEVE_EXTRACT =
struct

(*--------------------------------------------------------------------------*)
(* get_ids : term -> (term list * term list * term list)                    *)
(*                                                                          *)
(* Function to take a term and return a triple:                             *)
(* (<constants>,<free variables>,<bound variables>)                         *)
(*                                                                          *)
(* Set union and set difference are used to avoid generating repetitions in *)
(* the lists derived. For function applications, the lists from the rator   *)
(* and the rand can simply be joined by set union. For abstractions, the    *)
(* bound variable is removed from the free variable list of the body, and   *)
(* is added to the bound variable list of the body.                         *)
(*--------------------------------------------------------------------------*)

fun get_ids t =
   case (dest_term t)
   of CONST _ => ([t],[],[])
    | VAR _ => ([],[t],[])
    | LAMB {Bvar = bv,Body = body} =>
         let val (cl,fvl,bvl) = get_ids body
         in  (cl,subtract fvl [bv],union bvl [bv])
         end
    | COMB {Rator = a,Rand = b} =>
         let val (cla,fvla,bvla) = get_ids a
             and (clb,fvlb,bvlb) = get_ids b
         in  (union cla clb,union fvla fvlb,union bvla bvlb)
         end;

(*--------------------------------------------------------------------------*)
(* get_consts    : term -> term list                                        *)
(* get_freevars  : term -> term list                                        *)
(* get_boundvars : term -> term list                                        *)
(*                                                                          *)
(* Functions to extract components from the get_ids triple.                 *)
(*--------------------------------------------------------------------------*)

val get_consts = #1 o get_ids
and get_freevars = #2 o get_ids
and get_boundvars = #3 o get_ids;

(*--------------------------------------------------------------------------*)
(* get_types : term -> hol_type list                                        *)
(*                                                                          *)
(* Function to obtain a list of the types which occur in a term.            *)
(*                                                                          *)
(* The lists of constants, free variables and bound variables are           *)
(* concatenated. The resulting identifiers are converted to their types,    *)
(* and then any repetitions are removed.                                    *)
(*--------------------------------------------------------------------------*)

fun get_types t =
   let val (cl,fvl,bvl) = get_ids t
       fun get_typ t = #Ty (Term.dest_const t handle _ => Term.dest_var t) 
   in  RetrieveSets.remove_rep (map get_typ (cl @ fvl @ bvl))
   end;

(*--------------------------------------------------------------------------*)
(* is_primtype : hol_type -> bool                                           *)
(*                                                                          *)
(* Function which applied to a HOL type returns true if the type is of the  *)
(* form `:'...` or `:op`, otherwise false is returned.                      *)
(*--------------------------------------------------------------------------*)

fun is_primtype typ = null (#Args (Type.dest_type typ)) handle _ => true;

(*--------------------------------------------------------------------------*)
(* subtypes : hol_type -> hol_type list                                     *)
(*                                                                          *)
(* Function which applied to a HOL type returns a list containing simply    *)
(* the type itself if it is `primitive' or the types from which it is       *)
(* constructed otherwise.                                                   *)
(*--------------------------------------------------------------------------*)

fun subtypes typ =
   if (is_primtype typ)
   then [typ]
   else #Args (Type.dest_type typ);

(*--------------------------------------------------------------------------*)
(* prim_subtypes : hol_type -> hol_type list                                *)
(*                                                                          *)
(* Function to break-up a type into its `primitive' types.                  *)
(*                                                                          *)
(* The function uses the predicate is_primtype, defined above. If the type  *)
(* is not `primitive', a list of the component types is obtained, to which  *)
(* the function is applied recursively. The resulting list of lists is then *)
(* `flattened' to give a list of `primitive' types, from which any          *)
(* repetitions are removed.                                                 *)
(*--------------------------------------------------------------------------*)

fun prim_subtypes typ =
   if (is_primtype typ)
   then [typ]
   else (RetrieveSets.remove_rep o flatten o map prim_subtypes o subtypes) typ;

(*--------------------------------------------------------------------------*)
(* get_primtypes : term -> hol_type list                                    *)
(*                                                                          *)
(* Function to obtain a list of the `primitive' types occurring in a term.  *)
(*                                                                          *)
(* A list of the types occurring in the term is obtained. Each of these     *)
(* types is converted to a list of its `primitive' types. The resulting     *)
(* list of lists is then `flattened', and any repetitions are removed.      *)
(*--------------------------------------------------------------------------*)

fun get_primtypes t =
   (RetrieveSets.remove_rep o flatten o map prim_subtypes o get_types) t;

(*--------------------------------------------------------------------------*)
(* get_primvartypes : term -> hol_type list                                 *)
(*                                                                          *)
(* Function to obtain a list of the `primitive' polymorphic types in a      *)
(* term.                                                                    *)
(*--------------------------------------------------------------------------*)

fun get_primvartypes t = filter Type.is_vartype (get_primtypes t);

end; (* RetrieveExtract *)
