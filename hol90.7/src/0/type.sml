(* ===================================================================== *)
(* FILE          : type.sml                                              *)
(* DESCRIPTION   : HOL types.                                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Type signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* ===================================================================== *)

functor TYPE (Lexis : Lexis_sig): Type_sig =
struct

fun TYPE_ERR{function,message} = HOL_ERR{origin_structure = "Type",
					 origin_function = function,
					 message = message}
fun UNIFY_ERR s = HOL_ERR{origin_structure = "Type",
			  origin_function = "unify",
			  message = s};
val INEQUAL_CONST_ERR = UNIFY_ERR "inequal constants";
val CONSTRAINT_CLASH = UNIFY_ERR "incompatible type variable constraints";
val OCCUR_CHECK = UNIFY_ERR "occurs check";

datatype hol_type = Stv of int           (* System generated type variables *)
                  | Utv of string        (* User-given type variables *)
                  | Tyc of string        (* Type constants  *)
                  | Link of hol_type ref (* Modifiable pointers *)
                  | Tyapp of {Tyop : string, Args : hol_type list};


(* HOL TYPE SIGNATURES *)

type type_record = {tyc   :hol_type, 
                    arity :int, 
                    theory:string};

type symtab = type_record list Array.array;

(***********************************************************************
 * The hash function for putting records into the symtab. "ordof" is
 * SML/NJ-specific.
 ***********************************************************************)
val table_size = 311;
fun hash s =
   let fun hsh(n,m) = hsh (((n*4) + ordof(s,m)) mod table_size, m+1)
                     handle Ord => n
   in hsh (0,0)
   end;

val symtab = ref (Array.array(table_size, ([]:type_record list)));

fun add_entry (entry as {tyc = Tyc name, ...}) =  
   let val i = hash name
       val L = Array.sub(!symtab, i)
   in
   Array.update(!symtab,i,(L@[entry]))
   end;

fun reset_symtab() = 
     symtab := Array.array (table_size,([]: type_record list));

fun symtab_copy () = 
   let val st_clone = Array.array (table_size,([]:type_record list))
       val _ = for_se 0 (table_size-1)
                        (fn i => Array.update(st_clone,i,Array.sub(!symtab,i)))
   in st_clone
   end;

fun replace_symtab st = symtab := st;

(***************************************************************************
 * For debugging and seeing the load
 * local val colon = ":"
 *       and space = " "
 *       fun print_st_entry({tyc = Tyc s,...}:type_record) = 
 *          output(std_out, s^space)
 * in
 * fun dump_symtab() =
 *    for_se 0 (table_size-1)
 *       (fn i => case Array.sub(!symtab,i)
 *                of [] => output(std_out, (int_to_string i)^colon^space)
 *                 | L =>(output(std_out,("\n"^(int_to_string i)^colon^space));
 *                            map print_st_entry L; ()))
 * end;
 *************************************************************************)
fun lookup_type s =
   let fun lft [] = raise NOT_FOUND
         | lft [tr as {tyc = Tyc name, ...}:type_record] = 
              if (s = name) then tr else raise NOT_FOUND
         | lft ((tr as {tyc = Tyc name, ...})::rst) = 
              if (s = name) then tr else lft rst
         | lft _ = raise TYPE_ERR{function = "lookup_type",
                                  message = "implementation error"}
   in  lft (Array.sub(!symtab, hash s))
   end;

fun type_decl x = 
   lookup_type x handle NOT_FOUND 
   => raise TYPE_ERR{function = "type_decl", 
                     message = Lib.quote x^" not found in signature"};

exception TYPE_SYMTAB_CLASH of {common_name:string, 
                                theory1:string, 
                                theory2:string};

(* If it's already there, raise an exception, otherwise install it. *)
fun add_type_const (entry as {theory = thry1,tyc = Tyc name, ...}) =
   let val {theory = thry2, ...} = lookup_type name
   in 
   raise TYPE_SYMTAB_CLASH{common_name=name, theory1=thry1, theory2=thry2}
   end
   handle NOT_FOUND => add_entry entry;

fun arity_of_type x = 
   #arity(lookup_type x) handle NOT_FOUND 
   => raise TYPE_ERR{function = "arity_of_type",
                     message = Lib.quote x^" not found in type signature"};

fun is_st_type_const x = (lookup_type x; true) handle NOT_FOUND => false;

(* END TYPE SIGNATURES *)


(* The variables in a type.     *)
local
fun tyvars (v as Utv _) vlist = 
      if (mem v vlist)
      then vlist
      else v::vlist
  | tyvars (Tyc _) vlist = vlist
  | tyvars (Tyapp{Args,...}) vlist = tyvarsl Args vlist
  | tyvars _ _ = raise TYPE_ERR{function = "tyvars",
				message = "type construction"}
and
    tyvarsl L vlist = rev_itlist tyvars L vlist
in
fun type_vars ty = rev(tyvars ty [])
fun type_varsl L = rev(tyvarsl L [])
end;

(* Make a type. Shares type constants. *)
local 
fun UNDEF_ERR s = raise TYPE_ERR{function = "mk_type",
                                 message = "type "^Lib.quote s^" not defined"}
in
fun mk_type{Tyop, Args = []} = 
     (case (lookup_type Tyop handle NOT_FOUND => UNDEF_ERR Tyop)
        of {tyc,arity = 0,...} => tyc
         | _ => raise TYPE_ERR{function = "mk_type", 
                               message = "arities don't match"})
     
  | mk_type(ty as {Tyop,Args}) =
      if ((#arity(lookup_type Tyop) = length Args) 
          handle NOT_FOUND => UNDEF_ERR Tyop)
      then Tyapp ty
      else raise TYPE_ERR{function = "mk_type", 
                          message = "arities don't match"}
end;

(* Take a type apart  *)
fun dest_type (Tyapp r) = r
  | dest_type (Tyc s) = {Tyop = s, Args = []}
  | dest_type _ = raise TYPE_ERR{function = "dest_type", message = ""};

(*************************************************************************
 * Make a type variable. Simple sharing scheme. A bonafide hash table 
 * would be better.
 *************************************************************************)
local
val alpha = Utv "'a"      val beta  = Utv "'b"
val c     = Utv "'c"      val d     = Utv "'d"
val e     = Utv "'e"      val f     = Utv "'f"
val g     = Utv "'g"      val h     = Utv "'h"
in
fun mk_vartype "'a" = alpha  | mk_vartype "'b" = beta
  | mk_vartype "'c" = c      | mk_vartype "'d" = d
  | mk_vartype "'e" = e      | mk_vartype "'f" = f
  | mk_vartype "'g" = g      | mk_vartype "'h" = h
  | mk_vartype s = 
      if (Lexis.allowed_user_type_var s)
      then Utv s
      else raise TYPE_ERR{function = "mk_vartype", 
                          message = "incorrect syntax"}
end;

(* Take a type variable apart *)
fun dest_vartype (Utv s) = s
  | dest_vartype _ = raise TYPE_ERR{function = "dest_vartype",
                                    message = "not a type variable"};

(* Is something a type variable.   *)
val is_vartype = can dest_vartype;


(**************************************************************************
 * Extends a "less-than" ordering on elements of a type to a lexicographic 
 *   ordering on lists of elements of that type. 
 **************************************************************************)
fun lex_order order =
   let fun ordered (t1::rst1) (t2::rst2) =
              if (order t1 t2) 
              then true
              else if (order t2 t1)
                   then false
                   else ordered rst1 rst2
         | ordered [] [] = false
         | ordered [] _  = true
         | ordered _  _  = false
   in ordered 
   end;

(* A total ordering on types *)
fun type_lt (Stv i1) (Stv i2) = (i1<i2)
  | type_lt (Stv _) _ = true

  | type_lt (Utv _) (Stv _)  = false
  | type_lt (Utv s1) (Utv s2) = (s1<s2)
  | type_lt (Utv _) _ = true

  | type_lt (Tyc s1) (Tyc s2) = (s1<s2)
  | type_lt (Tyc _) (Link _) = true
  | type_lt (Tyc _) (Tyapp _) = true
  | type_lt (Tyc _) _ = false

  | type_lt (Link (ref ty1)) (Link (ref ty2)) = type_lt ty1 ty2
  | type_lt (Link _) (Tyapp _) = true
  | type_lt (Link _) _ = false

  | type_lt (Tyapp{Tyop=s1, Args = L1}) (Tyapp{Tyop=s2, Args=L2}) =
       if (s1<s2)
       then true
       else if (s2<s1)
            then false
            else lex_order type_lt L1 L2
  | type_lt (Tyapp _) _ = false;


(* Used in type inference.   *)
local
val tyv_num = ref 0
in
fun new_type_var() = ( inc tyv_num;  Link(ref(Stv(!tyv_num))))
fun reset_type_num() = (tyv_num := 0)
end;

(* An "all" function defined for uncurried predicates.   *)
fun pr_all2 f =
   let fun trav (a1::rst1) (a2::rst2) = f(a1,a2) andalso trav rst1 rst2
         | trav [] [] = true
   in trav
   end;

(* Are two types equal? Slower than the more clearly written version. *)
fun ty_eq pr = 
   (op =) pr
   orelse 
   (case pr
     of (Tyapp{Tyop = s1, Args = A1},Tyapp{Tyop = s2, Args = A2}) =>
            ((s1=s2) andalso pr_all2 ty_eq A1 A2)
      | (Link(ref ty1), Link(ref ty2)) => ty_eq(ty1,ty2)
      | (Link(ref ty1),ty2) => ty_eq(ty1,ty2)
      | (ty1, Link(ref ty2)) => ty_eq(ty1,ty2)
      | _ => false);


(* The occurs check. We know that the first argument is an Stv. *)
fun occurs v =
   let fun occ (Tyapp{Args, ...}) = exists occ Args
         | occ (Link (ref ty)) = occ ty
         | occ ty = (v = ty)
   in occ
   end;

(**************************************************************************
 * Unification of types by pointer redirection.
 *
 * The order of the first three clauses of unif is delicate. They ensure 
 * that the hol_type in the first argument, if it is an assignable variable, 
 * gets assigned. 
 ***************************************************************************)
fun unify ty1 ty2 = if ty_eq(ty1,ty2) 
                    then ()
                    else unif(ty1,ty2)
and
    unif (Link(r as ref(s as Stv _)), ty) = 
        if (occurs s ty)
        then raise OCCUR_CHECK
        else r := ty
  | unif (Link(ref ty1), ty2) = unify ty1 ty2
  | unif (ty, v as Link (ref (Stv _))) = unify v ty
  | unif (ty1, Link (ref ty2)) = unify ty1 ty2
  | unif (Tyapp{Tyop = s1, Args = args1},Tyapp{Tyop = s2, Args = args2}) =
      if (s1 = s2)
      then rev_itlist2 (fn ty1 => fn ty2 => fn _ => unify ty1 ty2)
                       args1 args2 ()
      else raise INEQUAL_CONST_ERR
  | unif _ = raise UNIFY_ERR "structural difference in types";


(*************************************************************************
 * Postprocessing of types. Delete all Links from a type. Raise an error 
 * if there is a system type variable left in the type.
 *************************************************************************)

(* version that rebuilds type *********************************************
 * fun shrink_type (Link(ref ty)) = shrink_type ty
 *   | shrink_type (Tyapp{Tyop, Args}) = Tyapp{Tyop = Tyop, 
 *                                             Args = map shrink_type Args}
 *   | shrink_type (Stv _) =
 *       raise TYPE_ERR{function = "shrink_type",
 *                      message = "Unconstrained type variable"}
 *   | shrink_type ty = ty;
 ***************************************************************************)

datatype 'a delta = NO_CHANGE | CHANGED of 'a;
datatype 'a args_changed = YUP of 'a list | NOPE of 'a list;

fun apply_subst_to_list f L =
   itlist(fn ty => 
          (fn (YUP L') 
              => YUP((case (f ty)
                        of NO_CHANGE => ty
                         | CHANGED ty' => ty')::L')
            | (NOPE L') 
              => (case (f ty)
                    of NO_CHANGE => NOPE(ty::L')
                     | CHANGED ty' => YUP(ty'::L'))))
         L (NOPE[]);

(* Structure-sharing version.        *)
fun shrink_type (Link(ref ty)) = 
      (case (shrink_type ty) of NO_CHANGE => CHANGED ty | x => x)
  | shrink_type (Tyapp{Tyop, Args}) = 
      (case (apply_subst_to_list shrink_type Args)
         of (YUP L') => CHANGED (Tyapp{Tyop = Tyop, Args = L'})
          | (NOPE _) => NO_CHANGE)
  | shrink_type (Stv _) =
      raise TYPE_ERR{function = "shrink_type",
                     message = "Unconstrained type variable"}
  | shrink_type ty = NO_CHANGE;


(****************************************************************************
 * Maps from hol_type to hol_type, with type variables consistently renamed.
 * Also deletes intermediate Links. Could be more careful: ground Tyapps 
 * get rebuilt unnecessarily.
 *****************************************************************************)

(*  Non-sharing version ***************************************************
 * local
 * val tv_pair_list = ref ([]:(hol_type * hol_type) list)
 * fun rn (v as Utv _) = 
 *     ( assoc v (!tv_pair_list)
 *       handle NOT_FOUND =>
 *             let val v' = new_type_var()
 *             in
 *             ( tv_pair_list := ((v,v')::(!tv_pair_list));
 *               v' )
 *             end )
 *   | rn (c as Tyc _) = c
 *   | rn (Link(ref ty)) = rn ty
 *   | rn (Tyapp{Tyop, Args}) = Tyapp{Tyop = Tyop, Args = map rn Args}
 *   | rn (Stv _) =
 *       raise TYPE_ERR{function = "rename_tv",
 *                      message = "attempt to rename system type variable"}
 * in
 * fun rename_tv ty = ( tv_pair_list := []; rn ty)
 * end;
 *****************************************************************************)

(* Sharing version.   *)
local
val tv_pair_list = ref ([]:(hol_type * hol_type) list)
fun rn (v as Utv _) = 
      CHANGED(assoc v (!tv_pair_list)
              handle NOT_FOUND =>
                let val v' = new_type_var()
                in
                ( tv_pair_list := ((v,v')::(!tv_pair_list));  v' )
                end)
  | rn (c as Tyc _) = NO_CHANGE
  | rn (Tyapp{Tyop, Args}) = 
      (case (apply_subst_to_list rn Args)
         of (YUP L) => CHANGED(Tyapp{Tyop = Tyop, Args = L})
          | (NOPE _) => NO_CHANGE)
  | rn _ = raise TYPE_ERR{function = "rename_tv",message = "type construction"}
in
fun rename_tv ty = ( tv_pair_list := []; rn ty)
end;


(* Substitute in a type   *)

(* Non-sharing version  ************************************************
 * fun type_subst [] ty = ty
 *   | type_subst theta (Tyapp{Tyop, Args}) = 
 *       Tyapp{Tyop = Tyop, Args = map (type_subst theta) Args}
 *   | type_subst theta (v as Utv _) = 
 *          (Lib.subst_assoc v theta handle NOT_FOUND => v)
 *   | type_subst theta (c as Tyc _) = c
 *   | type_subst _ _ = raise TYPE_ERR{function = "type_subst",
 *                                     message = "type construction"};
 *************************************************************************)


(* Sharing version *)
fun ty_sub [] ty = NO_CHANGE
  | ty_sub theta (Tyapp{Tyop,Args}) =
      (case (apply_subst_to_list (ty_sub theta) Args)
         of (YUP L') => CHANGED (Tyapp{Tyop = Tyop, Args = L'})
          | (NOPE _) => NO_CHANGE)
  | ty_sub theta (v as Utv _) = 
      (case (Lib.subst_assoc (fn x => (x = v)) theta)
         of NONE => NO_CHANGE
          | SOME ty => CHANGED ty)
  | ty_sub theta (Tyc _) = NO_CHANGE
  | ty_sub _ _ = raise TYPE_ERR{function = "ty_sub",
                                message = "type construction"};
                                                
fun type_subst theta ty = case (ty_sub theta ty)
                            of NO_CHANGE => ty
                             | CHANGED ty' => ty';

(* Is a type polymorphic? *)
fun polymorphic (Utv _) = true
  | polymorphic (Tyc _) = false
  | polymorphic (Tyapp{Args,...}) = exists polymorphic Args
  | polymorphic _ = raise TYPE_ERR{function="polymorphic",
                                   message="type construction"};

end; (* TYPE *)
