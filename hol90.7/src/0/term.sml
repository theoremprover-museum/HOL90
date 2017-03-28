(* ===================================================================== *)
(* FILE          : term.sml                                              *)
(* DESCRIPTION   : Simply typed lambda terms.                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Term signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* ===================================================================== *)

functor TERM (structure Lexis: Lexis_sig
              structure Type : Type_sig) : Term_sig =
struct
structure Type = Type;

fun TERM_ERR{function,message} = HOL_ERR{origin_structure = "Term",
					 origin_function = function,
					 message = message}

type atom = {Name : string, Ty : Type.hol_type}

(* For logical constants - an attribute that is held in symtab. *)
datatype fixity = Infix of int | Prefix | Binder;

(***************************************************************************
 * deBruijn terms. ty_antiq is an annoyance, caused by having quotations
 * be frag lists. This requires all antiquotes in a quotation to have the
 * same type. Thus we use ty_antiq to cast types to terms, in order that all 
 * antiquotes be terms.
 ***************************************************************************)
datatype term = Fv of atom
              | Bv of int
              | Const of atom
              | Comb of {Rator : term, Rand : term}
              | Abs of {Bvar : term, Body : term}
              | ty_antiq of Type.hol_type;

(* For efficiency tests by Morten *)
datatype lambda = VAR of atom
                | CONST of atom
                | COMB of {Rator : term, Rand : term}
                | LAMB of {Bvar : term, Body : term};


fun TY_ANTIQ_ERR s = TERM_ERR{function = s, message = "ty_antiq in term"};

(* Computing the type of a term *)
local
fun chase (Type.Tyapp{Tyop = "fun", Args = [_,ty]}) = ty
  | chase _ = raise TERM_ERR {function = "chase", message = ""}
fun lookup 0 (ty::_) = ty
  | lookup n (_::rst) = lookup (n-1) rst
  | lookup _ [] = raise TERM_ERR{function = "type_of", message = "lookup"}
fun ty_of (Fv{Ty, ...}) _ = Ty
  | ty_of (Const{Ty, ...}) _ = Ty
  | ty_of (Comb{Rator, ...}) E = chase (ty_of Rator E)
  | ty_of (Abs{Bvar = Fv{Ty,...},Body}) E = 
         Type.Tyapp{Tyop = "fun", Args = [Ty, ty_of Body (Ty::E)]}
  | ty_of (Bv i) E = lookup i E
  | ty_of _ _ = raise TERM_ERR{function = "ty_of",
			       message = "term construction"}
in
fun type_of tm = ty_of tm []
end;


(* HOL TERM SIGNATURES *)
type term_record = {const :term, place :fixity, theory :string};
type symtab = term_record list Array.array;

datatype add_style = Defining | Loading;

(***********************************************************************
 * The hash function for putting records into the symtab. "ordof" is
 *  SML/NJ-specific.
 ***********************************************************************)
val table_size = 1021
fun hash s =
   let fun hsh(n,m) = hsh (((n*4) + ordof(s,m)) mod table_size, m+1)
                     handle Ord => n
   in hsh (0,0)
   end;

val symtab = ref (Array.array (table_size,([]:term_record list)));

fun add_entry (entry as {const = Const{Name,...},...}) =  
   let val i = hash Name
       val L = Array.sub(!symtab, i)
   in
   Array.update(!symtab,i,(L@[entry]))
   end;

fun reset_symtab() = 
     symtab := Array.array (table_size,([]: term_record list));

fun symtab_copy () = 
   let val st_clone = Array.array (table_size,([]:term_record list))
       val _ = for_se 0 (table_size-1)
                        (fn i => Array.update(st_clone,i,Array.sub(!symtab,i)))
   in st_clone
   end;

fun replace_symtab st = symtab := st;

(*****************************************************************************
 * local val colon = ":"
 *       and space = " "
 *       fun print_st_entry({const = Const{Name,...},...}:term_record) = 
 *            output(std_out, Name^space)
 * in
 * fun dump_symtab() =
 *    for_se 0 (table_size-1)
 *       (fn i => case Array.sub(!symtab,i)
 *                of [] => output(std_out, (int_to_string i)^colon^space)
 *                 | L =>(output(std_out,("\n"^(int_to_string i)^colon^space));
 *                            map print_st_entry L; ()))
 * end;
 ****************************************************************************)
fun lookup s = 
   let fun lft [tr as {const = Const{Name, ...}, ...}:term_record] = 
              if (s = Name) then tr else raise NOT_FOUND
         | lft ((tr as {const = Const{Name,...},...})::rst) = 
              if (s = Name) then tr else lft rst
         | lft [] = raise NOT_FOUND
   in
   lft (Array.sub(!symtab, hash s))
   end;

fun lookup_const s = #const(lookup s);


exception TERM_SYMTAB_CLASH of {common_name:string, 
                                theory1:string, 
                                theory2:string};

(* **************************************************************************
 * Here's a minor mess; binary format stores both constant and "dollared"
 * constant in .holsig file, while ascii format stores only one
 * (non-dollared) constant. Hence in binary format, when loading a theory 
 * file, we only add 1 entry (since the dollared entry, because in the theory, 
 * will also automatically be added), but in ascii format, we have to make 
 * another, dollared, entry.
 *
 * Defining is used in Theory.new_constant, while Loading used in 
 * Theory_ops.install_hol_sig.
 *****************************************************************************)
fun add_term_const DorL (entry as {theory=thry1, const=Const{Name,Ty},place}) =
   let val {theory = thry2, ... } = lookup Name
   in raise TERM_SYMTAB_CLASH {common_name=Name, theory1=thry1, theory2=thry2}
   end
   handle NOT_FOUND
   => (add_entry entry;
       case DorL  
        of Defining 
           => add_entry{theory = thry1, 
                        const = Const{Name="$"^Name,Ty = Ty},
                        place = Prefix}
         | Loading 
           => if (Sys_params.theory_file_option=Sys_params.make_binary)
              then ()
              else add_entry{theory = thry1, 
                             const = Const{Name="$"^Name,Ty = Ty},
                             place = Prefix});

(* Return constant just as it was declared *)
fun const_decl x = 
   lookup x handle NOT_FOUND 
   => raise TERM_ERR{function = "const_decl", 
                     message = Lib.quote x^" not found in signature"};

(* Is a constant infix, prefix, or a binder *)
fun fixity_of_term x =
   #place(lookup x)
   handle NOT_FOUND
   => if (Lexis.is_num_literal x orelse Lexis.is_string_literal x)
      then Prefix
      else raise TERM_ERR{function = "fixity_of_term", 
                     message = Lib.quote x^" not found in signature"};

fun is_binder "\\" = true
  | is_binder s = (fixity_of_term s = Binder)
                  handle _ => false;

fun is_infix s = (case (fixity_of_term s)
                   of (Infix _) => true
                    | _ => false) handle _ => false;

(* The precedence of a term.   *)
fun prec_of_term x = 
   (case (#place (lookup x))
      of (Infix i) => i
       | _ => 0)
   handle NOT_FOUND
   => if (Lexis.is_num_literal x orelse Lexis.is_string_literal x)
      then 0
      else raise TERM_ERR{function = "prec_of_term", 
                          message = Lib.quote x^" not found in signature"};

(* Is a string the name of a defined constant.   *)
fun is_st_term_const x = 
   (lookup x; true) 
   handle NOT_FOUND
   => ((Lexis.is_num_literal x andalso Globals.nums_defined())
       orelse
       (Lexis.is_string_literal x andalso Globals.strings_defined()));

(* Is a string the name of a polymorphic constant.   *)
fun is_polymorphic x =
   Type.polymorphic(type_of(lookup_const x)) handle _ => false;

(* END TERM SIGNATURE *)



(* The free variables of a lambda term.   *)
local
fun frees(v as Fv _) free_list = 
      if (mem v free_list) then free_list else v::free_list
  | frees(Comb{Rator, Rand}) free_list = frees Rand (frees Rator free_list)
  | frees(Abs{Body,...}) free_list = frees Body free_list
  | frees _ free_list = free_list
in
fun free_vars tm = frees tm []
end;


(* All the variables in a term.   *)
local
fun vars (v as Fv _) vlist = 
      if (mem v vlist) then vlist else v::vlist
  | vars(Comb{Rator, Rand}) vlist = vars Rand (vars Rator vlist)
  | vars(Abs{Bvar, Body}) vlist = vars Body (vars Bvar vlist)
  | vars _ vlist = vlist
in
fun all_vars tm = vars tm []
end;

fun free_varsl tm_list = itlist (union o free_vars) tm_list []
fun all_varsl tm_list = itlist (union o all_vars) tm_list [];

(* Does tm occur free in M. This is not defined modulo aconvability.
 * Maybe it should be? 
 ***********************************************************************)
fun free_in tm M =
   let fun f1 (Comb{Rator,Rand}) = (f2 Rator) orelse (f2 Rand)
         | f1 (Abs{Body,...}) = f2 Body
         | f1 _ = false
       and f2 t = (t=tm) orelse (f1 t)
   in f2 M
   end;


(* Total ordering on terms.   *)
local
fun atom_lt {Name=(s1:string),Ty=ty1} {Name=s2,Ty=ty2} = 
   (s1<s2) andalso (Type.type_lt ty1 ty2)
val TYANTIQ_ERR = TERM_ERR{function = "term_lt",
                           message="type antiquotes are not terms"}
in
fun term_lt (ty_antiq _) _ = raise TYANTIQ_ERR
  | term_lt _ (ty_antiq _)= raise TYANTIQ_ERR
  | term_lt (Fv v1) (Fv v2) = atom_lt v1 v2
  | term_lt (Fv _) _ = true
  
  | term_lt (Bv _) (Fv _) = false
  | term_lt (Bv i1) (Bv i2) = i1<i2
  | term_lt (Bv _) _ = true

  | term_lt (Const _) (Fv _) = false
  | term_lt (Const _) (Bv _) = false
  | term_lt (Const c1) (Const c2) = atom_lt c1 c2
  | term_lt (Const _) _ = true

  | term_lt (Comb{Rator=rator1,Rand=rand1}) (Comb{Rator=rator2,Rand=rand2}) =
      if (term_lt rator1 rator2)
      then true
      else if (term_lt rator2 rator1)
           then false
           else (term_lt rand1 rand2)
  | term_lt (Comb _) (Abs _) = true
  | term_lt (Comb _) _ = false

  | term_lt (Abs{Bvar=bv1, Body=body1}) (Abs{Bvar=bv2, Body=body2}) =
      if (term_lt bv1 bv2)
      then true
      else if (term_lt bv2 bv1)
           then false
           else term_lt body1 body2
  | term_lt (Abs _) _ = false
end;


(* Making variables *)

(* A good place to investigate sharing. *)
val mk_var = Fv

fun mk_primed_var(v as {Name,Ty}) =
   if (is_st_term_const Name)
   then mk_primed_var{Name = Name^"'", Ty = Ty}
   else mk_var v;


val gname = Lib.fresh_name "%%genvar%%"
fun genvar ty = Fv{Name = gname(), Ty = ty};

fun genvars _ 0 = []
  | genvars ty n = genvar ty::genvars ty (n-1);


(* ***************************************************************************
 * Given a variable and a list of variables, if the variable does not exist on
 * the list, then return the variable. Otherwise, prime the variable and try
 * again.
 *****************************************************************************)
local 
fun var_name(Fv{Name,...}) = Name
  | var_name _ = raise TERM_ERR{function = "variant.var_name",
		          message = "first arg. should be a list of variables"}
in
fun string_variant slist =
   let fun pass str = if (mem str slist) then pass (str^"'") else str
   in pass 
   end
fun variant vlist (Fv{Name,Ty}) =
      mk_primed_var{Name = string_variant (map var_name vlist) Name, Ty = Ty}
  | variant _ _ = raise(TERM_ERR{function = "variant",
				 message = "2nd arg. should be a variable"})
end;

fun type_vars_in_term (Fv{Ty, ...}) = Type.type_vars Ty
  | type_vars_in_term (Const{Ty,...}) = Type.type_vars Ty
  | type_vars_in_term (Comb{Rator,Rand}) = union (type_vars_in_term Rator) 
                                                 (type_vars_in_term Rand)
  | type_vars_in_term (Abs{Bvar,Body}) = union (type_vars_in_term Bvar)
                                               (type_vars_in_term Body)
  | type_vars_in_term (Bv _) = []
  | type_vars_in_term (ty_antiq _) = raise TY_ANTIQ_ERR "type_vars_in_term";


(*****************************************************************************
 * Making constants without matching. Does anybody need this?
 * fun prim_mk_const name =
 *   let val (c as Const{Ty,...}) = 
 *          lookup_const name handle _ => 
 *           raise TERM_ERR{func = "mk_const",
 *                          mesg = Lib.quote name^" has not been defined"}
 *   in fn [] => c
 *       | theta => Const{Name = name, Ty = Type.type_subst theta Ty}
 *   end;
 *****************************************************************************)

(* Making applications *)
local
val INCOMPAT_TYPES = TERM_ERR{function = "list_mk_comb",
                              message = "incompatible types"}
in
fun list_mk_comb (f,L) =
   let fun loop (A,_) [] = A
         | loop (A,Type.Tyapp{Tyop = "fun",Args=[ty1,ty2]}) (tm::rst2) =
               if (type_of tm = ty1)
               then loop(Comb{Rator=A,Rand=tm},ty2) rst2
               else raise INCOMPAT_TYPES
         | loop _ _ = raise INCOMPAT_TYPES
   in
   loop(f,type_of f) L
   end
end;

(*************************************************************************
 * Special case when Rator is an abstraction - examine the type of
 * the bound variable.
 *************************************************************************)
fun mk_comb(r as {Rator = Abs{Bvar = Fv{Ty,...},...}, Rand}) = 
      if (type_of Rand = Ty)
      then Comb r
      else raise TERM_ERR{function = "mk_comb",message = "incompatible types"}
  | mk_comb{Rator,Rand} = list_mk_comb (Rator,[Rand]);

local
val bv0  = Bv 0  val bv1  = Bv 1  val bv2=Bv 2 val bv3 = Bv 3 val bv4 = Bv 4
val bv5  = Bv 5  val bv6  = Bv 6  val bv7=Bv 7 val bv8=Bv 8 val bv9 = Bv 9 
val bv10 = Bv 10 val bv11 = Bv 11 val bv12=Bv 12 val bv13=Bv 13 val bv14=Bv 14
val bv15 = Bv 15 val bv16 = Bv 16 val bv17 = Bv 17 val bv18 = Bv 18 
val bv19 = Bv 19 val bv20 = Bv 20 val bv21 = Bv 21 val bv22 = Bv 22  
val bv23 = Bv 23 val bv24 = Bv 24 val bv25 = Bv 25 val bv26 = Bv 26 
val bv27 = Bv 27 val bv28 = Bv 28 val bv29 = Bv 29 val bv30 = Bv 30
val bv31 = Bv 31 val bv32 = Bv 32 val bv33 = Bv 33 val bv34 = Bv 34
in
fun mk_bv(1) = bv1 | mk_bv(2) = bv2 | mk_bv(3) = bv3 | mk_bv(4) = bv4
  | mk_bv(5) = bv5 | mk_bv(6) = bv6 | mk_bv(7) = bv7 | mk_bv(8) = bv8
  | mk_bv(9) = bv9 | mk_bv(10) = bv10 | mk_bv(11) = bv11 | mk_bv(12) = bv12
  | mk_bv(13) = bv13 | mk_bv(14) = bv14 | mk_bv(15) = bv15 | mk_bv(16) = bv16
  | mk_bv(17) = bv17 | mk_bv(18) = bv18 | mk_bv(19) = bv19 | mk_bv(20) = bv20
  | mk_bv(21) = bv21 | mk_bv(22) = bv22 | mk_bv(23) = bv23 | mk_bv(24) = bv24
  | mk_bv(25) = bv25 | mk_bv(26) = bv26 | mk_bv(27) = bv27 | mk_bv(28) = bv28
  | mk_bv(29) = bv29 | mk_bv(30) = bv30 | mk_bv(31) = bv31 | mk_bv(32) = bv32
  | mk_bv(33) = bv33 | mk_bv(34) = bv34 | mk_bv(n) = Bv(n)
end
(* Make a lambda abstraction. Try for some sharing.   *)
fun mk_abs{Bvar as Fv _, Body} =
      let fun bind (v as Fv _) i = if (v=Bvar) then mk_bv(i) else v
            | bind (Comb{Rator,Rand}) i = Comb{Rator = bind Rator i, 
                                               Rand = bind Rand i}
            | bind (Abs{Bvar = bv, Body = tm}) i = Abs{Bvar = bv, 
                                                       Body = bind tm (i+1)}
            | bind (ty_antiq _) _ = raise TY_ANTIQ_ERR "mk_abs"
            | bind tm _ = tm
      in
      Abs{Bvar = Bvar, Body = bind Body 0}
      end
  | mk_abs _ = raise TERM_ERR{function = "mk_abs",
			      message = "Bvar not a variable"};


fun dest_var (Fv v) = v
  | dest_var _ = raise TERM_ERR{function = "dest_var", message = "not a var"}
fun dest_const (Const c) = c
  | dest_const _ = raise TERM_ERR{function="dest_const",message="not a const"}
fun dest_comb (Comb cmb) = cmb
  | dest_comb _ = raise TERM_ERR{function = "dest_comb",message = "not a comb"}

(* **********************************************************************
 * The pure way to do abstraction destruction. Problem is that you may 
 * get a form of variable capture: consider
 *
 *     Abs{Bvar = v, Body = Comb{Rator = Bv 0, Rand = v}}
 *
 * If you do a dest_abs on this, you will identify Rator and Rand unless 
 * you rename. So what? Well, if you don't rename in this situation, 
 *
 *   mk_abs o dest_abs <> I
 *
 *
 * fun dest_abs(Abs{Bvar,Body}) =
 *      let fun unbind i (v as (Bv j)) = if (i=j) then Bvar else v
 *            | unbind i (Comb{Rator,Rand}) = 
 *                Comb{Rator = unbind i Rator, Rand = unbind i Rand}
 *            | unbind i (Abs{Bvar,Body}) = 
 *                Abs{Bvar=Bvar,Body=unbind (i+1) Body}
 *            | unbind _ tm = tm
 *      in
 *      {Bvar = Bvar, Body = unbind 0 Body}
 *      end
 *  | dest_abs _ = raise TERM_ERR{function = "dest_abs",
 *                                message = "not a lambda abstraction"};
 *****************************************************************************)
local exception CLASH
in
fun dest_abs(Abs{Bvar as Fv{Name,Ty},Body}) =
   let fun dest (v as (Bv j), i) = if (i=j) then Bvar else v
         | dest (v as Fv{Name = s,...}, _) = 
               if (Name = s) then raise CLASH else v
         | dest (Comb{Rator,Rand},i) = Comb{Rator = dest(Rator,i), 
                                            Rand = dest(Rand,i)}
         | dest (Abs{Bvar,Body},i) = Abs{Bvar=Bvar,Body = dest(Body,i+1)}
         | dest (tm,_) = tm
   in {Bvar = Bvar, Body = dest(Body,0)}
      handle CLASH => 
      dest_abs(Abs{Bvar = variant (free_vars Body) Bvar, Body = Body})
   end
  | dest_abs _ = raise TERM_ERR{function = "dest_abs",
                                message = "not a lambda abstraction"}
end;

(* Only for use in peculiar situations *)
fun break_abs(Abs a) = a
  | break_abs _ = raise TERM_ERR{function = "break_abs",
				 message = "not a lambda abstraction"};

(* Discriminators.   *)
fun is_bvar(Bv _) = true 
  | is_bvar _ = false;

fun is_var  (Fv _) = true    | is_var _   = false;
fun is_const(Const _) = true | is_const _ = false;
fun is_comb (Comb _) = true  | is_comb _  = false;
fun is_abs  (Abs _) = true   | is_abs _   = false;

(* Derived operations     *)
fun rator (Comb{Rator, ...}) = Rator
  | rator _ = raise TERM_ERR{function = "rator",message = "not a comb"}

fun rand (Comb{Rand, ...}) = Rand
  | rand _ = raise TERM_ERR{function = "rand",message = "not a comb"}

val bvar = #Bvar o dest_abs;
val body = #Body o dest_abs;


fun dest_term (Fv a) = VAR a
  | dest_term (Const a) = CONST a
  | dest_term (Comb r) = COMB r
  | dest_term (a as Abs _) = LAMB(dest_abs a)
  | dest_term _ = raise TERM_ERR{function = "dest_term",
                                 message = "badly formed term"};


(* Prelogic *)

fun aconv (Comb{Rator = M1, Rand = M2}) (Comb{Rator=N1,Rand=N2}) =
          aconv M1 N1 andalso aconv M2 N2
  | aconv (Abs{Bvar=Fv{Ty=ty1,...}, Body = body1})
          (Abs{Bvar=Fv{Ty=ty2,...}, Body = body2}) = 
                         (ty1=ty2) andalso (aconv body1 body2)
  | aconv tm1 tm2 = (tm1=tm2);



(************************************************************************
 * General term substitution. It's only this complicated because we rename. 
 * Why, if we have dB terms? Because we want to be able to re-parse 
 * prettyprinted terms, i.e., parse o pp = I
 *
 * When we are trying to replace in term M using a substitution theta,
 * we
 * 1. Go through the substitution checking that the types of the redex and
 *    residue are the same. (This could be lazified, but isn't.) 
 * 
 * 2. start with M; try to find a {redex,incoming} record in theta s.t. redex
 *    is aconv with M. Since we are using dB terms, this automatically checks
 *    if M is free (modulo alpha convertibility).
 * 
 * 3a. Suppose this isn't possible; recurse into the structure of M
 * 
 * 3b. Suppose this is possible. Now we have some work to do.
 * 
 *     1. Check that the free_variables of the residue are not bound by the 
 *        current scope. If the scope is empty, there is no need to compute 
 *        FV(residue). Otherwise, we compute the names of all free variables
 *        in residue (if that hasn't been done already), and store them in 
 *        the cell "fn_residue" of the binding. Now we call function "itr" 
 *        which iterates back in the scope, checking for each element "s" of
 *        the scope, whether it is a name of a free variable in residue. If 
 *        it is, we have found a clash. However, our heuristic is to go to 
 *        the "most outlying clash" (this allows a subtle optimization), so we
 *        iterate through the entire scope, keeping track of the index of the 
 *        last clash. If we come out of the scope and there were no clashes, 
 *        then we do the replacement. Otherwise, there was a clash; 
 *        compute all the free variable names that could come in from theta 
 *        (if it hasn't already been done). Then raise the CLASH exception,
 *        with the index of the lambda to propagate to. (This index allows 
 *        us to ignore problems having to do with propagating back to the 
 *        most outlying clash when there are duplicated variables in the 
 *        scope, e.g., \x x.M.)
 * 
 * 3a1. Suppose we were at an "\v.M" and we recursed into M, adding the name 
 *      of v to the scope. We have to handle the CLASH exception.
 * 
 *      - If it is 0, then we are the most outlying clash. We rename the bound
 *        variable to be different than "anything in sight", i.e., the scope 
 *        (of the Abs), all the names of variables (free or bound) in M, and 
 *        the names of all free variables that could possibly come in from 
 *        theta. Now recurse. If there is a CLASH arising from this recursive
 *        call, it cannot possibly be a result of the newly chosen name, 
 *        so simply decrement the index and propagate the CLASH. (This is 
 *        our subtle optimization, since otherwise, the CLASH could have 
 *        been from our newly chosen name, and we would have to again search 
 *        for a new variable name at this node.)
 * 
 *      - if it is not 0, then decrement the index and propagate.
 * 
 *****************************************************************************)

type binding = {redex : term, 
                incoming : {residue:term,
                            fn_residue : string list option ref}};

local
fun frees(v as Fv{Name,...}) free_list = 
       if (mem Name free_list) then free_list else Name::free_list
  | frees(Comb{Rator, Rand}) free_list = frees Rand (frees Rator free_list)
  | frees(Abs{Body,...}) free_list = frees Body free_list
  | frees _ free_list = free_list
in
fun free_var_names tm = frees tm []
end;

(* The numbers of lambdas to go back through. *)
exception CLASH of int;

fun check ([],S) = S
  | check ({redex,residue}::rst, S) = 
         if (type_of redex = type_of residue)
         then check(rst,{redex=redex,
                         incoming={residue=residue,fn_residue=ref NONE}}::S)
         else raise TERM_ERR{function = "subst",
                             message="redex and residue have different types"};

fun subst [] tm = tm
  | subst theta tm =
    let val bindings = check (theta,[])
        val incoming_names = ref (NONE:string list option)
        fun opr {residue, fn_residue as ref NONE} =
               let val L = free_var_names residue
               in fn_residue := SOME L;  L
               end                           
          | opr {residue, fn_residue = ref (SOME L)} = L
        fun mk_incoming() =
             (case (!incoming_names) 
              of (SOME L) => L   (* already computed *)
               | NONE => let val L = rev_itlist (Lib.union o opr o #incoming) 
                                                bindings []
                         in incoming_names := SOME L;  L
                         end)
        fun lookup (tm, scope) =
           let fun check_for_clash({residue,...},[]) = SOME residue
                 | check_for_clash({residue,fn_residue},scope) =
                    let val names = 
                           (case (!fn_residue) 
                            of NONE => let val L = free_var_names residue
                                           val _ = fn_residue := SOME L
                                       in L
                                       end
                             | (SOME L) => L)
                        fun itr([],_,NONE) = SOME residue
                          | itr ([],_, SOME i) = 
                              (mk_incoming();  raise CLASH i)
                          | itr (s::S,n,top) = 
                               itr(S, n+1, if (mem s names)
                                           then (SOME n) else top)
                    in  itr(scope,0,NONE)
                    end
               fun assc [] = NONE
                 | assc ({redex,incoming}::rst) = 
                    if (aconv tm redex) 
                    then check_for_clash(incoming,scope)
                    else (assc rst)
           in
           assc bindings
           end

    fun subs(tm,scope) = 
     case lookup(tm,scope)
       of (SOME residue) => residue
        | NONE => (case tm
                   of (Comb{Rator,Rand}) => Comb{Rator=subs(Rator,scope),
                                                 Rand=subs(Rand,scope)}
                   | (Abs{Bvar as Fv{Name,Ty},Body})
                      => (Abs{Bvar=Bvar,Body=subs(Body,Name::scope)}
                          handle CLASH 0
                          => let
                             val body_names = map (#Name o dest_var) 
                                                  (all_vars Body)
                             val taken = body_names@scope@mk_incoming()
                             val Name' = string_variant taken Name
                             in
                             Abs{Bvar = Fv{Name=Name',Ty=Ty},
                                 Body = subs(Body,Name'::scope)}
                             handle CLASH i => raise CLASH (i-1)
                             (*not due to this abstraction (we just renamed) *)
                             end
                          | CLASH i => raise CLASH(i-1))
                   | _ => tm)
    in 
    subs (tm,[])
    end;


(***************************************************************************
 * Tests
 * Example from LCF code:
 *
 *   theta = { x'/z; x/y }  (* i.e., the parallel replacement of z by x' 
 *                                   and y by x *)
 *   tm = "\x'. ((f y z) (\x. g x' x y z))"
     Term.subst [--`z:bool`-- |-> --`x':bool`--,
                 --`y:bool`-- |-> --`x:bool`--]
      (--`(\x'. f (y:bool) (z:bool) (\x:bool. g x' x y z:bool)):bool->bool`--);
 *    = "\x''. ((f x x') (\x'''. g x'' x''' x x'))"
 *
 *
 *Another tricky one:
 *   theta = { x'/y; x/z }
 *   tm = "\x. (f y z)"
     Term.subst [--`y:bool`-- |-> --`x':bool`--,
                 --`z:bool`-- |-> --`x:bool`--]
           (--`\x:bool. f (y:bool) (z:bool) : bool`--);
 *   = (--`\x''. f x' x`--) : term
 *
 *
    Term.subst [--`y:bool`-- |-> --`x:bool`--]
               (--`\x:bool.\x:bool.(y:bool)`--);
 *  = (--`\x' x''. x`--) : Term.term
 *
 *
 *
    Term.subst [--`x:bool`-- |-> --`z':bool`--,
                --`y:bool`-- |-> --`z:bool`--]
               (--`\z:bool. f (x:bool) (y:bool) (z:bool) : bool`--);
 *  = (--`\z''. f z' z z''`--) : Term.term

 * This example shows that names alone are important, not types.

        subst [--`x:bool`-- |-> --`f (y:bool):bool`--]
              (--`\y :'a. (x:bool)`--) handle e => Raise e;
 * val it = (--`\y'. f y`--) : term

 * cut-down version of Klaus Schneider bug 

      val tm = --`\(p:'a) (q:'a). f (x:'a) (y:'a) : 'a`--;
      val theta = [--`x:'a`-- |-> --`q:'a`--, --`y:'a`-- |-> --`p:'a`--];
      subst theta tm;

 *   val it = (--`\p' q'. f q p`--) : term


 * And reverse, for thoroughness

     val tm = --`\(p:'a) (q:'a). f (y:'a) (x:'a) : 'a`--;
     val theta = [--`x:'a`-- |-> --`q:'a`--,
                  --`y:'a`-- |-> --`p:'a`--];
     subst theta tm;
 *   val it = (--`\p' q'. f p q`--) : term
 *
 * Now a recent one by Elsa Gunter:
 *
     val y  = --`y:bool`--;
     val y' = --`y':bool`--;
     val x  = --`x:bool`--;

     val tm = --`\^y.(^x, \^y'.^y)`--;
     subst [x |-> y] tm;
 *
 * `\y''. y,(\y'. y'')`
 ***************************************************************************)

(****************************************************************************
 * General term substitution without renaming
 *local
 *fun check [] = ()
 *  | check ({redex,residue}::rst) = 
 *      if (type_of redex = type_of residue)
 *      then check rst
 *      else raise TERM_ERR{function = "subst",
 *                          message = "redex has different type than residue"}
 *fun aconv_assoc item =
 *   let fun assc ({redex,residue}::rst) = 
 *            if (aconv item redex)
 *            then SOME residue
 *            else assc rst
 *         | assc _ = NONE
 *   in assc
 *   end
 *in
 *fun subst [] = Lib.I
 *  | subst s =
 *      let val _ = check s
 *          fun subs tm = 
 *             case (aconv_assoc tm s)
 *               of (SOME residue) => residue
 *                | NONE => 
 *                  (case tm
 *                   of (Comb{Rator,Rand}) => Comb{Rator = subs Rator, 
 *                                                 Rand = subs Rand}
 *                    | (Abs{Bvar,Body}) => Abs{Bvar = Bvar, 
 *                                              Body = subs Body}
 *                    | _ => tm)
 *      in subs
 *      end
 *end;
 ****************************************************************************)


fun beta_conv (Comb{Rator = Abs{Body,...}, Rand}) =
   let val fn_rand = ref NONE
       fun free_rand_names() = 
           (case (!fn_rand)
              of (SOME L) => L
               | NONE => let val L = free_var_names Rand
                             val _ = fn_rand := SOME L
                         in  L
                         end)
       fun check([]) = Rand
         | check(scope) =
              let val names = free_rand_names()
                  fun itr([],_,NONE) = Rand
                    | itr ([],_, SOME i) = raise CLASH i
                    | itr (s::S,n,top) = itr(S, n+1, if (mem s names)
                                                     then (SOME n) else top)
              in  itr(scope,0,NONE)
              end
       fun subs ((tm as Bv j),i,scope) = if (i=j) then check scope else tm
         | subs (Comb{Rator,Rand},i,scope) = Comb{Rator=subs(Rator,i,scope),
                                                  Rand=subs(Rand,i,scope)}
         | subs (Abs{Bvar as Fv{Name,Ty},Body},i,scope) = 
                  (Abs{Bvar=Bvar,Body=subs(Body,i+1,Name::scope)}
                   handle CLASH 0
                   => let val body_names = map(#Name o dest_var)(all_vars Body)
                          val taken = body_names@scope@free_rand_names()
                          val Name' = string_variant taken Name
                      in
                      Abs{Bvar=Fv{Name=Name', Ty = Ty}, 
                                  Body = subs(Body,i+1,Name'::scope)}
                      handle CLASH i => raise CLASH(i-1)
                      end
                   | CLASH i => raise CLASH(i-1))
         | subs (tm,_,_) = tm
   in
   subs (Body,0,[])
   end
| beta_conv _ = raise TERM_ERR{function="beta_conv", 
                               message = "not a beta-redex"};


(* *************************************************************************
 * Non-renaming betaconv.
 * fun beta_conv (Comb{Rator = Abs{Body,...}, Rand}) =
 *   let fun bconv (tm as (Bv j)) i = if (i=j) then Rand else tm
 *         | bconv (Comb{Rator,Rand}) i = Comb{Rator = bconv Rator i,
 *                                             Rand = bconv Rand i}
 *         | bconv (Abs{Bvar,Body}) i = Abs{Bvar=Bvar,Body=bconv Body (i+1)}
 *         | bconv tm _ = tm
 *   in
 *   bconv Body 0
 *   end;
 ****************************************************************************)

(* Compute lambda to get thrown out to.  *)
fun capture_depth (v,scope) =
   let fun it ([],_) = ~1  (* aka infinity *)
         | it (s::S,n) = if (s=v) then n else it(S, n+1)
   in it(scope,0)
   end;

exception INST_CLASH of {var : term, scope : term list};

(* Note: different from hol88 inst, in that no "away-from" list required *)
(* Could share consts and free vars *)
fun inst [] tm = tm
  | inst theta tm =
     if (Lib.all (fn {redex,...} => Type.is_vartype redex) theta)
     then let 
          fun inst1 ((bv as Bv _),_,_) = bv
            | inst1 (Const{Name,Ty},scope1,scope2) = 
                     Const{Name=Name, Ty = Type.type_subst theta Ty}
            | inst1 (Fv{Name,Ty},scope1,scope2) = 
                let val v' = Fv{Name=Name,Ty = Type.type_subst theta Ty}
                in if (capture_depth(v',scope2) = ~1)
                   then v'
                   else raise INST_CLASH{var = v', scope = scope2}
                end
            | inst1 (Comb{Rator,Rand},scope1,scope2) = 
                     Comb{Rator = inst1(Rator,scope1,scope2),
                          Rand = inst1(Rand,scope1,scope2)}
            | inst1 (Abs{Bvar as Fv{Name,Ty},Body},scope1,scope2) = 
                let val v = Fv{Name=Name,Ty=Type.type_subst theta Ty}
                    val Bvar' = 
                       if (capture_depth(Bvar,scope1)=capture_depth(v,scope2))
                       then v
                       else variant scope2 v
                in Abs{Bvar=Bvar',Body=inst1(Body,Bvar::scope1,Bvar'::scope2)}
                   handle (e as INST_CLASH{var,scope})
                   => if (var = Bvar')
                      then let val Bvar'' = variant (v::scope) Bvar'
                           in
                           Abs{Bvar = Bvar'',
                               Body = inst1(Body,Bvar::scope1,Bvar''::scope2)}
                           end
                      else raise e
                end
            | inst1 (ty_antiq _, _,_) = raise TY_ANTIQ_ERR "inst"
            | inst1 (_, _,_) = raise TERM_ERR{function = "inst.inst1",
                                              message = "badly formed term"}
          in
          inst1 (tm,[],[])
          end
     else raise TERM_ERR{function="inst",
			 message="redex in type substitution not a variable"};


(* Non renaming version of inst: different from hol88 inst, in that no 
 * "away-from" list required
 *local
 *val check : Type.hol_type subst -> bool = 
 *    Lib.all (fn {redex,...} => Type.is_vartype redex)
 *in
 *fun inst [] tm = tm
 *  | inst theta tm =
 *     if (check theta)
 *     then let fun inst1 (Fv{Name,Ty}) = Fv{Name=Name, 
 *                                           Ty = Type.type_subst theta Ty}
 *                | inst1 (Const{Name,Ty}) = Const{Name=Name, 
 *                                                 Ty=Type.type_subst theta Ty}
 *                | inst1 (Comb{Rator,Rand}) = Comb{Rator = inst1 Rator,
 *                                                  Rand = inst1 Rand}
 *                | inst1 (Abs{Bvar,Body}) = Abs{Bvar = inst1 Bvar,
 *                                               Body = inst1 Body}
 *                | inst1 (bv as Bv _) = bv
 *                | inst1 (ty_antiq _) = raise TY_ANTIQ_ERR "inst"
 *          in
 *          inst1 tm
 *          end
 *     else raise TERM_ERR{function = "inst",
 *			 message = "redex in type substitution not a variable"}
 *end;
 *****************************************************************************)

(*****************************************************************************
 * A term is OK to export if all variables in it have "ok" identifiers,
 * i.e., not genvar'ed. We also go through and accumulate all the free 
 * variables. This doesn't solve the problem completely, though, since another
 * criterion is that a free variable name shouldn't also be the name of a
 * constant. (Why? Because it will get parsed back in as a constant - see
 * thy_yak.)
 *****************************************************************************)
(*****************************************************************************
 * fun ok_to_export tm =
 *   let fun chk (Comb{Rator,Rand},r) = chk(Rand,chk(Rator,r))
 *         | chk (Abs{Bvar = Fv{Name,...},Body},{ok,frees}) = 
 *                chk(Body,{ok = ok andalso (Lib.ok_identifier Name),
 *                          frees = frees})
 *         | chk ((v as Fv{Name,...}),{ok,frees}) =
 *             {ok = ok andalso (Lib.ok_identifier Name),
 *              frees = Lib.union aconv frees [v]}
 *         | chk (_,r) = r
 *   in chk (tm,{ok = true, frees = []})
 *   end
 * 
 * fun rename tm =
 *   let fun rn (Comb{Rator,Rand},E) = 
 *             let val (R1,E') = rn(Rator,E)
 *                 val (R2,E'') = rn(Rand,E')
 *             in (Comb{Rator=R1,Rand=R2},E'')
 *             end
 *         | rn (Abs{Bvar,Body},E) =
 *             let val (bocc,E') = rn(Bvar,E)
 *                 val (body,E'') = rn(Body,E')
 *             in (Abs{Bvar=bocc,Body=body},E'')
 *             end
 *         | rn ((v as Fv{Name,...}),E) =
 *             if (Lib.ok_identifier Name)
 *             then (v,E)
 *             else (Lib.assoc v E, E)
 *                  handle NOT_FOUND 
 *                  => let val v' = variant E v
 *         | rn x = x
 *   in #1(rn (tm,[]))
 *   end
 *****************************************************************************)
end; (* TERM *)
