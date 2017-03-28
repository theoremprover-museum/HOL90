(* Derived syntax for higher order logic *)
functor DSYNTAX (structure Match : Match_sig
                 structure Term : Term_sig
                 structure Lexis: Lexis_sig
                 sharing Match.Term = Term) : Dsyntax_sig =
struct
structure Term = Term;
open Term;

fun DSYNTAX_ERR{function : string, message : string} = 
        HOL_ERR{origin_structure = "Dsyntax",
		origin_function = function,
		message = message};


(*************************************************************************
 * Tries to reuse constants already in symtab, i.e., it doesn't create
 * a new one if it doesn't have to. It could be a little more serious,
 * by caching polymorphic instances, but that would require some serious
 * profiling and other implementation work that I don't have time to get 
 * into now.
 *************************************************************************)
fun get_const_from_symtab (r as {Name,Ty}) =
   let val (c as Const{Ty=ty,...}) = Term.lookup_const Name
   in if (Type.polymorphic ty)
      then if (can (Match.match_type ty) Ty)
           then Const r
           else raise DSYNTAX_ERR{function = "get_const_from_symtab",
                              message = "not a type instance: "^Lib.quote Name}
      else c
   end handle NOT_FOUND 
   => raise DSYNTAX_ERR{function = "mk_const",
                        message = "not in term signature: "^Lib.quote Name};

fun mk_const (r as {Name, Ty = Type.Tyc "num"}) = 
       if (Lexis.is_num_literal Name)
       then Const r
       else get_const_from_symtab r
  | mk_const (r as {Ty = Type.Tyc "string",Name}) = 
       if (Lexis.is_string_literal Name)
       then Const r
       else get_const_from_symtab r
  | mk_const r = get_const_from_symtab r;



(****************************************************************************
 * A bit of forward reference that ought to go, on the next pass of 
 * implementation.
 ****************************************************************************)
fun infix_ty ty1 ty2 = 
    Type.Tyapp{Tyop = "fun", 
               Args = [ty1, Type.Tyapp{Tyop = "fun", Args = [ty1, ty2]}]};

val bool = Type.Tyc "bool";
val b2b2b = infix_ty bool bool
val imp = Term.Const{Name = "==>",Ty = b2b2b};
val conj = Term.Const{Name = "/\\",Ty = b2b2b};
val disj = Term.Const{Name = "\\/",Ty = b2b2b};
val F = Term.Const{Name = "F", Ty = bool};
val neg = Term.Const{Name = "~", 
                     Ty = Type.Tyapp{Tyop="fun",Args=[bool,bool]}}


fun select_ty ty = 
   Type.Tyapp{Tyop = "fun", Args = [Type.Tyapp{Tyop = "fun", 
                                               Args = [ty,bool]},ty]};

(* Derived syntax from theory "min" *)
fun mk_eq{lhs,rhs} = 
   list_mk_comb(mk_const{Name="=",Ty=infix_ty(type_of lhs) bool},[lhs,rhs])
   handle _ => raise DSYNTAX_ERR{function = "mk_eq", 
                                 message = "lhs and rhs have different types"}
fun mk_imp{ant,conseq} = list_mk_comb(imp,[ant,conseq])
                         handle _ => raise DSYNTAX_ERR{function = "mk_imp",
                                              message = "Non-boolean argument"}
fun mk_select(s as {Bvar, Body}) = 
   mk_comb{Rator = mk_const{Name="@",Ty=select_ty (type_of Bvar)},
           Rand = mk_abs s}
   handle _ => raise DSYNTAX_ERR{function="mk_select", message = ""};



fun dest_eq(Comb{Rator = Comb{Rator = Const{Name = "=", ...}, Rand = tm1},
                 Rand = tm2}) = {lhs = tm1, rhs = tm2}
  | dest_eq _ = raise DSYNTAX_ERR{function = "dest_eq",
                                  message = "not an \"=\""};
val lhs = #lhs o dest_eq
and rhs = #rhs o dest_eq

fun dest_imp(Comb{Rator = Comb{Rator = Const{Name = "==>", ...}, Rand = tm1},
                  Rand = tm2}) = {ant = tm1,conseq = tm2}
  | dest_imp(Comb{Rator = Const{Name = "~", ...}, Rand}) = 
        {ant = Rand, conseq = F}
  | dest_imp _ = raise DSYNTAX_ERR{function = "dest_imp",
                                   message = "not an \"==>\""};
fun dest_select(Comb{Rator = Const{Name = "@",...}, 
                     Rand as Abs _}) = dest_abs Rand
  | dest_select _ = raise DSYNTAX_ERR{function = "dest_select",
                                      message = "not a \"@\""};


(* Derived syntax from theory "bool" *)

(* Logic binders *)

local
fun quant_ty ty = Type.Tyapp{Tyop = "fun", 
                              Args = [Type.Tyapp{Tyop = "fun", 
                                                 Args = [ty,bool]},bool]};
fun mk_quant s (a as {Bvar,...}) = 
   mk_comb{Rator = mk_const{Name = s, Ty = quant_ty (type_of Bvar)},
           Rand = mk_abs a}
   handle _ => raise DSYNTAX_ERR{function = "mk_quant", message = "not a "^s}
in
val mk_forall = mk_quant "!"
and mk_exists = mk_quant "?"
end;

fun dest_forall (Comb{Rator = Const{Name = "!",...}, 
                      Rand as Abs _}) = dest_abs Rand
  | dest_forall _ = raise DSYNTAX_ERR{function = "dest_forall",
                                      message = "not a forall"};
fun dest_exists (Comb{Rator = Const{Name = "?",...}, 
                      Rand as Abs _}) = dest_abs Rand
  | dest_exists _ = raise DSYNTAX_ERR{function = "dest_exists",
                                      message = "not an exists"};


(* Negation *)

fun mk_neg trm = mk_comb{Rator = neg, Rand = trm};
fun dest_neg (Comb{Rator = Const{Name = "~",...}, Rand}) = Rand
  | dest_neg _ = raise DSYNTAX_ERR{function = "dest_neg",message="not a neg"};

(* /\  \/ *)

fun mk_conj{conj1,conj2}= list_mk_comb(conj,[conj1,conj2])
                          handle _ => raise DSYNTAX_ERR{function = "mk_conj",
                                             message = "Non-boolean argument"}
and mk_disj{disj1,disj2} = list_mk_comb(disj,[disj1,disj2])
                           handle _ => raise DSYNTAX_ERR{function = "mk_disj",
                                             message = "Non-boolean argument"};

fun dest_conj(Comb{Rator = Comb{Rator = Const{Name = "/\\",...}, Rand = t1}, 
                   Rand = t2}) = {conj1 = t1, conj2 = t2}
  | dest_conj _ = raise DSYNTAX_ERR{function = "dest_conj",
                                    message = "not a conj"}

fun dest_disj(Comb{Rator = Comb{Rator = Const{Name = "\\/",...}, Rand = t1},
                                Rand = t2}) = {disj1 = t1, disj2 = t2}
  | dest_disj _ = raise DSYNTAX_ERR{function = "dest_disj",
                                    message = "not a disj"};

(* Conditional *)
local
fun cond_ty ty = 
   Type.Tyapp{Tyop = "fun",
              Args = [bool, 
                      Type.Tyapp{Tyop = "fun", 
                                 Args = [ty, Type.Tyapp{Tyop = "fun",
                                                        Args = [ty,ty]}]}]}
in
fun mk_cond {cond,larm,rarm} = 
  list_mk_comb(mk_const{Name="COND",Ty=cond_ty(type_of larm)},[cond,larm,rarm])
  handle _ => raise DSYNTAX_ERR{function="mk_cond", message = ""}
end;

fun dest_cond (Comb{Rator=Comb{Rator=Comb{Rator=Const{Name="COND",...},
                                          Rand=b},Rand=t1},Rand=t2}) = 
        {cond = b, larm = t1, rarm = t2}
  | dest_cond _ = raise DSYNTAX_ERR{function = "dest_cond", 
                                    message = "not a cond"};


(* The theory of pairs *)

local
fun prod_ty ty1 ty2 = 
   Type.Tyapp{Tyop = "fun", 
         Args = [ty1, Type.Tyapp{Tyop = "fun", 
                                 Args=[ty2, Type.Tyapp{Tyop="prod",
                                                       Args = [ty1,ty2]}]}]}
in
fun mk_pair{fst, snd} = 
   let val ty1 = type_of fst
       and ty2 = type_of snd
   in list_mk_comb(mk_const{Name = ",", Ty = prod_ty ty1 ty2},[fst,snd])
   end
end;

fun dest_pair(Comb{Rator=Comb{Rator=Const{Name=",",...},Rand=t1},Rand=t2}) =
     {fst = t1, snd = t2}
  | dest_pair _ = raise DSYNTAX_ERR{function="dest_pair",message="not a pair"};


(* Let terms *)
(* ===================================================================== *)
(* Syntax functions for let-terms:                                       *)
(*                                                                       *)
(* dest_let "LET f x" = ("f","x")                                        *)
(* mk_let ("f","x") = "LET f x"                                          *)
(* ===================================================================== *)

fun mk_let{func, arg} =
   let val fty = type_of func
       val c = mk_const{Name = "LET", 
                        Ty = Type.Tyapp{Tyop = "fun",Args = [fty,fty]}}
   in list_mk_comb(c,[func,arg])
   end handle _ => raise DSYNTAX_ERR{function = "mk_let",message = ""};

fun dest_let(Comb{Rator=Comb{Rator=Const{Name="LET",...},Rand=f},Rand=x}) =
               {func = f, arg = x}
  | dest_let _ = raise DSYNTAX_ERR{function = "dest_let",
                                   message = "not a let term"};


(* ===================================================================== *)
(* Syntax functions for lists added [RJB 90.10.24].                      *)
(* ===================================================================== *)

(* mk_cons ("t","[t1;...;tn]") ----> "[t;t1;...;tn]" *)

local
fun cons_ty hty tty = 
    Type.Tyapp{Tyop = "fun",
               Args = [hty,Type.Tyapp{Tyop = "fun", Args = [tty,tty]}]}
in
fun mk_cons{hd, tl} =
   let val hty = type_of hd
       and tty = type_of tl
   in list_mk_comb(mk_const{Name="CONS",Ty=cons_ty hty tty},[hd,tl])
   end
   handle _ => raise DSYNTAX_ERR{function="mk_cons", message = ""}
end;

(* dest_cons "[t;t1;...;tn]" ----> ("t","[t1;...;tn]") *)

fun dest_cons (Comb{Rator = Comb{Rator = Const{Name = "CONS",...},
                                 Rand = h},
                    Rand = t}) = {hd = h, tl = t}
  | dest_cons _ = raise DSYNTAX_ERR{function = "dest_cons",
                                    message = "not a cons"};

val is_cons = can dest_cons;

(* mk_list (["t1";...;"tn"],":ty") ----> "[t1;...;tn]:(ty)list" *)

fun mk_list{els,ty} = 
   itlist (fn h => fn t => mk_cons{hd = h, tl = t})
          els (mk_const{Name="NIL",Ty=Type.mk_type{Tyop="list",Args = [ty]}})
   handle _ => raise DSYNTAX_ERR{function = "mk_list",message = ""};

(* dest_list "[t1;...;tn]:(ty)list" ----> (["t1";...;"tn"],":ty") *)
fun dest_list tm =
   if (is_cons tm)
   then let val {hd,tl} = dest_cons tm 
            val {els,ty} = dest_list tl
        in {els = hd::els, ty = ty}
        end
   else let val {Name = "NIL", Ty = Type.Tyapp{Tyop = "list", Args = [ty]}} = 
                dest_const tm
        in {els = [], ty = ty}
        end handle _ => raise DSYNTAX_ERR{function = "dest_list",
                                          message = "not a list term"};

val is_list = can dest_list;

(* If list_mk_cons were to be implemented it should behave as follows:       *)
(*                                                                           *)
(* list_mk_cons (["h1";...;"hm"],"[t1;...;tn]") ----> "[h1;...;hm;t1;...;tn]"*)
(*                                                                           *)
(* though I don't think it would be used much [RJB 90.10.24].                *)



val is_eq = can dest_eq
val is_imp = can dest_imp
val is_select = can dest_select;
val is_forall = can dest_forall
and is_exists = can dest_exists;
val is_neg  = can dest_neg;
val is_conj = can dest_conj
and is_disj = can dest_disj;
val is_cond = can dest_cond;
val is_pair = can dest_pair;
val is_let = can dest_let;




(* Construction and destruction functions that deal with SML lists *)

(* list_mk_comb defined in term.sml *)
fun list_mk_abs (vars,t) = itlist (fn v => fn b => mk_abs{Bvar = v, Body = b})
                                  vars t;
fun list_mk_imp(antel,conc) = itlist(fn a => fn tm => mk_imp{ant=a,conseq=tm})
                              antel conc;
fun list_mk_exists (vlist,t) = 
   itlist (fn v => fn b => mk_exists{Bvar = v, Body = b}) vlist t;
fun list_mk_forall (vlist,t) = 
   itlist (fn v => fn b => mk_forall{Bvar = v, Body = b}) vlist t;
fun gen_all tm = list_mk_forall (Term.free_vars tm, tm);

val list_mk_conj = end_itlist(fn c1 => fn tm => mk_conj{conj1=c1, conj2=tm})
val list_mk_disj = end_itlist(fn d1 => fn tm => mk_disj{disj1=d1, disj2=tm})
val list_mk_pair = end_itlist(fn a => fn p => mk_pair{fst = a, snd = p});


local
fun dest (Comb{Rator, Rand}) rands = dest Rator (Rand::rands)
  | dest tm rands = (tm,rands)
in
fun strip_comb tm = dest tm []
end;

fun strip_abs tm =
   if (is_abs tm)
   then let val {Bvar,Body} = dest_abs tm
            val (bvs, core) = strip_abs Body
        in (Bvar::bvs, core)
        end
  else ([],tm);

(* Strips leading lambdas off a term, not bothering to adjust indices *)
fun de_abs (Abs{Bvar,Body}) =
        let val (bvs, core) = de_abs Body
        in (Bvar::bvs, core)
        end
  | de_abs tm = ([],tm);
 

fun strip_imp fm =
   if (is_imp fm)
   then let val {ant,conseq} = dest_imp fm
	    val (was,wb) = strip_imp conseq
        in ((ant::was), wb)
        end
   else ([],fm);

fun strip_forall fm =
   if (is_forall fm)
   then let val {Bvar,Body} = dest_forall fm
            val (bvs,core) = strip_forall Body
        in ((Bvar::bvs), core)
        end
   else ([],fm);


fun strip_exists fm =
   if (is_exists fm)
   then let val {Bvar, Body} = dest_exists fm 
            val (bvs,core) = strip_exists Body
        in
        ((Bvar::bvs), core)
        end
   else ([],fm);

fun strip_conj w = 
   if (is_conj w)
   then let val {conj1,conj2} = dest_conj w
        in
        (strip_conj conj1)@(strip_conj conj2)
        end
   else [w];


fun strip_disj w =
   if (is_disj w)
   then let val {disj1,disj2} = dest_disj w 
        in
        (strip_disj disj1)@(strip_disj disj2)
        end
   else [w];

fun strip_pair tm = 
   if (is_pair tm) 
   then let val {fst,snd} = dest_pair tm
            fun dtuple t =
               if (is_pair t)
               then let val{fst,snd} = dest_pair t
                    in (fst :: dtuple snd)
                    end
               else [t]
        in fst::dtuple snd
        end
   else [tm];



(*===========================================================================*)
(* Constructor, destructor and discriminator functions for paired            *)
(* abstractions.                                                             *)
(* [JRH 91.07.17]                                                            *)
(*===========================================================================*)

(*--------------------------------------*)
(* mk_pabs - Makes a paired abstraction *)
(*--------------------------------------*)

local
fun mk_uncurry(xt,yt,zt) =
   mk_const{Name = "UNCURRY",
            Ty = Type.Tyapp{Tyop = "fun",
                       Args = [Type.Tyapp{Tyop = "fun",
                                     Args = [xt, Type.Tyapp{Tyop = "fun",
                                                       Args = [yt,zt]}]},
                               Type.Tyapp{Tyop = "fun",
                                          Args=[Type.mk_type{Tyop = "prod",
                                                        Args=[xt,yt]},
                                                zt]}]}}
fun mpa(varstruct,body) =
   if (is_var varstruct)
   then mk_abs{Bvar = varstruct, Body = body}
   else let val {fst,snd} = dest_pair varstruct
            val cab = mpa(fst,mpa(snd,body))
        in mk_comb{Rator = mk_uncurry(type_of fst, type_of snd, type_of body),
                   Rand = cab}
        end
in
fun mk_pabs{varstruct,body} = 
   mpa(assert is_pair varstruct,body)
   handle _ => raise DSYNTAX_ERR{function ="mk_pabs",message = ""}
end;

(*-------------------------------------------------------------*)
(* dest_pabs - Destroys (possibly multiply) paired abstraction *)
(*-------------------------------------------------------------*)

local
val ucheck = assert (curry (op =) "UNCURRY" o #Name o dest_const)
fun dpa tm =
   let val {Bvar,Body} = dest_abs tm
   in {varstruct = Bvar, body = Body}
   end handle _ => let val {Rator,Rand} = dest_comb tm
                       val _ = ucheck Rator
                       val {varstruct = lv,body} = dpa Rand
                       val {varstruct = rv,body} = dpa body
                   in {varstruct = mk_pair{fst = lv, snd = rv},body = body}
                   end
in
fun dest_pabs tm = 
   let val (pr as {varstruct, ...}) = dpa tm
   in if (is_pair varstruct)
   then pr
   else raise DSYNTAX_ERR{function = "dest_pabs", 
                          message = "not a paired abstraction"}
   end
end;

val is_pabs = can dest_pabs;


(* Miscellaneous *)

(* Search a term for a sub-term satisfying the predicate p. *)
fun find_term p =
   let fun find_tm tm =
      if (p tm)
      then  tm 
      else if (is_abs tm)
           then find_tm (#Body(dest_abs tm))
           else if (is_comb tm)
                then find_tm (#Rator(dest_comb tm))
                     handle _ => find_tm (#Rand(dest_comb tm))
                else raise DSYNTAX_ERR{function = "find_term",message = ""}
   in find_tm
   end;

(* find_terms: (term -> bool) -> term -> term list
 * 
 *  Find all subterms in a term that satisfy a given predicate p.
 *
 * Added TFM 88.03.31							
 *******************************************************************)
fun find_terms p tm =
   let fun accum tl tm =
      let val tl' = if (p tm) then (tm::tl) else tl 
      in if (is_abs tm)
         then accum tl' (#Body(dest_abs tm))
         else if (is_comb tm)
              then accum (accum tl' (#Rator(dest_comb tm))) 
                        (#Rand(dest_comb tm))
              else tl' 
      end
   in accum [] tm
   end;



(* Subst_occs 
 * Put a new variable in tm2 at designated (and free) occurrences of redex.
 * Rebuilds the entire term.
 **************************************************************************)
local
fun splice ({redex,...}:{redex:term,residue:term}) v occs tm2 =
   let fun graft (r as {occs = [], ...}) = r
         | graft {tm, occs, count} =
          if (redex = tm)
          then if (hd occs = count+1)
               then {tm = v, occs = tl occs, count = count+1}
               else {tm = tm, occs = occs, count = count+1}
          else if (is_comb tm)
               then let val {Rator, Rand} = dest_comb tm
                        val {tm = Rator', occs = occs', count = count'} =
                                        graft {tm=Rator,occs=occs,count=count}
                        val {tm = Rand', occs = occs'', count = count''} =
                                        graft {tm=Rand,occs=occs',count=count'}
                    in {tm = mk_comb{Rator = Rator', Rand = Rand'},
                        occs = occs'', count = count''}
                    end
               else if (is_abs tm)
                    then let val {Bvar,Body} = dest_abs tm
                             val {tm, count, occs} =
                                        graft{tm=Body,count=count,occs=occs}
                         in {tm = mk_abs{Bvar = Bvar, Body = tm},
                             count = count, occs = occs}
                         end
                    else {tm = tm, occs = occs, count = count}
   in #tm(graft {tm = tm2, occs = occs, count = 0})
   end

fun rev_itlist3 f L1 L2 L3 base_value =
   let fun rev_it3 (a::rst1) (b::rst2) (c::rst3) base = 
               rev_it3 rst1 rst2 rst3 (f a b c base)
         | rev_it3 [] [] [] base = base
         | rev_it3 _ _ _ _ = raise DSYNTAX_ERR{function = "rev_itlist3",
                                      message = "not all lists have same size"}
   in rev_it3 L1 L2 L3 base_value
   end

val sort = Lib.sort (curry (op <=) : int -> int -> bool)
in
fun subst_occs occ_lists tm_subst tm =
   let val occ_lists' = map sort occ_lists
       val (new_vars,theta) = 
               itlist (fn {redex,residue} => fn (V,T) =>
                         let val v = genvar(type_of redex)
                         in (v::V,  (v |-> residue)::T)
                         end)
                      tm_subst ([],[])
       val template = rev_itlist3 splice tm_subst new_vars occ_lists' tm
   in subst theta template
   end
end;



(* *************************************************************************
 * For restricted binders. Adding a pair "(B,R)" to this list, if "B" is the 
 * name of a binder, and "R" is the name of a constant will enable parsing 
 * of terms with the form 
 *
 *     B <varstruct list>::<restr>. M
 ***************************************************************************)
local
val basic_binders = ["!","?","@","\\"]
val basic_restrictions = 
  zip basic_binders ["RES_FORALL","RES_EXISTS","RES_SELECT","RES_ABSTRACT"]
val restricted_binders = ref basic_restrictions
in
fun binder_restrictions() = !restricted_binders
fun associate_restriction(p as(binder_str,const_name)) = 
   case (assoc1 binder_str (!restricted_binders))
     of NONE =>
         if (Term.is_binder binder_str)
         then if (Term.is_st_term_const const_name)
              then restricted_binders := p::(!restricted_binders)
              else raise DSYNTAX_ERR{function = "restrict_binder",
                 message=Lib.quote const_name^" is not the name of a constant"}
         else raise DSYNTAX_ERR{function = "restrict_binder",
                   message=Lib.quote binder_str^" is not the name of a binder"}

      | (SOME _) => raise DSYNTAX_ERR{function = "restrict_binder",
            message = "Binder "^Lib.quote binder_str^" is already restricted"}

fun delete_restriction binder =
   if (mem binder basic_binders)
   then raise DSYNTAX_ERR{function = "delete_restriction",
            message = Lib.quote binder^" cannot have its restriction deleted"}
   else 
   restricted_binders :=
     Lib.set_diff (!restricted_binders)
                  [(binder,assoc binder(!restricted_binders))]
                  handle Lib.NOT_FOUND
                  => raise DSYNTAX_ERR{function = "delete_restriction",
                             message = Lib.quote binder^" is not restricted"}
end;

end; (* DSYNTAX *)
