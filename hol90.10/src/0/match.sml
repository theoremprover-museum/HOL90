(* ===================================================================== *)
(* FILE          : match.sml                                             *)
(* DESCRIPTION   : Implements first order matching for types and terms.  *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


functor MATCH (structure Term : Term_sig) : Match_sig =
struct
structure Term = Term;

open Exception Lib Term;
open Type;

infix 5 |->


val MTY_ERR = HOL_ERR{origin_structure = "Match",
                      origin_function = "match_type",
                              message = ""};
val MTM_ERR = HOL_ERR{origin_structure = "Match",
                      origin_function = "match_term",
                              message = ""};

fun lookup i = Lib.subst_assoc (fn x => x = i);

fun type_reduce (v as Utv _) ty S = 
     (case (lookup v S)
       of NONE => (v |-> ty)::S
        | (SOME residue) => if (residue=ty) then S else raise MTY_ERR)
  | type_reduce (Tyc c1) (Tyc c2) S = if (c1=c2) then S else raise MTY_ERR
  | type_reduce (pat as Tyapp{Tyop = f, Args = args1})
                (ob as  Tyapp{Tyop = g, Args = args2}) S = 
      if (f=g) then Lib.rev_itlist2 type_reduce args1 args2 S
      else raise MTY_ERR
  | type_reduce _  _  _ = raise MTY_ERR;

fun seen v tm theta =
   case (lookup v theta)
     of NONE     => false
      | SOME tm' => aconv tm' tm orelse raise MTM_ERR;

local fun free (Bv i) n = i<n
        | free (Comb{Rator,Rand}) n = free Rator n andalso free Rand n
        | free (Abs{Body,...}) n = free Body (n+1)
        | free _ _ = true
in
fun is_free tm = free tm 0
end;

fun tm_reduce (v as Fv{Ty,...}) tm (tm_theta,ty_theta) =
     if (is_free tm)
      then (if (seen v tm tm_theta) then tm_theta else (v |-> tm)::tm_theta, 
            type_reduce Ty (type_of tm) ty_theta)
       else raise MTM_ERR
  | tm_reduce (Const{Name=s1, Ty=ty1}) 
              (Const{Name=s2, Ty=ty2}) (tm_theta,ty_theta) =
     if (s1=s2) then (tm_theta,type_reduce ty1 ty2 ty_theta) else raise MTM_ERR
  | tm_reduce (Comb{Rator=M1, Rand=M2})
              (Comb{Rator=N1, Rand=N2}) S = tm_reduce M2 N2 (tm_reduce M1 N1 S)
  | tm_reduce (Abs{Bvar=Fv{Ty=ty1,...}, Body=M})
              (Abs{Bvar=Fv{Ty=ty2,...}, Body=N}) (tm_theta,ty_theta) =
        tm_reduce M N (tm_theta,type_reduce ty1 ty2 ty_theta)
  | tm_reduce (Bv i) (Bv j) S = if (i=j) then S else raise MTM_ERR
  | tm_reduce _ _ _ = raise MTM_ERR;


fun remove_ids S =
   rev_itlist (fn (r as {redex,residue}) => fn S =>
                 if (redex=residue) then S else (r::S))
              S [];

fun match_type pat ob = remove_ids(type_reduce pat ob []);

fun match_term pat ob = 
   let val (tm_subst,ty_subst) = tm_reduce pat ob ([],[])
   in ( rev_itlist(fn {redex,residue} => fn S =>
                    let val redex' = inst ty_subst redex
                    in if (redex'=residue) then S else (redex' |-> residue)::S
                    end) tm_subst [], 
        remove_ids ty_subst )
   end;

end; (* MATCH *)
