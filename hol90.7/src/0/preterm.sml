functor PRETERM (structure Term : Term_sig
                 structure Dsyntax : Dsyntax_sig
                 structure Hol_pp : Hol_pp_sig
                 sharing 
                  Hol_pp.Term = Dsyntax.Term = Term) : Preterm_sig =
struct
structure Term = Term;
structure Type = Term.Type;

fun PRETERM_ERR{function,message} = HOL_ERR{origin_structure = "Preterm",
					    origin_function = function,
					    message = message}

datatype preterm = Var of {Name : string, Ty : Type.hol_type}
                 | Const of {Name : string, Ty : Type.hol_type}
                 | Comb of {Rator : preterm, Rand : preterm}
                 | Abs of {Bvar : preterm, Body : preterm}
                 | Constrained of (preterm * Type.hol_type)
                 | Antiq of Term.term



fun to_term (Var n) = Term.Fv n
  | to_term (Const n) = Term.Const n
  | to_term (Comb{Rator,Rand}) = Term.Comb{Rator = to_term Rator,
                                           Rand = to_term Rand}
  | to_term (Abs{Bvar,Body}) = Term.mk_abs{Bvar = to_term Bvar,
                                           Body = to_term Body}
  | to_term (Antiq tm) = tm
  | to_term (Constrained(tm,_)) = to_term tm;

fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom _ = false;

local
fun mk_fun_type ty1 ty2 = Type.Tyapp{Tyop = "fun", Args = [ty1,ty2]}
fun chase (Type.Tyapp{Tyop = "fun", Args = [_,ty]}) = ty
  | chase (Type.Link(ref ty)) = chase ty
  | chase _ = raise PRETERM_ERR{function = "TC.type_of.chase", message = ""}
fun type_of (Var{Ty, ...}) = Ty
  | type_of (Const{Ty, ...}) = Ty
  | type_of (Comb{Rator, ...}) = chase (type_of Rator)
  | type_of (Abs{Bvar,Body}) = Type.Tyapp{Tyop = "fun", 
                                          Args = [type_of Bvar, type_of Body]}
  | type_of (Constrained(_,ty)) = ty
  | type_of (Antiq tm) = Term.type_of tm
in
fun TC (Comb{Rator, Rand}) = 
      (TC Rator; TC Rand;
       Type.unify (type_of Rator)
                  (mk_fun_type (type_of Rand) (Type.new_type_var()))
       handle (e as HOL_ERR{origin_structure="Type", 
                            origin_function="unify",message}) =>
         let val tmp = !Globals.show_types
             val _ = Globals.show_types := true
             val ptm = Lib.say o Hol_pp.term_to_string
             val pty = Lib.say o Hol_pp.type_to_string
             val Rator' = to_term Rator
             val Rand' = to_term Rand
         in
           Lib.say "\nType inference failure: unable to infer a type \
                            \for the application of\n\n";
           ptm Rator';
           Lib.say "\n\n";
           if (is_atom Rator)
           then ()
           else (Lib.say "which has type\n\n";
                 pty(type_of Rator);
                 Lib.say "\n\n");
           Lib.say "to\n\n"; ptm Rand';
           Lib.say "\n\n";
           if (is_atom Rand)
           then ()
           else (Lib.say "which has type\n\n";
                 pty(type_of Rand);
                 Lib.say "\n\n");

           Lib.say ("unification failure message: "^message^"\n");
           Globals.show_types := tmp;
           raise PRETERM_ERR{function="typecheck",message ="failed"}
         end)
  | TC (Abs{Bvar, Body}) = (TC Bvar; TC Body)
  | TC (Constrained(tm,ty)) = 
       (TC tm; Type.unify (type_of tm) ty
       handle (e as HOL_ERR{origin_structure="Type", 
                            origin_function="unify",message}) =>
         let val tmp = !Globals.show_types
             val _ = Globals.show_types := true
             val ptm = Lib.say o Hol_pp.term_to_string
             val pty = Lib.say o Hol_pp.type_to_string
         in
           Lib.say "\nType inference failure: the term\n\n"; 
           ptm (to_term tm);
           Lib.say "\n\n"; 
           if (is_atom tm)
           then ()
           else (Lib.say "which has type\n\n"; 
                 pty (type_of tm);
                 Lib.say "\n\n");
           Lib.say "can not be constrained to be of type\n\n"; 
           pty ty;
           Lib.say ("\n\nunification failure message: "^message^"\n");
           Globals.show_types := tmp;
           raise PRETERM_ERR{function="typecheck",message ="failed"}
         end)
  | TC _ = ()
end;

fun typecheck tm = (TC tm; tm);



(* Non-sharing version *)
fun string_tl str = substring(str,1,(size str - 1))

val ascii_dollar = ordof("$",0)

fun strip_dollar "" = raise PRETERM_ERR{function = "strip_dollar",
					message = "empty string"}
  | strip_dollar s = 
      if (ordof(s,0) = ascii_dollar)
      then (string_tl s)
      else s;

fun shr ty = case (Type.shrink_type ty)
               of Type.NO_CHANGE => ty
                | (Type.CHANGED ty') => ty';

fun typecheck_cleanup (Var{Name,Ty}) = 
     (Term.Fv{Name = strip_dollar Name, Ty = shr Ty}
      handle HOL_ERR{origin_structure="Type",origin_function="shrink_type",...}
      => let val say = Lib.say
             val ptm = Lib.say o Hol_pp.term_to_string
             val tmp = !Globals.show_types
             val _ = Globals.show_types := true
         in say "Unconstrained type variable in the variable\n   ";
            ptm (Term.Fv{Name = Name, Ty = Ty});
            say "\n";
            Globals.show_types := tmp;
            raise PRETERM_ERR{function = "typecheck_cleanup", message =""}
         end)
  | typecheck_cleanup (Const{Name,Ty}) = 
     (Term.Const{Name=strip_dollar Name, Ty = shr Ty}
      handle HOL_ERR{origin_structure="Type",origin_function="shrink_type",...}
      => let val say = Lib.say
             val ptm = Lib.say o Hol_pp.term_to_string
             val tmp = !Globals.show_types
             val _ = Globals.show_types := true
         in say "Unconstrained type variable in the constant\n   ";
            ptm (Term.Const{Name = Name, Ty = Ty});
            say "\n";
            Globals.show_types := tmp;
            raise PRETERM_ERR{function = "typecheck_cleanup", message =""}
         end)
  | typecheck_cleanup (Comb{Rator,Rand}) = 
                       Term.Comb{Rator = typecheck_cleanup Rator,
                                 Rand = typecheck_cleanup Rand}
  | typecheck_cleanup (Abs{Bvar,Body}) =
                       Term.mk_abs{Bvar = typecheck_cleanup Bvar,
                                   Body = typecheck_cleanup Body}
  | typecheck_cleanup (Antiq tm) = tm
  | typecheck_cleanup (Constrained(tm,_)) = typecheck_cleanup tm;


(* Sharing version
local
open Type
fun string_tl str = substring(str,1,(size str - 1))
val ascii_dollar = ordof("$",0)
fun strip_dollar "" = NONE
  | strip_dollar s = 
      if (ordof(s,0) = ascii_dollar)
      then SOME (string_tl s)
      else NONE
fun build_atom tag {Name,Ty} =
   case (strip_dollar Name, Type.shrink_type Ty)
     of (NONE,NO_CHANGE) => NO_CHANGE
      | (NONE, CHANGED ty) => CHANGED(tag{Name = Name, Ty = ty})
      | (SOME name, NO_CHANGE) => CHANGED(tag{Name = name, Ty = Ty})
      | (SOME name, CHANGED ty) => CHANGED(tag{Name = name, Ty = ty})

fun tc_cleanup (Var v) = build_atom Var v
  | tc_cleanup (Const c) = build_atom Const c
  | tc_cleanup (Comb{Rator,Rand}) = 
      (case (tc_cleanup Rator, tc_cleanup Rand)
         of (NO_CHANGE,NO_CHANGE) => NO_CHANGE
          | (CHANGED Rator, NO_CHANGE) => CHANGED(Comb{Rator = Rator, 
                                                       Rand = Rand})
          | (NO_CHANGE, CHANGED Rand) => CHANGED(Comb{Rator = Rator, 
                                                      Rand = Rand})
          | (CHANGED Rator, CHANGED Rand) => CHANGED(Comb{Rator = Rator, 
                                                          Rand = Rand}))
  | tc_cleanup (Abs{Bvar,Body}) = 
      (case (tc_cleanup Bvar, tc_cleanup Body)
         of (NO_CHANGE, NO_CHANGE) => NO_CHANGE
          | (CHANGED v, NO_CHANGE) => CHANGED(Abs{Bvar = v, Body = Body})
          | (NO_CHANGE, CHANGED body) => CHANGED(Abs{Bvar = Bvar, Body = body})
          | (CHANGED v, CHANGED body) => CHANGED(Abs{Bvar = v, Body = body}))
  | tc_cleanup (Antiq tm) = CHANGED tm
  | tc_cleanup (Constrained(tm,_)) = (case(tc_cleanup tm)
                                        of NO_CHANGE => CHANGED tm
                                         | x => x)
in
fun typecheck_cleanup tm = case (tc_cleanup tm)
                             of NO_CHANGE => tm
                              | (CHANGED tm') => tm'
end;
*)


(* For loading from theory files *)
fun preterm_to_term(Var _) = raise PRETERM_ERR{function="preterm_to_term",
                                              message="unconstrained variable"}
  | preterm_to_term(Const{Name,Ty}) = Term.Const{Name=strip_dollar Name,Ty=Ty}
  | preterm_to_term(Constrained(Const{Name,...},ty)) =
            Term.Const{Name=strip_dollar Name,Ty=ty}
  | preterm_to_term(Comb{Rator,Rand}) = Term.Comb{Rator=preterm_to_term Rator,
                                                  Rand=preterm_to_term Rand}
  | preterm_to_term(Abs{Bvar = Constrained(Var{Name,...},ty),Body}) =
               Term.mk_abs{Bvar=Term.Fv{Name=Name,Ty=ty},
                           Body=preterm_to_term Body}
  | preterm_to_term(Constrained(Var{Name,...},ty)) = Term.Fv{Name=Name,Ty=ty}
  | preterm_to_term _ = raise PRETERM_ERR{function="preterm_to_term",
                                          message="badly formed preterm"};

end; (* PRETERM *)
