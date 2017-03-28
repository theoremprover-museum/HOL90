functor PRETERM (structure Term : Term_sig
                 structure Hol_pp : Hol_pp_sig
                 sharing Hol_pp.Term = Term) : Preterm_sig =
struct
structure Term = Term;
structure Type = Term.Type;
open Lib;

fun PRETERM_ERR{function,message} = 
 Exception.HOL_ERR{origin_structure = "Preterm",
                   origin_function = function,
                   message = message};


datatype preterm = Var   of {Name : string,  Ty : Type.hol_type}
                 | Const of {Name : string,  Ty : Type.hol_type}
                 | Comb  of {Rator: preterm, Rand : preterm}
                 | Abs   of {Bvar : preterm, Body : preterm}
                 | Constrained of preterm * Type.hol_type
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


(*---------------------------------------------------------------------------
 * Type inference for HOL terms. Looks ugly because of error messages, which
 * could be improved, but the algorithm itself is quite simple.
 *---------------------------------------------------------------------------*)
local infix 5 -->
      fun (ty1 --> ty2) = Type.Tyapp{Tyop = "fun", Args = [ty1,ty2]}
      fun chase (Type.Tyapp{Tyop = "fun", Args = [_,ty]}) = ty
        | chase (Type.Link(ref ty)) = chase ty
        | chase _ = raise PRETERM_ERR{function="TC.type_of.chase", message=""}
      fun type_of (Var{Ty, ...}) = Ty
        | type_of (Const{Ty, ...}) = Ty
        | type_of (Comb{Rator, ...}) = chase (type_of Rator)
        | type_of (Abs{Bvar,Body}) = type_of Bvar --> type_of Body
        | type_of (Constrained(_,ty)) = ty
        | type_of (Antiq tm) = Term.type_of tm
in
fun TC tyvars = 
let fun check(Comb{Rator, Rand}) = 
        (check Rator; check Rand;
         Type.unify (type_of Rator) 
                    (type_of Rand --> Lib.state(Lib.next tyvars))
         handle (e as Exception.HOL_ERR{origin_structure="Type", 
                                        origin_function="unify",message})
         => let val tmp = !Globals.show_types
                val _   = Globals.show_types := true
                val ptm = Lib.say o Hol_pp.term_to_string
                val pty = Lib.say o Hol_pp.type_to_string
                val Rator' = to_term Rator
                val Rand'  = to_term Rand
            in
            Lib.say "\nType inference failure: unable to infer a type \
                              \for the application of\n\n";
            ptm Rator';
            Lib.say "\n\n";
            if (is_atom Rator) then ()
            else(Lib.say"which has type\n\n";pty(type_of Rator);Lib.say"\n\n");
            Lib.say "to\n\n"; ptm Rand'; Lib.say "\n\n";
            if (is_atom Rand) then ()
            else(Lib.say"which has type\n\n";pty(type_of Rand);Lib.say"\n\n");
   
            Lib.say ("unification failure message: "^message^"\n");
            Globals.show_types := tmp;
            raise PRETERM_ERR{function="typecheck",message ="failed"}
            end)
      | check (Abs{Bvar, Body}) = (check Bvar; check Body)
      | check (Constrained(tm,ty)) = 
          (check tm; Type.unify (type_of tm) ty
            handle (e as Exception.HOL_ERR{origin_structure="Type", 
                                           origin_function="unify",message}) 
            => let val tmp = !Globals.show_types
                   val _ = Globals.show_types := true
                   val ptm = Lib.say o Hol_pp.term_to_string
                   val pty = Lib.say o Hol_pp.type_to_string
               in
               Lib.say "\nType inference failure: the term\n\n"; 
               ptm (to_term tm); Lib.say "\n\n"; 
               if (is_atom tm) then () 
               else(Lib.say"which has type\n\n";pty(type_of tm);Lib.say"\n\n");
               Lib.say "can not be constrained to be of type\n\n"; 
               pty ty;
               Lib.say ("\n\nunification failure message: "^message^"\n");
               Globals.show_types := tmp;
               raise PRETERM_ERR{function="typecheck",message ="failed"}
               end)
      | check _ = ()
in check
end end;

(*---------------------------------------------------------------------------
 * Post-type inference processing. Currently, this just guesses type 
 * variables for the remaining unconstrained type variables.
 *---------------------------------------------------------------------------*)

local fun string_tl str = substring(str,1, size str - 1)
      val ascii_dollar = ordof("$",0)
in 
fun zap_dollar s = 
 if (s="") then raise PRETERM_ERR{function="zap_dollar",message="empty string"}
  else if (ordof(s,0) = ascii_dollar) then string_tl s 
    else s
end;

local open Type
in
fun tyvars (v as Utv _) vlist = insert v vlist
  | tyvars (v as Stv _) vlist = insert v vlist
  | tyvars (Tyc _) vlist = vlist
  | tyvars (Tyapp{Args,...}) vlist = rev_itlist tyvars Args vlist
  | tyvars (Link(ref ty)) vlist = tyvars ty vlist;
end;


val tyVars =
 let fun union [] S = S
       | union S [] = S
       | union (h::t) S = union t (insert h S)
     fun tyV (Var{Ty,...}) L       = tyvars Ty L
       | tyV (Const{Ty,...}) L     = tyvars Ty L
       | tyV (Comb{Rator,Rand}) L  = tyV Rand(tyV Rator L)
       | tyV (Abs{Bvar,Body}) L    = tyV Body(tyV Bvar L)
       | tyV (Antiq tm) L          = union (Term.type_vars_in_term tm) L
       | tyV (Constrained(tm,_)) L = tyV tm L
 in rev o C tyV []
 end;

local fun askii n = Portable.Char.toString(Char.chr (n + 97));
      fun nonzero 0 = "" | nonzero n = Int.toString n;
      nonfix div mod
      val div = Portable.Int.div and mod = Portable.Int.mod 
in
fun num2tyv m = Type.mk_vartype 
  (Portable.String.concat(["'",askii(mod(m,26)), nonzero(div(m,26))]))
end;


(*---------------------------------------------------------------------------
 * Use the "src" stream to generate new elements, not in "taken", up to 
 * the quantity equal to the length of the list (1st parameter to V). The
 * 2nd parameter to V is just the accumulator, which is not hidden.
 *---------------------------------------------------------------------------*)
fun vary src taken =
  let fun V [] fresh = rev fresh
        | V (_::rst) fresh =
             let val _ = while (mem (state src) taken) do next src
                 val v' = state src before (next src;())
             in V rst (v'::fresh)
             end
  in  V  end;

local open Type
in 
fun shrink_type alist =
  let fun shrink (Link(ref ty)) = shrink ty
        | shrink (Tyapp{Tyop,Args}) = Tyapp{Tyop=Tyop, Args=map shrink Args}
        | shrink (s as Stv _) = assoc s alist
        | shrink ty = ty
  in shrink
end end;

fun listify [] = []
  | listify [x] = [x]
  | listify (x::rst) = (x::", "::listify rst);

fun cleanup tm = 
 let val V = tyVars tm
     val (utvs,stvs) = Lib.partition Term.Type.is_vartype V
     val utv_src = mk_istream (fn x => x+1) 0 num2tyv
     val new_utvs = vary utv_src utvs stvs []
     val _ = Lib.mesg (not(null stvs) andalso !Globals.notify_on_tyvar_guess)
             ("inventing new type variable names: "
               ^String.concat(listify (map Type.dest_vartype new_utvs)))
     val shr = shrink_type (zip stvs new_utvs)
     fun clean(Var{Name,Ty})     = Term.Fv{Name=zap_dollar Name,Ty=shr Ty}
       | clean(Const{Name,Ty})   = Term.Const{Name=zap_dollar Name,Ty=shr Ty}
       | clean(Comb{Rator,Rand}) = Term.Comb{Rator=clean Rator,Rand=clean Rand}
       | clean (Abs{Bvar,Body})  = Term.mk_abs{Bvar=clean Bvar,Body=clean Body}
       | clean (Antiq tm)        = tm
       | clean (Constrained(tm,_)) = clean tm
 in clean tm
 end;

fun typecheck fresh_tyvs tm = (TC fresh_tyvs tm; cleanup tm);

(* For loading from theory files *)
fun preterm_to_term(Var _) = raise PRETERM_ERR{function="preterm_to_term",
                                              message="unconstrained variable"}
  | preterm_to_term(Const{Name,Ty}) = Term.Const{Name=zap_dollar Name,Ty=Ty}
  | preterm_to_term(Constrained(Const{Name,...},ty)) =
            Term.Const{Name=zap_dollar Name,Ty=ty}
  | preterm_to_term(Comb{Rator,Rand}) = Term.Comb{Rator=preterm_to_term Rator,
                                                  Rand=preterm_to_term Rand}
  | preterm_to_term(Abs{Bvar = Constrained(Var{Name,...},ty),Body}) =
               Term.mk_abs{Bvar=Term.Fv{Name=Name,Ty=ty},
                           Body=preterm_to_term Body}
  | preterm_to_term(Constrained(Var{Name,...},ty)) = Term.Fv{Name=Name,Ty=ty}
  | preterm_to_term _ = raise PRETERM_ERR{function="preterm_to_term",
                                          message="badly formed preterm"};

end; (* PRETERM *)
