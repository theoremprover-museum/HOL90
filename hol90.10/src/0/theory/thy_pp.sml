(* ===================================================================== *)
(* FILE          : thy_pp.sml                                            *)
(* DESCRIPTION   : Prettyprints terms and types to theory files          *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : November 7, 1992                                      *)
(* ===================================================================== *)


functor THY_PP((* structure Lib : Lib_sig *)
	       structure Term : Term_sig
               structure Hol_pp : Hol_pp_sig
               sharing 
                  Term = Hol_pp.Term) : Thy_pp_sig =
struct
structure Term = Term;
open Term;
open Term.Type;

fun THY_PP_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Hol_pp",
		      origin_function = function,
		      message = message}
val space = " "
val comma = ","
val dot = "."
val dollar = "$";

val CONSISTENT = PP.CONSISTENT
val INCONSISTENT = PP.INCONSISTENT;

fun pr_list pfun dfun bfun L =
   let fun pr [] = ()
         | pr [i] = pfun i
         | pr (i::rst) = ( pfun i; dfun(); bfun(); pr rst )
   in  pr L   end;

(* Used in printing out a holsig file *)
fun pp_type_rep ppstrm =
   let val {add_string,add_break,begin_block,end_block,...} = 
              PP.with_ppstream ppstrm
       fun pr(Utv x) = add_string x
         | pr(Tyc x) = add_string x
         | pr(Tyapp{Tyop,Args}) = 
             ( begin_block CONSISTENT 3;
               add_string "(";
               add_string(Tyop^comma);
               add_break(0,0);
               begin_block INCONSISTENT 1;
               add_string"["; 
               pr_list pr (fn () => add_string ",")
                          (fn () => add_break(0,0))
                          Args;
               add_string "]";
               end_block();
              add_string")";
              end_block()
            )
        | pr _ = raise THY_PP_ERR{function = "pp_type_rep",
                                  message = "badly formed type"}
  in  pr
  end;

(*---------------------- Term Pretty Printer -------------------------------*)

fun pp_term ppstrm tm = 
   let val pp_type = Hol_pp.pp_type ppstrm
       val {add_string,add_break,begin_block,end_block,...} = 
              PP.with_ppstream ppstrm
       fun pr_term (Fv {Name,Ty}) = 
            ( add_string "(";
              add_string Name;
              add_string " :";
              pp_type Ty ~1;
              add_string ")"
            )
        | pr_term (Bv i) = add_string (dollar^(Lib.int_to_string i))
        | pr_term (Const {Name,Ty}) = 
            let val ptype = (Term.is_polymorphic Name)
            in
              if ptype then add_string "(" else ();
              add_string Name;
              if ptype
              then (add_string " :"; pp_type Ty ~1; add_string ")")
              else () 
            end
        | pr_term (Abs{Bvar,Body}) = 
            ( add_string "(";
              add_string "\\";
              pr_term Bvar;
              add_string dot;
              add_break(1,0);
              pr_term Body;
              add_string ")"
            )
        | pr_term (Comb{Rator, Rand}) =
           ( add_string "(";
             pr_term Rator;
             add_break(1,0);
             pr_term Rand;
             add_string ")"
           )
        | pr_term _ = raise THY_PP_ERR{function="pr_term",
                                       message="term construction"}
   in
     begin_block INCONSISTENT 0;
     pr_term tm;
     end_block()
   end;


end; (* THY_PP *)
