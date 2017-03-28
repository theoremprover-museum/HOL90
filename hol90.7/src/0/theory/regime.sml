(* This gives a decomposition of the theory into a hol_sig and a hol_thms. *)
functor REGIME (Theory_data : Theory_data_sig) : Regime_sig =
struct
structure Theory_data = Theory_data;
structure Thm = Theory_data.Thm;

fun REGIME_ERR{function,message} = HOL_ERR{origin_structure = "Regime",
                                           origin_function = function,
                                           message = message};

type type_record = {tyc:Thm.Term.Type.hol_type, arity :int, theory:string}
type term_record = {const:Thm.Term.term, theory:string, place:Thm.Term.fixity};

type hol_sig = { thid: Theory_data.theory_id,
                 parents : Theory_data.theory_id list,
                 type_constants : type_record list,
                 term_constants : term_record list
               };

type hol_thms = { thid: Theory_data.theory_id,
                  axioms : (string * Theory_data.Thm.thm) list,
                  definitions : (string * Theory_data.Thm.thm) list,
                  theorems : (string * Theory_data.Thm.thm) list
                }

val mk_hol_sig = I;
val dest_hol_sig = I;

val mk_hol_thms = Lib.I;
val dest_hol_thms = Lib.I;

fun split_theory(th:Theory_data.theory) =
   ( { thid = Theory_data.theory_id th,
       parents = Theory_data.theory_parents th,
       type_constants = Theory_data.theory_type_constants th,
       term_constants = Theory_data.theory_term_constants th}
     ,
     { thid = Theory_data.theory_id th,
       axioms = Theory_data.theory_axioms th,
       definitions = Theory_data.theory_definitions th,
       theorems = Theory_data.theory_theorems th}
   );

val theory_to_hol_sig = fst o split_theory;

fun mk_theory_from_parts (hsig:hol_sig) (thms:hol_thms) : Theory_data.theory = 
   if (Theory_data.theory_id_eq (#thid hsig, #thid thms))
   then let val thry = Theory_data.mk_theory (#thid hsig)
          val thry1 = itlist Theory_data.add_parent (#parents hsig) thry
          val thry2 = itlist Theory_data.add_type (#type_constants hsig)thry1
          val thry3 = itlist Theory_data.add_term (#term_constants hsig)thry2
          val thry4 = itlist Theory_data.add_axiom (#axioms thms) thry3
          val thry5 = itlist Theory_data.add_definition(#definitions thms)thry4
          val thry6 = itlist Theory_data.add_theorem (#theorems thms) thry5
        in thry6
        end
   else raise REGIME_ERR{function = "mk_theory_from_parts",
                        message = "holsig and thms have different theory_ids"};
end (* REGIME *)
