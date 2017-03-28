signature Hol_datatype_sig =
sig
 type term
 type fixity
 type thm
 type tactic
  val current : unit -> 
                (string * 
                 {axiom :thm, 
                  case_const:term, case_def:thm, case_cong:thm,
                  constructors:term list,
                  definer:{def:term, fixity:fixity, name:string} -> thm,
                  distinct:thm list, induct_tac:tactic, induction:thm,
                  nchotomy:thm, one_one:thm list, simpls:RW.simpls})  list

  val add_info: (string * 
                 {axiom :thm, 
                  case_const:term, case_def:thm, case_cong:thm,
                  constructors:term list,
                  definer:{def:term, fixity:fixity, name:string} -> thm,
                  distinct:thm list, nchotomy:thm, one_one:thm list,
                  induction:thm, induct_tac:tactic, simpls:RW.simpls})
               -> unit

  val hol_datatype : term frag list
                     -> string * 
                        {axiom:thm, 
                         case_const:term, case_cong:thm,
                         case_def:thm, constructors:term list,
                         definer:{def:term, fixity:fixity, name:string} -> thm,
                         distinct:thm list, induct_tac:tactic, induction:thm,
                         nchotomy:thm, one_one:thm list, simpls:RW.simpls}

  val hol_datatype_tools 
    : thm -> thm -> 
        string * {axiom:thm,
                  case_const:term,
                  case_cong:thm,
                  case_def:thm, 
                  constructors:term list,
                  definer:{def:term, fixity:fixity, name:string} -> thm,
                  distinct:thm list, 
                  induct_tac:tactic, 
                  induction:thm,
                  nchotomy:thm, 
                  one_one:thm list,
                  simpls:RW.simpls}

  val CASES_TAC : tactic
end;
