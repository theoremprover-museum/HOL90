signature PPTheory_sig =
sig
  structure Thm:Thm_sig 
    val pp_theory_sig : Portable.PrettyPrint.ppstream 
                        -> {name : string,
                            parents : string list,
                            types     : {Arity:int, Name:string} list,
                            constants : Thm.Term.term list,
                            axioms    : (string * Thm.thm) list,
                            definitions: (string * Thm.thm) list,
                            theorems  : (string * Thm.thm) list} -> unit

    val pp_theory_struct : Portable.PrettyPrint.ppstream 
                           -> {name      : string,
                               parents   : string list,
                               types     : {Arity:int, Name:string} list,
                               constants : Thm.Term.term list,
                               axioms     :(string * Thm.thm) list,
                               definitions:(string * Thm.thm) list,
                               theorems   :(string * Thm.thm) list} -> unit

end;
