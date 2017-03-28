signature Regime_sig =
sig
structure Theory_data : Theory_data_sig
type hol_sig
type hol_thms
val dest_hol_sig : hol_sig 
 -> { thid : Theory_data.theory_id,
      parents : Theory_data.theory_id list,
      type_constants : {tyc:Theory_data.Thm.Term.Type.hol_type, 
                        arity :int, theory:string} list,
      term_constants : {const:Theory_data.Thm.Term.term, theory:string, 
                        place:Theory_data.Thm.Term.fixity} list }
val mk_hol_sig 
   : { thid : Theory_data.theory_id,
       parents : Theory_data.theory_id list,
       type_constants : {tyc:Theory_data.Thm.Term.Type.hol_type, 
                         arity :int, theory:string} list,
       term_constants : {const:Theory_data.Thm.Term.term, theory:string, 
                         place:Theory_data.Thm.Term.fixity} list }  -> hol_sig

val dest_hol_thms : hol_thms -> 
                   { thid : Theory_data.theory_id,
                     axioms : (string * Theory_data.Thm.thm) list,
                     definitions : (string * Theory_data.Thm.thm) list,
                     theorems : (string * Theory_data.Thm.thm) list }
val mk_hol_thms : {  thid : Theory_data.theory_id,
                     axioms : (string * Theory_data.Thm.thm) list,
                     definitions : (string * Theory_data.Thm.thm) list,
                     theorems : (string * Theory_data.Thm.thm) list }
                  -> hol_thms
                   
val split_theory : Theory_data.theory -> (hol_sig * hol_thms)
val mk_theory_from_parts : hol_sig -> hol_thms -> Theory_data.theory
val theory_to_hol_sig : Theory_data.theory -> hol_sig
end;
