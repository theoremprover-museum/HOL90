signature Theory_io_sig =
sig
  structure Theory_data : Theory_data_sig
  type hol_sig
  type hol_thms
  val dest_hol_sig : hol_sig -> 
     {thid : Theory_data.theory_id,
     parents : Theory_data.theory_id list,
     type_constants : {tyc:Theory_data.Thm.Term.Type.hol_type,
                       arity :int, theory:string}list,
     term_constants : {const:Theory_data.Thm.Term.term, 
                       theory:string, place:Theory_data.Thm.Term.fixity} list}

  val theory_to_hol_sig : Theory_data.theory -> hol_sig

  (* We want to read either a hol_sig or a whole theory *)
  val get_hol_sig_by_name : string list -> string -> {data:hol_sig,path:string}
  val get_hol_sig_by_uid : string list -> 
                           Theory_data.theory_id -> {data:hol_sig, path:string}
  val get_thms :string list -> 
                Theory_data.theory_id -> {data:hol_thms, path:string}
  val mk_theory : hol_sig -> hol_thms -> Theory_data.theory

  (* But we write a theory out atomically *)
  val put_theory_to_disk : Theory_data.theory -> unit

  (* val theory_exists : string list -> string -> bool *)
end;
