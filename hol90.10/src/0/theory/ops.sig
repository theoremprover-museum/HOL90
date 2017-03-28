signature Theory_ops_sig =
sig
  structure Theory_data : Theory_data_sig
  structure Theory_io : Theory_io_sig
  structure Theory_cache : Theory_cache_sig
  structure Theory_graph : Theory_graph_sig
  sharing 
     Theory_io.Theory_data = Theory_data

  val grab_ances_theory : string -> Theory_data.theory
  val perform_atomic_theory_op : (unit -> 'a) -> 'a
  val install_new_parent : string * Theory_io.hol_sig -> unit
  val goto_theory : string -> Theory_data.theory_id -> Theory_data.theory
  val export_theory : unit -> unit
  val close : unit -> unit
end;
