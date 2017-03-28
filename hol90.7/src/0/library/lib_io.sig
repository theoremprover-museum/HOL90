signature Lib_io_sig =
sig
 structure Lib_data : Lib_data_sig
 val get_lib_by_name : string list -> string -> Lib_data.lib_data
 val get_lib_by_uid : string list -> Lib_data.lib_id -> Lib_data.lib_data
 val write_lib_to_disk : (string * Lib_data.lib_data) -> unit
end;
