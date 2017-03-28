structure Lib_data : Lib_data_sig = 
struct

structure Lib_id = UID();
type lib_id = Lib_id.uid;
val new_lib_id = Lib_id.mk_uid
val mk_lib_id = Lib_id.re_mk_uid
val lib_id_name = Lib_id.name
val lib_id_timestamp = Lib_id.timestamp
val lib_id_eq = Lib_id.eq

type lib_data = {lib_id : lib_id,
                 doc : string,
                 path : string,
                 parents : lib_id list,
                 theories : string list,
                 code : string list,
                 help : string list,
                 loaded : string}

val dest_lib_data = Lib.I
val mk_lib_data = Lib.I

end;
