signature Lib_desc_sig =
sig
type lib_id
val new_lib_id :string -> lib_id
val mk_lib_id :{name:string,timestamp:time} -> lib_id
val lib_id_name :lib_id -> string

type lib_desc
val dest_lib_desc : lib_desc -> {lib_id : lib_id,
                                 doc : string,
                                 path : string,
                                 parents : lib_id list,
                                 theories : string list,
                                 code : string list,
                                 help : string list,
                                 loaded : string}

end;
