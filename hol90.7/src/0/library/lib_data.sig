signature Lib_data_sig =
sig
type lib_id
val new_lib_id :string -> lib_id
val mk_lib_id :{name:string,timestamp:time} -> lib_id
val lib_id_name :lib_id -> string
val lib_id_timestamp :lib_id -> time
val lib_id_eq :lib_id * lib_id -> bool

type lib_data
val dest_lib_data : lib_data -> {lib_id : lib_id,
                                 doc : string,
                                 path : string,
                                 parents : lib_id list,
                                 theories : string list,
                                 code : string list,
                                 help : string list,
                                 loaded : string}

val mk_lib_data : {lib_id : lib_id,
                   doc : string,
                   path : string,
                   parents : lib_id list,
                   theories : string list,
                   code : string list,
                   help : string list,
                   loaded : string} -> lib_data

end;
