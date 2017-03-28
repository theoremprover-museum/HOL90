signature File_sig =
sig
val get_file_by_name : {reader : instream -> 'a, suffix : string}
                        -> string list  -> string -> {data:'a, path :string}
val get_file_by_key :{reader : instream -> 'a,
                      suffix : string,
                      eq : ('b * 'b) -> bool,
                      key_of : 'a -> 'b,
                      name_of : 'b -> string}
                      -> string list -> 'b -> {data :'a, path :string}
end;
