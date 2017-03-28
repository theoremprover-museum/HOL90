functor UID () =
struct

fun UID_ERR{function, message} = HOL_ERR{origin_structure = "Uid",
                                         origin_function = function,
                                         message = message};
(* An abstract type of unique ids. *)
abstype uid = ID of {name : string, timestamp : time}
with
  fun mk_uid s = ID{name = s, timestamp = Lib.timestamp()};
  fun re_mk_uid id = ID id;
  fun dest_uid (ID id) = id;

  fun name (ID{name,...}) = name
  fun timestamp(ID{timestamp,...}) = timestamp
  fun eq (ID id1,ID id2) = (id1=id2)
end
end (* UID *)
