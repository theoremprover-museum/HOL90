signature Uid_sig =
sig
type uid
val mk_uid :string -> uid
val re_mk_uid :{name :string, timestamp : time} -> uid
val dest_uid :uid -> {name :string, timestamp : time}
val name : uid -> string
val timestamp : uid -> time
val eq : (uid * uid) -> bool
end;
