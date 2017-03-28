signature Uid_sig =
sig
type uid
val mk_uid :string -> uid
val re_mk_uid :{name :string, timestamp : Portable.Time.time} -> uid
val dest_uid :uid -> {name :string, timestamp : Portable.Time.time}
val name : uid -> string
val timestamp : uid -> Portable.Time.time
val eq : (uid * uid) -> bool
end;
