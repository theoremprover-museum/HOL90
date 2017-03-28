signature Theory_cache_sig =
sig
type object
eqtype key
val add_object_to_cache : object -> unit
val get_object_from_cache : key -> object
val delete_object_from_cache : key -> unit
val delete_cache : unit -> unit
val objects_in_cache : unit -> key list
val is_object_in_cache : key -> bool
end;
