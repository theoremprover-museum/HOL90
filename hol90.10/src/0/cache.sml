signature Key_sig =
    sig
	type object
	eqtype key
	val key_of : object -> key
    end;

functor CACHE((* structure Lib : Lib_sig *)
	      structure Key : Key_sig) = 
struct
type object = Key.object;
type key = Key.key;

val the_cache = ref ([]: object list);
fun add_object_to_cache ob = the_cache := ob::(!the_cache);
fun same_key k ob = (Key.key_of ob = k)
fun get_object_from_cache k = Lib.first (same_key k) (!the_cache);

local
fun rem_once _ [] L = L
  | rem_once p (a::rst) L = 
      if (p a) 
      then L@rst 
      else rem_once p rst (a::L)
in
fun delete_object_from_cache k = the_cache := rem_once (same_key k) 
                                                       (!the_cache) []
end;

fun delete_cache() = the_cache := [];

fun objects_in_cache() =
    Lib.rev_itlist (Lib.curry (op ::) o Key.key_of) (!the_cache) [];

val is_object_in_cache = Lib.can get_object_from_cache

end; (* CACHE *)
