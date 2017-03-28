functor CACHE(type object
              eqtype key
              val key_of : object -> key) = 
struct
type object = object;
type key = key;

val the_cache = ref ([]: object list);
fun add_object_to_cache ob = the_cache := ob::(!the_cache);
fun same_key k ob = (key_of ob = k)
fun get_object_from_cache k = first (same_key k) (!the_cache);

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

fun objects_in_cache() = rev_itlist (curry (op ::) o key_of) (!the_cache) [];

val is_object_in_cache = can get_object_from_cache

end; (* CACHE *)
