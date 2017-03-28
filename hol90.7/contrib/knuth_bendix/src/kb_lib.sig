signature KBlib_sig =
  sig
    val iota : int -> int -> int list
    val is_subset : ''a list -> ''a list -> bool
    val split : ('a -> bool) -> 'a list -> 'a list * 'a list
    val lex_gt : (''a -> ''a -> bool) -> ''a list -> ''a list -> bool
    val merge_sort : ('a -> 'a -> bool) -> 'a list -> 'a list
    val multiset_gt : (''a -> ''a -> bool) -> ''a list -> ''a list -> bool
    val permute : 'a list -> 'a list list
  end
