(* ===================================================================== *)
(* FILE          : lib.sig                                               *)
(* DESCRIPTION   : Signature for library of useful SML functions.        *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Lib_sig =
sig
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val append : 'a list -> 'a list -> 'a list
  val concat : string -> string -> string
  val equal : ''a -> ''a -> bool
  val ## : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val A : ('a -> 'b) -> 'a -> 'b
  val B : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val I : 'a -> 'a
  val K : 'a -> 'b -> 'a
  val S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val can : ('a -> 'b) -> 'a -> bool
  val assert : ('a -> bool) -> 'a -> 'a
  val tryfind : ('a -> 'b) -> 'a list -> 'b
  val el : int -> 'a list -> 'a
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val all : ('a -> bool) -> 'a list -> bool
  val all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val first : ('a -> bool) -> 'a list -> 'a
  val split_after : int -> 'a list -> 'a list * 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val gather : ('a -> bool) -> 'a list -> 'a list
  val filter : ('a -> bool) -> 'a list -> 'a list
  val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val itlist2 :('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_itlist2 :('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val combine : 'a list * 'b list -> ('a * 'b) list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val split : ('a * 'b) list -> 'a list * 'b list
  val mapfilter : ('a -> 'b) -> 'a list -> 'b list
  val flatten : 'a list list -> 'a list
  exception NOT_FOUND
  exception NO_CHANGE
  val assoc : ''a -> (''a * 'b) list -> 'b
  val assoc1 : ''a -> (''a * 'b) list -> (''a * 'b) option
  val assoc2 : ''a -> ('b * ''a) list -> ('b * ''a) option
  type 'a subst
  val subst_assoc : ('a -> bool) -> 'a subst -> 'a option
  val |-> :('a * 'a) -> {redex:'a, residue:'a}
  val mem : ''a -> ''a list -> bool
  val mk_set : ''a list -> ''a list
  val union : ''a list -> ''a list -> ''a list
  val U : ''a list list -> ''a list
  val set_diff : ''a list -> ''a list -> ''a list
  val subtract : ''a list -> ''a list -> ''a list
  val intersect : ''a list -> ''a list -> ''a list
  val null_intersection : ''a list -> ''a list -> bool
  val set_eq : ''a list -> ''a list -> bool
  val op_mem : ('a -> 'b -> bool) -> 'a -> 'b list -> bool
  val op_union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val op_U : ('a -> 'a -> bool) -> 'a list list -> 'a list
  val op_intersect: ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val for : int -> int -> (int -> 'a) -> 'a list
  val for_se : int -> int -> (int -> 'a) -> unit
  val list_of_array : 'a array -> 'a list
  val int_to_string : int -> string
  val string_to_int : string -> int
  val sort : ('a -> 'a -> bool) -> 'a list -> 'a list
  val int_sort : int list -> int list
  val clean_directory : string -> unit
  val file_exists_for_reading : string -> bool
  val find_path : string list -> string -> string
  val cons_path : string -> string list ref -> unit
  val append_path : string -> string list ref -> unit
  type time
  val timestamp : unit -> time
  val time_eq : time -> time -> bool
  val time_lt : time -> time -> bool
  val exit : unit -> 'a
  val compile : string -> unit
  val interpret : string -> unit
  val fresh_name : string -> unit -> string
  val use_string : string -> unit
  val say : string -> unit
  val quote : string -> string
  val eval_string : string -> unit
  val cd : string -> unit
  val pwd : unit -> string
  val ls : unit -> int
  val words2 : string -> string -> string list
  val front_n_back : 'a list -> ('a list * 'a)
  val funpow : int -> ('a -> 'a) -> 'a -> 'a
end
