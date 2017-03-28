signature ML_ext_sig =
 sig
    val WIN_ERR : {function:string, message:string} -> 'a
    val after : ''a list -> ''a list -> ''a list
    val best : ('a * 'a -> bool) -> 'a list -> 'a
    val fail : unit -> 'a
    val front : int -> 'a list -> 'a list
    val merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
    val prefix : ''a list -> ''a list -> bool
    val replicate : 'a -> int -> 'a list
    val tryfirst : ('a -> 'b) -> 'a list -> 'b
end;
