signature PP_sig =
sig
  type ppstream
  type ppconsumer
  datatype break_style = CONSISTENT | INCONSISTENT

  val mk_consumer : {consumer : string -> unit,
                     linewidth : int,
                     flush : unit -> unit} ->  ppconsumer
  val defaultConsumer : unit -> {consumer : string -> unit,
                                 linewidth : int, 
                                 flush : unit -> unit}
  val mk_ppstream : ppconsumer -> ppstream
  val dest_ppstream : ppstream -> ppconsumer
  val add_break : ppstream -> int * int -> unit
  val add_newline : ppstream -> unit
  val add_string : ppstream -> string -> unit
  val begin_block : ppstream -> break_style -> int -> unit
  val end_block : ppstream -> unit
  val clear_ppstream : ppstream -> unit
  val flush_ppstream : ppstream -> unit
  val with_pp : ppconsumer -> (ppstream -> unit) -> unit
  val install_pp : string list -> (ppstream -> 'a -> unit) -> unit
  val pp_to_string : int -> (ppstream -> 'a -> unit) -> 'a -> string
  val with_ppstream: ppstream
                     -> {add_break:int * int -> unit, 
                         add_newline:unit -> unit,
                         add_string:string -> unit,
                         begin_block:break_style -> int -> unit,
                         clear_ppstream:unit -> unit, 
                         end_block:unit -> unit,
                         flush_ppstream:unit -> unit}
  val pr_list :('a -> unit) -> (unit -> 'b) -> (unit -> 'c) -> 'a list -> unit
end;
