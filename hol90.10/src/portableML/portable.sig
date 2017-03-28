(* ===================================================================== *)
(* FILE          : portable.sig                                          *)
(* DESCRIPTION   : Signature for SML System dependent functions.         *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 7 October, 1993                                       *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)

(* Share and Enjoy *)

signature Portable_sig =
sig

structure General :
  sig
    exception Bind
    exception Match
    exception Subscript
    exception Size
    exception Overflow
    exception Div
    exception Fail of string

    datatype 'a option = NONE | SOME of 'a

    datatype order = LESS | EQUAL | GREATER

    val <> : ''a * ''a -> bool

    val !  : 'a ref -> 'a
    val := : ('a ref * 'a) -> unit

    val o      : ('b -> 'c) * ('a -> 'b) -> ('a -> 'c)
    val before : ('a * 'b) -> 'a
    val ignore : 'a -> unit

  end

structure Int :
  sig
    eqtype int
    exception Div
    exception Mod
    val * : int * int -> int
    val + : int * int -> int
    val - : int * int -> int
    val < : int * int -> bool
    val <= : int * int -> bool
    val > : int * int -> bool
    val >= : int * int -> bool
    val abs : int -> int
    val div : int * int -> int
    val mod : int * int -> int
    val max : int * int -> int
    val min : int * int -> int
    val ~ : int -> int
  end

structure List :
  sig
    type 'a list
    sharing type list = List.list
    exception Empty
    val null : 'a list -> bool
    val hd : 'a list -> 'a
    val tl : 'a list -> 'a list
    val last : 'a list -> 'a
    val nth : 'a list * int -> 'a
    val take : 'a list * int -> 'a list
    val drop : 'a list * int -> 'a list
    val length : 'a list -> int
    val rev : 'a list -> 'a list
    val @ : 'a list * 'a list -> 'a list
    val concat : 'a list list -> 'a list
    val revAppend : 'a list * 'a list -> 'a list
    val app : ('a -> unit) -> 'a list -> unit
    val map : ('a -> 'b) -> 'a list -> 'b list
    val mapPartial : ('a -> 'b General.option) -> 'a list -> 'b list
    val find : ('a -> bool) -> 'a list -> 'a General.option
    val filter : ('a -> bool) -> 'a list -> 'a list
    val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
    val foldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
    val exists : ('a -> bool) -> 'a list -> bool
    val all : ('a -> bool) -> 'a list -> bool
    val tabulate : int * (int -> 'a) -> 'a list
  end

structure Vector :
  sig
    type 'a vector
    sharing type vector = Vector.vector
    val maxLen : int
(*    val vector : 'a list -> 'a vector *)
    val fromList : 'a list -> 'a vector
    val tabulate : int * (int -> 'a) -> 'a vector
    val length : 'a vector -> int
    val sub : 'a vector * int -> 'a
    val extract : 'a vector * int * int General.option -> 'a vector
    val concat : 'a vector list -> 'a vector
  end

structure Array :
  sig
    type 'a array
    sharing type array = Array.array
    val maxLen : int
    val array : int * '1a -> '1a array
    val tabulate : int * (int -> '1a) -> '1a array
(*    val arrayoflist : '1a list -> '1a array *)
    val fromList : '1a list -> '1a array
    val length : 'a array -> int
    val sub : 'a array * int -> 'a
    val update : 'a array * int * 'a -> unit
    val extract : 'a array * int * int General.option -> 'a Vector.vector
  end

structure ByteArray :
  sig
    eqtype bytearray
    exception Range
    val array : int * int -> bytearray
    val length : bytearray -> int
    val sub : bytearray * int -> int
    val update : bytearray * int * int -> unit
    val extract : bytearray * int * int General.option -> string
  end

structure Ref :
    sig
	val inc : int ref -> unit
	val dec : int ref -> unit
    end

structure Char :
  sig
    eqtype char
    exception Chr
    val chr : int -> char
    val ord : char -> int
    val maxOrd : int
    val < : char * char -> bool
    val <= : char * char -> bool
    val > : char * char -> bool
    val >= : char * char -> bool
  end

structure String :
  sig
    exception Ord
    eqtype string
    sharing type string = String.string
    val maxLen : int 
    val size : string -> int
    val sub : string * int -> Char.char
    val substring : string * int * int -> string
    val concat : string list -> string
    val ^ : string * string -> string
    val str : Char.char -> string
    val ordof : string * int -> int
    val implode : Char.char list -> string
    val explode : string -> Char.char list
    val <= : string * string -> bool
    val < : string * string -> bool
    val >= : string * string -> bool
    val > : string * string -> bool
  end

structure PrettyPrint :
  sig
    type ppstream
    datatype break_style = CONSISTENT | INCONSISTENT
    val mk_ppstream : {consumer : string -> unit,
		       flush : unit -> unit,
		       linewidth : int} -> ppstream
    val dest_ppstream : ppstream -> {consumer : string -> unit,
				     flush : unit -> unit,
				     linewidth : int}
    val add_break : ppstream -> int * int -> unit
    val add_newline : ppstream -> unit
    val add_string : ppstream -> string -> unit
    val begin_block : ppstream -> break_style -> int -> unit
    val end_block : ppstream -> unit
    val clear_ppstream : ppstream -> unit
    val flush_ppstream : ppstream -> unit
    val with_pp : {consumer : string -> unit,
		   flush : unit -> unit,
		   linewidth : int} -> (ppstream -> unit) -> unit
    val install_pp : string list -> string -> (ppstream -> 'a -> unit) -> unit
    val pp_to_string : int -> (ppstream -> 'a -> unit) -> 'a -> string
    val with_ppstream : ppstream
                        -> {add_break:int * int -> unit, 
			    add_string:string -> unit,
			    begin_block:break_style -> int -> unit,
			    end_block:unit -> unit, 
			    add_newline:unit -> unit, 
			    clear_ppstream:unit -> unit,
			    flush_ppstream:unit -> unit}
    val defaultConsumer : unit -> {consumer : string -> unit,
				   linewidth : int, 
				   flush : unit -> unit}
  end

structure Time :
  sig
    eqtype time (* = TIME of {sec:int, usec:int} *)
    val dest_time : time -> {sec:int, usec:int}
    val mk_time : {sec:int, usec:int} -> time
    val timestamp : unit -> time
    val time_eq : time -> time -> bool
    val time_lt : time -> time -> bool
    val time_to_string : time -> String.string
  end

structure Timer :
  sig

    type cpu_timer
    type real_timer

    val totalCPUTimer : unit -> cpu_timer
    val startCPUTimer : unit -> cpu_timer
    val checkCPUTimer : cpu_timer -> {
	    usr : Time.time, sys : Time.time, gc : Time.time
	  }

    val totalRealTimer : unit -> real_timer
    val startRealTimer : unit -> real_timer
    val checkRealTimer : real_timer -> Time.time

  end (* TIMER *)


(*-------------------------------------------------------------------
 * Misc: Things which manipulate the ML environment
 *
 * use - compile/interpret a file directly from source
 * use_stream - compile/interpret a file from input stream
 * load - load a compiled version of the files if they exist, 
 *        otherwise compile them and "use" them.
 *------------------------------------------------------------------*)

(* exception SysError  of (int * string)*)
val use : string -> unit
val use_stream : instream -> unit
val unfiltered_use_stream : instream -> unit
val interp : bool ref

val load : string list -> unit

(*-------------------------------------------------------------------
 * Misc. I/O and OS interaction
 *------------------------------------------------------------------*)

val execute : string * string list -> instream * outstream
val say : string -> unit
val linewidth : int ref
(* val environ : unit -> string list *)
val getEnv : string -> string General.option
val cd : string -> unit
val pwd : unit -> string
val listDir : string -> string list
val ls : unit -> int
val system : string -> int
(* val argv : unit -> string list *)
val getArgs : unit -> string list

val arch : string
val version : {system:string, date:string, version_id:int list}
val sml_banner : string
val file_exists_for_reading : string -> bool
val exit : unit -> unit
val use_and_exit : (exn -> 'a) -> string -> unit

val HOL_base_directory : string

(*---------------------------------------------------------------------
 * Misc. conversions.
 *--------------------------------------------------------------------*)

val int_to_string : int -> String.string
val real_to_string : real -> String.string

(*---------------------------------------------------------------------
 * Exporting the executable. 
 *--------------------------------------------------------------------*)

val export : string -> unit 

val flush_out : outstream -> unit
val input_line : instream -> string
val open_string : string -> instream

val pointer_eq : ''a * ''a -> bool


end

