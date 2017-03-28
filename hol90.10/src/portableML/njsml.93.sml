(* ===================================================================== *)
(* FILE          : portable.njsml.93.sml                                 *)
(* DESCRIPTION   : Structure for SML System dependent functions.         *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 7 October, 1993                                       *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)

(* Share and Enjoy *)

structure Portable : Portable_sig =
struct

(* Set system variables relavent to the interactive mode of hol90 *)

val _ = (System.Control.Print.printLength := 1000;
         System.Control.Print.printDepth := 350;
         System.Control.Print.stringDepth := 250;
         System.Control.Print.signatures := 2);

structure General =
    struct
	exception Bind = Bind
	exception Match = Match
	exception Subscript
	exception Size
	exception Overflow
	exception Div = Div
	exception Fail = Fail

	open Bool

	datatype order = LESS | EQUAL | GREATER

	val op <> = op <>

	val ! = !
	val op := = op :=

	val op o = op o
	val op before = op before
	val ignore = fn _ => ()
    end

structure Int = Integer;

structure List =
    struct
	open List
	open General
	exception Empty
	val hd = fn l => hd l handle Hd => raise Empty
	val tl = fn l => tl l handle Tl => raise Empty
	fun last [] = raise Empty
	  | last [x] = x
	  | last (_::r) = last r

	fun nth (l,n) =
	    let
		fun loop ((e::_),0) = e
		  | loop ([],_) = raise Subscript
		  | loop ((_::t),n) = loop(t,n-1)
	    in
		if n >= 0 then loop (l,n) else raise Subscript
	    end

	fun take (l, n) =
	    let
		fun loop (l, 0) = []
		  | loop ([], _) = raise Subscript
		  | loop ((x::t), n) = x :: loop (t, n-1)
	    in
		if n >= 0 then loop (l, n) else raise Subscript
	    end

	fun drop (l, n) =
	    let
		fun loop (l,0) = l
		  | loop ([],_) = raise Subscript
		  | loop ((_::t),n) = loop(t,n-1)
	    in
		if n >= 0 then loop (l,n) else raise Subscript
	    end

	fun concat [] = []
	  | concat (l::r) = l @ concat r

	fun revAppend ([],l) = l
	  | revAppend (h::t,l) = revAppend(t,h::l)

	fun mapPartial pred l =
	    let
		fun mapp ([], l) = rev l
		  | mapp (x::r, l) = (case (pred x)
					  of SOME y => mapp(r, y::l)
					| NONE => mapp(r, l)
	    (* end case *))
	    in
		mapp (l, [])
	    end

	fun find pred [] = NONE
	  | find pred (a::rest) = if pred a then SOME a else (find pred rest)

	fun filter pred [] = []
	  | filter pred (a::rest) = if pred a then a::(filter pred rest) 
				    else (filter pred rest)

	fun partition pred l =
	    let
		fun loop ([],trueList,falseList) =
		    (rev trueList, rev falseList)
		  | loop (h::t,trueList,falseList) = 
		    if pred h then loop(t, h::trueList, falseList)
		    else loop(t, trueList, h::falseList)
	    in loop (l,[],[])
	    end

	fun foldr f b =
	    let
		fun f2 [] = b
		  | f2 (a::t) = f(a,f2 t)
	    in f2
	    end

	fun foldl f b l =
	    let
		fun f2 ([],b) = b
		  | f2 (a::r,b) = f2(r,f(a,b))
	    in f2 (l,b)
	    end

	fun all pred =
	    let 
		fun f [] = true
		  | f (h::t) = pred h andalso f t
	    in f
	    end

	fun tabulate (len, genfn) = 
	    if len < 0 then raise Size
	    else let
		     fun loop n = if n = len then []
				  else (genfn n)::(loop(n+1))
		 in loop 0
		 end

    end

structure Vector =
    struct
	open Vector
	val maxLen = 33554431
	val fromList = vector
        fun sub (vector,i) =
            Vector.sub (vector,i) handle Subscript => raise General.Subscript
	fun listofvector {start_index,length = 0,vector,list} = list
	  | listofvector {start_index,length,vector,list} =
	    let val new_length = length - 1
	    in listofvector {start_index = start_index,
			    length = new_length,
			    vector = vector,
			    list = Vector.sub(vector,start_index + new_length)
			           :: list}
	    end
	fun extract (a,start_index,lengthopt) =
            let val length =
                   case lengthopt
                   of General.SOME l => l
		    | General.NONE => Vector.length a - start_index
	    in  Vector.vector (listofvector{vector = a,
					    start_index = start_index,
					    length = length,
					    list = []})
	    end
	val concat =
	    fn vector_list => 
	    Vector.vector
	    (fold (fn (vector,list) =>
		      listofvector{vector = vector,
				   start_index = 0,
				   length = Vector.length vector,
				   list = list})
		     vector_list
		     [])
    end

structure Array =
    struct
	open Array
	val maxLen = 33554431
	val fromList = arrayoflist
        fun sub (array,i) =
            Array.sub (array,i) handle Subscript => raise General.Subscript
        fun update (array,i,x) =
            Array.update (array,i,x)
            handle Subscript => raise General.Subscript
	fun listofarray {start_index,length = 0,array,list} = list
	  | listofarray {start_index,length,array,list} =
	    let val new_length = length - 1
	    in listofarray {start_index = start_index,
			    length = new_length,
			    array = array,
			    list = Array.sub(array,start_index + new_length)
			           :: list}
	    end
	fun extract (a,start_index,lengthopt) =
            let val length =
                   case lengthopt
                   of General.SOME l => l
		    | General.NONE => Array.length a - start_index
	    in  Vector.vector (listofarray{array = a,
					   start_index = start_index,
					   length = length,
					   list = []})
	    end
    end

structure ByteArray =
    struct
        open ByteArray
        fun extract (a,i,nopt) =
            let val l = ByteArray.length a
                val n =
                    case nopt of General.SOME n => n | General.NONE => l - i
            in  ByteArray.extract (a,i,n)
            end
    end

structure Ref = Ref;

structure Char =
    struct
	type char = String.string
	exception Chr
	val maxOrd = 255
	open String
    end

structure String =
    struct
	open String
	type string = String.string
	val maxLen = 33554431
	fun str c = c
	val concat = String.implode
	fun substring(s,i,n) =
            String.substring(s,i,n) handle Substring => raise General.Subscript
	fun sub(s,i) =
            String.substring(s,i,1) handle Substring => raise General.Subscript
        fun ordof (s,i) =
            String.ordof (s,i) handle Ord => raise General.Subscript
	exception Ord = General.Subscript
    end

structure PrettyPrint =
struct
open System.PrettyPrint

fun install_pp path s = System.PrettyPrint.install_pp path;

fun with_ppstream ppstrm = 
   {add_string=add_string ppstrm, 
    add_break=add_break ppstrm, 
    begin_block=begin_block ppstrm, 
    end_block=fn () => end_block ppstrm, 
    add_newline=fn () => add_newline ppstrm, 
    clear_ppstream=fn () => clear_ppstream ppstrm, 
    flush_ppstream=fn () => flush_ppstream ppstrm}

fun defaultConsumer () =
      {consumer = System.Control.Print.say,
       linewidth = !System.Control.Print.linewidth,
       flush = System.Control.Print.flush}

end

structure Time =
struct
open System.Timer
val timestamp : unit -> System.Timer.time =
      System.Unsafe.CInterface.c_function "timeofday"

fun time_eq (t1:System.Timer.time) t2 = (t1 = t2)
fun time_lt (t1:System.Timer.time) t2 = System.Timer.earlier(t1,t2)
fun mk_time (t:{sec:int, usec:int}) = System.Timer.TIME t
fun dest_time (System.Timer.TIME t) = t:{sec:int, usec:int}
val time_to_string = System.Timer.makestring
end

structure Timer =
struct
open System.Timer
type cpu_timer = System.Timer.timer
val startCPUTimer = System.Timer.start_timer
fun checkCPUTimer t = 
    {usr = check_timer t, sys = check_timer_sys t, gc = check_timer_gc t}
val init_CPU_time = ref(System.Timer.start_timer())
fun totalCPUTimer () = !init_CPU_time
val init_time = ref(Time.timestamp())
abstype real_timer = Real_time of unit -> Time.time
with
fun startRealTimer () =
    let val time_cell = ref(Time.timestamp())
    in Real_time
	(fn () => System.Timer.sub_time(Time.timestamp(),!time_cell))
    end
fun checkRealTimer (Real_time f) = f ()
fun totalRealTimer () =
    Real_time(fn () => System.Timer.sub_time(Time.timestamp(),!init_time))
end (* abstype *)
end

val say = System.Control.Print.say
val linewidth = System.Control.Print.linewidth

local
fun get_suffix ([],l) = SOME l
  | get_suffix (_,[]) = NONE
  | get_suffix (s::pre,t::l) = if s = t then get_suffix (pre,l) else NONE
fun find_env (var,(s::rst)) =
    (case get_suffix (var,explode s)
	 of NONE => find_env (var,rst)
       | SOME v => SOME (implode v))
  | find_env (_,[]) = NONE
in
fun getEnv str = find_env(explode (str^"="), System.environ())
end
    
val cd = System.Directory.cd
(* Doesn't work with Linux
val pwd = System.Directory.getWD
*)
fun pwd () =
   let val (is,os) = IO.execute ("/bin/pwd",[])
       val dir = input_line is
   in  close_in is; close_out os; String.substring (dir,0,String.size dir - 1)
   end;
val listDir = System.Directory.listDir
fun ls() = System.system "ls"
val system = System.system
val getArgs = System.argv

(* suffix to distinquish hol90s for different architectures. 
   Implode.tl.explode used to get rid of leading "."
*)
val arch =
   case getEnv "ARCH"
   of General.SOME s => s
    | General.NONE =>
     let val s = !System.architecture
     in  String.substring (s,1,String.length s - 1)
     end;

(*--------------------------------------------------------------------
 * Misc. - interactions which manipulate the ML environment
 *-------------------------------------------------------------------*)

val execute = IO.execute

(* The contents of the following declarations are *)
(* Copyright 1996 by University of Cambridge      *)

val HOL_base_directory =
   case getEnv "HOL_DIR"
   of General.SOME s => s
    | General.NONE => raise General.Fail "HOL_DIR variable not bound"

local

val unix_pid = System.Unsafe.CInterface.getpid ();

val pipe = HOL_base_directory ^ "/bin/pipe"

val quote_filter = HOL_base_directory ^ "/bin/quote-filter." ^ arch

fun connect_streams (is,os) =
    if (end_of_stream is)
    then IO.flush_out os
    else (output (os,input (is,1)); connect_streams (is,os))

(* Doesn't work
fun restore_filename filename out =
   let val (is,os) =
          IO.execute ("/bin/sed",["s/<instream>/" ^ filename ^ "/"])
   in  connect_streams (is,out); close_in is; os
   end
*)
fun restore_filename filename out = out

in

(* Resorted to using a tmp file! Sigh ... *)
fun use_stream str =
   let val time = case System.Unsafe.CInterface.gettimeofday ()
                  of System.Timer.TIME x => x
       val tmp_file = "/tmp/hol90_use_file." ^ makestring unix_pid ^ "." ^
                      makestring (#sec time) ^ "." ^ makestring (#usec time)
       val tmp = open_out tmp_file
       val _ = (connect_streams (str,tmp); close_out tmp)
       val (is,os) = IO.execute (pipe,[tmp_file,quote_filter])
   in  close_out os;
       (System.Compile.use_stream is handle e => (close_in is; raise e));
       close_in is;
       System.system ("/bin/rm " ^ tmp_file);
       ()
   end

fun use filename =
   let val out = !System.Print.out
       val is = (output (out,"[opening " ^ filename ^ "]\n");
                 open_in filename handle e as Io s =>
                 (output (out,"[use failed: " ^ s ^ "]\n"); raise e))
       val _ = close_in is
       val (is,os) = IO.execute (pipe,[filename,quote_filter])
       val new_out = restore_filename filename out
       fun tidy_up () =
          (System.Print.out := out; (* close_out new_out; *) close_in is)
   in  close_out os;
       System.Print.out := new_out;
       (System.Compile.use_stream is handle e => (tidy_up (); raise e));
       tidy_up ()
   end

end;

(* End of University of Cambridge copyright *)

val unfiltered_use_stream = System.Compile.use_stream;

val interp = System.Control.interp

fun load files = (map use files; ());

val sml_banner = System.version;

local
    exception OutOfRange
    fun eat_head_whitespace [] = []
      | eat_head_whitespace (cl as char::char_list) =
      if char = " " then eat_head_whitespace char_list else cl
    fun chars_upto_char (char,[],rev_front_chars) =
	(List.rev rev_front_chars,[])
      | chars_upto_char (char,c::tail_chars,rev_front_chars) =
	(if c = char
	     then (List.rev rev_front_chars,eat_head_whitespace tail_chars)
	 else chars_upto_char(char,tail_chars,c::rev_front_chars))
    fun digit c = if String.ord c >= 48 andalso String.ord c <= 57
		      then String.ord c - 48 else raise OutOfRange
    fun chars_to_int (c::cl,(num,rev_num_list)) =
	chars_to_int (cl,
		      (((num * 10) + digit c,rev_num_list)
		       handle OutOfRange =>
			   (0,num::rev_num_list)))
      | chars_to_int ([],(num,rev_num_list)) = List.rev (num::rev_num_list)
    val (system,id_and_date) =
	chars_upto_char(",",String.explode sml_banner,[])
    val (v_id,date) = chars_upto_char (",",id_and_date,[])
    val (_,id) = chars_upto_char (".",v_id,[])
in
val version = {system = String.implode system,
	       version_id = chars_to_int (id,(0,[])),
	       date = String.implode date}
end

(*  ( close_in(open_in s); true ) handle _ => false         *)
fun file_exists_for_reading s =
   System.Unsafe.SysIO.access(s,[System.Unsafe.SysIO.A_READ])
   handle System.Unsafe.CInterface.SystemCall _ => false

fun exit() = System.Unsafe.CInterface.exit 0

fun use_and_exit print_err filename =
   (use filename; exit ())
   handle e => (print_err e; System.Unsafe.CInterface.exit 1)

val int_to_string = makestring : int -> string
val real_to_string = makestring : real -> string

(* ???
val store_hol_in_HOLdir = ref true

fun export str =
    let val dir = if !store_hol_in_HOLdir
		      then !Sys_params.HOL_base_directory ^ "src/"
		  else pwd()
    in
	(exportML (dir^str) before
	 (Timer.init_CPU_time := Timer.startCPUTimer();
	  Timer.init_time := Time.timestamp()))
    end
*)
fun export str = (IO.exportML str; ());

val flush_out = IO.flush_out
val input_line = IO.input_line
val open_string = IO.open_string

fun pointer_eq (x,y) =
    ((System.Unsafe.cast x : int) = (System.Unsafe.cast y : int))


end (* structure Portable *)
