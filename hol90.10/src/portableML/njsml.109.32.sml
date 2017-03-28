(* ===================================================================== *)
(* FILE          : portable.njsml.1xx.sml                                *)
(* DESCRIPTION   : Structure for SML System dependent functions.         *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 7 October, 1993                                       *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)

(* Share and Enjoy *)

structure Portable = 
struct

(* Set system variables relevant to the interactive mode of hol90 *)

val _ = Compiler.Control.quotation := true;

val _ = (Compiler.Control.Print.printLength := 1000;
         Compiler.Control.Print.printDepth := 350;
         Compiler.Control.Print.stringDepth := 250;
         Compiler.Control.Print.signatures := 2);

structure General = General

structure Int =
    struct
        open Int
        exception Div = General.Div
        exception Mod = General.Div
    end

structure List = List

structure Vector = Vector

structure Array = Array

(* Should check range of integers *)
structure ByteArray =
    struct
        type bytearray = int Array.array (* or Word8Array.array *)
        exception Range
        open Array
        (* The next definition isn't quite right *)
        fun extract (a,i,nopt) =
            let val l = Array.length a
                val n =
                    case nopt of Option.SOME n => n | Option.NONE => l - i
                fun bytes j =
                    if (j >= i + n) then []
                    else Array.sub (a,j) :: bytes (j + 1)
            in String.implode (map Char.chr (bytes i))
            end
    end;

structure Ref =
    struct
	fun inc cell = cell := !cell + 1
	fun dec cell = cell := !cell - 1
    end

structure Char = Char

structure String =
    struct
	exception Ord = General.Subscript
	open String
	fun ordof (string,place) = Char.ord(String.sub(string,place))
	val charof = str o chr
    end

val string_to_int = Int.fromString;
val real_to_string = Real.toString
val implode = String.concat;
val explode = map String.str o String.explode;


structure PrettyPrint =
struct
fun install_pp path s = Compiler.PPTable.install_pp path;

open Compiler.PrettyPrint

fun with_ppstream ppstrm = 
   {add_string=add_string ppstrm, 
    add_break=add_break ppstrm, 
    begin_block=begin_block ppstrm, 
    end_block=fn () => end_block ppstrm, 
    add_newline=fn () => add_newline ppstrm, 
    clear_ppstream=fn () => clear_ppstream ppstrm, 
    flush_ppstream=fn () => flush_ppstream ppstrm}

fun defaultConsumer () =
      {consumer = Compiler.Control.Print.say,
       linewidth = !Compiler.Control.Print.linewidth,
       flush = Compiler.Control.Print.flush}

fun pp_to_string linewidth ppfn ob = 
    let val l = ref ([]:string list)
        fun attach s = l := (s::(!l))
     in with_pp {consumer = attach, linewidth=linewidth, flush = fn()=>()}
                (fn ppstrm =>  ppfn ppstrm ob);
        String.concat(List.rev(!l))
    end
end


structure Time =
    struct
       open Time

      (* Some minor renamings, etc. *)

          val timestamp = Time.now
          val time_to_string = Time.toString
          fun dest_time t =
	    let val sec = Time.toSeconds t
		val usec = Time.toMicroseconds
                           (Time.-(t, Time.fromSeconds sec))
	    in
		{sec = Int32.toString sec, usec = Int32.toString usec}
	    end
          exception MK_TIME
         
          fun mk_time {sec,usec} = 
              let fun padleft s =
                   case String.size s 
                    of 1 => "00000"^s
                     | 2 => "0000"^s
                     | 3 => "000"^s
                     | 4 => "00"^s
                     | 5 => "0"^s
                     | 6 => s
                     | _ => raise MK_TIME
              in
                case (Time.fromString (sec^"."^padleft usec))
                 of Option.NONE => raise MK_TIME
                  | Option.SOME t => t
              end
	  fun time_eq (t1:Time.time) t2 = (t1 = t2)
	  fun time_lt (t1:Time.time) t2 = Time.<(t1,t2)
    end;


structure Timer = Timer;

val say = Compiler.Control.Print.say
val linewidth = Compiler.Control.Print.linewidth

val getEnv = OS.Process.getEnv
val cd = OS.FileSys.chDir
val pwd = OS.FileSys.getDir


fun listDir dir_name =
    let val dirstream = OS.FileSys.openDir dir_name
	fun read_all {dirstream, dir_listing} =
	    let val entry = OS.FileSys.readDir dirstream
	    in
		if entry = "" then List.rev dir_listing
		else read_all {dirstream = dirstream,
			       dir_listing = entry :: dir_listing}
	    end
	val listing = read_all {dirstream = dirstream, dir_listing = []}
	val _ = OS.FileSys.closeDir dirstream
    in listing
    end;

fun system s = OS.Process.system s
fun ls() = system "ls"
val getArgs = SMLofNJ.getArgs
val argv = getArgs;

fun file_exists_for_reading s =
    OS.FileSys.access(s,[OS.FileSys.A_READ])

fun exit() = OS.Process.exit OS.Process.success

val version = Compiler.version
val sml_banner = Compiler.banner 

(*--------------------------------------------------------------------
 * Misc. - interactions which manipulate the ML environment
 *-------------------------------------------------------------------*)

val execute = Unix.streamsOf o Unix.execute

fun reap proc = (Unix.reap proc; ()) handle OS.SysErr _ => ();

val unfiltered_use_stream = Compiler.Interact.useStream;
val unfiltered_use_file = Compiler.Interact.useFile;

fun use_and_exit print_err filename =
   (Compiler.Interact.useFile filename; exit ())
   handle e => (print_err e; OS.Process.exit OS.Process.failure);

val interp = Compiler.Control.interp;

fun load files = app Compiler.Interact.useFile files; 

(*--------------------------------------------------------------------
 * Exporting the executable.
 *-------------------------------------------------------------------*)

fun exportML str = (SMLofNJ.exportML str; ());

exception Io of string;

type instream = TextIO.instream 
type outstream = TextIO.outstream 
val std_out = TextIO.stdOut
val stdin  = TextIO.stdIn
fun open_in file = TextIO.openIn file handle OS.SysErr (s,_) => raise Io s;
fun open_out file = TextIO.openOut file handle OS.SysErr (s,_) => raise Io s;
val output = TextIO.output
fun outputc strm s = output(strm,s)
val close_in = TextIO.closeIn
val close_out = TextIO.closeOut
val flush_out = TextIO.flushOut
val input_line = TextIO.inputLine
val open_string = TextIO.openString
val end_of_stream = TextIO.endOfStream;


fun pointer_eq(x,y) = ((Unsafe.cast x:int) = (Unsafe.cast y:int))

(*---------------------------------------------------------------------------*
 * The contents of the following declarations are                            *
 *                                                                           *
 *      Copyright 1996 by University of Cambridge                            *
 *---------------------------------------------------------------------------*)

local

val unix_pid = 0 (* Should be the Unix process number *)

val pipe = SysParams.HOL_base_directory ^ "bin/pipe"

val quote_filter = SysParams.HOL_base_directory 
                   ^ "bin/quote-filter." 
                   ^ SysParams.arch

fun connect_streams (is,os) =
   if (end_of_stream is)
   then flush_out os
   else (output (os,TextIO.inputN (is,1)); connect_streams (is,os))

fun restore_filename filename s =
   if (String.substring (s,0,10) = "<instream>"
       handle General.Subscript => false)
   then filename ^ String.substring (s,10,String.size s - 10)
   else s

in

(* Resorted to using a tmp file! Sigh ... *)
fun use_stream str =
   let val tmp_file = "/tmp/hol90_use_file." ^ Int.toString unix_pid ^ "." ^
                      Time.toString (Time.now ())
       val tmp = open_out tmp_file
       val _ = (connect_streams (str,tmp); close_out tmp)
       val proc = Unix.execute (pipe,[tmp_file,quote_filter])
       val (is,os) = Unix.streamsOf proc
       fun tidy_up () = (close_in is; reap proc)
   in  close_out os;
       (Compiler.Interact.useStream is handle e => (tidy_up (); raise e));
       tidy_up ();
       OS.Process.system ("/bin/rm " ^ tmp_file);
       ()
   end

fun use filename =
   let val out = !Compiler.Control.Print.out
       val is = (#say out ("[opening " ^ filename ^ "]\n");
                 open_in filename handle e as OS.SysErr (s,_) =>
                 (#say out ("[use failed: " ^ s ^ "]\n"); raise e))
       val _ = close_in is
       val proc = Unix.execute (pipe,[filename,quote_filter])
       val (is,os) = Unix.streamsOf proc
       fun tidy_up () =
          (Compiler.Control.Print.out := out; close_in is; reap proc)
   in  close_out os;
       Compiler.Control.Print.out :=
          {flush = #flush out,say = #say out o restore_filename filename};
       (Compiler.Interact.useStream is handle e => (tidy_up (); raise e));
       tidy_up ()
   end

end;

(*---------------------------------------------------------------------------*
 *  End of University of Cambridge copyright                                 *
 *---------------------------------------------------------------------------*)

datatype frag = datatype SMLofNJ.frag;

end (* structure Portable *)
