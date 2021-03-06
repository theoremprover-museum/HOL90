(* ===================================================================== *)
(* FILE          : portable.njsml.1xx.sml                                *)
(* DESCRIPTION   : Structure for SML System dependent functions.         *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 7 October, 1993                                       *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)

(* Share and Enjoy *)

structure Portable : Portable_sig =
struct

(* Set system variables relevant to the interactive mode of hol90 *)

val _ = (Compiler.Control.Print.printLength := 1000;
         Compiler.Control.Print.printDepth := 350;
         Compiler.Control.Print.stringDepth := 250;
         Compiler.Control.Print.signatures := 2);

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure General = General

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Int =
    struct
        open Int
        exception Div = General.Div
        exception Mod = General.Div
    end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure List = List

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Vector = Vector

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Array = Array

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

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
                    case nopt of General.SOME n => n | General.NONE => l - i
                fun bytes j =
                    if (j >= i + n) then []
                    else Array.sub (a,j) :: bytes (j + 1)
            in String.implode (map Char.chr (bytes i))
            end
    end;

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Ref =
    struct
	fun inc cell = cell := !cell + 1
	fun dec cell = cell := !cell - 1
    end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Char = Char

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure String =
    struct
	exception Ord = General.Subscript
	open String
	fun ordof (string,place) = Char.ord(String.sub(string,place))
    end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

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

end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Time =
    struct
	open Time
	val timestamp : unit -> time = now
	val time_to_string : time -> String.string = toString
	fun dest_time t =
	    let val sec = toSeconds t
		val usec = toMicroseconds (t - fromSeconds sec)
	    in
		{sec = sec, usec = usec}
	    end
	fun mk_time {sec,usec} = fromSeconds sec + fromMicroseconds usec
	fun time_eq (t1:time) t2 = (t1 = t2)
	fun time_lt (t1:time) t2 = Time.<(t1,t2)
    end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Timer = Timer;


(*--------------------------------------------------------------------
 * String conversions.
 *-------------------------------------------------------------------*)

val int_to_string = Int.toString
val real_to_string = Real.toString

(*--------------------------------------------------------------------
 * Misc. - IO/Interaction with OS
 *-------------------------------------------------------------------*)

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

fun file_exists_for_reading s =
    OS.FileSys.access(s,[OS.FileSys.A_READ])

fun exit() = OS.Process.exit OS.Process.success

(*--------------------------------------------------------------------
 * Some parameters.
 *-------------------------------------------------------------------*)

val version = Compiler.version
val sml_banner = Compiler.banner 
(* Built-in that doesn't distinguish SunOs from Solaris
val arch = Compiler.architecture;
*)
val arch =
   case getEnv "ARCH"
   of General.SOME s => s
    | General.NONE => Compiler.architecture;

(*--------------------------------------------------------------------
 * Misc. - interactions which manipulate the ML environment
 *-------------------------------------------------------------------*)

val execute = Unix.streamsOf o Unix.execute

fun reap proc = (Unix.reap proc; ()) handle OS.SysErr _ => ();

(* The contents of the following declarations are *)
(* Copyright 1996 by University of Cambridge      *)

val HOL_base_directory =
   case getEnv "HOL_DIR"
   of General.SOME s => s
    | General.NONE => raise General.Fail "HOL_DIR variable not bound"

local

val unix_pid = 0 (* Should be the Unix process number *)

val pipe = HOL_base_directory ^ "/bin/pipe"

val quote_filter = HOL_base_directory ^ "/bin/quote-filter." ^ arch

fun connect_streams (is,os) =
   if (end_of_stream is)
   then IO.flush_out os
   else (output (os,input (is,1)); connect_streams (is,os))

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
       (Compiler.Interact.use_stream is handle e => (tidy_up (); raise e));
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
       (Compiler.Interact.use_stream is handle e => (tidy_up (); raise e));
       tidy_up ()
   end

end;

(* End of University of Cambridge copyright *)

val unfiltered_use_stream = Compiler.Interact.use_stream;

fun use_and_exit print_err filename =
   (use filename; exit ())
   handle e => (print_err e; OS.Process.exit OS.Process.failure);

(* Things behave badly in 109 when Compiler.Control.interp is set to true.
val interp = Compiler.Control.interp;
*)
val interp = ref false;

fun load files = (map use files; ());

(*--------------------------------------------------------------------
 * Exporting the executable.
 *-------------------------------------------------------------------*)

fun export str = (Export.exportML str; ());

(*
val sml = List.last (getArgs ())

fun export {dir,file} = 
    let val exec_file = IO.open_out str
        val _ = case Portable.system ("/bin/mkdir "^dir)
                  of 0 => ()
                   | _ => raise Fail ("can't make directory."^dir)
	val _ = IO.output (exec_file,
			   String.concat
			   ["#!/bin/sh \n\n",
			    sml, " @SMLload=", dir, "/.heap/",file,".",arch,"\n"])
	val _ = IO.close_out exec_file;
	val _ = system ("chmod a+x " ^ file)
	val _ = Compiler.exportML (str^".heap")
    in
       ()
    end
*)

val flush_out = IO.flush_out
val input_line = IO.input_line
val open_string = IO.open_string

fun pointer_eq (x,y) =
    ((System.Unsafe.cast x : int) = (System.Unsafe.cast y : int))


end (* structure Portable *)


exception Io of string;

fun open_out file = IO.open_out file handle OS.SysErr (s,_) => raise Io s;

