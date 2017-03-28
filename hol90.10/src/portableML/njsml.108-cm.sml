(* ===================================================================== *)
(* FILE          : portable.njsml.108-cm.sml                             *)
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

structure General =
    struct
        open General
	datatype order = LESS | EQUAL | GREATER
    end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Int =
    struct
        open Integer
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

structure Vector =
    struct
        open Vector
        fun extract (v,i,nopt) =
            let val l = Vector.length v
                val n =
                    case nopt of General.SOME n => n | General.NONE => l - i
            in  Vector.extract (v,i,n)
            end
    end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

structure Array =
    struct
        open Array
        fun extract (a,i,nopt) =
            let val l = Array.length a
                val n =
                    case nopt of General.SOME n => n | General.NONE => l - i
            in  Array.extract (a,i,n)
            end
    end

(*--------------------------------------------------------------------
 *
 *-------------------------------------------------------------------*)

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

val int_to_string = Makestring.int
val real_to_string = Makestring.real

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

val execute = IO.execute

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
   let val tmp_file = "/tmp/hol90_use_file." ^ Integer.toString unix_pid ^
                      "." ^ Time.toString (Time.now ())
       val tmp = open_out tmp_file
       val _ = (connect_streams (str,tmp); close_out tmp)
       val (is,os) = execute (pipe,[tmp_file,quote_filter])
   in  close_out os;
       (Compiler.Interact.use_stream is handle e => (close_in is; raise e));
       close_in is;
       OS.Process.system ("/bin/rm " ^ tmp_file);
       ()
   end

fun use filename =
   let val out = !Compiler.Control.Print.out
       val is = (#say out ("[opening " ^ filename ^ "]\n");
                 open_in filename handle e as Io s =>
                 (#say out ("[use failed: " ^ s ^ "]\n"); raise e))
       val _ = close_in is
       val (is,os) = execute (pipe,[filename,quote_filter])
       fun tidy_up () = (Compiler.Control.Print.out := out; close_in is)
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

val interp = Compiler.Control.interp;

(*--------------------------------------------------------------------
 * load attempts to load a binary version of the file if it exists.
 * It does this by setting the current pervasive environment to
 * the current top level environment (layered over the old
 * pervasive environment), then calling CM's "make", which will
 * compile the file in that (current) environment.  The results
 * of executing the compilation unit are added to the
 * top level environment.  We then pick up these results,
 * add them to the (old) top level environment and the pervasive
 * environment is returned to its old value.
 *
 * This seems to work - a miracle.  There is an annoying pause
 * after CM begins its work, as it analyses the pervasive environment.
 * It would be great if the dependency analysis could be skipped
 * altogether
 * 
 * Possible problems: The files (which are normally precompiled
 * library source code modules) got compiled by CM when CM knew about
 * all the modules in the system.  When we are loading them back in 
 * CM only knows about one file at a time.  The above technique will 
 * surely fail if the modules get loaded in the wrong order, but will
 * hopefully work with any acceptable load order.
 *
 * 
 *-------------------------------------------------------------------*)

local 
  open Compiler.Environment 
in

fun load files = 
  let val os = open_out "./.load.cm"
      val _ = output (os,"Group is ")
      val _ = map (fn s => output(os,"\n"^s)) files
      val _ = close_out os
      val _ = CM.make' (CM.cmfile "./.load.cm")
      val new_toplevel = #get topLevelEnvRef ()
      val old_pervasive = #get pervasiveEnvRef ()
      val _ = #set pervasiveEnvRef (layerEnv (new_toplevel,old_pervasive));
      val _ = #set topLevelEnvRef emptyEnv
  in ()
  end 

end; (* local *)

(*--------------------------------------------------------------------
 * Exporting the executable.
 *-------------------------------------------------------------------*)

fun export s = CM.export (s,NONE);

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
