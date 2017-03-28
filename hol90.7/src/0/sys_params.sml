(* ===================================================================== *)
(* FILE          : sys_params.sml                                        *)
(* DESCRIPTION   : Contains the system parameters that need to be        *)
(*                 provided at building time.                            *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 29 September, 1992                                    *)
(* ===================================================================== *)

(* Copyright 1992 by AT&T Bell Laboratories *)

functor SYS_PARAMS () : Sys_params_sig =
struct

(* *************************************************************************
 *
 * This module codifies the arguments given to make_hol. The calling 
 * convention for make_hol is:
 * 
 *     make_hol <sml> [-n | -b | -o] [-d <path>]
 * 
 * The default, calling make_hol with no parameters, tells the system to
 * re-use the existing ascii theory files. One must be in hol90.4/src to
 * invoke this. If you aren't there, the "-d" option must be used.
 * 
 *     -o  This is the same as calling the default.
 * 
 *     -n  The "-n" option tells the system to rebuild all its theories. Be
 *         warned that a consequence of this option is that all user theories 
 *         at the site will have to be rebuilt.
 * 
 *     -b  The "-b" option tells the system to build binary theories. This 
 *         is not advised, and some editing of the sys01.sml file is 
 *         necessary to get this approach to work.
 * 
 *     -d <path> This option to make_hol is used to establish the root
 *         directory for hol90. If your current directory at the 
 *         time of calling "make_hol" is not hol90.4/src, then you 
 *         will need to supply the full directory path to the hol90.4 
 *         directory.
 * 
 * The default and the "-n" and "-o" options entail that theory files will
 * be in ascii. This is preferable, since ascii files are portable between
 * architectures and are much smaller than binary theory files.
 ***************************************************************************)

datatype thy_opt = make_binary | make_new_ascii | use_old_ascii


fun last_char str = substring (str, size str - 1, 1);

fun normalize p = 
   if (last_char p = "/")
   then p 
   else (p^"/");

local
fun head_dir wd =
   let val hd_size = (size wd) - 1
   in if last_char wd = "/"
      then wd
      else head_dir (substring (wd, 0, hd_size))
   end
in
fun base() = head_dir (System.Directory.getWD ())
end;

exception MAKE_HOL_FAILED
val argv = System.argv()
fun fail () = (output(std_out, ("\nmake_hol failed: format is\
                  \ \"make_hol <sml> [-n | -b | -o] [-d <path>]\"\n"));
				raise MAKE_HOL_FAILED)

local
fun mem x [] = false | mem x (y::ys) = (x = y) orelse mem x ys
in
val theory_file_option =
    if mem "-b" argv
	then if mem "-o" argv orelse mem "-n" argv
		 then fail()
	     else make_binary
    else if mem "-n" argv
	     then if mem "-o" argv then fail() else make_new_ascii
	 else use_old_ascii
end

fun find_directory [] = base()
  | find_directory (flag::[]) = (case flag of "-d" => fail() | _ => base ())
  | find_directory (flag::(rest as next::_)) =
    (case flag of "-d" => normalize next | _ => find_directory rest)

val HOL_base_directory = find_directory argv


(*
Manual configuration.

One can manually configure the system by 

    a) Setting the values of theory_file_option and HOL_base_directory in
       this file.

    b) By commenting out the code that currently sets these values in
       this file.

    c) By not using the line

           $* < sys01.sml

       in the make_hol shell script. Instead one would invoke sml, then do a
   
           use "sys01.sml";

       After that finished, the rest of the make_hol shell script should be 
       invoked.


Here are some hints for part a.

If you want ascii theory files and you want to rebuild all the
theories anew, you should do

    val theory_file_option = make_new_ascii

If you want binary versions of theory files, you should use

    val theory_file_option = make_binary

If you chose either of the above two options, you will have to remake
all libraries and site theories. If you use binary format you will have
to modify the file sys01.sml too.

If you wish to reuse existing ascii theory files, thereby avoiding
having to remake libraries and local theories, you should use

    val theory_file_option = use_old_ascii

You will need to use the "use_old_ascii" option on all but the first
build when building hol90 on multiple architectures which are all to
share the same theory files.

Warning: the "use_old_ascii" option is not as secure as the other two.
It also may not always be possible when building a new version of hol90
for the first time at your site. SYSTEM THEORY FILES MAY CHANGE BETWEEN
RELEASES.

*)

end (* functor SYS_PARAMS *)
