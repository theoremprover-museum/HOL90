(* ===================================================================== *)
(* FILE          : help.sml                                              *)
(* DESCRIPTION   : The online help facility. I have copied the sed script*)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : December 13, 1991                                     *)
(* ===================================================================== *)

functor HELP(structure Globals : Globals_sig) : Help_sig =
struct

fun HELP_ERR{function,message} = HOL_ERR{origin_structure = "Help",
					 origin_function = function,
					 message = message}

fun find_file s = 
   let fun find [] = raise (HELP_ERR{function = "find_file",
                     message = "Unable to find documentation for \""^s^"\"\n"})
         | find (h::t) = 
             let val fname = h^s^".doc"
             in if (Lib.file_exists_for_reading fname)
                then fname
                else find_file s t
             end
   in find
   end;

fun helper path s = 
   ( (* sml/nj 93 System.Unsafe.CInterface.system *)
     (* sml/nj 102 System.system *)
      System.Unsafe.CInterface.system
        (implode ["/bin/sed -f ",
                  !Globals.HOLdir, "tools/", "doc-to-help.sed ",
                  "'", (find_file s path), "'",
                  " | ",
                  !Globals.output_help, "\n"]);
     ())
   handle e as HOL_ERR _ => Raise e
        | System.Unsafe.CInterface.SysError(i,m) =>
	      Raise (HELP_ERR{function = "help",
             message = "System error: unable to sed the documentation for \""^
                       s^"\" because of: "^m^"\n"});

fun help s = helper (!Globals.help_path) s;


(* If you don't have a lot of memory, the above version of help may not
   spawn a process, i.e., will fail, while this version will always work.
*)
fun help1 s =
   let val instr = open_in (find_file s (!Globals.help_path))
   in
     while (not (end_of_stream instr))
     do output(std_out, input_line instr);
     close_in instr
   end;

end; (* HELP *)
