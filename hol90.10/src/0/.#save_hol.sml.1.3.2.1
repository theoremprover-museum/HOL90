structure Save_hol : Save_hol_sig =
struct

open Portable;

fun SAVE_HOL_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Save_hol",
		      origin_function = function,
		      message = message}


fun print_banner date =
 ( output(std_out, "\n\n");
   output(std_out,
"          HHH                 LL\n \
\         HHH                  LL\n \
\         HHH                   LL\n \
\         HHH                    LL\n \
\         HHH          OOOO       LL\n \
\         HHHHHHH     OO  OO       LL\n \
\         HHHHHHH     OO  OO       LLL\n \
\         HHH          OOOO        LLLL\n \
\         HHH                     LL  LL\n \
\         HHH                    LL    LL\n \
\         HHH                   LL      LL\n \
\         HHH                  LL        LL90."^Globals.version_number^"\n\n"^
"Created on "^date^"using: " ^ Portable.sml_banner ^"\n\n\n"));


local
val init_fname = "/hol-init.sml"
val local_init_fname = "."^init_fname

in
fun save_hol str = 
    let val (I,O) = Portable.execute ("/bin/date",[])
	val date = Portable.input_line I;
        val _ = close_in I
        val _ = close_out O
    in 
       Portable.exportML str;
       print_banner date;
       if (!Globals.use_init_file)
       then if (Lib.file_exists_for_reading local_init_fname)
            then Portable.use local_init_fname
            else
		(case Portable.getEnv "HOME"
		     of NONE => () 
		   (*
		    We don't raise the following:
		    raise SAVE_HOL_ERR{function = "save_hol.parse_HOME",
		    message = "can not find HOME variable in environment"}
		    because non-unix systems may not have a HOME env var.
		    *)
		   | SOME home_init =>
			 let val home_init_fname = home_init ^init_fname
			 in if (Lib.file_exists_for_reading home_init_fname)
				then Portable.use home_init_fname
			    else ()
			 end)
       else ()
    end
end;

end; (* SAVE_HOL *)
