functor SAVE_HOL(Globals : Globals_sig) : Save_hol_sig =
struct

fun SAVE_HOL_ERR{function,message} = HOL_ERR{origin_structure = "Save_hol",
					     origin_function = function,
					     message = message}

(* sml/nj 93
 * fun print_banner date =
 *  ( output(std_out, "\n\n");
 *    output(std_out,
 * "          HHH                 LL\n \
 * \         HHH                  LL\n \
 * \         HHH                   LL\n \
 * \         HHH                    LL\n \
 * \         HHH          OOOO       LL\n \
 * \         HHHHHHH     OO  OO       LL\n \
 * \         HHHHHHH     OO  OO       LLL\n \
 * \         HHH          OOOO        LLLL\n \
 * \         HHH                     LL  LL\n \
 * \         HHH                    LL    LL\n \
 * \         HHH                   LL      LL\n \
 * \         HHH                  LL        LL90."^
 * (Lib.int_to_string Globals.version_number)^"\n\n"^
 * "Created on "^date^"using: " ^ System.version ^"\n\n\n"));
 *
 ************************)

(* sml/nj 102
 * fun print_banner date =
 *  ( output(std_out, "\n\n");
 *    output(std_out,
 * "          HHH                 LL\n \
 * \         HHH                  LL\n \
 * \         HHH                   LL\n \
 * \         HHH                    LL\n \
 * \         HHH          OOOO       LL\n \
 * \         HHHHHHH     OO  OO       LL\n \
 * \         HHHHHHH     OO  OO       LLL\n \
 * \         HHH          OOOO        LLLL\n \
 * \         HHH                     LL  LL\n \
 * \         HHH                    LL    LL\n \
 * \         HHH                   LL      LL\n \
 * \         HHH                  LL        LL90."^
 * (Lib.int_to_string Globals.version_number)^"\n\n"^
 * "Created on "^date^"using: " ^Compiler.version ^"\n\n\n"));
 **************************)

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
\         HHH                  LL        LL90."^
(Lib.int_to_string Globals.version_number)^"\n\n"^
"Created on "^date^"using: " ^ System.version ^"\n\n\n"));


local
val init_fname = "/hol-init.sml"
val local_init_fname = "."^init_fname
fun parse_HOME [] = raise SAVE_HOL_ERR{function = "save_hol.parse_HOME",
                         message = "can not find HOME variable in environment"}
  | parse_HOME (s::rst) =
       case (explode s)
         of ("H"::"O"::"M"::"E"::"="::path) => implode path
          | _ => parse_HOME rst
in
fun save_hol str = 
    let val (I,O) = execute_in_env ("/bin/date",[],[])
	val date = input_line I;
        val _ = close_in I
        val _ = close_out O
    in 
       exportML str;
       print_banner date;
       if (!Globals.use_init_file)
       then if (Lib.file_exists_for_reading local_init_fname)
            then use local_init_fname
            else let val home_init_fname = parse_HOME(System.environ())
                                           ^init_fname
                 in if (Lib.file_exists_for_reading home_init_fname)
                    then use home_init_fname
                    else ()
                 end
       else ()
    end
end;

end; (* SAVE_HOL *)
