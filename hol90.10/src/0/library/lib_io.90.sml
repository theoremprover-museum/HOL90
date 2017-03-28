(* Makes parsers and prettyprinters for ".hol_lib" files. *)

functor LIB_IO (structure File : File_sig
                structure Lib_parse : PARSER
                structure Lib_data : Lib_data_sig 
                sharing type Lib_parse.arg = unit
                sharing type
                  Lib_parse.result = Lib_data.lib_data) : Lib_io_sig =
struct
structure Lib_data = Lib_data


fun LIB_IO_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Lib_io",
		      origin_function = function,
		      message = message};

val lib_suffix = ".hol_lib";


(* Parsing library files *)
fun lib_error (s,_,_) = 
   (Portable.output(Portable.std_out,"library parser error: "^s^"\n");
    raise LIB_IO_ERR{function = "parse_lib", message = s});

fun read_lib istrm =
   let val lexer = Lib_parse.makeLexer(fn _ => Portable.input_line istrm) 
       val (res,_) = Lib_parse.parse(0,lexer,lib_error,())
   in res
   end;

fun get_lib_by_name path =
   #data o File.get_file_by_name{reader = read_lib,
                                 suffix = lib_suffix} path;

fun get_lib_by_uid path =
   #data o File.get_file_by_key{reader = read_lib,
                                suffix = lib_suffix,
                                eq = Lib_data.lib_id_eq,
                                key_of = #lib_id o Lib_data.dest_lib_data,
                                name_of = Lib_data.lib_id_name} path;


(* Pretty printing of library files *)

(* Print a list of items.

       pfun = print_function
       dfun = delim_function
       bfun = break_function
*)
fun pr_list pfun dfun bfun =
   let fun pr [] = ()
         | pr [i] = pfun i
         | pr (i::rst) = ( pfun i; dfun(); bfun(); pr rst )
   in pr
   end;

                                    
fun write_lib(ostm, {lib_id,doc,path,parents,theories,code,help,loaded}) =
   let val ppstrm = PP.mk_ppstream
                       {linewidth=70,consumer=Portable.outputc ostm,
                        flush=fn() => Portable.flush_out ostm}
       val {add_string,add_break,begin_block,end_block,
            add_newline,flush_ppstream,...} = PP.with_ppstream ppstrm
       val bbc = begin_block PP.CONSISTENT
       val bbi = begin_block PP.INCONSISTENT
       val eb = end_block
       val S = add_string 
       fun lparen() = S "("
       fun rparen() = S ")"
       fun comma() = S ","
       fun lbracket() = S "["
       fun rbracket() = S "]"
       fun lbrace() = S "{"
       fun rbrace() = S "}"
       fun space() = add_break(1,0)
       val nl = add_newline
       fun pr_sml_list f L = 
          ( bbi 1;lbracket();pr_list f comma space L;rbracket();eb())
       fun pp_lib_id lib_id = 
          let val n = Lib_data.lib_id_name lib_id
              and {sec,usec} =
                   Portable.Time.dest_time(Lib_data.lib_id_timestamp lib_id)
          in
            bbi 1;
            lparen();S n;comma();space();
                     S (Lib.int_to_string sec);comma();space();
                     S (Lib.int_to_string usec);
            rparen();eb()
          end
       fun add_lib_id lib_id =
          ( bbc 0;S "lib_id =";space();pp_lib_id lib_id;eb())
       fun add_doc doc_string =
          ( bbc 0;S "doc =";space();S (Lib.quote doc_string);eb())
       fun add_path path =
          ( bbc 0;S "path =";space();S path;eb())
       fun add_parents lib_id_list = 
          ( bbc 0;S "parents =";space();pr_sml_list pp_lib_id lib_id_list;
            eb())
       fun pr_string_list field str_list =
          ( bbc 0;S (field^" =");space();pr_sml_list S str_list;
            eb())
       val add_theories = pr_string_list "theories"
       val add_code  = pr_string_list "code"
       val add_help = pr_string_list "help"
(* This should be done by pattern matching against characters, but that
   is not compatible with pre100 versions of sml-nj.*)
       fun embed_quote {char_list = [], result_string} = result_string
	 | embed_quote {char_list = ch::char_list, result_string} =
	   if ch = Portable.List.hd (Portable.String.explode "\"")
	       then embed_quote {char_list = char_list,
				 result_string = result_string^"\\\""}
	   else embed_quote {char_list = char_list,
			     result_string =
			     result_string^(Portable.String.str ch)}
       fun add_loaded code_string =
          ( bbc 0;S "loaded =";space();
            S (Lib.quote (embed_quote {char_list = explode code_string,
				       result_string = ""}));
           eb())
   in
     bbc 0;
     add_lib_id lib_id;
     nl();
     add_doc doc;
     nl();
     add_path path;
     nl();
     add_parents parents;
     nl();
     add_theories theories;
     nl();
     add_code code;
     nl();
     add_help help;
     nl();
     add_loaded loaded;
     nl();
     eb();flush_ppstream()
   end;


fun write_lib_to_disk (path,lib) =
   let val ldata = Lib_data.dest_lib_data lib
       val lib_id = #lib_id ldata
       val name = Lib_data.lib_id_name lib_id
       val file = path^name^lib_suffix
       val ostm = Portable.open_out file 
                  handle _ => raise LIB_IO_ERR{function="write_file_to_disk",
                             message = "unable to write file "^Lib.quote file}
   in write_lib(ostm,ldata) handle e => (Portable.close_out ostm; raise e);
      Portable.close_out ostm
   end;
end;


