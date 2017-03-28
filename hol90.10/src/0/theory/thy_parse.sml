(* ===================================================================== *)
(* FILE          : thy_parse.sml                                         *)
(* DESCRIPTION   : Implements parsing of simple HOL terms and types.     *)
(*                 Used in parsing theories from disk.                   *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind                                          *)
(* DATE          : November 10, 1992                                     *)
(* ===================================================================== *)


functor THY_PARSE (structure P : sig include PARSER end where type arg = unit
                   structure Term : Term_sig
                   sharing 
                     type P.result = Term.term) : Thy_parse_sig =

struct
structure Term = Term;

fun THY_PARSE_ERR{function,message} = 
    Exception.HOL_ERR{origin_structure = "Thy_parse",
		      origin_function = function,
		      message = message}


fun error (s,_,_) = 
 (Portable.output(Portable.std_out,("Theory term parser error: "^s^"\n"));
  raise THY_PARSE_ERR{function = "first pass of parsing", message = s});

fun theory_term_parser s =
   let val strm = Portable.open_string s
       val lexer = P.makeLexer(fn _ => Portable.input_line strm) 
       val (res,_) = P.parse(0,lexer,error,())
   in Portable.close_in strm; res
   end;



end; (* THY_PARSE *)
