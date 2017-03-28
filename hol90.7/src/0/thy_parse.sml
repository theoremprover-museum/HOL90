(* ===================================================================== *)
(* FILE          : thy_parse.sml                                         *)
(* DESCRIPTION   : Implements parsing of simple HOL terms and types.     *)
(*                 Used in parsing theories from disk.                   *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind                                          *)
(* DATE          : November 10, 1992                                     *)
(* ===================================================================== *)


functor THY_PARSE (structure P : PARSER
                   structure Term : Term_sig
                   sharing 
                     type P.result = Term.term
                   sharing 
                     type P.arg = unit) : Thy_parse_sig =

struct
structure Term = Term;

fun THY_PARSE_ERR{function,message} = 
          HOL_ERR{origin_structure = "Thy_parse",
                  origin_function = function,
                  message = message}


fun error (s,_,_) = (output(std_out,("Theory term parser error: "^s^"\n"));
                     raise THY_PARSE_ERR{function = "first pass of parsing",
				         message = s});

fun theory_term_parser s =
   let val strm = open_string s
       val lexer = P.makeLexer(fn _ => input_line strm) 
       val (res,_) = P.parse(0,lexer,error,())
   in
   res
   end;



end; (* THY_PARSE *)
