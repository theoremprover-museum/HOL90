(* ===================================================================== *)
(* FILE          : parse.sml                                             *)
(* DESCRIPTION   : Implements parsing of HOL terms and types.            *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


functor PARSE (structure P : ARG_PARSER
               structure Parse_support : Parse_support_sig
               sharing
                 P.Parse_support = Parse_support
               sharing 
                 type P.result = Parse_support.parse
               sharing 
                 type P.arg = unit) : Parse_sig =

struct
structure Parse_support = Parse_support
structure Preterm = Parse_support.Preterm
structure Term = Parse_support.Preterm.Term;

fun PARSE_ERR{function,message} = HOL_ERR{origin_structure = "Parse",
					  origin_function = function,
					  message = message}

local
fun T [] ol ml = (ol, rev ml) |
    T ((ANTIQUOTE  x)::rst) ol ml = T rst (ol^"^") (x::ml) |
    T ((QUOTE s)::rst) ol ml = T rst (ol^s) ml
in
fun format (q:'a frag list) = T q "" []
end;

fun error (s,_,_) = (output(std_out,("HOL parser error: "^s^"\n"));
                     raise PARSE_ERR{function = "first pass of parsing",
				     message = s});

(* Performs the first pass, parsing into preterms. *)
fun p (ol_frag_list:Term.term frag list) =
   let val _ = Term.Type.reset_type_num()
       val (s,antiq_list) = format ol_frag_list
       val strm = open_string s
       val lexer = P.makeLexer(fn _ => input_line strm) 
                              (ref antiq_list : Term.term list ref)
       val (res,_) = P.parse(0,lexer,error,())
   in res
   end;


(* string to preterm (also types, via ty_antiq) *)
fun ps s =
   let val _ = Term.Type.reset_type_num()
       val strm = open_string s
       val lexer = P.makeLexer(fn _ => input_line strm) 
                              (ref [] : Term.term list ref)
       val (res,_) = P.parse(0,lexer,error,())
   in res
   end;


(* Parsing of terms *)
(* val term_parser = Preterm.typecheck_cleanup o Preterm.typecheck o p; *)

fun preterm_parser frag_list =
  (Globals.in_type_spec := NONE;
   case (p frag_list)
     of (Parse_support.PTM ptm) => ptm
      | _ => raise PARSE_ERR{function = "preterm_parser",
			     message = "Not a preterm."});

fun string_to_preterm s =
  (Globals.in_type_spec := NONE;
   case (ps s)
     of (Parse_support.PTM ptm) => ptm
      | _ => raise PARSE_ERR{function = "string_to_preterm",
			     message = "Not a preterm."});

fun term_parser frag_list =
  (Globals.in_type_spec := NONE;
   case (p frag_list)
     of (Parse_support.PTM ptm) => 
                Preterm.typecheck_cleanup(Preterm.typecheck ptm)
      | _ => raise PARSE_ERR{function = "term_parser",
			     message = "Not a term."});

fun -- frag_list _ = term_parser frag_list handle e => Raise e;

(* val string_to_term = Preterm.typecheck_cleanup o Preterm.typecheck o ps; *)
fun string_to_term s =
  (Globals.in_type_spec := NONE;
   case (ps s)
     of (Parse_support.PTM ptm) => 
                Preterm.typecheck_cleanup(Preterm.typecheck ptm)
      | _ => raise PARSE_ERR{function = "string_to_term",
			     message = "Not a term."});


(* Parsing of types *)

fun type_parser frag_list =
  (Globals.in_type_spec := NONE;
   case (p frag_list)
     of (Parse_support.TY ty) => ty
      | _ => raise PARSE_ERR{function = "type_parser",
			     message = "Not a type."});

fun == frag_list _ = (type_parser frag_list) handle e => Raise e;

fun string_to_type s =
  (Globals.in_type_spec := NONE;
   case (ps s)
     of (Parse_support.TY ty) => ty
      | _ => raise PARSE_ERR{function = "string_to_type",
			     message = "Not a type."});


(* Parsing of type specifications *)
fun colon s = ":"^s;

fun type_spec_parser (QUOTE s :: rst) =
     (Globals.in_type_spec := SOME "";
      case ((p (QUOTE(colon s)::rst)) handle e => Raise e)
        of (Parse_support.TY_SPEC sp) => sp
         | _ => raise PARSE_ERR{function = "type_spec_parser",
                                message = "Not a type specification."})
  | type_spec_parser _ = raise PARSE_ERR{function = "type_spec_parser",
                                          message = "Badly formed quotation."};


fun string_to_type_spec s =
  (Globals.in_type_spec := SOME "";
   case (ps (colon s))
     of (Parse_support.TY_SPEC sp) => sp
      | _ => raise PARSE_ERR{function = "string_to_type_spec",
			     message = "Not a type specification."});

end; (* PARSE *)
