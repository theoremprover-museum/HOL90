functor THY_LEX(structure Tokens : thy_TOKENS)=
   struct
    structure UserDeclarations =
      struct
type pos = int;
val line:pos = 0;
type svalue = Tokens.svalue;
type ('a,'b) token = ('a,'b) Tokens.token;
type lexresult = (svalue,pos) Tokens.token;


fun error(s,_,_) = output(std_out,"Theory lexer error: "^s^"\n");
fun eof () = Tokens.EOF(line,line);

val type_paren_count = ref 0;
val string_list = ref ([]:string list);

local
fun ch_list_to_num ("$"::(L as (_::_))) =
      let fun rev_it([],A) = A
            | rev_it ((ch::rst),A) = rev_it (rst, (A*10)+(ord ch-48))
      in
      rev_it(L,0)
      end
  | ch_list_to_num _ = raise HOL_ERR{origin_structure = "Theory_lexer",
                                     origin_function="ch_list_to_num",
                                     message = "malformed dB"}
in
fun break_dB "$0" = 0    | break_dB "$1" = 1
  | break_dB "$2" = 2    | break_dB "$3" = 3
  | break_dB "$4" = 4    | break_dB "$5" = 5
  | break_dB "$6" = 6    | break_dB "$7" = 7
  | break_dB "$8" = 8    | break_dB "$9" = 9
  | break_dB "$10" = 10  | break_dB "$11" = 11
  | break_dB "$12" = 12  | break_dB "$13" = 13
  | break_dB "$14" = 14  | break_dB "$15" = 15
  | break_dB "$16" = 16
  | break_dB s = ch_list_to_num (explode s)
end;

exception LEX_ERR of string;

end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s0 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s1 =
"\007\007\007\007\007\007\007\007\007\021\023\007\021\007\007\007\
\\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\
\\021\008\020\008\018\008\008\007\017\016\008\008\008\008\015\008\
\\013\013\013\013\013\013\013\013\013\013\008\008\008\008\008\008\
\\008\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\007\012\007\007\008\
\\007\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\007\008\007\008\007\
\\007"
val s3 =
"\024\024\024\024\024\024\024\024\024\036\038\024\036\024\024\024\
\\024\024\024\024\024\024\024\024\024\024\024\024\024\024\024\024\
\\036\024\024\035\024\024\024\033\032\031\024\030\029\027\024\024\
\\025\025\025\025\025\025\025\025\025\025\024\024\024\024\024\024\
\\024\025\025\025\025\025\025\025\025\025\025\025\025\025\025\025\
\\025\025\025\025\025\025\025\025\025\025\025\024\024\024\024\024\
\\024\025\025\025\025\025\025\025\025\025\025\025\025\025\025\025\
\\025\025\025\025\025\025\025\025\025\025\025\024\024\024\024\024\
\\024"
val s5 =
"\039\039\039\039\039\039\039\039\039\039\043\039\039\039\039\039\
\\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\
\\039\039\042\039\039\039\039\039\039\039\039\039\039\039\039\039\
\\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\
\\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\
\\039\039\039\039\039\039\039\039\039\039\039\039\040\039\039\039\
\\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\
\\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\039\
\\039"
val s8 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\009\000\009\000\009\009\000\000\000\009\009\009\009\000\009\
\\000\000\000\000\000\000\000\000\000\000\009\009\009\009\009\009\
\\009\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\009\000\000\009\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\009\000\009\000\
\\000"
val s10 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\011\000\000\000\000\000\000\000\000\
\\011\011\011\011\011\011\011\011\011\011\000\000\000\000\000\000\
\\000\011\011\011\011\011\011\011\011\011\011\011\011\011\011\011\
\\011\011\011\011\011\011\011\011\011\011\011\000\000\000\000\011\
\\000\011\011\011\011\011\011\011\011\011\011\011\011\011\011\011\
\\011\011\011\011\011\011\011\011\011\011\011\000\000\000\000\000\
\\000"
val s13 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\011\000\000\000\000\000\000\000\000\
\\014\014\014\014\014\014\014\014\014\014\000\000\000\000\000\000\
\\000\011\011\011\011\011\011\011\011\011\011\011\011\011\011\011\
\\011\011\011\011\011\011\011\011\011\011\011\000\000\000\000\011\
\\000\011\011\011\011\011\011\011\011\011\011\011\011\011\011\011\
\\011\011\011\011\011\011\011\011\011\011\011\000\000\000\000\000\
\\000"
val s18 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\019\019\019\019\019\019\019\019\019\019\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s21 =
"\000\000\000\000\000\000\000\000\000\022\022\000\022\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s25 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\000\
\\026\026\026\026\026\026\026\026\026\026\000\000\000\000\000\000\
\\000\026\026\026\026\026\026\026\026\026\026\026\026\026\026\026\
\\026\026\026\026\026\026\026\026\026\026\026\000\000\000\000\026\
\\000\026\026\026\026\026\026\026\026\026\026\026\026\026\026\026\
\\026\026\026\026\026\026\026\026\026\026\026\000\000\000\000\000\
\\000"
val s27 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\028\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s33 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\034\034\034\034\034\034\034\034\034\034\034\034\034\034\034\
\\034\034\034\034\034\034\034\034\034\034\034\000\000\000\000\000\
\\000\034\034\034\034\034\034\034\034\034\034\034\034\034\034\034\
\\034\034\034\034\034\034\034\034\034\034\034\000\000\000\000\000\
\\000"
val s34 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\034\034\034\034\034\034\034\034\034\034\000\000\000\000\000\000\
\\000\034\034\034\034\034\034\034\034\034\034\034\034\034\034\034\
\\034\034\034\034\034\034\034\034\034\034\034\000\000\000\000\034\
\\000\034\034\034\034\034\034\034\034\034\034\034\034\034\034\034\
\\034\034\034\034\034\034\034\034\034\034\034\000\000\000\000\000\
\\000"
val s36 =
"\000\000\000\000\000\000\000\000\000\037\037\000\037\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\037\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s40 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\041\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
in Vector.vector
[{fin = [], trans = s0},
{fin = [], trans = s1},
{fin = [], trans = s1},
{fin = [], trans = s3},
{fin = [], trans = s3},
{fin = [], trans = s5},
{fin = [], trans = s5},
{fin = [(N 29)], trans = s0},
{fin = [(N 27),(N 29)], trans = s8},
{fin = [(N 27)], trans = s8},
{fin = [(N 24),(N 29)], trans = s10},
{fin = [(N 24)], trans = s10},
{fin = [(N 8),(N 27),(N 29)], trans = s8},
{fin = [(N 17),(N 24),(N 29)], trans = s13},
{fin = [(N 17),(N 24)], trans = s13},
{fin = [(N 10),(N 29)], trans = s0},
{fin = [(N 14),(N 29)], trans = s0},
{fin = [(N 12),(N 29)], trans = s0},
{fin = [(N 29)], trans = s18},
{fin = [(N 21)], trans = s18},
{fin = [(N 6),(N 29)], trans = s0},
{fin = [(N 4),(N 29)], trans = s21},
{fin = [(N 4)], trans = s21},
{fin = [(N 1),(N 4)], trans = s21},
{fin = [(N 56)], trans = s0},
{fin = [(N 41),(N 56)], trans = s25},
{fin = [(N 41)], trans = s25},
{fin = [(N 56)], trans = s27},
{fin = [(N 44)], trans = s0},
{fin = [(N 50),(N 56)], trans = s0},
{fin = [(N 46),(N 56)], trans = s0},
{fin = [(N 54),(N 56)], trans = s0},
{fin = [(N 52),(N 56)], trans = s0},
{fin = [(N 56)], trans = s33},
{fin = [(N 38)], trans = s34},
{fin = [(N 48),(N 56)], trans = s0},
{fin = [(N 34),(N 56)], trans = s36},
{fin = [(N 34)], trans = s36},
{fin = [(N 31),(N 34)], trans = s36},
{fin = [(N 65)], trans = s0},
{fin = [(N 65)], trans = s40},
{fin = [(N 61)], trans = s0},
{fin = [(N 63),(N 65)], trans = s0},
{fin = [(N 58)], trans = s0}]
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val INITIAL = STARTSTATE 1;
val STRING = STARTSTATE 5;
val TYPE = STARTSTATE 3;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

fun makeLexer yyinput = 
let 
	val yyb = ref "\n" 		(* buffer *)
	val yybl = ref 1		(*buffer length *)
	val yybufpos = ref 1		(* location of next character to use *)
	val yygone = ref 1		(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex () : Internal.result =
let fun continue() = lex() in
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0) =
	let fun action (i,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk => 
			(let val yytext = substring(!yyb,i0,i-i0)
			     val yypos = i0+ !yygone
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of 

			(* Application actions *)

  1 => (continue())
| 10 => (Tokens.dot(line,line))
| 12 => (Tokens.lparen(line,line))
| 14 => (Tokens.rparen(line,line))
| 17 => (Tokens.num(yytext,line,line))
| 21 => (Tokens.db_index(break_dB yytext,line,line))
| 24 => (Tokens.ident(yytext,line,line))
| 27 => ( case yytext 
              of ":" => ( YYBEGIN TYPE; 
                          type_paren_count := 0;
                          Tokens.colon(line,line))
               |   _  => Tokens.ident(yytext,line,line))
| 29 => (raise LEX_ERR "INITIAL.catchall")
| 31 => (continue())
| 34 => (continue())
| 38 => (Tokens.type_var_ident(yytext,line,line))
| 4 => (continue())
| 41 => (Tokens.type_ident(yytext,line,line))
| 44 => (Tokens.type_right_arrow(line,line))
| 46 => (Tokens.type_plus(line,line))
| 48 => (Tokens.type_hash(line,line))
| 50 => (Tokens.type_comma(line,line))
| 52 => (inc type_paren_count; Tokens.type_lparen(line,line))
| 54 => (if (!type_paren_count = 0)
               then (YYBEGIN INITIAL; Tokens.rparen(line,line))
               else (dec type_paren_count; Tokens.type_rparen(line,line)))
| 56 => (raise LEX_ERR "TYPE.catchall")
| 58 => (string_list :=  yytext::(!string_list); continue())
| 6 => ( YYBEGIN STRING; string_list := [yytext]; continue())
| 61 => (string_list := "\""::(!string_list); continue())
| 63 => (YYBEGIN INITIAL; 
              Tokens.string_(implode(rev(yytext::(!string_list))),line,line))
| 65 => (string_list :=  yytext::(!string_list); continue())
| 8 => (Tokens.lambda(line,line))
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Vector.sub(Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof ()
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := substring(!yyb,i0,l-i0)^newchars;
		     yygone := !yygone+i0;
		     yybl := size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = ordof(!yyb,l)
		val NewState = if NewChar<128 then ordof(trans,NewChar) else ordof(trans,128)
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
end
  in lex
  end
end
