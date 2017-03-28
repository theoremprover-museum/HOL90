type pos = int;
val line:pos = 0;
type svalue = Tokens.svalue;
type ('a,'b) token = ('a,'b) Tokens.token;
type lexresult = (svalue,pos) Tokens.token;


fun error(s,_,_) = 
   Portable.output(Portable.std_out,"Theory lexer error: "^s^"\n");
fun eof () = Tokens.EOF(line,line);

val type_paren_count = ref 0;
val string_list = ref ([]:string list);

local
fun ch_list_to_num (#"$"::(L as (_::_))) =
      let fun rev_it([],A) = A
            | rev_it ((ch::rst),A) = rev_it (rst, (A*10)+(ord ch-48))
      in
      rev_it(L,0)
      end
  | ch_list_to_num _ = raise Exception.HOL_ERR
                          {origin_structure = "Theory_lexer",
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
  | break_dB s = ch_list_to_num (String.explode s)
end;

val inc = Portable.Ref.inc;
val dec = Portable.Ref.dec;

exception LEX_ERR of string;

%%
%header (functor THY_LEX(structure Tokens : thy_TOKENS));

%s TYPE STRING;
ident = [A-Za-z0-9] [A-Za-z0-9_']*;
symbolic_ident = [#\?\+\*\/\\\=\<\>&%@!:\,\;_\|\~-]+;
type_var_ident = ['] [A-Za-z][A-Za-z0-9_]*;
num = [0-9]+;
db_ident = [$] ([0-9]+);
ws = [\ \t \010 \012];
%%
<INITIAL>\n => (continue());
<INITIAL>{ws}+ => (continue());
<INITIAL>"\"" => ( YYBEGIN STRING; string_list := [yytext]; continue());
<INITIAL>"\\" => (Tokens.lambda(line,line));
<INITIAL>"." => (Tokens.dot(line,line));
<INITIAL>"(" => (Tokens.lparen(line,line));
<INITIAL>")" => (Tokens.rparen(line,line));
<INITIAL>{num} => (Tokens.num(yytext,line,line));
<INITIAL>{db_ident} => (Tokens.db_index(break_dB yytext,line,line));
<INITIAL>{ident} => (Tokens.ident(yytext,line,line));
<INITIAL>{symbolic_ident} => 
          ( case yytext 
              of ":" => ( YYBEGIN TYPE; 
                          type_paren_count := 0;
                          Tokens.colon(line,line))
               |   _  => Tokens.ident(yytext,line,line));

<INITIAL>. => (raise LEX_ERR "INITIAL.catchall");

<TYPE>\n => (continue());
<TYPE>{ws}+ => (continue());
<TYPE>{type_var_ident} => (Tokens.type_var_ident(yytext,line,line));
<TYPE>{ident} => (Tokens.type_ident(yytext,line,line));
<TYPE>"->" => (Tokens.type_right_arrow(line,line));
<TYPE>"+" => (Tokens.type_plus(line,line));
<TYPE>"#" => (Tokens.type_hash(line,line));
<TYPE>"," => (Tokens.type_comma(line,line));

<TYPE>"("  => (inc type_paren_count; Tokens.type_lparen(line,line));
<TYPE>")"  => (if (!type_paren_count = 0)
               then (YYBEGIN INITIAL; Tokens.rparen(line,line))
               else (dec type_paren_count; Tokens.type_rparen(line,line)));
<TYPE>. => (raise LEX_ERR "TYPE.catchall");

<STRING>"\n" => (string_list :=  yytext::(!string_list); continue());
<STRING>"\\\"" =>(string_list := "\""::(!string_list); continue());
<STRING>"\"" => (YYBEGIN INITIAL; 
      Tokens.string_(Portable.implode(rev(yytext::(!string_list))),line,line));
<STRING>. => (string_list :=  yytext::(!string_list); continue());
