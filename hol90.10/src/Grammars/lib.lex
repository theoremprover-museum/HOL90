type pos = int;
val line:pos = 0;
type svalue = Tokens.svalue;
type ('a,'b) token = ('a,'b) Tokens.token;
type lexresult = (svalue,pos) Tokens.token;


fun error(s,_,_) = 
  Portable.output(Portable.std_out,"library lexer error: "^s^"\n");

fun eof () = Tokens.EOF(line,line);
exception LEX_ERR of string;
val string_list = ref ([]:string list);

%%
%header (functor LIB_LEX(structure Tokens : lib_TOKENS));

%s STRING;
ws = [\ \t \010 \012];
num = [0-9]+;
id = ([A-Za-z0-9_'\.\/-]+);

%%
<INITIAL>\n => (continue());
<INITIAL>{ws}+ => (continue());
<INITIAL>"\"" => ( YYBEGIN STRING; string_list := []; continue());
<INITIAL>"{" => (Tokens.lbrace(line,line));
<INITIAL>"}" => (Tokens.rbrace(line,line));
<INITIAL>"[" => (Tokens.lbracket(line,line));
<INITIAL>"]" => (Tokens.rbracket(line,line));
<INITIAL>"(" => (Tokens.lparen(line,line));
<INITIAL>")" => (Tokens.rparen(line,line));
<INITIAL>"=" => (Tokens.eq(line,line));
<INITIAL>"," => (Tokens.comma(line,line));
<INITIAL>"lib_id" => (Tokens.lib_id(line,line));
<INITIAL>"doc" => (Tokens.doc(line,line));
<INITIAL>"path" => (Tokens.path(line,line));
<INITIAL>"parents" => (Tokens.parents(line,line));
<INITIAL>"code" => (Tokens.code(line,line));
<INITIAL>"theories" => (Tokens.theories(line,line));
<INITIAL>"help" => (Tokens.help(line,line));
<INITIAL>"loaded" => (Tokens.loaded(line,line));
<INITIAL>{num} => (Tokens.num(yytext,line,line));
<INITIAL>{id} => (Tokens.id(yytext,line,line));
<INITIAL>. => (raise LEX_ERR "INITIAL.catchall");

<STRING>"\n" => (string_list :=  yytext::(!string_list); continue());
<STRING>"\\\"" =>(string_list := "\""::(!string_list); continue());
<STRING>"\"" => (YYBEGIN INITIAL; 
     Tokens.string_constant(Portable.implode(rev(!string_list)),line,line));
<STRING>. => (string_list :=  yytext::(!string_list); continue());
