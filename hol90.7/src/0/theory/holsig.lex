type pos = int;
val line:pos = 0;
type svalue = Tokens.svalue;
type ('a,'b) token = ('a,'b) Tokens.token;
type lexresult = (svalue,pos) Tokens.token;


fun error(s,_,_) = output(std_out,"theory lexer error: "^s^"\n");

fun eof () = Tokens.EOF(line,line);
exception LEX_ERR of string;
val string_list = ref ([]:string list);

%%
%header (functor HOLSIG_LEX(structure Tokens : holsig_TOKENS));

%s STRING;
ws = [\ \t \010 \012];
num = [0-9]+;
id = ([A-Za-z] [A-Za-z0-9_']*);
symbolic = [\$]?([#\?\+\*\/\\\=\<\>&%@!:\,\;_\|\~-]+);
type_var = ['] [A-Za-z][A-Za-z0-9_]*;

%%
<INITIAL>\n => (continue());
<INITIAL>{ws}+ => (continue());
<INITIAL>"\"" => ( YYBEGIN STRING; string_list := [yytext]; continue());
<INITIAL>"{" => (Tokens.lbrace(line,line));
<INITIAL>"}" => (Tokens.rbrace(line,line));
<INITIAL>"[" => (Tokens.lbracket(line,line));
<INITIAL>"]" => (Tokens.rbracket(line,line));
<INITIAL>"(" => (Tokens.lparen(line,line));
<INITIAL>")" => (Tokens.rparen(line,line));
<INITIAL>"=" => (Tokens.eq(line,line));
<INITIAL>"," => (Tokens.comma(line,line));
<INITIAL>"thid" => (Tokens.thid(line,line));
<INITIAL>"name" => (Tokens.name(line,line));
<INITIAL>"fixity" => (Tokens.fixity(line,line));
<INITIAL>"Binder" => (Tokens.Binder(line,line));
<INITIAL>"Prefix" => (Tokens.Prefix(line,line));
<INITIAL>"Infix" => (Tokens.Infix(line,line));
<INITIAL>"ty" => (Tokens.ty(line,line));
<INITIAL>"parents" => (Tokens.parents(line,line));
<INITIAL>"types" => (Tokens.types(line,line));
<INITIAL>"constants" => (Tokens.constants(line,line));
<INITIAL>{num} => (Tokens.num(yytext,line,line));
<INITIAL>{id} => (Tokens.id(yytext,line,line));
<INITIAL>{symbolic} => (Tokens.symbolic(yytext,line,line));
<INITIAL>{type_var} => (Tokens.type_var(yytext,line,line));
<INITIAL>. => (raise LEX_ERR "INITIAL.catchall");

<STRING>"\n" => (string_list :=  yytext::(!string_list); continue());
<STRING>"\\\"" =>(string_list := yytext::(!string_list); continue());
<STRING>"\"" => (YYBEGIN INITIAL; 
                 Tokens.string_constant(implode(rev(yytext::(!string_list))),
                                        line,line));
<STRING>. => (string_list :=  yytext::(!string_list); continue());
