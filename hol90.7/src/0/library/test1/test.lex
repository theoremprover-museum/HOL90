type pos = int;

type svalue = Tokens.svalue;
type ('a,'b) token = ('a,'b) Tokens.token;
type lexresult = (svalue,pos) token;

val pos = 0;
fun eof() = Tokens.EOF(pos, pos);
fun error(err_str,_,_) = output(std_out,("error: "^err_str^"\n"));
%%
%header (functor test1_lex(structure Tokens : test1_TOKENS));
ident = [A-Za-z] [A-Za-z0-9_']*;
ws = [\ \t];
%%
\n => (lex());
{ws}+ => (lex());
"," => (Tokens.comma(0,0));
{ident} => (Tokens.ident(yytext,0,0));
. => (error (("lexer: ignoring bad character "^yytext),0,0); lex());
