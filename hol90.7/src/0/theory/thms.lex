type pos = int;
val line:pos = 0;
type svalue = Tokens.svalue;
type ('a,'b) token = ('a,'b) Tokens.token;
type lexresult = (svalue,pos) Tokens.token;

fun error(s,_,_) = output(std_out,"thms lexer error: "^s^"\n");

fun eof () = Tokens.EOF(line,line);
val quote_list = ref ([]:string list);
exception LEX_ERR of string;

(* Lexical difficulties here: some derived principles of definition may
   define symbolic constants, and need to generate a name to store the
   definition with on a theory file. Usually this name generation is done
   by prepending the name of the constant being defined with "_DEF". This 
   can give us strange names, like 

       ;;_DEF

   which I just got bit by. How to handle? I'm going to be subtle and give
   {symb}?{id} as a possible name. Warning! (I don't know why I'm putting
   this here, but ...) We will be now able to have theory bindings on
   disk that are not autoloadable, which is OK, because this is checked
   for in add_to_sml.
*)

%%
%header (functor THMS_LEX(structure Tokens : thms_TOKENS));

%s QWOTE ;
ws = [\ \t \010 \012];
num = ([0-9]+);
symb = ([#\?\+\*\/\\\=\<\>&%@!:\,\;_\|\~-]+);
id = ({symb}?([A-Za-z_']|[0-9])+);
%%
<INITIAL>\n => (continue());
<INITIAL>{ws}+ => (continue());
<INITIAL>"[" => (Tokens.lbracket(line,line));
<INITIAL>"]" => (Tokens.rbracket(line,line));
<INITIAL>"(" => (Tokens.lparen(line,line));
<INITIAL>")" => (Tokens.rparen(line,line));
<INITIAL>"=" => (Tokens.eq(line,line));
<INITIAL>"," => (Tokens.comma(line,line));
<INITIAL>"thid" => (Tokens.thid(line,line));
<INITIAL>"axioms" => (Tokens.axioms(line,line));
<INITIAL>"definitions" => (Tokens.definitions(line,line));
<INITIAL>"theorems" => (Tokens.theorems(line,line));
<INITIAL>{num} => (Tokens.num(yytext,line,line));
<INITIAL>{id} => (Tokens.id(yytext,line,line));
<INITIAL>{symb} => (Tokens.id(yytext,line,line));
<INITIAL>"`" => (YYBEGIN QWOTE; quote_list := []; continue());
<INITIAL>. => (raise LEX_ERR "INITIAL.catchall");

<QWOTE>"`" => (YYBEGIN INITIAL;
               Tokens.quote(implode (rev (!quote_list)),line,line));
<QWOTE>\n => (quote_list := yytext::(!quote_list); continue());
<QWOTE>. => (quote_list := yytext::(!quote_list); continue());
