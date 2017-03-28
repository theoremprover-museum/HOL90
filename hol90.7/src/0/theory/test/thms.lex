datatype lexresult = 
      lparen   | rparen
    | lbracket | rbracket
    | comma
    | eq
    | thid
    | axioms
    | definitions
    | theorems
    | quote of string
    | id of string
    | num of string
    | EOF ;

val error = fn x => output(std_out,x^"\n");
val eof = fn () => EOF;
val quote_list = ref ([]:string list);
%%
%structure test_lex

%s QWOTE;
ws = [\ \t \010 \012];
num = ([0-9]+);
symb = ([#\?\+\*\/\\\=\<\>&%@!:\,\;_\|-]+);
id = ({symb}?([A-Za-z_']|[0-9])+);
%%
<INITIAL>\n => (lex());
<INITIAL>{ws}+ => (lex());
<INITIAL>"[" => (lbracket);
<INITIAL>"]" => (rbracket);
<INITIAL>"(" => (lparen);
<INITIAL>")" => (rparen);
<INITIAL>"=" => (eq);
<INITIAL>"," => (comma);
<INITIAL>"thid" => (thid);
<INITIAL>"axioms" => (axioms);
<INITIAL>"definitions" => (definitions);
<INITIAL>"theorems" => (theorems);
<INITIAL>{num} => (num(yytext));
<INITIAL>{id} => (id(yytext));
<INITIAL>"`" => (YYBEGIN QWOTE; quote_list := []; lex());
<INITIAL>. => (error"INITIAL.catchall"; lex());

<QWOTE>"`" => (YYBEGIN INITIAL;
               quote(implode (rev (!quote_list))));
<QWOTE>\n => (quote_list := yytext::(!quote_list); lex());
<QWOTE>. => (quote_list := yytext::(!quote_list); lex());
