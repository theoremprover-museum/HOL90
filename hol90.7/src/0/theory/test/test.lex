datatype lexresult = lbrace | rbrace
    | lbracket | rbracket
    | lparen | rparen
    | eq
    | comma
    | lib_id
    | doc
    | path
    | parents
    | theories
    | code
    | help
    | loaded
    | id of string
    | num of string
    | string_constant of string
    | EOF ;

val error = fn x => output(std_out,x^"\n");
val eof = fn () => EOF;
val string_list = ref ([]:string list);
%%
%structure test_lex
%s STRING;
ws = [\ \t \010 \012];
num = [0-9]+;
id = ([A-Za-z0-9_'\.\/-]+);
%%
<INITIAL>\n => (lex());
<INITIAL>{ws}+ => (lex());
<INITIAL>"\"" => ( YYBEGIN STRING; string_list := []; lex());
<INITIAL>"{" => (lbrace);
<INITIAL>"}" => (rbrace);
<INITIAL>"[" => (lbracket);
<INITIAL>"]" => (rbracket);
<INITIAL>"(" => (lparen);
<INITIAL>")" => (rparen);
<INITIAL>"=" => (eq);
<INITIAL>"," => (comma);
<INITIAL>"lib_id" => (lib_id);
<INITIAL>"doc" => (doc);
<INITIAL>"path" => (path);
<INITIAL>"parents" => (parents);
<INITIAL>"code" => (code);
<INITIAL>"theories" => (theories);
<INITIAL>"help" => (help);
<INITIAL>"loaded" => (loaded);
<INITIAL>{num} => (num(yytext));
<INITIAL>{id} => (id(yytext));
<INITIAL>. => (error "catchall ERROR"; lex());

<STRING>"\n" => (string_list :=  yytext::(!string_list); lex());
<STRING>"\\\"" =>(string_list := "\""::(!string_list); lex());
<STRING>"\"" => (YYBEGIN INITIAL; 
                 string_constant(implode(rev(!string_list))));
<STRING>. => (string_list :=  yytext::(!string_list); lex());
