structure Parse_support = Parse_support;
structure Tokens = Tokens;

type pos = int;
val line:pos = 0;
type svalue = Tokens.svalue;
type ('a,'b) token = ('a,'b) Tokens.token;
type lexresult = (svalue,pos) Tokens.token;
type arg = CoreHol.Term.term list ref;
fun eof (_:arg) = Tokens.EOF(line,line); 

fun error(s,_,_) = 
  Portable.output(Portable.std_out,"HOL lexer error: "^s^"\n");

val type_paren_count = ref 0;
val comment_paren_count = ref 0;
val string_list = ref ([]:string list);
exception AQ_ERR of string;
exception LEX_ERR of string;

val ordof = Portable.String.ordof;
fun ord s = ordof(s,0);
val inc = Portable.Ref.inc;
val dec = Portable.Ref.dec;

local val tilde = ord "~"
      val comma = ord ","
      val semicolon = ord ";"
in
fun has_tilde s =
   let fun f i = let val oof = ordof(s,i)
                 in (oof = tilde) orelse (oof = comma) orelse 
                    (oof=semicolon) orelse f(i+1) end
   in f 0 handle _ => false end
end;

local val dollar = ord "$"
in
fun drop_dollar s =
   if (ordof(s,0) = dollar) then substring(s,1,String.size s - 1)  else s
end;


local open Parse_support.Preterm.Term
      val dquote = ord"\""
      fun is_string_literal s =
          Portable.Int.> (String.size s, 1)
           andalso (ordof(s,0) = dquote)
           andalso (ordof(s, String.size s - 1) = dquote)
in
fun string_aq tm = 
  let val s = #Name(dest_const tm)
      val _ = Lib.assert is_string_literal s
  in Portable.String.substring(s,1,String.size s-2)
  end
end;


(*---------------------------------------------------------------------------
 * fun break s = snd
 *    (itlist (fn ch => fn (current_frag,seen) =>
 *              if (ch = "~")
 *              then if (null current_frag)
 *                   then ([],(ch::seen))
 *                   else ([],(ch::(implode current_frag)::seen))
 *              else ((ch::current_frag),seen))
 *            (""::explode s) ([],[]));
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * Confusion warning: symbolic_ident means roughly 
 *
 *       Maybe a $ followed by any sequence of symbols
 *---------------------------------------------------------------------------*)
%%
%header (functor HolLex(structure Tokens : Hol_TOKENS
                        structure Parse_support 
                          : sig include Parse_support_sig end
                            where type Preterm.Term.term = CoreHol.Term.term));

%arg (aqlist : UserDeclarations.arg);
%s TYPE TYCOMMENT COMMENT STRING;
%reject
ident = [\$]?([A-Za-z0-9] [A-Za-z0-9_']*);
symbolic_ident_or_tilde = [\$]?([#\?\+\*\/\\\=\<\>&%@!:\,\;_\|\~-]+);
symbolic_ident =          [\$]?([#\?\+\*\/\\\=\<\>&%@!:\;_\|-]+);
type_var_ident = ['] [A-Za-z][A-Za-z0-9_]*;
ws = [\ \t \010 \012];
%%
<INITIAL>\n => (continue());
<INITIAL>{ws}+ => (continue());
<INITIAL>"(*" => ( YYBEGIN COMMENT; comment_paren_count := 1; continue());
<INITIAL>"\"" => ( YYBEGIN STRING; string_list := [yytext]; continue());
<INITIAL>"." => (Tokens.dot(line,line));
<INITIAL>"(" => (Tokens.lparen(line,line));
<INITIAL>")" => (Tokens.rparen(line,line));
<INITIAL>"{" => (Tokens.lbrace(line,line));
<INITIAL>"}" => (Tokens.rbrace(line,line));
<INITIAL>"[" => (Tokens.lbracket(line,line));
<INITIAL>"]" => (Tokens.rbracket(line,line));
<INITIAL>"^" => (let val (L as ref (x::t)) = aqlist
                     val _ = L := t
                 in Tokens.aq(x,line,line)
                 end
                 handle _ => raise AQ_ERR "lexer.INITIAL");
<INITIAL>{ident} => (case yytext
         of "let" => Tokens.let_(line,line)
          | "in" => Tokens.in_(line,line)
          | "and" => Tokens.and_(line,line)
          | "of" => (case (!Globals.in_type_spec)
                     of NONE => raise LEX_ERR(Lib.quote"of"^" is a keyword.")
                      | (SOME"")=>raise LEX_ERR(Lib.quote"of"^" is a keyword.")
                       |(SOME _) => (YYBEGIN TYPE; type_paren_count := 0;
                                      Tokens.of_(line,line)))
          |    _ => if (Parse_support.is_binder yytext)
                    then Tokens.binder(yytext,line,line)
                    else Tokens.ident(yytext,line,line));
<INITIAL>{symbolic_ident_or_tilde} => 
   ( if (has_tilde yytext
         andalso (Lib.mem (drop_dollar yytext) (!Globals.tilde_symbols)))
     then if (Parse_support.is_binder yytext)
          then Tokens.binder(yytext,line,line)
          else Tokens.symbolic_ident(yytext,line,line)
     else REJECT());

<INITIAL>{symbolic_ident} => ( case yytext 
         of ";" => Tokens.semi_colon(line,line)
          | "=>" => Tokens.eq_gt(line,line)
          | "="  => Tokens.eq(line,line)
          | "|"  => Tokens.bar(line,line)
          | "::" => Tokens.dcolon(line,line)
          | ":" => ((case(!Globals.in_type_spec)
                       of NONE => (YYBEGIN TYPE;  type_paren_count := 0)
                        | _ => ());
                    Tokens.colon(line,line))
          |   _  => if (Parse_support.is_binder yytext)
                    then Tokens.binder(yytext,line,line)
                    else Tokens.symbolic_ident(yytext,line,line));

<INITIAL>"$~" => (Tokens.ident("~",line,line));
<INITIAL>"~"  => (Tokens.ident("~",line,line));
<INITIAL>"$," => (Tokens.symbolic_ident("$,",line,line));
<INITIAL>","  => (Tokens.symbolic_ident(",",line,line));

<INITIAL>. => (raise LEX_ERR "INITIAL.catchall");

<TYPE>\n => (continue());
<TYPE>{ws}+ => (continue());
<TYPE>"(*" => ( YYBEGIN TYCOMMENT; comment_paren_count := 1; continue());
<TYPE>{type_var_ident} => (Tokens.type_var_ident(yytext,line,line));
<TYPE>{ident} => (case yytext
                    of "let" => (YYBEGIN INITIAL; Tokens.let_(line,line))
                     | "in"  => (YYBEGIN INITIAL; Tokens.in_(line,line))
                     | "and" => (YYBEGIN INITIAL; Tokens.and_(line,line))
                     |    _ => Tokens.type_ident(yytext,line,line));
<TYPE>"^" => (let val (L as ref (x::t)) = aqlist
                  val () = L := t
              in Tokens.aq(x,line,line) end
              handle _ => raise AQ_ERR "lexer.TYPE");

<TYPE>"->" => (Tokens.arrow(line,line));
<TYPE>"+" => (Tokens.type_plus(line,line));
<TYPE>"#" => (Tokens.type_hash(line,line));
<TYPE>"," => (if (!type_paren_count = 0)
              then (YYBEGIN INITIAL; Tokens.symbolic_ident(",",line,line))
              else Tokens.type_comma(line,line));

<TYPE>"."  =>  (YYBEGIN INITIAL; Tokens.dot(line,line));
<TYPE>"("  => (inc type_paren_count; Tokens.type_lparen(line,line));
<TYPE>")"  => (if (!type_paren_count = 0)
               then (YYBEGIN INITIAL; Tokens.rparen(line,line))
               else (dec type_paren_count; Tokens.type_rparen(line,line)));
<TYPE>"[" => (YYBEGIN INITIAL; Tokens.lbracket(line,line));
<TYPE>"]" => (YYBEGIN INITIAL; Tokens.rbracket(line,line));
<TYPE>"{" => (YYBEGIN INITIAL; Tokens.lbrace(line,line));
<TYPE>"}" => (YYBEGIN INITIAL; Tokens.rbrace(line,line));

<TYPE>"=>" => ((case (!Globals.in_type_spec)
                  of (SOME _) => ()
                   | NONE => YYBEGIN INITIAL);
               Tokens.eq_gt(line,line));

<TYPE>{symbolic_ident_or_tilde} => 
   ( if (has_tilde yytext 
         andalso (Lib.mem (drop_dollar yytext) (!Globals.tilde_symbols)))
     then( YYBEGIN INITIAL;
           if (Parse_support.is_binder yytext)
           then Tokens.binder(yytext,line,line)
           else Tokens.symbolic_ident(yytext,line,line))
     else REJECT());

<TYPE>{symbolic_ident} => 
        ( YYBEGIN INITIAL;
          case yytext 
            of ";"  => Tokens.semi_colon(line,line)
             | "=>" => Tokens.eq_gt(line,line)
             | "="  => Tokens.eq(line,line)
             | "|"  => Tokens.bar(line,line)
             | "::" => Tokens.dcolon(line,line)
             |   _  => if (Parse_support.is_binder yytext)
                       then Tokens.binder(yytext,line,line)
                       else Tokens.symbolic_ident(yytext,line,line));
<TYPE>"$~" => (YYBEGIN INITIAL;Tokens.ident("~",line,line));
<TYPE>"~"  => (YYBEGIN INITIAL;Tokens.ident("~",line,line));
<TYPE>"$," => (YYBEGIN INITIAL;Tokens.symbolic_ident("$,",line,line));
<TYPE>","  => (YYBEGIN INITIAL;Tokens.symbolic_ident(",",line,line));

<TYPE>. => (raise LEX_ERR "TYPE.catchall");


<TYCOMMENT>"\n" => (continue());
<TYCOMMENT>"(*" => (inc comment_paren_count; continue());
<TYCOMMENT>"*)" => (dec comment_paren_count;
                    if (!comment_paren_count = 0) then YYBEGIN TYPE else ();
                    continue());
<TYCOMMENT>"^"  => (let val (L as ref (_::t)) = aqlist
                        val () = L := t
                    in continue() end);
<TYCOMMENT>.    => (continue());

<COMMENT>"\n" => (continue());
<COMMENT>"(*" => (inc comment_paren_count; continue());
<COMMENT>"*)" => (dec comment_paren_count;
                  if (!comment_paren_count = 0) then YYBEGIN INITIAL else ();
                  continue());
<COMMENT>"^"  => (let val (L as ref (_::t)) = aqlist
                      val () = L := t
                  in continue() end);
<COMMENT>.    => (continue());


<STRING>"\n"   => (string_list :=  yytext::(!string_list); continue());
<STRING>"\\\"" => (string_list := yytext::(!string_list); continue());
<STRING>"\""   => (YYBEGIN INITIAL; 
     Tokens.string_(Portable.implode(rev(yytext::(!string_list))),line,line));
<STRING>"\\^" => (let val (L as ref (_::t)) = aqlist
                       val () = L := t
                       val () = string_list := "^"::(!string_list)
                  in continue() end);
<STRING>"^"    => (let val (L as ref (x::t)) = aqlist
                       val () = L := t
                       val () = string_list := string_aq x::(!string_list)
                   in continue() end);
<STRING>. => (string_list := yytext::(!string_list); continue());
