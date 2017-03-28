signature thy_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val EOLEX:  'a * 'a -> (svalue,'a) token
val string_: (string) *  'a * 'a -> (svalue,'a) token
val type_plus:  'a * 'a -> (svalue,'a) token
val type_hash:  'a * 'a -> (svalue,'a) token
val type_right_arrow:  'a * 'a -> (svalue,'a) token
val dot:  'a * 'a -> (svalue,'a) token
val colon:  'a * 'a -> (svalue,'a) token
val type_comma:  'a * 'a -> (svalue,'a) token
val type_rparen:  'a * 'a -> (svalue,'a) token
val type_lparen:  'a * 'a -> (svalue,'a) token
val rparen:  'a * 'a -> (svalue,'a) token
val lparen:  'a * 'a -> (svalue,'a) token
val num: (string) *  'a * 'a -> (svalue,'a) token
val db_index: (int) *  'a * 'a -> (svalue,'a) token
val lambda:  'a * 'a -> (svalue,'a) token
val type_var_ident: (string) *  'a * 'a -> (svalue,'a) token
val type_ident: (string) *  'a * 'a -> (svalue,'a) token
val ident: (string) *  'a * 'a -> (svalue,'a) token
end
signature thy_LRVALS=
sig
structure Tokens : thy_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
