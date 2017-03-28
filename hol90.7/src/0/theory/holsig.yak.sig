signature holsig_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val EOLEX:  'a * 'a -> (svalue,'a) token
val num: (string) *  'a * 'a -> (svalue,'a) token
val id: (string) *  'a * 'a -> (svalue,'a) token
val string_constant: (string) *  'a * 'a -> (svalue,'a) token
val symbolic: (string) *  'a * 'a -> (svalue,'a) token
val type_var: (string) *  'a * 'a -> (svalue,'a) token
val constants:  'a * 'a -> (svalue,'a) token
val types:  'a * 'a -> (svalue,'a) token
val parents:  'a * 'a -> (svalue,'a) token
val Infix:  'a * 'a -> (svalue,'a) token
val Prefix:  'a * 'a -> (svalue,'a) token
val Binder:  'a * 'a -> (svalue,'a) token
val fixity:  'a * 'a -> (svalue,'a) token
val ty:  'a * 'a -> (svalue,'a) token
val name:  'a * 'a -> (svalue,'a) token
val thid:  'a * 'a -> (svalue,'a) token
val eq:  'a * 'a -> (svalue,'a) token
val comma:  'a * 'a -> (svalue,'a) token
val rparen:  'a * 'a -> (svalue,'a) token
val lparen:  'a * 'a -> (svalue,'a) token
val rbracket:  'a * 'a -> (svalue,'a) token
val lbracket:  'a * 'a -> (svalue,'a) token
val rbrace:  'a * 'a -> (svalue,'a) token
val lbrace:  'a * 'a -> (svalue,'a) token
end
signature holsig_LRVALS=
sig
structure Tokens : holsig_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
