signature lib_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val EOLEX:  'a * 'a -> (svalue,'a) token
val string_constant: (string) *  'a * 'a -> (svalue,'a) token
val num: (string) *  'a * 'a -> (svalue,'a) token
val id: (string) *  'a * 'a -> (svalue,'a) token
val loaded:  'a * 'a -> (svalue,'a) token
val help:  'a * 'a -> (svalue,'a) token
val code:  'a * 'a -> (svalue,'a) token
val theories:  'a * 'a -> (svalue,'a) token
val parents:  'a * 'a -> (svalue,'a) token
val path:  'a * 'a -> (svalue,'a) token
val doc:  'a * 'a -> (svalue,'a) token
val lib_id:  'a * 'a -> (svalue,'a) token
val comma:  'a * 'a -> (svalue,'a) token
val eq:  'a * 'a -> (svalue,'a) token
val rparen:  'a * 'a -> (svalue,'a) token
val lparen:  'a * 'a -> (svalue,'a) token
val rbracket:  'a * 'a -> (svalue,'a) token
val lbracket:  'a * 'a -> (svalue,'a) token
val rbrace:  'a * 'a -> (svalue,'a) token
val lbrace:  'a * 'a -> (svalue,'a) token
end
signature lib_LRVALS=
sig
structure Tokens : lib_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
