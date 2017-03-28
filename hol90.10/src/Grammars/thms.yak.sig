signature thms_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val EOLEX:  'a * 'a -> (svalue,'a) token
val num: (string) *  'a * 'a -> (svalue,'a) token
val id: (string) *  'a * 'a -> (svalue,'a) token
val quote: (string) *  'a * 'a -> (svalue,'a) token
val theorems:  'a * 'a -> (svalue,'a) token
val definitions:  'a * 'a -> (svalue,'a) token
val axioms:  'a * 'a -> (svalue,'a) token
val thid:  'a * 'a -> (svalue,'a) token
val eq:  'a * 'a -> (svalue,'a) token
val comma:  'a * 'a -> (svalue,'a) token
val rbracket:  'a * 'a -> (svalue,'a) token
val lbracket:  'a * 'a -> (svalue,'a) token
val rparen:  'a * 'a -> (svalue,'a) token
val lparen:  'a * 'a -> (svalue,'a) token
end
signature thms_LRVALS=
sig
structure Tokens : thms_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
