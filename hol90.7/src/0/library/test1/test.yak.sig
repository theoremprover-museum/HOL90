signature test1_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val comma:  'a * 'a -> (svalue,'a) token
val ident: (string) *  'a * 'a -> (svalue,'a) token
end
signature test1_LRVALS=
sig
structure Tokens : test1_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
