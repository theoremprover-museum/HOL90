signature hol_TOKENS =
sig
type ('a,'b) token
type svalue
structure Parse_support : Parse_support_sig
val hoare_assign:  'a * 'a -> (svalue,'a) token
val hoare_command_sep:  'a * 'a -> (svalue,'a) token
val hoare_done:  'a * 'a -> (svalue,'a) token
val hoare_do:  'a * 'a -> (svalue,'a) token
val hoare_while:  'a * 'a -> (svalue,'a) token
val hoare_variant:  'a * 'a -> (svalue,'a) token
val hoare_invariant:  'a * 'a -> (svalue,'a) token
val hoare_assert:  'a * 'a -> (svalue,'a) token
val hoare_fi:  'a * 'a -> (svalue,'a) token
val hoare_else:  'a * 'a -> (svalue,'a) token
val hoare_then:  'a * 'a -> (svalue,'a) token
val hoare_if:  'a * 'a -> (svalue,'a) token
val hoare_abort:  'a * 'a -> (svalue,'a) token
val hoare_skip:  'a * 'a -> (svalue,'a) token
val hoare_rbrace:  'a * 'a -> (svalue,'a) token
val hoare_lbrace:  'a * 'a -> (svalue,'a) token
val hoare_rbracket:  'a * 'a -> (svalue,'a) token
val hoare_lbracket:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
val EOLEX:  'a * 'a -> (svalue,'a) token
val string_: (string) *  'a * 'a -> (svalue,'a) token
val of_:  'a * 'a -> (svalue,'a) token
val in_:  'a * 'a -> (svalue,'a) token
val and_:  'a * 'a -> (svalue,'a) token
val let_:  'a * 'a -> (svalue,'a) token
val bar:  'a * 'a -> (svalue,'a) token
val type_plus:  'a * 'a -> (svalue,'a) token
val type_hash:  'a * 'a -> (svalue,'a) token
val eq:  'a * 'a -> (svalue,'a) token
val eq_gt:  'a * 'a -> (svalue,'a) token
val type_right_arrow:  'a * 'a -> (svalue,'a) token
val semi_colon:  'a * 'a -> (svalue,'a) token
val dot:  'a * 'a -> (svalue,'a) token
val colon:  'a * 'a -> (svalue,'a) token
val type_comma:  'a * 'a -> (svalue,'a) token
val rbrace:  'a * 'a -> (svalue,'a) token
val lbrace:  'a * 'a -> (svalue,'a) token
val rbracket:  'a * 'a -> (svalue,'a) token
val lbracket:  'a * 'a -> (svalue,'a) token
val type_rparen:  'a * 'a -> (svalue,'a) token
val type_lparen:  'a * 'a -> (svalue,'a) token
val rparen:  'a * 'a -> (svalue,'a) token
val lparen:  'a * 'a -> (svalue,'a) token
val aq: (Parse_support.Preterm.Term.term) *  'a * 'a -> (svalue,'a) token
val qualified_binder: ( ( string*string ) ) *  'a * 'a -> (svalue,'a) token
val binder: (string) *  'a * 'a -> (svalue,'a) token
val type_var_ident: (string) *  'a * 'a -> (svalue,'a) token
val qualified_type_ident: ( ( string*string ) ) *  'a * 'a -> (svalue,'a) token
val type_ident: (string) *  'a * 'a -> (svalue,'a) token
val qualified_ident: ( ( string*string ) ) *  'a * 'a -> (svalue,'a) token
val symbolic_ident: (string) *  'a * 'a -> (svalue,'a) token
val ident: (string) *  'a * 'a -> (svalue,'a) token
end
signature hol_LRVALS=
sig
structure Tokens : hol_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
