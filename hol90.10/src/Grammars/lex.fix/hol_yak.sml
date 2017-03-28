
functor holLrValsFun (structure Token : TOKEN
                               structure Parse_support : Parse_support_sig) = 
struct
structure ParserData=
struct
structure Header = 
struct
structure Parse_support = Parse_support;

fun HOL_PARSE_ERR{function,message} = 
     HOL_ERR{origin_structure = "hol grammar file (hol_yak)",
             origin_function = function,
             message = message};

type term = Parse_support.Preterm.Term.term
type hol_type = Parse_support.Preterm.Term.Type.hol_type
type preterm_in_env = Parse_support.preterm_in_env
type binder_in_env = Parse_support.binder_in_env


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\163\000\002\000\163\000\004\000\165\000\007\000\163\000\
\\009\000\163\000\010\000\163\000\011\000\163\000\013\000\163\000\
\\014\000\163\000\015\000\163\000\016\000\163\000\017\000\163\000\
\\018\000\163\000\019\000\163\000\020\000\163\000\021\000\163\000\
\\022\000\163\000\023\000\163\000\024\000\163\000\025\000\163\000\
\\026\000\163\000\027\000\163\000\028\000\163\000\029\000\163\000\
\\030\000\163\000\031\000\163\000\033\000\163\000\034\000\163\000\
\\035\000\163\000\000\000\
\\001\000\001\000\164\000\002\000\164\000\004\000\168\000\007\000\164\000\
\\009\000\164\000\010\000\164\000\011\000\164\000\013\000\164\000\
\\014\000\164\000\015\000\164\000\016\000\164\000\017\000\164\000\
\\018\000\164\000\019\000\164\000\020\000\164\000\021\000\164\000\
\\022\000\164\000\023\000\164\000\024\000\164\000\025\000\164\000\
\\026\000\164\000\027\000\164\000\028\000\164\000\029\000\164\000\
\\030\000\164\000\031\000\164\000\033\000\164\000\034\000\164\000\
\\035\000\164\000\000\000\
\\001\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\019\000\011\000\
\\020\000\010\000\025\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\001\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\020\000\010\000\
\\025\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\001\000\001\000\028\000\009\000\027\000\010\000\026\000\000\000\
\\001\000\001\000\042\000\004\000\041\000\006\000\040\000\009\000\039\000\
\\012\000\038\000\000\000\
\\001\000\001\000\082\000\002\000\081\000\033\000\080\000\000\000\
\\001\000\002\000\077\000\011\000\076\000\019\000\054\000\000\000\
\\001\000\004\000\041\000\006\000\040\000\009\000\039\000\012\000\038\000\000\000\
\\001\000\004\000\058\000\000\000\
\\001\000\011\000\067\000\000\000\
\\001\000\011\000\104\000\000\000\
\\001\000\013\000\087\000\018\000\086\000\000\000\
\\001\000\013\000\110\000\000\000\
\\001\000\015\000\066\000\000\000\
\\001\000\017\000\063\000\000\000\
\\001\000\017\000\101\000\000\000\
\\001\000\020\000\069\000\021\000\068\000\000\000\
\\001\000\021\000\102\000\000\000\
\\001\000\025\000\055\000\000\000\
\\001\000\025\000\057\000\000\000\
\\001\000\028\000\071\000\000\000\
\\001\000\031\000\052\000\000\000\
\\001\000\034\000\000\000\035\000\000\000\000\000\
\\118\000\000\000\
\\119\000\000\000\
\\120\000\000\000\
\\121\000\000\000\
\\122\000\000\000\
\\123\000\000\000\
\\124\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\020\000\010\000\
\\024\000\022\000\025\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\125\000\000\000\
\\126\000\019\000\050\000\000\000\
\\127\000\000\000\
\\128\000\019\000\019\000\000\000\
\\129\000\000\000\
\\130\000\000\000\
\\131\000\000\000\
\\132\000\000\000\
\\133\000\000\000\
\\134\000\000\000\
\\135\000\000\000\
\\136\000\000\000\
\\137\000\000\000\
\\138\000\000\000\
\\139\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\020\000\010\000\
\\025\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\140\000\022\000\065\000\000\000\
\\140\000\022\000\065\000\028\000\064\000\000\000\
\\141\000\000\000\
\\142\000\000\000\
\\143\000\000\000\
\\144\000\000\000\
\\145\000\000\000\
\\146\000\001\000\028\000\009\000\027\000\010\000\026\000\019\000\054\000\000\000\
\\147\000\000\000\
\\148\000\000\000\
\\149\000\000\000\
\\150\000\000\000\
\\151\000\000\000\
\\152\000\002\000\077\000\019\000\054\000\000\000\
\\153\000\000\000\
\\154\000\030\000\093\000\000\000\
\\155\000\000\000\
\\156\000\000\000\
\\157\000\000\000\
\\158\000\023\000\060\000\000\000\
\\159\000\000\000\
\\160\000\027\000\061\000\000\000\
\\161\000\000\000\
\\162\000\026\000\059\000\000\000\
\\166\000\000\000\
\\167\000\000\000\
\\169\000\000\000\
\\170\000\018\000\111\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\000\000\
\\174\000\000\000\
\\175\000\000\000\
\\176\000\000\000\
\\177\000\028\000\096\000\000\000\
\\178\000\000\000\
\\179\000\000\000\
\\180\000\032\000\098\000\000\000\
\\181\000\032\000\097\000\000\000\
\\182\000\000\000\
\\183\000\000\000\
\\184\000\000\000\
\\185\000\024\000\114\000\000\000\
\"
val actionRowNumbers =
"\002\000\027\000\034\000\030\000\
\\024\000\038\000\004\000\039\000\
\\040\000\005\000\045\000\045\000\
\\003\000\037\000\004\000\036\000\
\\035\000\008\000\028\000\032\000\
\\003\000\022\000\053\000\019\000\
\\004\000\056\000\055\000\020\000\
\\026\000\001\000\070\000\009\000\
\\069\000\065\000\067\000\025\000\
\\008\000\076\000\074\000\075\000\
\\079\000\015\000\047\000\014\000\
\\046\000\010\000\017\000\033\000\
\\008\000\021\000\003\000\052\000\
\\008\000\003\000\007\000\006\000\
\\000\000\008\000\008\000\008\000\
\\012\000\043\000\003\000\045\000\
\\042\000\041\000\003\000\003\000\
\\031\000\003\000\051\000\057\000\
\\061\000\004\000\054\000\063\000\
\\080\000\078\000\082\000\084\000\
\\083\000\068\000\064\000\066\000\
\\008\000\077\000\016\000\048\000\
\\050\000\018\000\029\000\004\000\
\\011\000\059\000\006\000\008\000\
\\008\000\013\000\073\000\044\000\
\\003\000\062\000\058\000\004\000\
\\081\000\086\000\088\000\085\000\
\\071\000\008\000\049\000\060\000\
\\008\000\072\000\087\000\023\000"
val gotoT =
"\
\\001\000\115\000\002\000\004\000\003\000\003\000\004\000\002\000\
\\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\004\000\019\000\005\000\018\000\000\000\
\\000\000\
\\000\000\
\\006\000\023\000\007\000\022\000\009\000\021\000\000\000\
\\000\000\
\\000\000\
\\012\000\035\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\020\000\028\000\
\\021\000\027\000\000\000\
\\002\000\042\000\003\000\003\000\004\000\002\000\005\000\001\000\
\\011\000\041\000\000\000\
\\002\000\044\000\003\000\003\000\004\000\002\000\005\000\001\000\
\\011\000\043\000\000\000\
\\002\000\045\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\006\000\046\000\007\000\022\000\000\000\
\\000\000\
\\000\000\
\\012\000\047\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\000\000\
\\000\000\
\\000\000\
\\002\000\049\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\006\000\051\000\007\000\022\000\000\000\
\\000\000\
\\007\000\054\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\060\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\068\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\000\000\
\\000\000\
\\002\000\070\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\012\000\071\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\000\000\
\\002\000\072\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\010\000\073\000\000\000\
\\022\000\077\000\023\000\076\000\000\000\
\\000\000\
\\013\000\081\000\015\000\032\000\016\000\031\000\017\000\030\000\
\\019\000\029\000\000\000\
\\012\000\082\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\000\000\
\\013\000\034\000\014\000\083\000\015\000\032\000\016\000\031\000\
\\017\000\030\000\019\000\029\000\000\000\
\\000\000\
\\000\000\
\\002\000\086\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\002\000\044\000\003\000\003\000\004\000\002\000\005\000\001\000\
\\011\000\087\000\000\000\
\\000\000\
\\000\000\
\\002\000\088\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\002\000\089\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\002\000\090\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\093\000\008\000\092\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\098\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\018\000\097\000\019\000\029\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\023\000\007\000\022\000\009\000\101\000\000\000\
\\000\000\
\\010\000\103\000\000\000\
\\022\000\104\000\023\000\076\000\000\000\
\\012\000\106\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\024\000\105\000\000\000\
\\012\000\106\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\024\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\110\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\007\000\093\000\008\000\111\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\098\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\018\000\113\000\019\000\029\000\000\000\
\\000\000\
\\000\000\
\\012\000\106\000\013\000\034\000\014\000\033\000\015\000\032\000\
\\016\000\031\000\017\000\030\000\019\000\029\000\024\000\114\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 116
val numrules = 68
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; ordof(!s,i) + ordof(!s,i+1) * 256
end
val string_to_list = fn s' =>
    let val len = String.length s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.length s'
 	 fun f ()=
	    if !index < len then convert_row() :: f()
	    else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
	fun f i =
	     if i=numstates then g i
	     else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
	   in f 0 handle Subscript => ()
	   end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.arrayoflist(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.arrayoflist(actionRows) in fn i=>Array.sub(a,i) end
in Array.arrayoflist(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | string_ of  (string)
 | aq of  (Parse_support.Preterm.Term.term)
 | qualified_binder of  ( ( string*string ) ) | binder of  (string)
 | type_var_ident of  (string)
 | qualified_type_ident of  ( ( string*string ) )
 | type_ident of  (string) | qualified_ident of  ( ( string*string ) )
 | symbolic_ident of  (string) | ident of  (string)
 | C_ARG_LIST of  (hol_type list)
 | TYPE_CLAUSE of  ({ constructor:string,args:hol_type list } )
 | TYPE_CLAUSES of  ({ constructor:string,args:Parse_support.arg list }  list)
 | TYI of  (string)
 | TYPE_SPEC of  ({ ty_name:string,clauses:{ constructor:string,args:Parse_support.arg list }  list } )
 | BASIC of  (hol_type) | TYPE_LIST of  (hol_type list)
 | BASIC_TYPE_ARG of  (hol_type list) | TYPE_ARG of  (hol_type list)
 | APP_TYPE of  (hol_type) | PLUS_TYPE of  (hol_type)
 | HASH_TYPE of  (hol_type) | TYPE of  (hol_type)
 | LIST of  (preterm_in_env list) | COMMA of  (unit)
 | BINDING_LIST of  ( ( binder_in_env list * preterm_in_env )  list)
 | VSTRUCT of  (binder_in_env list) | BV of  (binder_in_env)
 | BV_LIST of  (binder_in_env list) | SUFFIX of  (preterm_in_env)
 | AEXP of  (preterm_in_env) | APP_EXP of  (preterm_in_env list)
 | PTRM of  (preterm_in_env) | START of  (Parse_support.parse)
end
type svalue = MlyValue.svalue
type result = Parse_support.parse
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_insert =
fn _ => false
val preferred_subst =
fn  _ => nil
val noShift = 
fn (T 34) => true | _ => false
val showTerminal =
fn (T 0) => "ident"
  | (T 1) => "symbolic_ident"
  | (T 2) => "qualified_ident"
  | (T 3) => "type_ident"
  | (T 4) => "qualified_type_ident"
  | (T 5) => "type_var_ident"
  | (T 6) => "binder"
  | (T 7) => "qualified_binder"
  | (T 8) => "aq"
  | (T 9) => "lparen"
  | (T 10) => "rparen"
  | (T 11) => "type_lparen"
  | (T 12) => "type_rparen"
  | (T 13) => "lbracket"
  | (T 14) => "rbracket"
  | (T 15) => "lbrace"
  | (T 16) => "rbrace"
  | (T 17) => "type_comma"
  | (T 18) => "colon"
  | (T 19) => "dcolon"
  | (T 20) => "dot"
  | (T 21) => "semi_colon"
  | (T 22) => "type_right_arrow"
  | (T 23) => "eq_gt"
  | (T 24) => "eq"
  | (T 25) => "type_hash"
  | (T 26) => "type_plus"
  | (T 27) => "bar"
  | (T 28) => "let_"
  | (T 29) => "and_"
  | (T 30) => "in_"
  | (T 31) => "of_"
  | (T 32) => "string_"
  | (T 33) => "EOLEX"
  | (T 34) => "EOF"
  | _ => "bogus-term"
val errtermvalue=
let open Header in
fn _ => MlyValue.VOID
end
val terms = (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13) :: (T 14)
 :: (T 15) :: (T 16) :: (T 17) :: (T 18) :: (T 19) :: (T 20) :: (T 21)
 :: (T 22) :: (T 23) :: (T 24) :: (T 25) :: (T 26) :: (T 27) :: (T 28)
 :: (T 29) :: (T 30) :: (T 31) :: (T 33) :: (T 34) :: nil
end
structure Actions =
struct 
exception mlyAction of int
val actions = 
let open Header
in
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.PTRM PTRM,PTRM1left,PTRM1right))::rest671) => let 
val result=MlyValue.START((Parse_support.make_preterm PTRM))
 in (LrTable.NT 0,(result,PTRM1left,PTRM1right),rest671) end
| (1,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::(_,(_,colon1left,_))::
rest671) => let val result=MlyValue.START((Parse_support.TY TYPE))
 in (LrTable.NT 0,(result,colon1left,TYPE1right),rest671) end
| (2,(_,(MlyValue.TYPE_SPEC TYPE_SPEC,_,TYPE_SPEC1right))::(_,(_,
colon1left,_))::rest671) => let val result=MlyValue.START((
Parse_support.TY_SPEC TYPE_SPEC))
 in (LrTable.NT 0,(result,colon1left,TYPE_SPEC1right),rest671) end
| (3,(_,(MlyValue.SUFFIX SUFFIX,SUFFIX1left,SUFFIX1right))::rest671)
 => let val result=MlyValue.PTRM((SUFFIX))
 in (LrTable.NT 1,(result,SUFFIX1left,SUFFIX1right),rest671) end
| (4,(_,(MlyValue.SUFFIX SUFFIX,_,SUFFIX1right))::(_,(MlyValue.APP_EXP
 APP_EXP,APP_EXP1left,_))::rest671) => let val result=MlyValue.PTRM((
Parse_support.prec_parse (rev(APP_EXP)@[SUFFIX])))
 in (LrTable.NT 1,(result,APP_EXP1left,SUFFIX1right),rest671) end
| (5,(_,(MlyValue.PTRM PTRM2,_,PTRM2right))::_::(_,(MlyValue.PTRM 
PTRM1,_,_))::_::(_,(MlyValue.APP_EXP APP_EXP,APP_EXP1left,_))::rest671
) => let val result=MlyValue.PTRM((
Parse_support.list_make_comb
                [Parse_support.make_atom "COND",
                 Parse_support.prec_parse (rev APP_EXP), 
                 PTRM1,PTRM2]
))
 in (LrTable.NT 1,(result,APP_EXP1left,PTRM2right),rest671) end
| (6,(_,(MlyValue.APP_EXP APP_EXP,APP_EXP1left,APP_EXP1right))::
rest671) => let val result=MlyValue.PTRM((
Parse_support.prec_parse (rev APP_EXP)))
 in (LrTable.NT 1,(result,APP_EXP1left,APP_EXP1right),rest671) end
| (7,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.AEXP AEXP,
_,_))::(_,(MlyValue.APP_EXP APP_EXP,APP_EXP1left,_))::rest671) => let 
val result=MlyValue.APP_EXP((
[Parse_support.make_constrained
               (Parse_support.prec_parse(rev (AEXP::APP_EXP))) TYPE]
))
 in (LrTable.NT 2,(result,APP_EXP1left,TYPE1right),rest671) end
| (8,(_,(MlyValue.AEXP AEXP,_,AEXP1right))::(_,(MlyValue.APP_EXP 
APP_EXP,APP_EXP1left,_))::rest671) => let val result=MlyValue.APP_EXP(
(AEXP::APP_EXP))
 in (LrTable.NT 2,(result,APP_EXP1left,AEXP1right),rest671) end
| (9,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.AEXP AEXP,
AEXP1left,_))::rest671) => let val result=MlyValue.APP_EXP((
[Parse_support.make_constrained AEXP TYPE]))
 in (LrTable.NT 2,(result,AEXP1left,TYPE1right),rest671) end
| (10,(_,(MlyValue.AEXP AEXP,AEXP1left,AEXP1right))::rest671) => let 
val result=MlyValue.APP_EXP(([AEXP]))
 in (LrTable.NT 2,(result,AEXP1left,AEXP1right),rest671) end
| (11,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.AEXP((Parse_support.make_atom ident))
 in (LrTable.NT 3,(result,ident1left,ident1right),rest671) end
| (12,(_,(MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=MlyValue.AEXP((
Parse_support.make_atom symbolic_ident))
 in (LrTable.NT 3,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| (13,(_,(MlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=MlyValue.AEXP((Parse_support.make_aq aq))
 in (LrTable.NT 3,(result,aq1left,aq1right),rest671) end
| (14,(_,(MlyValue.string_ string_,string_1left,string_1right))::
rest671) => let val result=MlyValue.AEXP((
Parse_support.make_string string_))
 in (LrTable.NT 3,(result,string_1left,string_1right),rest671) end
| (15,(_,(_,eq1left,eq1right))::rest671) => let val result=
MlyValue.AEXP((Parse_support.make_atom "="))
 in (LrTable.NT 3,(result,eq1left,eq1right),rest671) end
| (16,(_,(_,dcolon1left,dcolon1right))::rest671) => let val result=
MlyValue.AEXP((Parse_support.make_atom "::"))
 in (LrTable.NT 3,(result,dcolon1left,dcolon1right),rest671) end
| (17,(_,(_,_,rparen1right))::(_,(MlyValue.PTRM PTRM,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.AEXP((PTRM))
 in (LrTable.NT 3,(result,lparen1left,rparen1right),rest671) end
| (18,(_,(_,_,rbracket1right))::(_,(MlyValue.LIST LIST,_,_))::(_,(_,
lbracket1left,_))::rest671) => let val result=MlyValue.AEXP((
Parse_support.make_list LIST))
 in (LrTable.NT 3,(result,lbracket1left,rbracket1right),rest671) end
| (19,(_,(_,_,rbrace1right))::(_,(MlyValue.LIST LIST,_,_))::(_,(_,
lbrace1left,_))::rest671) => let val result=MlyValue.AEXP((
Parse_support.make_set LIST))
 in (LrTable.NT 3,(result,lbrace1left,rbrace1right),rest671) end
| (20,(_,(_,_,rbrace1right))::(_,(MlyValue.PTRM PTRM2,_,_))::_::(_,(
MlyValue.PTRM PTRM1,_,_))::(_,(_,lbrace1left,_))::rest671) => let val 
result=MlyValue.AEXP((Parse_support.make_set_abs (PTRM1,PTRM2)))
 in (LrTable.NT 3,(result,lbrace1left,rbrace1right),rest671) end
| (21,rest671) => let val result=MlyValue.LIST(([]))
 in (LrTable.NT 10,(result,defaultPos,defaultPos),rest671) end
| (22,(_,(MlyValue.PTRM PTRM,PTRM1left,PTRM1right))::rest671) => let 
val result=MlyValue.LIST(([PTRM]))
 in (LrTable.NT 10,(result,PTRM1left,PTRM1right),rest671) end
| (23,(_,(MlyValue.LIST LIST,_,LIST1right))::_::(_,(MlyValue.PTRM PTRM
,PTRM1left,_))::rest671) => let val result=MlyValue.LIST((PTRM::LIST))
 in (LrTable.NT 10,(result,PTRM1left,LIST1right),rest671) end
| (24,(_,(MlyValue.PTRM PTRM2,_,PTRM2right))::_::(_,(MlyValue.PTRM 
PTRM1,_,_))::_::(_,(MlyValue.BV_LIST BV_LIST,_,_))::(_,(
MlyValue.binder binder,binder1left,_))::rest671) => let val result=
MlyValue.SUFFIX((
Parse_support.bind_restr_term binder BV_LIST PTRM1 PTRM2))
 in (LrTable.NT 4,(result,binder1left,PTRM2right),rest671) end
| (25,(_,(MlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(MlyValue.BV_LIST 
BV_LIST,_,_))::(_,(MlyValue.binder binder,binder1left,_))::rest671)
 => let val result=MlyValue.SUFFIX((
Parse_support.bind_term binder BV_LIST PTRM))
 in (LrTable.NT 4,(result,binder1left,PTRM1right),rest671) end
| (26,(_,(MlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(
MlyValue.BINDING_LIST BINDING_LIST,_,_))::(_,(_,let_1left,_))::rest671
) => let val result=MlyValue.SUFFIX((
Parse_support.make_let BINDING_LIST PTRM))
 in (LrTable.NT 4,(result,let_1left,PTRM1right),rest671) end
| (27,(_,(MlyValue.BV_LIST BV_LIST,_,BV_LIST1right))::(_,(MlyValue.BV 
BV,BV1left,_))::rest671) => let val result=MlyValue.BV_LIST((
BV::BV_LIST))
 in (LrTable.NT 5,(result,BV1left,BV_LIST1right),rest671) end
| (28,(_,(MlyValue.BV BV,BV1left,BV1right))::rest671) => let val 
result=MlyValue.BV_LIST(([BV]))
 in (LrTable.NT 5,(result,BV1left,BV1right),rest671) end
| (29,(_,(_,_,rparen1right))::(_,(MlyValue.BV BV,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.BV((BV))
 in (LrTable.NT 6,(result,lparen1left,rparen1right),rest671) end
| (30,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.BV((Parse_support.make_binding_occ ident))
 in (LrTable.NT 6,(result,ident1left,ident1right),rest671) end
| (31,(_,(MlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=MlyValue.BV((Parse_support.make_aq_binding_occ aq))
 in (LrTable.NT 6,(result,aq1left,aq1right),rest671) end
| (32,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.BV BV,
BV1left,_))::rest671) => let val result=MlyValue.BV((
Parse_support.make_constrained_vstruct BV TYPE))
 in (LrTable.NT 6,(result,BV1left,TYPE1right),rest671) end
| (33,(_,(_,_,rparen1right))::(_,(MlyValue.VSTRUCT VSTRUCT,_,_))::_::(
_,(MlyValue.BV BV,_,_))::(_,(_,lparen1left,_))::rest671) => let val 
result=MlyValue.BV((Parse_support.make_vstruct (BV::VSTRUCT)))
 in (LrTable.NT 6,(result,lparen1left,rparen1right),rest671) end
| (34,(_,(MlyValue.BV BV,BV1left,BV1right))::rest671) => let val 
result=MlyValue.VSTRUCT(([BV]))
 in (LrTable.NT 7,(result,BV1left,BV1right),rest671) end
| (35,(_,(MlyValue.VSTRUCT VSTRUCT,_,VSTRUCT1right))::_::(_,(
MlyValue.BV BV,BV1left,_))::rest671) => let val result=
MlyValue.VSTRUCT((BV::VSTRUCT))
 in (LrTable.NT 7,(result,BV1left,VSTRUCT1right),rest671) end
| (36,(_,(MlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(MlyValue.BV_LIST 
BV_LIST,BV_LIST1left,_))::rest671) => let val result=
MlyValue.BINDING_LIST(([(BV_LIST,PTRM)]))
 in (LrTable.NT 8,(result,BV_LIST1left,PTRM1right),rest671) end
| (37,(_,(MlyValue.BINDING_LIST BINDING_LIST,_,BINDING_LIST1right))::_
::(_,(MlyValue.PTRM PTRM,_,_))::_::(_,(MlyValue.BV_LIST BV_LIST,
BV_LIST1left,_))::rest671) => let val result=MlyValue.BINDING_LIST((
(BV_LIST,PTRM)::BINDING_LIST))
 in (LrTable.NT 8,(result,BV_LIST1left,BINDING_LIST1right),rest671)
 end
| (38,(_,(MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=MlyValue.COMMA((
if (symbolic_ident = ",")
                        then ()
                        else raise HOL_PARSE_ERR{function = "",
                                   message = "expecting a \",\" in varstruct"}
))
 in (LrTable.NT 9,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| (39,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.PLUS_TYPE
 PLUS_TYPE,PLUS_TYPE1left,_))::rest671) => let val result=
MlyValue.TYPE((
Parse_support.make_type_app
                                        ("fun",[PLUS_TYPE, TYPE])
))
 in (LrTable.NT 11,(result,PLUS_TYPE1left,TYPE1right),rest671) end
| (40,(_,(MlyValue.PLUS_TYPE PLUS_TYPE,PLUS_TYPE1left,PLUS_TYPE1right)
)::rest671) => let val result=MlyValue.TYPE((PLUS_TYPE))
 in (LrTable.NT 11,(result,PLUS_TYPE1left,PLUS_TYPE1right),rest671)
 end
| (41,(_,(MlyValue.PLUS_TYPE PLUS_TYPE,_,PLUS_TYPE1right))::_::(_,(
MlyValue.HASH_TYPE HASH_TYPE,HASH_TYPE1left,_))::rest671) => let val 
result=MlyValue.PLUS_TYPE((
Parse_support.make_type_app
                                           ("sum",[HASH_TYPE,PLUS_TYPE])
))
 in (LrTable.NT 13,(result,HASH_TYPE1left,PLUS_TYPE1right),rest671)
 end
| (42,(_,(MlyValue.HASH_TYPE HASH_TYPE,HASH_TYPE1left,HASH_TYPE1right)
)::rest671) => let val result=MlyValue.PLUS_TYPE((HASH_TYPE))
 in (LrTable.NT 13,(result,HASH_TYPE1left,HASH_TYPE1right),rest671)
 end
| (43,(_,(MlyValue.HASH_TYPE HASH_TYPE,_,HASH_TYPE1right))::_::(_,(
MlyValue.APP_TYPE APP_TYPE,APP_TYPE1left,_))::rest671) => let val 
result=MlyValue.HASH_TYPE((
Parse_support.make_type_app
                                          ("prod",[APP_TYPE,HASH_TYPE])
))
 in (LrTable.NT 12,(result,APP_TYPE1left,HASH_TYPE1right),rest671) end
| (44,(_,(MlyValue.APP_TYPE APP_TYPE,APP_TYPE1left,APP_TYPE1right))::
rest671) => let val result=MlyValue.HASH_TYPE((APP_TYPE))
 in (LrTable.NT 12,(result,APP_TYPE1left,APP_TYPE1right),rest671) end
| (45,(_,(MlyValue.type_ident type_ident,_,type_ident1right))::(_,(
MlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=MlyValue.APP_TYPE((
Parse_support.make_type_app
                                    (type_ident, TYPE_ARG)
))
 in (LrTable.NT 14,(result,TYPE_ARG1left,type_ident1right),rest671)
 end
| (46,(_,(MlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=MlyValue.APP_TYPE((BASIC))
 in (LrTable.NT 14,(result,BASIC1left,BASIC1right),rest671) end
| (47,(_,(MlyValue.type_ident type_ident,_,type_ident1right))::(_,(
MlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=MlyValue.TYPE_ARG((
[Parse_support.make_type_app
                                         (type_ident,TYPE_ARG)]
))
 in (LrTable.NT 15,(result,TYPE_ARG1left,type_ident1right),rest671)
 end
| (48,(_,(MlyValue.BASIC_TYPE_ARG BASIC_TYPE_ARG,BASIC_TYPE_ARG1left,
BASIC_TYPE_ARG1right))::rest671) => let val result=MlyValue.TYPE_ARG((
BASIC_TYPE_ARG))
 in (LrTable.NT 15,(result,BASIC_TYPE_ARG1left,BASIC_TYPE_ARG1right),
rest671) end
| (49,(_,(_,_,type_rparen1right))::(_,(MlyValue.TYPE_LIST TYPE_LIST,_,
_))::_::(_,(MlyValue.TYPE TYPE,_,_))::(_,(_,type_lparen1left,_))::
rest671) => let val result=MlyValue.BASIC_TYPE_ARG((TYPE::TYPE_LIST))
 in (LrTable.NT 16,(result,type_lparen1left,type_rparen1right),rest671
) end
| (50,(_,(MlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=MlyValue.BASIC_TYPE_ARG(([BASIC]))
 in (LrTable.NT 16,(result,BASIC1left,BASIC1right),rest671) end
| (51,(_,(MlyValue.TYPE_LIST TYPE_LIST,_,TYPE_LIST1right))::_::(_,(
MlyValue.TYPE TYPE,TYPE1left,_))::rest671) => let val result=
MlyValue.TYPE_LIST((TYPE::TYPE_LIST))
 in (LrTable.NT 17,(result,TYPE1left,TYPE_LIST1right),rest671) end
| (52,(_,(MlyValue.TYPE TYPE,TYPE1left,TYPE1right))::rest671) => let 
val result=MlyValue.TYPE_LIST(([TYPE]))
 in (LrTable.NT 17,(result,TYPE1left,TYPE1right),rest671) end
| (53,(_,(MlyValue.type_var_ident type_var_ident,type_var_ident1left,
type_var_ident1right))::rest671) => let val result=MlyValue.BASIC((
Parse_support.Preterm.Term.Type.mk_vartype type_var_ident))
 in (LrTable.NT 18,(result,type_var_ident1left,type_var_ident1right),
rest671) end
| (54,(_,(MlyValue.type_ident type_ident,type_ident1left,
type_ident1right))::rest671) => let val result=MlyValue.BASIC((
case (!Globals.in_type_spec)
          of NONE => Parse_support.make_atomic_type type_ident
           | (SOME s)
              => if (type_ident = s)
                 then if (can Parse_support.make_atomic_type type_ident)
                      then raise HOL_PARSE_ERR{function="",
                           message=(Lib.quote type_ident^" is already a type")}
                      else (Parse_support.rec_occ)
                 else Parse_support.make_atomic_type type_ident
))
 in (LrTable.NT 18,(result,type_ident1left,type_ident1right),rest671)
 end
| (55,(_,(MlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=MlyValue.BASIC((Parse_support.extract_type_antiq aq))
 in (LrTable.NT 18,(result,aq1left,aq1right),rest671) end
| (56,(_,(_,_,type_rparen1right))::(_,(MlyValue.TYPE TYPE,_,_))::(_,(_
,type_lparen1left,_))::rest671) => let val result=MlyValue.BASIC((TYPE
))
 in (LrTable.NT 18,(result,type_lparen1left,type_rparen1right),rest671
) end
| (57,(_,(MlyValue.TYPE_CLAUSES TYPE_CLAUSES,_,TYPE_CLAUSES1right))::_
::(_,(MlyValue.TYI TYI,TYI1left,_))::rest671) => let val result=
MlyValue.TYPE_SPEC(({ty_name=TYI,clauses=TYPE_CLAUSES}))
 in (LrTable.NT 19,(result,TYI1left,TYPE_CLAUSES1right),rest671) end
| (58,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.TYI((Globals.in_type_spec := SOME ident; ident
))
 in (LrTable.NT 20,(result,ident1left,ident1right),rest671) end
| (59,(_,(MlyValue.TYPE_CLAUSE TYPE_CLAUSE,TYPE_CLAUSE1left,
TYPE_CLAUSE1right))::rest671) => let val result=MlyValue.TYPE_CLAUSES(
([Parse_support.make_type_clause TYPE_CLAUSE]))
 in (LrTable.NT 21,(result,TYPE_CLAUSE1left,TYPE_CLAUSE1right),rest671
) end
| (60,(_,(MlyValue.TYPE_CLAUSES TYPE_CLAUSES,_,TYPE_CLAUSES1right))::_
::(_,(MlyValue.TYPE_CLAUSE TYPE_CLAUSE,TYPE_CLAUSE1left,_))::rest671)
 => let val result=MlyValue.TYPE_CLAUSES((
Parse_support.make_type_clause TYPE_CLAUSE::TYPE_CLAUSES))
 in (LrTable.NT 21,(result,TYPE_CLAUSE1left,TYPE_CLAUSES1right),
rest671) end
| (61,(_,(MlyValue.string_ string_,string_1left,string_1right))::
rest671) => let val result=MlyValue.TYPE_CLAUSE((
{constructor=string_ , args=[]}))
 in (LrTable.NT 22,(result,string_1left,string_1right),rest671) end
| (62,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.TYPE_CLAUSE(({constructor=ident, args=[]}))
 in (LrTable.NT 22,(result,ident1left,ident1right),rest671) end
| (63,(_,(MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=
MlyValue.TYPE_CLAUSE(({constructor=symbolic_ident, args=[]}))
 in (LrTable.NT 22,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| (64,(_,(MlyValue.C_ARG_LIST C_ARG_LIST,_,C_ARG_LIST1right))::_::(_,(
MlyValue.ident ident,ident1left,_))::rest671) => let val result=
MlyValue.TYPE_CLAUSE(({constructor=ident,args = C_ARG_LIST}))
 in (LrTable.NT 22,(result,ident1left,C_ARG_LIST1right),rest671) end
| (65,(_,(MlyValue.C_ARG_LIST C_ARG_LIST,_,C_ARG_LIST1right))::_::(_,(
MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,_))::
rest671) => let val result=MlyValue.TYPE_CLAUSE((
{constructor=symbolic_ident,args=C_ARG_LIST}))
 in (LrTable.NT 22,(result,symbolic_ident1left,C_ARG_LIST1right),
rest671) end
| (66,(_,(MlyValue.C_ARG_LIST C_ARG_LIST,_,C_ARG_LIST1right))::_::(_,(
MlyValue.TYPE TYPE,TYPE1left,_))::rest671) => let val result=
MlyValue.C_ARG_LIST((TYPE::C_ARG_LIST))
 in (LrTable.NT 23,(result,TYPE1left,C_ARG_LIST1right),rest671) end
| (67,(_,(MlyValue.TYPE TYPE,TYPE1left,TYPE1right))::rest671) => let 
val result=MlyValue.C_ARG_LIST(([TYPE]))
 in (LrTable.NT 23,(result,TYPE1left,TYPE1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : hol_TOKENS =
struct
type svalue = ParserData.svalue
structure Parse_support = Parse_support;
type ('a,'b) token = ('a,'b) Token.token
fun ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.ident i,p1,p2))
fun symbolic_ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.symbolic_ident i,p1,p2))
fun qualified_ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.qualified_ident i,p1,p2))
fun type_ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.type_ident i,p1,p2))
fun qualified_type_ident (i,p1,p2) = Token.TOKEN (
ParserData.LrTable.T 4,(ParserData.MlyValue.qualified_type_ident i,p1,p2))
fun type_var_ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.type_var_ident i,p1,p2))
fun binder (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.binder i,p1,p2))
fun qualified_binder (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.qualified_binder i,p1,p2))
fun aq (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.aq i,p1,p2))
fun lparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun rparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun type_lparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun type_rparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun lbracket (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun rbracket (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun lbrace (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun rbrace (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun type_comma (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun colon (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun dcolon (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun dot (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun semi_colon (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun type_right_arrow (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun eq_gt (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun eq (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun type_hash (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun type_plus (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun bar (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun let_ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun and_ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun in_ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun of_ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun string_ (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.string_ i,p1,p2))
fun EOLEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID,p1,p2))
end
end