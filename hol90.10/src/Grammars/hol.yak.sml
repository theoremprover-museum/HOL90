functor HolLrValsFun (Token : TOKEN) = 
struct
structure ParserData=
struct
structure Header = 
struct
open CoreHol
open Parse_support;

fun make_cond tyvars tm0 tm1 tm2 =
    list_make_comb[make_atom tyvars "COND", prec_parse tm0, tm1, tm2];

val rbinder = bind_restr_term;

fun HOL_PARSE_ERR{function,message} = 
 Exception.HOL_ERR{origin_structure = "HOL grammar",
             origin_function = function,
             message = message};

type arg = (int,Type.hol_type) Lib.istream

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\155\000\002\000\155\000\004\000\157\000\007\000\155\000\
\\009\000\155\000\010\000\155\000\011\000\155\000\013\000\155\000\
\\014\000\155\000\015\000\155\000\016\000\155\000\017\000\155\000\
\\018\000\155\000\019\000\155\000\020\000\155\000\021\000\155\000\
\\022\000\155\000\023\000\155\000\024\000\155\000\025\000\155\000\
\\026\000\155\000\027\000\155\000\028\000\155\000\029\000\155\000\
\\030\000\155\000\031\000\155\000\033\000\155\000\034\000\155\000\
\\035\000\155\000\000\000\
\\001\000\001\000\156\000\002\000\156\000\004\000\159\000\007\000\156\000\
\\009\000\156\000\010\000\156\000\011\000\156\000\013\000\156\000\
\\014\000\156\000\015\000\156\000\016\000\156\000\017\000\156\000\
\\018\000\156\000\019\000\156\000\020\000\156\000\021\000\156\000\
\\022\000\156\000\023\000\156\000\024\000\156\000\025\000\156\000\
\\026\000\156\000\027\000\156\000\028\000\156\000\029\000\156\000\
\\030\000\156\000\031\000\156\000\033\000\156\000\034\000\156\000\
\\035\000\156\000\000\000\
\\001\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\019\000\011\000\
\\020\000\010\000\024\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\001\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\020\000\010\000\
\\024\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\001\000\001\000\028\000\009\000\027\000\010\000\026\000\000\000\
\\001\000\001\000\038\000\004\000\037\000\006\000\036\000\009\000\035\000\
\\012\000\034\000\000\000\
\\001\000\001\000\078\000\002\000\077\000\033\000\076\000\000\000\
\\001\000\002\000\073\000\011\000\072\000\019\000\050\000\000\000\
\\001\000\004\000\037\000\006\000\036\000\009\000\035\000\012\000\034\000\000\000\
\\001\000\004\000\054\000\000\000\
\\001\000\011\000\063\000\000\000\
\\001\000\011\000\100\000\000\000\
\\001\000\013\000\083\000\018\000\082\000\025\000\057\000\026\000\056\000\
\\027\000\055\000\000\000\
\\001\000\013\000\106\000\000\000\
\\001\000\015\000\062\000\000\000\
\\001\000\017\000\059\000\000\000\
\\001\000\017\000\097\000\000\000\
\\001\000\020\000\065\000\021\000\064\000\000\000\
\\001\000\021\000\098\000\000\000\
\\001\000\024\000\051\000\000\000\
\\001\000\024\000\053\000\000\000\
\\001\000\028\000\067\000\000\000\
\\001\000\031\000\048\000\000\000\
\\001\000\034\000\000\000\035\000\000\000\000\000\
\\114\000\000\000\
\\115\000\025\000\057\000\026\000\056\000\027\000\055\000\000\000\
\\116\000\000\000\
\\117\000\000\000\
\\118\000\000\000\
\\119\000\000\000\
\\120\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\020\000\010\000\
\\023\000\022\000\024\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\121\000\025\000\057\000\026\000\056\000\027\000\055\000\000\000\
\\122\000\019\000\046\000\000\000\
\\123\000\025\000\057\000\026\000\056\000\027\000\055\000\000\000\
\\124\000\019\000\019\000\000\000\
\\125\000\000\000\
\\126\000\000\000\
\\127\000\000\000\
\\128\000\000\000\
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
\\139\000\000\000\
\\140\000\000\000\
\\141\000\025\000\057\000\026\000\056\000\027\000\055\000\000\000\
\\142\000\000\000\
\\143\000\002\000\073\000\019\000\050\000\000\000\
\\144\000\000\000\
\\145\000\030\000\089\000\000\000\
\\146\000\000\000\
\\147\000\000\000\
\\148\000\001\000\028\000\009\000\027\000\010\000\026\000\019\000\050\000\000\000\
\\149\000\001\000\018\000\002\000\017\000\007\000\016\000\009\000\015\000\
\\010\000\014\000\014\000\013\000\016\000\012\000\020\000\010\000\
\\024\000\009\000\029\000\008\000\033\000\007\000\000\000\
\\150\000\022\000\061\000\000\000\
\\150\000\022\000\061\000\028\000\060\000\000\000\
\\151\000\000\000\
\\152\000\025\000\057\000\026\000\056\000\027\000\055\000\000\000\
\\153\000\026\000\056\000\027\000\055\000\000\000\
\\154\000\026\000\056\000\000\000\
\\158\000\000\000\
\\160\000\000\000\
\\161\000\000\000\
\\162\000\000\000\
\\163\000\000\000\
\\164\000\000\000\
\\165\000\018\000\107\000\025\000\057\000\026\000\056\000\027\000\055\000\000\000\
\\166\000\000\000\
\\167\000\000\000\
\\168\000\028\000\092\000\000\000\
\\169\000\000\000\
\\170\000\000\000\
\\171\000\032\000\094\000\000\000\
\\172\000\032\000\093\000\000\000\
\\173\000\000\000\
\\174\000\000\000\
\\175\000\000\000\
\\176\000\023\000\110\000\025\000\057\000\026\000\056\000\027\000\055\000\000\000\
\\177\000\000\000\
\"
val actionRowNumbers =
"\002\000\027\000\034\000\030\000\
\\024\000\038\000\004\000\039\000\
\\040\000\005\000\059\000\059\000\
\\003\000\037\000\004\000\036\000\
\\035\000\008\000\028\000\032\000\
\\003\000\022\000\058\000\019\000\
\\004\000\050\000\049\000\020\000\
\\026\000\001\000\009\000\025\000\
\\008\000\069\000\067\000\068\000\
\\074\000\015\000\061\000\014\000\
\\060\000\010\000\017\000\033\000\
\\008\000\021\000\003\000\057\000\
\\008\000\003\000\007\000\006\000\
\\000\000\008\000\008\000\008\000\
\\012\000\043\000\003\000\059\000\
\\042\000\041\000\003\000\003\000\
\\031\000\003\000\047\000\051\000\
\\055\000\004\000\048\000\084\000\
\\075\000\073\000\077\000\079\000\
\\078\000\064\000\065\000\063\000\
\\008\000\070\000\016\000\062\000\
\\046\000\018\000\029\000\004\000\
\\011\000\053\000\006\000\008\000\
\\008\000\013\000\072\000\044\000\
\\003\000\056\000\052\000\004\000\
\\076\000\081\000\083\000\080\000\
\\066\000\008\000\045\000\054\000\
\\008\000\071\000\082\000\023\000"
val gotoT =
"\
\\001\000\111\000\002\000\004\000\003\000\003\000\004\000\002\000\
\\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\004\000\019\000\005\000\018\000\000\000\
\\000\000\
\\000\000\
\\006\000\023\000\007\000\022\000\009\000\021\000\000\000\
\\000\000\
\\000\000\
\\012\000\031\000\013\000\030\000\015\000\029\000\016\000\028\000\
\\017\000\027\000\000\000\
\\002\000\038\000\003\000\003\000\004\000\002\000\005\000\001\000\
\\011\000\037\000\000\000\
\\002\000\040\000\003\000\003\000\004\000\002\000\005\000\001\000\
\\011\000\039\000\000\000\
\\002\000\041\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\006\000\042\000\007\000\022\000\000\000\
\\000\000\
\\000\000\
\\012\000\043\000\013\000\030\000\015\000\029\000\000\000\
\\000\000\
\\000\000\
\\002\000\045\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\006\000\047\000\007\000\022\000\000\000\
\\000\000\
\\007\000\050\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\056\000\013\000\030\000\015\000\029\000\000\000\
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
\\012\000\064\000\013\000\030\000\015\000\029\000\000\000\
\\000\000\
\\002\000\066\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\012\000\067\000\013\000\030\000\015\000\029\000\000\000\
\\002\000\068\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\010\000\069\000\000\000\
\\018\000\073\000\019\000\072\000\000\000\
\\000\000\
\\012\000\077\000\013\000\030\000\015\000\029\000\000\000\
\\012\000\078\000\013\000\030\000\015\000\029\000\000\000\
\\012\000\079\000\013\000\030\000\015\000\029\000\000\000\
\\000\000\
\\000\000\
\\002\000\082\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\002\000\040\000\003\000\003\000\004\000\002\000\005\000\001\000\
\\011\000\083\000\000\000\
\\000\000\
\\000\000\
\\002\000\084\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\002\000\085\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\002\000\086\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\089\000\008\000\088\000\000\000\
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
\\012\000\094\000\013\000\030\000\014\000\093\000\015\000\029\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\023\000\007\000\022\000\009\000\097\000\000\000\
\\000\000\
\\010\000\099\000\000\000\
\\018\000\100\000\019\000\072\000\000\000\
\\012\000\102\000\013\000\030\000\015\000\029\000\020\000\101\000\000\000\
\\012\000\102\000\013\000\030\000\015\000\029\000\020\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\106\000\003\000\003\000\004\000\002\000\005\000\001\000\000\000\
\\000\000\
\\000\000\
\\007\000\089\000\008\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\094\000\013\000\030\000\014\000\109\000\015\000\029\000\000\000\
\\000\000\
\\000\000\
\\012\000\102\000\013\000\030\000\015\000\029\000\020\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 112
val numrules = 64
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
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
    let val len = String.size s'
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
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg =  ( int,Type.hol_type )  Lib.istream
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | string_ of  (string)
 | aq of  (CoreHol.Term.term)
 | qualified_binder of  ( ( string*string ) ) | binder of  (string)
 | type_var_ident of  (string)
 | qualified_type_ident of  ( ( string*string ) )
 | type_ident of  (string) | qualified_ident of  ( ( string*string ) )
 | symbolic_ident of  (string) | ident of  (string)
 | CARGS of  (Type.hol_type list)
 | CLAUSE of  ({ constructor:string,args:Type.hol_type list } )
 | CLAUSES of  ({ constructor:string,args:Parse_support.arg list }  list)
 | TYID of  (string)
 | TYSPEC of  ({ ty_name:string,clauses:{ constructor:string,args:Parse_support.arg list }  list } )
 | BASIC of  (Type.hol_type) | TYPE_LIST of  (Type.hol_type list)
 | TYPE_ARG of  (Type.hol_type list) | TYPE of  (Type.hol_type)
 | LIST of  (preterm_in_env list) | COMMA of  (unit)
 | BINDL of  ( ( binder_in_env list * preterm_in_env )  list)
 | VSTRUCT of  (binder_in_env list) | BV of  (binder_in_env)
 | BVL of  (binder_in_env list) | SUFFIX of  (preterm_in_env)
 | AEXP of  (preterm_in_env) | APP of  (preterm_in_env list)
 | PTRM of  (preterm_in_env) | START of  (parse)
end
type svalue = MlyValue.svalue
type result = parse
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change = 
nil
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
  | (T 22) => "eq_gt"
  | (T 23) => "eq"
  | (T 24) => "arrow"
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
local open Header in
val errtermvalue=
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
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (tyvars):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.PTRM PTRM,PTRM1left,PTRM1right))::rest671) => let 
val result=MlyValue.START((PTM (make_preterm PTRM)))
 in (LrTable.NT 0,(result,PTRM1left,PTRM1right),rest671) end
| (1,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::(_,(_,colon1left,_))::
rest671) => let val result=MlyValue.START((TY TYPE))
 in (LrTable.NT 0,(result,colon1left,TYPE1right),rest671) end
| (2,(_,(MlyValue.TYSPEC TYSPEC,_,TYSPEC1right))::(_,(_,colon1left,_))
::rest671) => let val result=MlyValue.START((TY_SPEC TYSPEC))
 in (LrTable.NT 0,(result,colon1left,TYSPEC1right),rest671) end
| (3,(_,(MlyValue.SUFFIX SUFFIX,SUFFIX1left,SUFFIX1right))::rest671)
 => let val result=MlyValue.PTRM((SUFFIX))
 in (LrTable.NT 1,(result,SUFFIX1left,SUFFIX1right),rest671) end
| (4,(_,(MlyValue.SUFFIX SUFFIX,_,SUFFIX1right))::(_,(MlyValue.APP APP
,APP1left,_))::rest671) => let val result=MlyValue.PTRM((
prec_parse (rev(APP)@[SUFFIX])))
 in (LrTable.NT 1,(result,APP1left,SUFFIX1right),rest671) end
| (5,(_,(MlyValue.PTRM PTRM2,_,PTRM2right))::_::(_,(MlyValue.PTRM 
PTRM1,_,_))::_::(_,(MlyValue.APP APP,APP1left,_))::rest671) => let 
val result=MlyValue.PTRM((make_cond tyvars (rev APP) PTRM1 PTRM2))
 in (LrTable.NT 1,(result,APP1left,PTRM2right),rest671) end
| (6,(_,(MlyValue.APP APP,APP1left,APP1right))::rest671) => let val 
result=MlyValue.PTRM((prec_parse (rev APP)))
 in (LrTable.NT 1,(result,APP1left,APP1right),rest671) end
| (7,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.AEXP AEXP,
_,_))::(_,(MlyValue.APP APP,APP1left,_))::rest671) => let val result=
MlyValue.APP(([make_constrained(prec_parse(rev(AEXP::APP)))TYPE]))
 in (LrTable.NT 2,(result,APP1left,TYPE1right),rest671) end
| (8,(_,(MlyValue.AEXP AEXP,_,AEXP1right))::(_,(MlyValue.APP APP,
APP1left,_))::rest671) => let val result=MlyValue.APP((AEXP::APP))
 in (LrTable.NT 2,(result,APP1left,AEXP1right),rest671) end
| (9,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.AEXP AEXP,
AEXP1left,_))::rest671) => let val result=MlyValue.APP((
[make_constrained AEXP TYPE]))
 in (LrTable.NT 2,(result,AEXP1left,TYPE1right),rest671) end
| (10,(_,(MlyValue.AEXP AEXP,AEXP1left,AEXP1right))::rest671) => let 
val result=MlyValue.APP(([AEXP]))
 in (LrTable.NT 2,(result,AEXP1left,AEXP1right),rest671) end
| (11,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.AEXP((make_atom tyvars ident))
 in (LrTable.NT 3,(result,ident1left,ident1right),rest671) end
| (12,(_,(MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=MlyValue.AEXP((
make_atom tyvars symbolic_ident))
 in (LrTable.NT 3,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| (13,(_,(MlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=MlyValue.AEXP((make_aq aq))
 in (LrTable.NT 3,(result,aq1left,aq1right),rest671) end
| (14,(_,(MlyValue.string_ string_,string_1left,string_1right))::
rest671) => let val result=MlyValue.AEXP((make_string string_))
 in (LrTable.NT 3,(result,string_1left,string_1right),rest671) end
| (15,(_,(_,eq1left,eq1right))::rest671) => let val result=
MlyValue.AEXP((make_atom tyvars "="))
 in (LrTable.NT 3,(result,eq1left,eq1right),rest671) end
| (16,(_,(_,dcolon1left,dcolon1right))::rest671) => let val result=
MlyValue.AEXP((make_atom tyvars "::"))
 in (LrTable.NT 3,(result,dcolon1left,dcolon1right),rest671) end
| (17,(_,(_,_,rparen1right))::(_,(MlyValue.PTRM PTRM,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.AEXP((PTRM))
 in (LrTable.NT 3,(result,lparen1left,rparen1right),rest671) end
| (18,(_,(_,_,rbracket1right))::(_,(MlyValue.LIST LIST,_,_))::(_,(_,
lbracket1left,_))::rest671) => let val result=MlyValue.AEXP((
make_list tyvars LIST))
 in (LrTable.NT 3,(result,lbracket1left,rbracket1right),rest671) end
| (19,(_,(_,_,rbrace1right))::(_,(MlyValue.LIST LIST,_,_))::(_,(_,
lbrace1left,_))::rest671) => let val result=MlyValue.AEXP((
make_set tyvars LIST))
 in (LrTable.NT 3,(result,lbrace1left,rbrace1right),rest671) end
| (20,(_,(_,_,rbrace1right))::(_,(MlyValue.PTRM PTRM2,_,_))::_::(_,(
MlyValue.PTRM PTRM1,_,_))::(_,(_,lbrace1left,_))::rest671) => let val 
result=MlyValue.AEXP((make_set_abs tyvars (PTRM1,PTRM2)))
 in (LrTable.NT 3,(result,lbrace1left,rbrace1right),rest671) end
| (21,(_,(MlyValue.PTRM PTRM2,_,PTRM2right))::_::(_,(MlyValue.PTRM 
PTRM1,_,_))::_::(_,(MlyValue.BVL BVL,_,_))::(_,(MlyValue.binder binder
,binder1left,_))::rest671) => let val result=MlyValue.SUFFIX((
rbinder tyvars binder BVL PTRM1 PTRM2))
 in (LrTable.NT 4,(result,binder1left,PTRM2right),rest671) end
| (22,(_,(MlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(MlyValue.BVL BVL,_
,_))::(_,(MlyValue.binder binder,binder1left,_))::rest671) => let val 
result=MlyValue.SUFFIX((bind_term binder BVL PTRM))
 in (LrTable.NT 4,(result,binder1left,PTRM1right),rest671) end
| (23,(_,(MlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(MlyValue.BINDL 
BINDL,_,_))::(_,(_,let_1left,_))::rest671) => let val result=
MlyValue.SUFFIX((make_let tyvars BINDL PTRM))
 in (LrTable.NT 4,(result,let_1left,PTRM1right),rest671) end
| (24,(_,(_,_,rparen1right))::(_,(MlyValue.BV BV,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.BV((BV))
 in (LrTable.NT 6,(result,lparen1left,rparen1right),rest671) end
| (25,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.BV((make_binding_occ tyvars ident))
 in (LrTable.NT 6,(result,ident1left,ident1right),rest671) end
| (26,(_,(MlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=MlyValue.BV((make_aq_binding_occ tyvars aq))
 in (LrTable.NT 6,(result,aq1left,aq1right),rest671) end
| (27,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.BV BV,
BV1left,_))::rest671) => let val result=MlyValue.BV((
make_constrained_vstruct BV TYPE))
 in (LrTable.NT 6,(result,BV1left,TYPE1right),rest671) end
| (28,(_,(_,_,rparen1right))::(_,(MlyValue.VSTRUCT VSTRUCT,_,_))::_::(
_,(MlyValue.BV BV,_,_))::(_,(_,lparen1left,_))::rest671) => let val 
result=MlyValue.BV((make_vstruct tyvars (BV::VSTRUCT)))
 in (LrTable.NT 6,(result,lparen1left,rparen1right),rest671) end
| (29,(_,(MlyValue.BV BV,BV1left,BV1right))::rest671) => let val 
result=MlyValue.VSTRUCT(([BV]))
 in (LrTable.NT 7,(result,BV1left,BV1right),rest671) end
| (30,(_,(MlyValue.VSTRUCT VSTRUCT,_,VSTRUCT1right))::_::(_,(
MlyValue.BV BV,BV1left,_))::rest671) => let val result=
MlyValue.VSTRUCT((BV::VSTRUCT))
 in (LrTable.NT 7,(result,BV1left,VSTRUCT1right),rest671) end
| (31,(_,(MlyValue.PTRM PTRM,_,PTRM1right))::_::(_,(MlyValue.BVL BVL,
BVL1left,_))::rest671) => let val result=MlyValue.BINDL(([(BVL,PTRM)])
)
 in (LrTable.NT 8,(result,BVL1left,PTRM1right),rest671) end
| (32,(_,(MlyValue.BINDL BINDL,_,BINDL1right))::_::(_,(MlyValue.PTRM 
PTRM,_,_))::_::(_,(MlyValue.BVL BVL,BVL1left,_))::rest671) => let val 
result=MlyValue.BINDL(((BVL,PTRM)::BINDL))
 in (LrTable.NT 8,(result,BVL1left,BINDL1right),rest671) end
| (33,(_,(MlyValue.BVL BVL,_,BVL1right))::(_,(MlyValue.BV BV,BV1left,_
))::rest671) => let val result=MlyValue.BVL((BV::BVL))
 in (LrTable.NT 5,(result,BV1left,BVL1right),rest671) end
| (34,(_,(MlyValue.BV BV,BV1left,BV1right))::rest671) => let val 
result=MlyValue.BVL(([BV]))
 in (LrTable.NT 5,(result,BV1left,BV1right),rest671) end
| (35,rest671) => let val result=MlyValue.LIST(([]))
 in (LrTable.NT 10,(result,defaultPos,defaultPos),rest671) end
| (36,(_,(MlyValue.PTRM PTRM,PTRM1left,PTRM1right))::rest671) => let 
val result=MlyValue.LIST(([PTRM]))
 in (LrTable.NT 10,(result,PTRM1left,PTRM1right),rest671) end
| (37,(_,(MlyValue.LIST LIST,_,LIST1right))::_::(_,(MlyValue.PTRM PTRM
,PTRM1left,_))::rest671) => let val result=MlyValue.LIST((PTRM::LIST))
 in (LrTable.NT 10,(result,PTRM1left,LIST1right),rest671) end
| (38,(_,(MlyValue.TYPE TYPE2,_,TYPE2right))::_::(_,(MlyValue.TYPE 
TYPE1,TYPE1left,_))::rest671) => let val result=MlyValue.TYPE((
make_type_app("fun",[TYPE1, TYPE2])))
 in (LrTable.NT 11,(result,TYPE1left,TYPE2right),rest671) end
| (39,(_,(MlyValue.TYPE TYPE2,_,TYPE2right))::_::(_,(MlyValue.TYPE 
TYPE1,TYPE1left,_))::rest671) => let val result=MlyValue.TYPE((
make_type_app("sum",[TYPE1, TYPE2])))
 in (LrTable.NT 11,(result,TYPE1left,TYPE2right),rest671) end
| (40,(_,(MlyValue.TYPE TYPE2,_,TYPE2right))::_::(_,(MlyValue.TYPE 
TYPE1,TYPE1left,_))::rest671) => let val result=MlyValue.TYPE((
make_type_app("prod",[TYPE1,TYPE2])))
 in (LrTable.NT 11,(result,TYPE1left,TYPE2right),rest671) end
| (41,(_,(MlyValue.type_ident type_ident,_,type_ident1right))::(_,(
MlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=MlyValue.TYPE((make_type_app(type_ident, TYPE_ARG)))
 in (LrTable.NT 11,(result,TYPE_ARG1left,type_ident1right),rest671)
 end
| (42,(_,(MlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=MlyValue.TYPE((BASIC))
 in (LrTable.NT 11,(result,BASIC1left,BASIC1right),rest671) end
| (43,(_,(MlyValue.type_ident type_ident,_,type_ident1right))::(_,(
MlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=MlyValue.TYPE_ARG(([make_type_app (type_ident,TYPE_ARG)]))
 in (LrTable.NT 12,(result,TYPE_ARG1left,type_ident1right),rest671)
 end
| (44,(_,(_,_,type_rparen1right))::(_,(MlyValue.TYPE_LIST TYPE_LIST,_,
_))::_::(_,(MlyValue.TYPE TYPE,_,_))::(_,(_,type_lparen1left,_))::
rest671) => let val result=MlyValue.TYPE_ARG((TYPE::TYPE_LIST))
 in (LrTable.NT 12,(result,type_lparen1left,type_rparen1right),rest671
) end
| (45,(_,(MlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=MlyValue.TYPE_ARG(([BASIC]))
 in (LrTable.NT 12,(result,BASIC1left,BASIC1right),rest671) end
| (46,(_,(MlyValue.type_var_ident type_var_ident,type_var_ident1left,
type_var_ident1right))::rest671) => let val result=MlyValue.BASIC((
Preterm.Term.Type.mk_vartype type_var_ident))
 in (LrTable.NT 14,(result,type_var_ident1left,type_var_ident1right),
rest671) end
| (47,(_,(MlyValue.type_ident type_ident,type_ident1left,
type_ident1right))::rest671) => let val result=MlyValue.BASIC((
make_atomic_type(type_ident,!Globals.in_type_spec)))
 in (LrTable.NT 14,(result,type_ident1left,type_ident1right),rest671)
 end
| (48,(_,(MlyValue.aq aq,aq1left,aq1right))::rest671) => let val 
result=MlyValue.BASIC((extract_type_antiq aq))
 in (LrTable.NT 14,(result,aq1left,aq1right),rest671) end
| (49,(_,(_,_,type_rparen1right))::(_,(MlyValue.TYPE TYPE,_,_))::(_,(_
,type_lparen1left,_))::rest671) => let val result=MlyValue.BASIC((TYPE
))
 in (LrTable.NT 14,(result,type_lparen1left,type_rparen1right),rest671
) end
| (50,(_,(MlyValue.TYPE_LIST TYPE_LIST,_,TYPE_LIST1right))::_::(_,(
MlyValue.TYPE TYPE,TYPE1left,_))::rest671) => let val result=
MlyValue.TYPE_LIST((TYPE::TYPE_LIST))
 in (LrTable.NT 13,(result,TYPE1left,TYPE_LIST1right),rest671) end
| (51,(_,(MlyValue.TYPE TYPE,TYPE1left,TYPE1right))::rest671) => let 
val result=MlyValue.TYPE_LIST(([TYPE]))
 in (LrTable.NT 13,(result,TYPE1left,TYPE1right),rest671) end
| (52,(_,(MlyValue.CLAUSES CLAUSES,_,CLAUSES1right))::_::(_,(
MlyValue.TYID TYID,TYID1left,_))::rest671) => let val result=
MlyValue.TYSPEC(({ty_name=TYID,clauses=CLAUSES}))
 in (LrTable.NT 15,(result,TYID1left,CLAUSES1right),rest671) end
| (53,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.TYID((
Globals.in_type_spec := SOME ident; ident))
 in (LrTable.NT 16,(result,ident1left,ident1right),rest671) end
| (54,(_,(MlyValue.CLAUSE CLAUSE,CLAUSE1left,CLAUSE1right))::rest671)
 => let val result=MlyValue.CLAUSES((
[Parse_support.make_type_clause CLAUSE]))
 in (LrTable.NT 17,(result,CLAUSE1left,CLAUSE1right),rest671) end
| (55,(_,(MlyValue.CLAUSES CLAUSES,_,CLAUSES1right))::_::(_,(
MlyValue.CLAUSE CLAUSE,CLAUSE1left,_))::rest671) => let val result=
MlyValue.CLAUSES((make_type_clause CLAUSE::CLAUSES))
 in (LrTable.NT 17,(result,CLAUSE1left,CLAUSES1right),rest671) end
| (56,(_,(MlyValue.string_ string_,string_1left,string_1right))::
rest671) => let val result=MlyValue.CLAUSE((
{constructor=string_ , args=[]}))
 in (LrTable.NT 18,(result,string_1left,string_1right),rest671) end
| (57,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.CLAUSE(({constructor=ident, args=[]}))
 in (LrTable.NT 18,(result,ident1left,ident1right),rest671) end
| (58,(_,(MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=MlyValue.CLAUSE((
{constructor=symbolic_ident, args=[]}))
 in (LrTable.NT 18,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| (59,(_,(MlyValue.CARGS CARGS,_,CARGS1right))::_::(_,(MlyValue.ident 
ident,ident1left,_))::rest671) => let val result=MlyValue.CLAUSE((
{constructor=ident,args = CARGS}))
 in (LrTable.NT 18,(result,ident1left,CARGS1right),rest671) end
| (60,(_,(MlyValue.CARGS CARGS,_,CARGS1right))::_::(_,(
MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,_))::
rest671) => let val result=MlyValue.CLAUSE((
{constructor=symbolic_ident,args=CARGS}))
 in (LrTable.NT 18,(result,symbolic_ident1left,CARGS1right),rest671)
 end
| (61,(_,(MlyValue.CARGS CARGS,_,CARGS1right))::_::(_,(MlyValue.TYPE 
TYPE,TYPE1left,_))::rest671) => let val result=MlyValue.CARGS((
TYPE::CARGS))
 in (LrTable.NT 19,(result,TYPE1left,CARGS1right),rest671) end
| (62,(_,(MlyValue.TYPE TYPE,TYPE1left,TYPE1right))::rest671) => let 
val result=MlyValue.CARGS(([TYPE]))
 in (LrTable.NT 19,(result,TYPE1left,TYPE1right),rest671) end
| (63,(_,(MlyValue.symbolic_ident symbolic_ident,symbolic_ident1left,
symbolic_ident1right))::rest671) => let val result=MlyValue.COMMA((
if (symbolic_ident = ",")
        then () else raise HOL_PARSE_ERR{function = "",
                                   message = "expecting a \",\" in varstruct"}
))
 in (LrTable.NT 9,(result,symbolic_ident1left,symbolic_ident1right),
rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : Hol_TOKENS =
struct
type svalue = ParserData.svalue
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
fun eq_gt (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun eq (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun arrow (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
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
