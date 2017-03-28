
functor thyLrValsFun (structure Token : TOKEN
                               structure Term : Term_sig) = 
struct
structure ParserData=
struct
structure Header = 
struct
structure Term = Term;

fun THY_YAK_ERR{function,message} = 
 Exception.HOL_ERR{origin_structure = "theory grammar file (thy_yak)",
             origin_function = function,
             message = message};


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\008\000\005\000\007\000\006\000\006\000\007\000\005\000\
\\017\000\004\000\000\000\
\\001\000\001\000\011\000\004\000\010\000\005\000\007\000\006\000\006\000\
\\007\000\005\000\017\000\004\000\000\000\
\\001\000\001\000\016\000\000\000\
\\001\000\002\000\066\000\008\000\064\000\010\000\064\000\011\000\064\000\
\\014\000\064\000\015\000\064\000\016\000\064\000\000\000\
\\001\000\002\000\069\000\008\000\065\000\010\000\065\000\011\000\065\000\
\\014\000\065\000\015\000\065\000\016\000\065\000\000\000\
\\001\000\002\000\026\000\003\000\025\000\009\000\024\000\000\000\
\\001\000\002\000\028\000\000\000\
\\001\000\007\000\013\000\000\000\
\\001\000\008\000\015\000\000\000\
\\001\000\008\000\032\000\000\000\
\\001\000\008\000\040\000\000\000\
\\001\000\008\000\048\000\000\000\
\\001\000\010\000\039\000\011\000\038\000\000\000\
\\001\000\010\000\044\000\000\000\
\\001\000\012\000\027\000\000\000\
\\001\000\013\000\043\000\000\000\
\\001\000\018\000\000\000\019\000\000\000\000\000\
\\050\000\000\000\
\\051\000\000\000\
\\052\000\000\000\
\\053\000\000\000\
\\054\000\000\000\
\\054\000\012\000\014\000\000\000\
\\055\000\000\000\
\\056\000\000\000\
\\057\000\000\000\
\\058\000\000\000\
\\059\000\014\000\030\000\000\000\
\\060\000\000\000\
\\061\000\016\000\031\000\000\000\
\\062\000\000\000\
\\063\000\015\000\029\000\000\000\
\\067\000\000\000\
\\068\000\000\000\
\\070\000\000\000\
\\071\000\011\000\045\000\000\000\
\\072\000\000\000\
\\073\000\000\000\
\\074\000\000\000\
\"
val actionRowNumbers =
"\000\000\017\000\019\000\001\000\
\\020\000\018\000\021\000\000\000\
\\007\000\022\000\008\000\002\000\
\\005\000\025\000\014\000\004\000\
\\032\000\006\000\031\000\027\000\
\\029\000\009\000\005\000\036\000\
\\037\000\005\000\003\000\005\000\
\\005\000\005\000\023\000\012\000\
\\010\000\030\000\026\000\028\000\
\\005\000\038\000\015\000\013\000\
\\035\000\000\000\033\000\005\000\
\\011\000\034\000\024\000\016\000"
val gotoT =
"\
\\001\000\047\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\007\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\010\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\021\000\004\000\020\000\005\000\019\000\006\000\018\000\
\\007\000\017\000\008\000\016\000\010\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\031\000\004\000\020\000\005\000\019\000\006\000\018\000\
\\007\000\017\000\008\000\016\000\010\000\015\000\000\000\
\\000\000\
\\000\000\
\\003\000\032\000\004\000\020\000\005\000\019\000\006\000\018\000\
\\007\000\017\000\008\000\016\000\010\000\015\000\000\000\
\\000\000\
\\004\000\033\000\006\000\018\000\007\000\017\000\008\000\016\000\
\\010\000\015\000\000\000\
\\003\000\034\000\004\000\020\000\005\000\019\000\006\000\018\000\
\\007\000\017\000\008\000\016\000\010\000\015\000\000\000\
\\004\000\020\000\005\000\035\000\006\000\018\000\007\000\017\000\
\\008\000\016\000\010\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\040\000\004\000\020\000\005\000\019\000\006\000\018\000\
\\007\000\017\000\008\000\016\000\009\000\039\000\010\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\044\000\000\000\
\\000\000\
\\003\000\040\000\004\000\020\000\005\000\019\000\006\000\018\000\
\\007\000\017\000\008\000\016\000\009\000\045\000\010\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 48
val numrules = 25
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
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | string_ of  (string)
 | num of  (string) | db_index of  (int) | type_var_ident of  (string)
 | type_ident of  (string) | ident of  (string)
 | BASIC of  (Term.Type.hol_type)
 | TYPE_LIST of  (Term.Type.hol_type list)
 | BASIC_TYPE_ARG of  (Term.Type.hol_type list)
 | TYPE_ARG of  (Term.Type.hol_type list)
 | APP_TYPE of  (Term.Type.hol_type)
 | PLUS_TYPE of  (Term.Type.hol_type)
 | HASH_TYPE of  (Term.Type.hol_type) | TYPE of  (Term.Type.hol_type)
 | TERM of  (Term.term) | START of  (Term.term)
end
type svalue = MlyValue.svalue
type result = Term.term
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change = 
nil
val noShift = 
fn (T 18) => true | _ => false
val showTerminal =
fn (T 0) => "ident"
  | (T 1) => "type_ident"
  | (T 2) => "type_var_ident"
  | (T 3) => "lambda"
  | (T 4) => "db_index"
  | (T 5) => "num"
  | (T 6) => "lparen"
  | (T 7) => "rparen"
  | (T 8) => "type_lparen"
  | (T 9) => "type_rparen"
  | (T 10) => "type_comma"
  | (T 11) => "colon"
  | (T 12) => "dot"
  | (T 13) => "type_right_arrow"
  | (T 14) => "type_hash"
  | (T 15) => "type_plus"
  | (T 16) => "string_"
  | (T 17) => "EOLEX"
  | (T 18) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 3) :: (T 6) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 
11) :: (T 12) :: (T 13) :: (T 14) :: (T 15) :: (T 17) :: (T 18) :: nil
end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.TERM TERM,TERM1left,TERM1right))::rest671) => let 
val result=MlyValue.START((TERM))
 in (LrTable.NT 0,(result,TERM1left,TERM1right),rest671) end
| (1,(_,(MlyValue.db_index db_index,db_index1left,db_index1right))::
rest671) => let val result=MlyValue.TERM((Term.Bv db_index))
 in (LrTable.NT 1,(result,db_index1left,db_index1right),rest671) end
| (2,(_,(MlyValue.string_ string_,string_1left,string_1right))::
rest671) => let val result=MlyValue.TERM((
Term.Const {Name=string_, Ty=Term.Type.Tyc "string"}))
 in (LrTable.NT 1,(result,string_1left,string_1right),rest671) end
| (3,(_,(MlyValue.num num,num1left,num1right))::rest671) => let val 
result=MlyValue.TERM((Term.Const{Name=num, Ty=Term.Type.Tyc"num"}))
 in (LrTable.NT 1,(result,num1left,num1right),rest671) end
| (4,(_,(MlyValue.ident ident,ident1left,ident1right))::rest671) => 
let val result=MlyValue.TERM((Term.lookup_const ident))
 in (LrTable.NT 1,(result,ident1left,ident1right),rest671) end
| (5,(_,(_,_,rparen1right))::(_,(MlyValue.TYPE TYPE,_,_))::_::(_,(
MlyValue.ident ident,_,_))::(_,(_,lparen1left,_))::rest671) => let 
val result=MlyValue.TERM((
(case (Term.lookup_const ident)
                of (Term.Const{Name,...})
                     => Term.Const{Name=Name,Ty=TYPE}
                 | _ => raise THY_YAK_ERR{function = "thy_yak",
                                          message = "impl. error"})
             handle NOT_FOUND
             => Term.Fv{Name=ident,Ty=TYPE}
))
 in (LrTable.NT 1,(result,lparen1left,rparen1right),rest671) end
| (6,(_,(_,_,rparen2right))::(_,(MlyValue.TERM TERM,_,_))::_::_::(_,(
MlyValue.TYPE TYPE,_,_))::_::(_,(MlyValue.ident ident,_,_))::_::_::(_,
(_,lparen1left,_))::rest671) => let val result=MlyValue.TERM((
Term.Abs{Bvar=Term.Fv{Name=ident,Ty=TYPE},
                      Body=TERM}
))
 in (LrTable.NT 1,(result,lparen1left,rparen2right),rest671) end
| (7,(_,(_,_,rparen1right))::(_,(MlyValue.TERM TERM2,_,_))::(_,(
MlyValue.TERM TERM1,_,_))::(_,(_,lparen1left,_))::rest671) => let val 
result=MlyValue.TERM((Term.Comb{Rator=TERM1, Rand=TERM2}))
 in (LrTable.NT 1,(result,lparen1left,rparen1right),rest671) end
| (8,(_,(MlyValue.TYPE TYPE,_,TYPE1right))::_::(_,(MlyValue.PLUS_TYPE 
PLUS_TYPE,PLUS_TYPE1left,_))::rest671) => let val result=MlyValue.TYPE
((Term.Type.Tyapp {Tyop="fun",Args=[PLUS_TYPE, TYPE]}))
 in (LrTable.NT 2,(result,PLUS_TYPE1left,TYPE1right),rest671) end
| (9,(_,(MlyValue.PLUS_TYPE PLUS_TYPE,PLUS_TYPE1left,PLUS_TYPE1right))
::rest671) => let val result=MlyValue.TYPE((PLUS_TYPE))
 in (LrTable.NT 2,(result,PLUS_TYPE1left,PLUS_TYPE1right),rest671) end
| (10,(_,(MlyValue.PLUS_TYPE PLUS_TYPE,_,PLUS_TYPE1right))::_::(_,(
MlyValue.HASH_TYPE HASH_TYPE,HASH_TYPE1left,_))::rest671) => let val 
result=MlyValue.PLUS_TYPE((
Term.Type.Tyapp
                                       {Tyop="sum",Args=[HASH_TYPE,PLUS_TYPE]}
))
 in (LrTable.NT 4,(result,HASH_TYPE1left,PLUS_TYPE1right),rest671) end
| (11,(_,(MlyValue.HASH_TYPE HASH_TYPE,HASH_TYPE1left,HASH_TYPE1right)
)::rest671) => let val result=MlyValue.PLUS_TYPE((HASH_TYPE))
 in (LrTable.NT 4,(result,HASH_TYPE1left,HASH_TYPE1right),rest671) end
| (12,(_,(MlyValue.HASH_TYPE HASH_TYPE,_,HASH_TYPE1right))::_::(_,(
MlyValue.APP_TYPE APP_TYPE,APP_TYPE1left,_))::rest671) => let val 
result=MlyValue.HASH_TYPE((
Term.Type.Tyapp
                                       {Tyop="prod",Args=[APP_TYPE,HASH_TYPE]}
))
 in (LrTable.NT 3,(result,APP_TYPE1left,HASH_TYPE1right),rest671) end
| (13,(_,(MlyValue.APP_TYPE APP_TYPE,APP_TYPE1left,APP_TYPE1right))::
rest671) => let val result=MlyValue.HASH_TYPE((APP_TYPE))
 in (LrTable.NT 3,(result,APP_TYPE1left,APP_TYPE1right),rest671) end
| (14,(_,(MlyValue.type_ident type_ident,_,type_ident1right))::(_,(
MlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=MlyValue.APP_TYPE((
Term.Type.Tyapp
                                {Tyop=type_ident, Args=TYPE_ARG}
))
 in (LrTable.NT 5,(result,TYPE_ARG1left,type_ident1right),rest671) end
| (15,(_,(MlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=MlyValue.APP_TYPE((BASIC))
 in (LrTable.NT 5,(result,BASIC1left,BASIC1right),rest671) end
| (16,(_,(MlyValue.type_ident type_ident,_,type_ident1right))::(_,(
MlyValue.TYPE_ARG TYPE_ARG,TYPE_ARG1left,_))::rest671) => let val 
result=MlyValue.TYPE_ARG((
[Term.Type.Tyapp
                                {Tyop=type_ident, Args=TYPE_ARG}]
))
 in (LrTable.NT 6,(result,TYPE_ARG1left,type_ident1right),rest671) end
| (17,(_,(MlyValue.BASIC_TYPE_ARG BASIC_TYPE_ARG,BASIC_TYPE_ARG1left,
BASIC_TYPE_ARG1right))::rest671) => let val result=MlyValue.TYPE_ARG((
BASIC_TYPE_ARG))
 in (LrTable.NT 6,(result,BASIC_TYPE_ARG1left,BASIC_TYPE_ARG1right),
rest671) end
| (18,(_,(_,_,type_rparen1right))::(_,(MlyValue.TYPE_LIST TYPE_LIST,_,
_))::_::(_,(MlyValue.TYPE TYPE,_,_))::(_,(_,type_lparen1left,_))::
rest671) => let val result=MlyValue.BASIC_TYPE_ARG((TYPE::TYPE_LIST))
 in (LrTable.NT 7,(result,type_lparen1left,type_rparen1right),rest671)
 end
| (19,(_,(MlyValue.BASIC BASIC,BASIC1left,BASIC1right))::rest671) => 
let val result=MlyValue.BASIC_TYPE_ARG(([BASIC]))
 in (LrTable.NT 7,(result,BASIC1left,BASIC1right),rest671) end
| (20,(_,(MlyValue.TYPE_LIST TYPE_LIST,_,TYPE_LIST1right))::_::(_,(
MlyValue.TYPE TYPE,TYPE1left,_))::rest671) => let val result=
MlyValue.TYPE_LIST((TYPE::TYPE_LIST))
 in (LrTable.NT 8,(result,TYPE1left,TYPE_LIST1right),rest671) end
| (21,(_,(MlyValue.TYPE TYPE,TYPE1left,TYPE1right))::rest671) => let 
val result=MlyValue.TYPE_LIST(([TYPE]))
 in (LrTable.NT 8,(result,TYPE1left,TYPE1right),rest671) end
| (22,(_,(MlyValue.type_var_ident type_var_ident,type_var_ident1left,
type_var_ident1right))::rest671) => let val result=MlyValue.BASIC((
Term.Type.Utv type_var_ident))
 in (LrTable.NT 9,(result,type_var_ident1left,type_var_ident1right),
rest671) end
| (23,(_,(MlyValue.type_ident type_ident,type_ident1left,
type_ident1right))::rest671) => let val result=MlyValue.BASIC((
Term.Type.Tyc type_ident))
 in (LrTable.NT 9,(result,type_ident1left,type_ident1right),rest671)
 end
| (24,(_,(_,_,type_rparen1right))::(_,(MlyValue.TYPE TYPE,_,_))::(_,(_
,type_lparen1left,_))::rest671) => let val result=MlyValue.BASIC((TYPE
))
 in (LrTable.NT 9,(result,type_lparen1left,type_rparen1right),rest671)
 end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : thy_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.ident i,p1,p2))
fun type_ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.type_ident i,p1,p2))
fun type_var_ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.type_var_ident i,p1,p2))
fun lambda (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun db_index (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.db_index i,p1,p2))
fun num (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.num i,p1,p2))
fun lparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun rparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun type_lparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun type_rparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun type_comma (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun colon (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun dot (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun type_right_arrow (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun type_hash (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun type_plus (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun string_ (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.string_ i,p1,p2))
fun EOLEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
end
end
