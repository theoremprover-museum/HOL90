
functor libLrValsFun (structure Token : TOKEN
                               structure Lib_data : Lib_data_sig) = 
struct
structure ParserData=
struct
structure Header = 
struct
fun LIB_PARSE_ERR(s1,s2) = 
 Exception.HOL_ERR{origin_structure = "Library_parse",
                   origin_function = s1, message = s2};


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\003\000\022\000\000\000\
\\001\000\003\000\030\000\000\000\
\\001\000\003\000\047\000\000\000\
\\001\000\003\000\052\000\000\000\
\\001\000\004\000\025\000\000\000\
\\001\000\004\000\042\000\000\000\
\\001\000\004\000\049\000\000\000\
\\001\000\004\000\054\000\000\000\
\\001\000\005\000\007\000\000\000\
\\001\000\006\000\019\000\000\000\
\\001\000\007\000\005\000\000\000\
\\001\000\007\000\010\000\000\000\
\\001\000\007\000\016\000\000\000\
\\001\000\007\000\021\000\000\000\
\\001\000\007\000\029\000\000\000\
\\001\000\007\000\046\000\000\000\
\\001\000\007\000\051\000\000\000\
\\001\000\007\000\056\000\000\000\
\\001\000\008\000\011\000\000\000\
\\001\000\008\000\015\000\000\000\
\\001\000\009\000\004\000\000\000\
\\001\000\010\000\008\000\000\000\
\\001\000\011\000\014\000\000\000\
\\001\000\012\000\020\000\000\000\
\\001\000\013\000\027\000\000\000\
\\001\000\014\000\044\000\000\000\
\\001\000\015\000\050\000\000\000\
\\001\000\016\000\055\000\000\000\
\\001\000\017\000\009\000\000\000\
\\001\000\017\000\018\000\000\000\
\\001\000\018\000\013\000\000\000\
\\001\000\018\000\017\000\000\000\
\\001\000\019\000\012\000\000\000\
\\001\000\019\000\057\000\000\000\
\\001\000\020\000\000\000\021\000\000\000\000\000\
\\059\000\000\000\
\\060\000\000\000\
\\061\000\000\000\
\\062\000\000\000\
\\063\000\000\000\
\\064\000\000\000\
\\065\000\000\000\
\\066\000\000\000\
\\067\000\000\000\
\\068\000\000\000\
\\069\000\000\000\
\\070\000\000\000\
\\071\000\009\000\041\000\010\000\040\000\011\000\039\000\012\000\038\000\
\\013\000\037\000\014\000\036\000\015\000\035\000\016\000\034\000\
\\017\000\033\000\000\000\
\\072\000\008\000\043\000\000\000\
\\073\000\000\000\
\\074\000\005\000\007\000\000\000\
\\075\000\008\000\026\000\000\000\
\\076\000\000\000\
\"
val actionRowNumbers =
"\020\000\035\000\010\000\008\000\
\\021\000\028\000\011\000\018\000\
\\032\000\030\000\022\000\019\000\
\\012\000\031\000\029\000\009\000\
\\023\000\037\000\013\000\000\000\
\\050\000\004\000\051\000\024\000\
\\050\000\014\000\052\000\001\000\
\\047\000\005\000\048\000\038\000\
\\046\000\045\000\044\000\043\000\
\\042\000\041\000\040\000\039\000\
\\025\000\047\000\015\000\049\000\
\\002\000\047\000\006\000\026\000\
\\016\000\003\000\047\000\007\000\
\\027\000\017\000\033\000\036\000\
\\034\000"
val gotoT =
"\
\\001\000\056\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\003\000\004\000\000\000\
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
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\022\000\006\000\021\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\022\000\006\000\026\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\030\000\005\000\029\000\000\000\
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
\\000\000\
\\004\000\030\000\005\000\043\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\030\000\005\000\046\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\030\000\005\000\051\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 57
val numrules = 18
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
datatype svalue = VOID | ntVOID of unit | string_constant of  (string)
 | num of  (string) | id of  (string)
 | LIB_ID_LIST of  (Lib_data.lib_id list) | ID_LIST of  (string list)
 | ID of  (string) | LIB_ID of  (Lib_data.lib_id)
 | LIB of  (Lib_data.lib_data) | START of  (Lib_data.lib_data)
end
type svalue = MlyValue.svalue
type result = Lib_data.lib_data
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change = 
nil
val noShift = 
fn (T 20) => true | _ => false
val showTerminal =
fn (T 0) => "lbrace"
  | (T 1) => "rbrace"
  | (T 2) => "lbracket"
  | (T 3) => "rbracket"
  | (T 4) => "lparen"
  | (T 5) => "rparen"
  | (T 6) => "eq"
  | (T 7) => "comma"
  | (T 8) => "lib_id"
  | (T 9) => "doc"
  | (T 10) => "path"
  | (T 11) => "parents"
  | (T 12) => "theories"
  | (T 13) => "code"
  | (T 14) => "help"
  | (T 15) => "loaded"
  | (T 16) => "id"
  | (T 17) => "num"
  | (T 18) => "string_constant"
  | (T 19) => "EOLEX"
  | (T 20) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13)
 :: (T 14) :: (T 15) :: (T 19) :: (T 20) :: nil
end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.LIB LIB,LIB1left,LIB1right))::rest671) => let val 
result=MlyValue.START((LIB))
 in (LrTable.NT 0,(result,LIB1left,LIB1right),rest671) end
| (1,(_,(MlyValue.string_constant string_constant2,_,
string_constant2right))::_::_::_::(_,(MlyValue.ID_LIST ID_LIST3,_,_))
::_::_::_::_::(_,(MlyValue.ID_LIST ID_LIST2,_,_))::_::_::_::_::(_,(
MlyValue.ID_LIST ID_LIST1,_,_))::_::_::_::_::(_,(MlyValue.LIB_ID_LIST 
LIB_ID_LIST,_,_))::_::_::_::(_,(MlyValue.id id,_,_))::_::_::(_,(
MlyValue.string_constant string_constant1,_,_))::_::_::(_,(
MlyValue.LIB_ID LIB_ID,_,_))::_::(_,(_,lib_id1left,_))::rest671) => 
let val result=MlyValue.LIB((
Lib_data.mk_lib_data{lib_id = LIB_ID,
                            doc = string_constant1,
                            path = id,
                            parents = LIB_ID_LIST,
                            theories = ID_LIST1,
                            code = ID_LIST2,
                            help = ID_LIST3,
                            loaded = string_constant2}
))
 in (LrTable.NT 1,(result,lib_id1left,string_constant2right),rest671)
 end
| (2,(_,(_,_,rparen1right))::(_,(MlyValue.num num2,_,_))::_::(_,(
MlyValue.num num1,_,_))::_::(_,(MlyValue.id id,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.LIB_ID((
Lib_data.mk_lib_id{name = id, 
                  timestamp = Portable.Time.mk_time{sec = num1,usec = num2}}
))
 in (LrTable.NT 2,(result,lparen1left,rparen1right),rest671) end
| (3,(_,(MlyValue.id id,id1left,id1right))::rest671) => let val result
=MlyValue.ID((id))
 in (LrTable.NT 3,(result,id1left,id1right),rest671) end
| (4,(_,(_,lib_id1left,lib_id1right))::rest671) => let val result=
MlyValue.ID(("lib_id"))
 in (LrTable.NT 3,(result,lib_id1left,lib_id1right),rest671) end
| (5,(_,(_,doc1left,doc1right))::rest671) => let val result=
MlyValue.ID(("doc"))
 in (LrTable.NT 3,(result,doc1left,doc1right),rest671) end
| (6,(_,(_,path1left,path1right))::rest671) => let val result=
MlyValue.ID(("path"))
 in (LrTable.NT 3,(result,path1left,path1right),rest671) end
| (7,(_,(_,parents1left,parents1right))::rest671) => let val result=
MlyValue.ID(("parents"))
 in (LrTable.NT 3,(result,parents1left,parents1right),rest671) end
| (8,(_,(_,theories1left,theories1right))::rest671) => let val result=
MlyValue.ID(("theories"))
 in (LrTable.NT 3,(result,theories1left,theories1right),rest671) end
| (9,(_,(_,code1left,code1right))::rest671) => let val result=
MlyValue.ID(("code"))
 in (LrTable.NT 3,(result,code1left,code1right),rest671) end
| (10,(_,(_,help1left,help1right))::rest671) => let val result=
MlyValue.ID(("help"))
 in (LrTable.NT 3,(result,help1left,help1right),rest671) end
| (11,(_,(_,loaded1left,loaded1right))::rest671) => let val result=
MlyValue.ID(("loaded"))
 in (LrTable.NT 3,(result,loaded1left,loaded1right),rest671) end
| (12,rest671) => let val result=MlyValue.ID_LIST(([]))
 in (LrTable.NT 4,(result,defaultPos,defaultPos),rest671) end
| (13,(_,(MlyValue.ID ID,ID1left,ID1right))::rest671) => let val 
result=MlyValue.ID_LIST(([ID]))
 in (LrTable.NT 4,(result,ID1left,ID1right),rest671) end
| (14,(_,(MlyValue.ID_LIST ID_LIST,_,ID_LIST1right))::_::(_,(
MlyValue.ID ID,ID1left,_))::rest671) => let val result=
MlyValue.ID_LIST((ID::ID_LIST))
 in (LrTable.NT 4,(result,ID1left,ID_LIST1right),rest671) end
| (15,rest671) => let val result=MlyValue.LIB_ID_LIST(([]))
 in (LrTable.NT 5,(result,defaultPos,defaultPos),rest671) end
| (16,(_,(MlyValue.LIB_ID LIB_ID,LIB_ID1left,LIB_ID1right))::rest671)
 => let val result=MlyValue.LIB_ID_LIST(([LIB_ID]))
 in (LrTable.NT 5,(result,LIB_ID1left,LIB_ID1right),rest671) end
| (17,(_,(MlyValue.LIB_ID_LIST LIB_ID_LIST,_,LIB_ID_LIST1right))::_::(
_,(MlyValue.LIB_ID LIB_ID,LIB_ID1left,_))::rest671) => let val result=
MlyValue.LIB_ID_LIST((LIB_ID::LIB_ID_LIST))
 in (LrTable.NT 5,(result,LIB_ID1left,LIB_ID_LIST1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : lib_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun lbrace (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun rbrace (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun lbracket (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun rbracket (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun lparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun rparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun eq (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun comma (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun lib_id (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun doc (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun path (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun parents (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun theories (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun code (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun help (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun loaded (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun id (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.id i,p1,p2))
fun num (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.num i,p1,p2))
fun string_constant (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.string_constant i,p1,p2))
fun EOLEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
end
end
