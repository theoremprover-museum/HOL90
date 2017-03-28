
functor thmsLrValsFun (structure Token : TOKEN
                                structure Thm : Thm_sig
                                structure Thy_parse : Thy_parse_sig
                                structure Theory_data : Theory_data_sig
                                sharing 
                                  Thm = Theory_data.Thm
                                and
                                  Thm.Term = Thy_parse.Term
                                  = Theory_data.Thm.Term) = 
struct
structure ParserData=
struct
structure Header = 
struct
structure Theory_data = Theory_data
structure Thm = Thm;
structure Thy_parse = Thy_parse;

type hol_thms = { thid: Theory_data.theory_id, 
                  axioms : (string * Thm.thm) list,
                  definitions : (string * Thm.thm) list,
                  theorems : (string * Thm.thm) list
                };

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\007\000\000\000\
\\001\000\001\000\027\000\000\000\
\\001\000\002\000\032\000\000\000\
\\001\000\002\000\034\000\000\000\
\\001\000\002\000\051\000\000\000\
\\001\000\003\000\019\000\000\000\
\\001\000\003\000\035\000\000\000\
\\001\000\003\000\038\000\000\000\
\\001\000\003\000\048\000\000\000\
\\001\000\004\000\025\000\000\000\
\\001\000\004\000\039\000\000\000\
\\001\000\004\000\043\000\000\000\
\\001\000\004\000\052\000\000\000\
\\001\000\005\000\016\000\006\000\015\000\007\000\014\000\008\000\013\000\
\\009\000\012\000\010\000\011\000\012\000\010\000\000\000\
\\001\000\005\000\018\000\000\000\
\\001\000\005\000\024\000\000\000\
\\001\000\005\000\036\000\000\000\
\\001\000\005\000\046\000\000\000\
\\001\000\006\000\005\000\000\000\
\\001\000\006\000\017\000\000\000\
\\001\000\006\000\033\000\000\000\
\\001\000\006\000\045\000\000\000\
\\001\000\007\000\004\000\000\000\
\\001\000\008\000\008\000\000\000\
\\001\000\009\000\029\000\000\000\
\\001\000\010\000\042\000\000\000\
\\001\000\011\000\049\000\000\000\
\\001\000\013\000\020\000\000\000\
\\001\000\013\000\028\000\000\000\
\\001\000\014\000\000\000\015\000\000\000\000\000\
\\054\000\000\000\
\\055\000\000\000\
\\056\000\000\000\
\\057\000\000\000\
\\058\000\000\000\
\\059\000\000\000\
\\060\000\000\000\
\\061\000\000\000\
\\062\000\000\000\
\\063\000\000\000\
\\064\000\000\000\
\\065\000\001\000\023\000\000\000\
\\066\000\005\000\026\000\000\000\
\\067\000\000\000\
\\068\000\011\000\041\000\000\000\
\\069\000\005\000\044\000\000\000\
\\070\000\000\000\
\"
val actionRowNumbers =
"\022\000\030\000\018\000\000\000\
\\023\000\013\000\019\000\014\000\
\\039\000\036\000\035\000\034\000\
\\033\000\037\000\038\000\005\000\
\\027\000\041\000\015\000\009\000\
\\042\000\001\000\028\000\024\000\
\\041\000\013\000\002\000\020\000\
\\043\000\003\000\032\000\006\000\
\\016\000\041\000\007\000\010\000\
\\044\000\025\000\011\000\045\000\
\\021\000\017\000\044\000\008\000\
\\026\000\046\000\041\000\004\000\
\\012\000\040\000\031\000\029\000"
val gotoT =
"\
\\001\000\051\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\004\000\000\000\
\\000\000\
\\004\000\007\000\000\000\
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
\\005\000\020\000\006\000\019\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\020\000\006\000\028\000\000\000\
\\004\000\029\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\020\000\006\000\035\000\000\000\
\\000\000\
\\000\000\
\\007\000\038\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\045\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\020\000\006\000\048\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 52
val numrules = 17
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
datatype svalue = VOID | ntVOID of unit | num of  (string)
 | id of  (string) | quote of  (string) | QUOTE_LIST of  (string list)
 | THM_LIST of  ( ( string*Thm.thm )  list)
 | THM of  ( ( string*Thm.thm ) ) | ID of  (string)
 | HOL_THMS of  (hol_thms) | CURR_THID of  (Theory_data.theory_id)
 | START of  (hol_thms)
end
type svalue = MlyValue.svalue
type result = hol_thms
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change = 
nil
val noShift = 
fn (T 14) => true | _ => false
val showTerminal =
fn (T 0) => "lparen"
  | (T 1) => "rparen"
  | (T 2) => "lbracket"
  | (T 3) => "rbracket"
  | (T 4) => "comma"
  | (T 5) => "eq"
  | (T 6) => "thid"
  | (T 7) => "axioms"
  | (T 8) => "definitions"
  | (T 9) => "theorems"
  | (T 10) => "quote"
  | (T 11) => "id"
  | (T 12) => "num"
  | (T 13) => "EOLEX"
  | (T 14) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 13) :: (T 14) :: nil
end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.HOL_THMS HOL_THMS,HOL_THMS1left,HOL_THMS1right))::
rest671) => let val result=MlyValue.START((HOL_THMS))
 in (LrTable.NT 0,(result,HOL_THMS1left,HOL_THMS1right),rest671) end
| (1,(_,(_,_,rbracket3right))::(_,(MlyValue.THM_LIST THM_LIST3,_,_))::
_::_::_::_::(_,(MlyValue.THM_LIST THM_LIST2,_,_))::_::_::_::_::(_,(
MlyValue.THM_LIST THM_LIST1,_,_))::_::_::_::(_,(MlyValue.CURR_THID 
CURR_THID,_,_))::_::(_,(_,thid1left,_))::rest671) => let val result=
MlyValue.HOL_THMS((
{thid = CURR_THID,
             axioms = THM_LIST1, 
             definitions = THM_LIST2,
             theorems = THM_LIST3}
))
 in (LrTable.NT 2,(result,thid1left,rbracket3right),rest671) end
| (2,(_,(_,_,rparen1right))::(_,(MlyValue.num num2,_,_))::_::(_,(
MlyValue.num num1,_,_))::_::(_,(MlyValue.ID ID,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.CURR_THID((
Theory_data.mk_theory_id
            {name = ID, 
             timestamp = Portable.Time.mk_time{sec = num1,usec = num2}}
))
 in (LrTable.NT 1,(result,lparen1left,rparen1right),rest671) end
| (3,(_,(_,thid1left,thid1right))::rest671) => let val result=
MlyValue.ID(("thid"))
 in (LrTable.NT 3,(result,thid1left,thid1right),rest671) end
| (4,(_,(_,axioms1left,axioms1right))::rest671) => let val result=
MlyValue.ID(("axioms"))
 in (LrTable.NT 3,(result,axioms1left,axioms1right),rest671) end
| (5,(_,(_,definitions1left,definitions1right))::rest671) => let val 
result=MlyValue.ID(("definitions"))
 in (LrTable.NT 3,(result,definitions1left,definitions1right),rest671)
 end
| (6,(_,(_,theorems1left,theorems1right))::rest671) => let val result=
MlyValue.ID(("theorems"))
 in (LrTable.NT 3,(result,theorems1left,theorems1right),rest671) end
| (7,(_,(_,eq1left,eq1right))::rest671) => let val result=MlyValue.ID(
("="))
 in (LrTable.NT 3,(result,eq1left,eq1right),rest671) end
| (8,(_,(_,comma1left,comma1right))::rest671) => let val result=
MlyValue.ID((","))
 in (LrTable.NT 3,(result,comma1left,comma1right),rest671) end
| (9,(_,(MlyValue.id id,id1left,id1right))::rest671) => let val result
=MlyValue.ID((id))
 in (LrTable.NT 3,(result,id1left,id1right),rest671) end
| (10,(_,(_,_,rparen2right))::(_,(MlyValue.quote quote,_,_))::_::_::(_
,(MlyValue.QUOTE_LIST QUOTE_LIST,_,_))::_::_::_::(_,(MlyValue.ID ID,_,
_))::_::(_,(_,lparen1left,_))::rest671) => let val result=MlyValue.THM
((
ID,Thm.mk_disk_thm(map Thy_parse.theory_term_parser QUOTE_LIST,
                          Thy_parse.theory_term_parser quote)
))
 in (LrTable.NT 4,(result,lparen1left,rparen2right),rest671) end
| (11,rest671) => let val result=MlyValue.THM_LIST(([]))
 in (LrTable.NT 5,(result,defaultPos,defaultPos),rest671) end
| (12,(_,(MlyValue.THM THM,THM1left,THM1right))::rest671) => let val 
result=MlyValue.THM_LIST(([THM]))
 in (LrTable.NT 5,(result,THM1left,THM1right),rest671) end
| (13,(_,(MlyValue.THM_LIST THM_LIST,_,THM_LIST1right))::_::(_,(
MlyValue.THM THM,THM1left,_))::rest671) => let val result=
MlyValue.THM_LIST((THM::THM_LIST))
 in (LrTable.NT 5,(result,THM1left,THM_LIST1right),rest671) end
| (14,rest671) => let val result=MlyValue.QUOTE_LIST(([]))
 in (LrTable.NT 6,(result,defaultPos,defaultPos),rest671) end
| (15,(_,(MlyValue.quote quote,quote1left,quote1right))::rest671) => 
let val result=MlyValue.QUOTE_LIST(([quote]))
 in (LrTable.NT 6,(result,quote1left,quote1right),rest671) end
| (16,(_,(MlyValue.QUOTE_LIST QUOTE_LIST,_,QUOTE_LIST1right))::_::(_,(
MlyValue.quote quote,quote1left,_))::rest671) => let val result=
MlyValue.QUOTE_LIST((quote::QUOTE_LIST))
 in (LrTable.NT 6,(result,quote1left,QUOTE_LIST1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : thms_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun lparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun rparen (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun lbracket (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun rbracket (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun comma (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun eq (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun thid (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun axioms (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun definitions (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun theorems (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun quote (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.quote i,p1,p2))
fun id (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.id i,p1,p2))
fun num (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.num i,p1,p2))
fun EOLEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
end
end
