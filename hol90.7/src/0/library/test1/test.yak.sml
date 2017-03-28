functor test1LrValsFun(structure Token : TOKEN)
 = 
struct
structure ParserData=
struct
structure Header = 
struct

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\004\000\003\000\009\000\000\000\
\\001\000\002\000\005\000\003\000\010\000\000\000\
\\001\000\003\000\000\000\000\000\
\\001\000\003\000\008\000\000\000\
\\001\000\003\000\011\000\000\000\
\"
val actionRowNumbers =
"\000\000\003\000\001\000\000\000\
\\004\000\002\000"
val gotoT =
"\
\\001\000\005\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\004\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 6
val numrules = 4
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
datatype svalue = VOID | ntVOID of unit ->  unit
 | ident of unit ->  (string) | LIST of unit ->  (string list)
 | START of unit ->  (string list)
end
type svalue = MlyValue.svalue
type result = string list
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
fn (T 2) => true | _ => false
val showTerminal =
fn (T 0) => "ident"
  | (T 1) => "comma"
  | (T 2) => "EOF"
  | _ => "bogus-term"
val errtermvalue=
let open Header in
fn _ => MlyValue.VOID
end
val terms = (T 1) :: (T 2) :: nil
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
of (0,(_,(MlyValue.LIST LIST1,LIST1left,LIST1right))::rest671) => let 
val result=MlyValue.START(fn _ => let val LIST as LIST1=LIST1 ()
 in (LIST) end
)
 in (LrTable.NT 0,(result,LIST1left,LIST1right),rest671) end
| (1,rest671) => let val result=MlyValue.LIST(fn _ => ([]))
 in (LrTable.NT 1,(result,defaultPos,defaultPos),rest671) end
| (2,(_,(MlyValue.ident ident1,ident1left,ident1right))::rest671) => 
let val result=MlyValue.LIST(fn _ => let val ident as ident1=ident1 ()
 in ([ident]) end
)
 in (LrTable.NT 1,(result,ident1left,ident1right),rest671) end
| (3,(_,(MlyValue.LIST LIST1,_,LIST1right))::_::(_,(MlyValue.ident 
ident1,ident1left,_))::rest671) => let val result=MlyValue.LIST(fn _
 => let val ident as ident1=ident1 ()
val LIST as LIST1=LIST1 ()
 in (ident::LIST) end
)
 in (LrTable.NT 1,(result,ident1left,LIST1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : test1_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun ident (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.ident (fn () => i),p1,p2))
fun comma (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
end
end
