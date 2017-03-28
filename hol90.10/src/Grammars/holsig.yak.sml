
functor holsigLrValsFun (structure Token : TOKEN
                                  structure Theory_data : Theory_data_sig
                                  structure Term: Term_sig
                                  sharing
                                    Theory_data.Thm.Term = Term) = 
struct
structure ParserData=
struct
structure Header = 
struct
structure Theory_data = Theory_data
structure Term = Term

type type_record = {tyc:Term.Type.hol_type, arity :int, theory:string}
type term_record = {const:Term.term, theory:string, place:Term.fixity};

type hol_sig = { thid: Theory_data.theory_id,
                 parents : Theory_data.theory_id list,
                 type_constants : type_record list,
                 term_constants : term_record list
               };

val global_theory_name = ref "";

fun THEORY_PARSE_ERR(s1,s2) = 
 Exception.HOL_ERR{origin_structure = "Theory_parse",
                   origin_function = s1,
                   message = s2};


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\002\000\091\000\000\000\
\\001\000\003\000\028\000\000\000\
\\001\000\003\000\044\000\000\000\
\\001\000\003\000\059\000\000\000\
\\001\000\003\000\084\000\000\000\
\\001\000\004\000\034\000\000\000\
\\001\000\004\000\050\000\000\000\
\\001\000\004\000\064\000\000\000\
\\001\000\004\000\093\000\000\000\
\\001\000\005\000\007\000\000\000\
\\001\000\005\000\069\000\000\000\
\\001\000\005\000\078\000\007\000\025\000\008\000\024\000\009\000\023\000\
\\010\000\022\000\011\000\021\000\012\000\020\000\013\000\019\000\
\\014\000\018\000\015\000\017\000\016\000\016\000\017\000\015\000\
\\018\000\014\000\019\000\077\000\020\000\013\000\021\000\012\000\
\\022\000\011\000\023\000\010\000\000\000\
\\001\000\006\000\041\000\000\000\
\\001\000\006\000\053\000\000\000\
\\001\000\006\000\060\000\000\000\
\\001\000\006\000\071\000\000\000\
\\001\000\006\000\095\000\000\000\
\\001\000\007\000\025\000\008\000\024\000\009\000\023\000\010\000\022\000\
\\011\000\021\000\012\000\020\000\013\000\019\000\014\000\018\000\
\\015\000\017\000\016\000\016\000\017\000\015\000\018\000\014\000\
\\020\000\013\000\021\000\012\000\022\000\011\000\023\000\010\000\000\000\
\\001\000\007\000\027\000\000\000\
\\001\000\007\000\033\000\000\000\
\\001\000\007\000\040\000\000\000\
\\001\000\007\000\045\000\000\000\
\\001\000\007\000\056\000\000\000\
\\001\000\007\000\072\000\000\000\
\\001\000\007\000\079\000\000\000\
\\001\000\007\000\082\000\000\000\
\\001\000\008\000\005\000\000\000\
\\001\000\008\000\026\000\000\000\
\\001\000\008\000\042\000\000\000\
\\001\000\008\000\057\000\000\000\
\\001\000\008\000\068\000\000\000\
\\001\000\008\000\074\000\000\000\
\\001\000\008\000\083\000\000\000\
\\001\000\009\000\004\000\000\000\
\\001\000\010\000\066\000\000\000\
\\001\000\011\000\073\000\000\000\
\\001\000\012\000\081\000\000\000\
\\001\000\013\000\088\000\014\000\087\000\015\000\086\000\000\000\
\\001\000\016\000\008\000\000\000\
\\001\000\017\000\038\000\000\000\
\\001\000\018\000\054\000\000\000\
\\001\000\023\000\029\000\000\000\
\\001\000\023\000\037\000\000\000\
\\001\000\023\000\043\000\000\000\
\\001\000\023\000\049\000\000\000\
\\001\000\023\000\058\000\000\000\
\\001\000\023\000\092\000\000\000\
\\001\000\024\000\000\000\025\000\000\000\000\000\
\\098\000\000\000\
\\099\000\000\000\
\\100\000\000\000\
\\101\000\000\000\
\\102\000\000\000\
\\103\000\000\000\
\\104\000\000\000\
\\105\000\000\000\
\\106\000\000\000\
\\107\000\000\000\
\\108\000\000\000\
\\109\000\000\000\
\\110\000\000\000\
\\111\000\000\000\
\\112\000\000\000\
\\113\000\000\000\
\\114\000\000\000\
\\115\000\000\000\
\\116\000\000\000\
\\117\000\000\000\
\\118\000\000\000\
\\119\000\000\000\
\\120\000\000\000\
\\121\000\000\000\
\\122\000\000\000\
\\123\000\000\000\
\\124\000\000\000\
\\125\000\000\000\
\\126\000\005\000\032\000\000\000\
\\127\000\007\000\035\000\000\000\
\\128\000\000\000\
\\129\000\005\000\078\000\007\000\025\000\008\000\024\000\009\000\023\000\
\\010\000\022\000\011\000\021\000\012\000\020\000\013\000\019\000\
\\014\000\018\000\015\000\017\000\016\000\016\000\017\000\015\000\
\\018\000\014\000\019\000\077\000\020\000\013\000\021\000\012\000\
\\022\000\011\000\023\000\010\000\000\000\
\\130\000\007\000\094\000\000\000\
\\131\000\000\000\
\\132\000\005\000\048\000\000\000\
\\133\000\007\000\051\000\000\000\
\\134\000\000\000\
\\135\000\001\000\063\000\000\000\
\\136\000\007\000\065\000\000\000\
\\137\000\000\000\
\"
val actionRowNumbers =
"\033\000\048\000\026\000\009\000\
\\038\000\017\000\027\000\018\000\
\\069\000\056\000\070\000\071\000\
\\068\000\067\000\066\000\064\000\
\\063\000\062\000\061\000\065\000\
\\060\000\059\000\057\000\058\000\
\\001\000\041\000\076\000\019\000\
\\005\000\077\000\017\000\042\000\
\\039\000\076\000\020\000\012\000\
\\028\000\078\000\043\000\050\000\
\\002\000\021\000\082\000\044\000\
\\006\000\083\000\017\000\013\000\
\\040\000\082\000\022\000\051\000\
\\029\000\084\000\045\000\003\000\
\\014\000\085\000\052\000\007\000\
\\086\000\034\000\049\000\085\000\
\\030\000\087\000\010\000\017\000\
\\015\000\023\000\035\000\031\000\
\\011\000\054\000\024\000\053\000\
\\017\000\036\000\025\000\032\000\
\\004\000\037\000\079\000\000\000\
\\046\000\073\000\072\000\008\000\
\\080\000\075\000\074\000\016\000\
\\079\000\055\000\081\000\047\000"
val gotoT =
"\
\\001\000\095\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\003\000\004\000\000\000\
\\000\000\
\\007\000\007\000\000\000\
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
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\029\000\013\000\028\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\034\000\000\000\
\\000\000\
\\000\000\
\\004\000\029\000\013\000\037\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\045\000\011\000\044\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\050\000\000\000\
\\000\000\
\\000\000\
\\005\000\045\000\011\000\053\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\009\000\060\000\012\000\059\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\009\000\060\000\012\000\065\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\068\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\074\000\007\000\073\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\078\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\083\000\000\000\
\\006\000\088\000\007\000\073\000\010\000\087\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\088\000\007\000\073\000\010\000\094\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 96
val numrules = 40
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
 | id of  (string) | string_constant of  (string)
 | symbolic of  (string) | type_var of  (string)
 | THID_LIST of  (Theory_data.theory_id list)
 | TMC_LIST of  (term_record list) | TYC_LIST of  (type_record list)
 | TY_LIST of  (Term.Type.hol_type list) | TMC of  (term_record)
 | FIX of  (Term.fixity) | CID of  (string)
 | TY of  (Term.Type.hol_type) | TYC of  (type_record)
 | THID of  (Theory_data.theory_id)
 | CURR_THID of  (Theory_data.theory_id) | HOLSIG of  (hol_sig)
 | START of  (hol_sig)
end
type svalue = MlyValue.svalue
type result = hol_sig
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change = 
nil
val noShift = 
fn (T 24) => true | _ => false
val showTerminal =
fn (T 0) => "lbrace"
  | (T 1) => "rbrace"
  | (T 2) => "lbracket"
  | (T 3) => "rbracket"
  | (T 4) => "lparen"
  | (T 5) => "rparen"
  | (T 6) => "comma"
  | (T 7) => "eq"
  | (T 8) => "thid"
  | (T 9) => "name"
  | (T 10) => "ty"
  | (T 11) => "fixity"
  | (T 12) => "Binder"
  | (T 13) => "Prefix"
  | (T 14) => "Infix"
  | (T 15) => "parents"
  | (T 16) => "types"
  | (T 17) => "constants"
  | (T 18) => "type_var"
  | (T 19) => "symbolic"
  | (T 20) => "string_constant"
  | (T 21) => "id"
  | (T 22) => "num"
  | (T 23) => "EOLEX"
  | (T 24) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13)
 :: (T 14) :: (T 15) :: (T 16) :: (T 17) :: (T 23) :: (T 24) :: nil
end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.HOLSIG HOLSIG,HOLSIG1left,HOLSIG1right))::rest671)
 => let val result=MlyValue.START((HOLSIG))
 in (LrTable.NT 0,(result,HOLSIG1left,HOLSIG1right),rest671) end
| (1,(_,(_,_,rbracket3right))::(_,(MlyValue.TMC_LIST TMC_LIST,_,_))::_
::_::_::_::(_,(MlyValue.TYC_LIST TYC_LIST,_,_))::_::_::_::_::(_,(
MlyValue.THID_LIST THID_LIST,_,_))::_::_::_::(_,(MlyValue.CURR_THID 
CURR_THID,_,_))::_::(_,(_,thid1left,_))::rest671) => let val result=
MlyValue.HOLSIG((
{ thid = CURR_THID,
                    parents = THID_LIST,
                    type_constants = TYC_LIST,
                    term_constants = TMC_LIST}
))
 in (LrTable.NT 1,(result,thid1left,rbracket3right),rest671) end
| (2,(_,(_,_,rparen1right))::(_,(MlyValue.num num2,_,_))::_::(_,(
MlyValue.num num1,_,_))::_::(_,(MlyValue.CID CID,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.CURR_THID((
global_theory_name := CID;
        Theory_data.mk_theory_id
            {name = CID, 
             timestamp = Portable.Time.mk_time{sec = num1, usec = num2}}
))
 in (LrTable.NT 2,(result,lparen1left,rparen1right),rest671) end
| (3,(_,(_,_,rparen1right))::(_,(MlyValue.num num2,_,_))::_::(_,(
MlyValue.num num1,_,_))::_::(_,(MlyValue.CID CID,_,_))::(_,(_,
lparen1left,_))::rest671) => let val result=MlyValue.THID((
Theory_data.mk_theory_id
            {name = CID, 
             timestamp = Portable.Time.mk_time{sec = num1, usec = num2}}
))
 in (LrTable.NT 3,(result,lparen1left,rparen1right),rest671) end
| (4,(_,(_,_,rparen1right))::(_,(MlyValue.num num,_,_))::_::(_,(
MlyValue.CID CID,_,_))::(_,(_,lparen1left,_))::rest671) => let val 
result=MlyValue.TYC((
{tyc = Term.Type.Tyc CID,
        arity = Lib.string_to_int num, theory = (!global_theory_name)}
))
 in (LrTable.NT 4,(result,lparen1left,rparen1right),rest671) end
| (5,(_,(MlyValue.type_var type_var,type_var1left,type_var1right))::
rest671) => let val result=MlyValue.TY((Term.Type.Utv type_var))
 in (LrTable.NT 5,(result,type_var1left,type_var1right),rest671) end
| (6,(_,(MlyValue.CID CID,CID1left,CID1right))::rest671) => let val 
result=MlyValue.TY((Term.Type.Tyc CID))
 in (LrTable.NT 5,(result,CID1left,CID1right),rest671) end
| (7,(_,(_,_,rparen1right))::_::(_,(MlyValue.TY_LIST TY_LIST,_,_))::_
::_::(_,(MlyValue.CID CID,_,_))::(_,(_,lparen1left,_))::rest671) => 
let val result=MlyValue.TY((
Term.Type.Tyapp{Tyop = CID, Args = TY_LIST}))
 in (LrTable.NT 5,(result,lparen1left,rparen1right),rest671) end
| (8,(_,(MlyValue.id id,id1left,id1right))::rest671) => let val result
=MlyValue.CID((id))
 in (LrTable.NT 6,(result,id1left,id1right),rest671) end
| (9,(_,(_,eq1left,eq1right))::rest671) => let val result=MlyValue.CID
(("="))
 in (LrTable.NT 6,(result,eq1left,eq1right),rest671) end
| (10,(_,(_,comma1left,comma1right))::rest671) => let val result=
MlyValue.CID((","))
 in (LrTable.NT 6,(result,comma1left,comma1right),rest671) end
| (11,(_,(_,thid1left,thid1right))::rest671) => let val result=
MlyValue.CID(("thid"))
 in (LrTable.NT 6,(result,thid1left,thid1right),rest671) end
| (12,(_,(_,name1left,name1right))::rest671) => let val result=
MlyValue.CID(("name"))
 in (LrTable.NT 6,(result,name1left,name1right),rest671) end
| (13,(_,(_,fixity1left,fixity1right))::rest671) => let val result=
MlyValue.CID(("fixity"))
 in (LrTable.NT 6,(result,fixity1left,fixity1right),rest671) end
| (14,(_,(_,Binder1left,Binder1right))::rest671) => let val result=
MlyValue.CID(("Binder"))
 in (LrTable.NT 6,(result,Binder1left,Binder1right),rest671) end
| (15,(_,(_,Prefix1left,Prefix1right))::rest671) => let val result=
MlyValue.CID(("Prefix"))
 in (LrTable.NT 6,(result,Prefix1left,Prefix1right),rest671) end
| (16,(_,(_,Infix1left,Infix1right))::rest671) => let val result=
MlyValue.CID(("Infix"))
 in (LrTable.NT 6,(result,Infix1left,Infix1right),rest671) end
| (17,(_,(_,ty1left,ty1right))::rest671) => let val result=
MlyValue.CID(("ty"))
 in (LrTable.NT 6,(result,ty1left,ty1right),rest671) end
| (18,(_,(_,parents1left,parents1right))::rest671) => let val result=
MlyValue.CID(("parents"))
 in (LrTable.NT 6,(result,parents1left,parents1right),rest671) end
| (19,(_,(_,types1left,types1right))::rest671) => let val result=
MlyValue.CID(("types"))
 in (LrTable.NT 6,(result,types1left,types1right),rest671) end
| (20,(_,(_,constants1left,constants1right))::rest671) => let val 
result=MlyValue.CID(("constants"))
 in (LrTable.NT 6,(result,constants1left,constants1right),rest671) end
| (21,(_,(MlyValue.num num,num1left,num1right))::rest671) => let val 
result=MlyValue.CID((num))
 in (LrTable.NT 6,(result,num1left,num1right),rest671) end
| (22,(_,(MlyValue.string_constant string_constant,
string_constant1left,string_constant1right))::rest671) => let val 
result=MlyValue.CID((string_constant))
 in (LrTable.NT 6,(result,string_constant1left,string_constant1right),
rest671) end
| (23,(_,(MlyValue.symbolic symbolic,symbolic1left,symbolic1right))::
rest671) => let val result=MlyValue.CID((symbolic))
 in (LrTable.NT 6,(result,symbolic1left,symbolic1right),rest671) end
| (24,(_,(_,Binder1left,Binder1right))::rest671) => let val result=
MlyValue.FIX((Term.Binder))
 in (LrTable.NT 7,(result,Binder1left,Binder1right),rest671) end
| (25,(_,(_,Prefix1left,Prefix1right))::rest671) => let val result=
MlyValue.FIX((Term.Prefix))
 in (LrTable.NT 7,(result,Prefix1left,Prefix1right),rest671) end
| (26,(_,(MlyValue.num num,_,num1right))::(_,(_,Infix1left,_))::
rest671) => let val result=MlyValue.FIX((
Term.Infix (Lib.string_to_int num)))
 in (LrTable.NT 7,(result,Infix1left,num1right),rest671) end
| (27,(_,(_,_,rbrace1right))::(_,(MlyValue.FIX FIX,_,_))::_::_::_::(_,
(MlyValue.TY TY,_,_))::_::_::_::_::(_,(MlyValue.CID CID,_,_))::_::_::_
::(_,(_,lbrace1left,_))::rest671) => let val result=MlyValue.TMC((
{const = Term.Const{Name = CID, Ty = TY},
       theory = !global_theory_name,
       place = FIX}
))
 in (LrTable.NT 8,(result,lbrace1left,rbrace1right),rest671) end
| (28,rest671) => let val result=MlyValue.THID_LIST(([]))
 in (LrTable.NT 12,(result,defaultPos,defaultPos),rest671) end
| (29,(_,(MlyValue.THID THID,THID1left,THID1right))::rest671) => let 
val result=MlyValue.THID_LIST(([THID]))
 in (LrTable.NT 12,(result,THID1left,THID1right),rest671) end
| (30,(_,(MlyValue.THID_LIST THID_LIST,_,THID_LIST1right))::_::(_,(
MlyValue.THID THID,THID1left,_))::rest671) => let val result=
MlyValue.THID_LIST((THID::THID_LIST))
 in (LrTable.NT 12,(result,THID1left,THID_LIST1right),rest671) end
| (31,rest671) => let val result=MlyValue.TY_LIST(([]))
 in (LrTable.NT 9,(result,defaultPos,defaultPos),rest671) end
| (32,(_,(MlyValue.TY TY,TY1left,TY1right))::rest671) => let val 
result=MlyValue.TY_LIST(([TY]))
 in (LrTable.NT 9,(result,TY1left,TY1right),rest671) end
| (33,(_,(MlyValue.TY_LIST TY_LIST,_,TY_LIST1right))::_::(_,(
MlyValue.TY TY,TY1left,_))::rest671) => let val result=
MlyValue.TY_LIST((TY::TY_LIST))
 in (LrTable.NT 9,(result,TY1left,TY_LIST1right),rest671) end
| (34,rest671) => let val result=MlyValue.TYC_LIST(([]))
 in (LrTable.NT 10,(result,defaultPos,defaultPos),rest671) end
| (35,(_,(MlyValue.TYC TYC,TYC1left,TYC1right))::rest671) => let val 
result=MlyValue.TYC_LIST(([TYC]))
 in (LrTable.NT 10,(result,TYC1left,TYC1right),rest671) end
| (36,(_,(MlyValue.TYC_LIST TYC_LIST,_,TYC_LIST1right))::_::(_,(
MlyValue.TYC TYC,TYC1left,_))::rest671) => let val result=
MlyValue.TYC_LIST((TYC::TYC_LIST))
 in (LrTable.NT 10,(result,TYC1left,TYC_LIST1right),rest671) end
| (37,rest671) => let val result=MlyValue.TMC_LIST(([]))
 in (LrTable.NT 11,(result,defaultPos,defaultPos),rest671) end
| (38,(_,(MlyValue.TMC TMC,TMC1left,TMC1right))::rest671) => let val 
result=MlyValue.TMC_LIST(([TMC]))
 in (LrTable.NT 11,(result,TMC1left,TMC1right),rest671) end
| (39,(_,(MlyValue.TMC_LIST TMC_LIST,_,TMC_LIST1right))::_::(_,(
MlyValue.TMC TMC,TMC1left,_))::rest671) => let val result=
MlyValue.TMC_LIST((TMC::TMC_LIST))
 in (LrTable.NT 11,(result,TMC1left,TMC_LIST1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : holsig_TOKENS =
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
fun comma (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun eq (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun thid (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun name (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun ty (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun fixity (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun Binder (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun Prefix (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun Infix (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun parents (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun types (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun constants (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun type_var (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.type_var i,p1,p2))
fun symbolic (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.symbolic i,p1,p2))
fun string_constant (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.string_constant i,p1,p2))
fun id (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.id i,p1,p2))
fun num (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.num i,p1,p2))
fun EOLEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
end
end
