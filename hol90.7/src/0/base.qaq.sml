(* ARG_PARSER and ARG_LEXER modified for qaq *)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* base.sig: Base signature file for SML-Yacc.  This file contains signatures
   that must be loaded before any of the files produced by ML-Yacc are loaded
*)

(* STREAM: signature for a lazy stream.*)

signature STREAM =
 sig type 'xa stream
     val streamify : (unit -> '_a) -> '_a stream
     val cons : '_a * '_a stream -> '_a stream
     val get : '_a stream -> '_a * '_a stream
 end

(* LR_TABLE: signature for an LR Table.

   The list of actions and gotos passed to mkLrTable must be ordered by state
   number. The values for state 0 are the first in the list, the values for
    state 1 are next, etc.
*)

signature LR_TABLE =
    sig
        datatype ('a,'b) pairlist = EMPTY | PAIR of 'a * 'b * ('a,'b) pairlist
	datatype state = STATE of int
	datatype term = T of int
	datatype nonterm = NT of int
	datatype action = SHIFT of state
			| REDUCE of int
			| ACCEPT
			| ERROR
	type table
	
	val numStates : table -> int
	val numRules : table -> int
	val describeActions : table -> state ->
				(term,action) pairlist * action
	val describeGoto : table -> state -> (nonterm,state) pairlist
	val action : table -> state * term -> action
	val goto : table -> state * nonterm -> state
	val initialState : table -> state
	exception Goto of state * nonterm

	val mkLrTable : {actions : ((term,action) pairlist * action) Array.array,
			 gotos : (nonterm,state) pairlist Array.array,
			 numStates : int, numRules : int,
			 initialState : state} -> table
    end

(* TOKEN: signature revealing the internal structure of a token. This signature
   TOKEN distinct from the signature {parser name}_TOKENS produced by ML-Yacc.
   The {parser name}_TOKENS structures contain some types and functions to
    construct tokens from values and positions.

   The representation of token was very carefully chosen here to allow the
   polymorphic parser to work without knowing the types of semantic values
   or line numbers.

   This has had an impact on the TOKENS structure produced by SML-Yacc, which
   is a structure parameter to lexer functors.  We would like to have some
   type 'a token which functions to construct tokens would create.  A
   constructor function for a integer token might be

	  INT: int * 'a * 'a -> 'a token.
 
   This is not possible because we need to have tokens with the representation
   given below for the polymorphic parser.

   Thus our constructur functions for tokens have the form:

	  INT: int * 'a * 'a -> (svalue,'a) token

   This in turn has had an impact on the signature that lexers for SML-Yacc
   must match and the types that a user must declare in the user declarations
   section of lexers.
*)

signature TOKEN =
    sig
	structure LrTable : LR_TABLE
        datatype ('a,'b) token = TOKEN of LrTable.term * ('a * 'b * 'b)
	val sameToken : ('a,'b) token * ('a,'b) token -> bool
    end

(* LR_PARSER: signature for a polymorphic LR parser *)

signature LR_PARSER =
    sig
	structure Stream: STREAM
	structure LrTable : LR_TABLE
	structure Token : TOKEN

	sharing LrTable = Token.LrTable

	exception ParseError

	val parse : {table : LrTable.table,
		     lexer : ('_b,'_c) Token.token Stream.stream,
		     arg: 'arg,
		     saction : int *
			       '_c *
				(LrTable.state * ('_b * '_c * '_c)) list * 
				'arg ->
				     LrTable.nonterm *
				     ('_b * '_c * '_c) *
				     ((LrTable.state *('_b * '_c * '_c)) list),
		     void : '_b,
		     ec : { is_keyword : LrTable.term -> bool,
			    noShift : LrTable.term -> bool,
			    preferred_subst : LrTable.term -> LrTable.term list,
			    preferred_insert : LrTable.term -> bool,
			    errtermvalue : LrTable.term -> '_b,
			    showTerminal : LrTable.term -> string,
			    terms: LrTable.term list,
			    error : string * '_c * '_c -> unit
			   },
		     lookahead : int  (* max amount of lookahead used in *)
				      (* error correction *)
			} -> '_b *
			     (('_b,'_c) Token.token Stream.stream)
    end

(* LEXER: a signature that most lexers produced for use with SML-Yacc's
   output will match.  The user is responsible for declaring type token,
   type pos, and type svalue in the UserDeclarations section of a lexer.

   Note that type token is abstract in the lexer.  This allows SML-Yacc to
   create a TOKENS signature for use with lexers produced by ML-Lex that
   treats the type token abstractly.  Lexers that are functors parametrized by
   a Tokens structure matching a TOKENS signature cannot examine the structure
   of tokens.
*)

signature LEXER =
   sig
       structure UserDeclarations :
	   sig
	        type ('a,'b) token
		type pos
		type svalue
	   end
	val makeLexer : (int -> string) -> unit -> 
         (UserDeclarations.svalue,UserDeclarations.pos) UserDeclarations.token
   end

(* ARG_LEXER: the %arg option of ML-Lex allows users to produce lexers which
   also take an argument before yielding a function from unit to a token
*)

signature ARG_LEXER =
   sig
    structure UserDeclarations :
    sig
      structure Parse_support : Parse_support_sig
        type ('a,'b) token
        type pos
        type svalue
    end
    val makeLexer :(int -> string) -> 
                   UserDeclarations.Parse_support.Preterm.Term.term list ref ->
                   unit -> 
                   (UserDeclarations.svalue,UserDeclarations.pos) 
                       UserDeclarations.token
   end

(* PARSER_DATA: the signature of ParserData structures in {parsername}LrValsFun
   produced by SML-Yacc. All such structures match this signature.

   The {parser name}LrValsFun produces a structure which contains all the 
   values except for the lexer needed to call the polymorphic parser mentioned
   before.
*)

signature PARSER_DATA =
   sig
        (* the type of line numbers *)

	type pos

	(* the type of semantic values *)

	type svalue

         (* the type of the user-supplied argument to the parser *)
 	type arg
 
	(* the intended type of the result of the parser.  This value is
	   produced by applying extract from the structure Actions to the
	   final semantic value resultiing from a parse.
	 *)

	type result

	structure LrTable : LR_TABLE
	structure Token : TOKEN
	sharing Token.LrTable = LrTable

	(* structure Actions contains the functions which mantain the
	   semantic values stack in the parser.  Void is used to provide
	   a default value for the semantic stack.
	 *)

	structure Actions : 
	  sig
	      val actions : int * pos *
		   (LrTable.state * (svalue * pos * pos)) list * arg->
		         LrTable.nonterm * (svalue * pos * pos) *
			 ((LrTable.state *(svalue * pos * pos)) list)
	      val void : svalue
	      val extract : svalue -> result
	  end

	(* structure EC contains information used to improve error
	   recovery in an error-correcting parser *)

	structure EC :
	   sig
             val is_keyword : LrTable.term -> bool
	     val noShift : LrTable.term -> bool
	     val preferred_subst : LrTable.term -> LrTable.term list
	     val preferred_insert : LrTable.term -> bool
	     val errtermvalue : LrTable.term -> svalue
	     val showTerminal : LrTable.term -> string
	     val terms: LrTable.term list
	   end

	(* table is the LR table for the parser *)

	val table : LrTable.table
    end

(* signature PARSER is the signature that most user parsers created by 
   SML-Yacc will match.
*)

signature PARSER =
    sig
        structure Token : TOKEN
	structure Stream : STREAM
	exception ParseError

	(* type pos is the type of line numbers *)

	type pos

	(* type result is the type of the result from the parser *)

	type result

         (* the type of the user-supplied argument to the parser *)
 	type arg
	
	(* type svalue is the type of semantic values for the semantic value
	   stack
	 *)

	type svalue

	(* val makeLexer is used to create a stream of tokens for the parser *)

	val makeLexer : (int -> string) ->
			 (svalue,pos) Token.token Stream.stream

	(* val parse takes a stream of tokens and a function to print
	   errors and returns a value of type result and a stream containing
	   the unused tokens
	 *)

	val parse : int * ((svalue,pos) Token.token Stream.stream) *
		    (string * pos * pos -> unit) * arg ->
				result * (svalue,pos) Token.token Stream.stream

	val sameToken : (svalue,pos) Token.token * (svalue,pos) Token.token ->
				bool
     end

(* signature ARG_PARSER is the signature that will be matched by parsers whose
    lexer takes an additional argument.
*)

signature ARG_PARSER = 
    sig
        structure Token : TOKEN
	structure Stream : STREAM
        structure Parse_support : Parse_support_sig
	exception ParseError

	type arg
	type pos
	type result
	type svalue
                                           
	val makeLexer : (int -> string) -> 
                        Parse_support.Preterm.Term.term list ref ->
			(svalue,pos) Token.token Stream.stream
	val parse : int * ((svalue,pos) Token.token Stream.stream) *
		    (string * pos * pos -> unit) * arg ->
                    result * (svalue,pos) Token.token Stream.stream

	val sameToken : (svalue,pos) Token.token * (svalue,pos) Token.token ->
			bool
     end

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* Stream: a structure implementing a lazy stream.  The signature STREAM
   is found in base.sig *)

abstraction Stream : STREAM =
struct
   datatype 'a str = EVAL of 'a * 'a str ref | UNEVAL of (unit->'a)

   type 'a stream = 'a str ref

   fun get(ref(EVAL t)) = t
     | get(s as ref(UNEVAL f)) = 
	    let val t = (f(), ref(UNEVAL f)) in s := EVAL t; t end

   fun streamify f = ref(UNEVAL f)
   fun cons(a,s) = ref(EVAL(a,s))

end;
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

structure LrTable : LR_TABLE = 
    struct
	datatype ('a,'b) pairlist = EMPTY
				  | PAIR of 'a * 'b * ('a,'b) pairlist
	datatype term = T of int
	datatype nonterm = NT of int
	datatype state = STATE of int
	datatype action = SHIFT of state
			| REDUCE of int (* rulenum from grammar *)
			| ACCEPT
			| ERROR
	exception Goto of state * nonterm
	type table = {states: int, rules : int,initialState: state,
		      action: ((term,action) pairlist * action) Array.array,
		      goto :  (nonterm,state) pairlist Array.array}
	val numStates = fn ({states,...} : table) => states
	val numRules = fn ({rules,...} : table) => rules
	val describeActions =
	   fn ({action,...} : table) => 
	           fn (STATE s) => Array.sub(action,s)
	val describeGoto =
	   fn ({goto,...} : table) =>
	           fn (STATE s) => Array.sub(goto, s)
	fun findTerm (T term,row,default) =
	    let fun find (PAIR (T key,data,r)) =
		       if key < term then find r
		       else if key=term then data
		       else default
		   | find EMPTY = default
	    in find row
	    end
	fun findNonterm (NT nt,row) =
	    let fun find (PAIR (NT key,data,r)) =
		       if key < nt then find r
		       else if key=nt then SOME data
		       else NONE
		   | find EMPTY = NONE
	    in find row
	    end
	val action = fn ({action,...} : table) =>
		fn (STATE state,term) =>
		  let val (row,default) = Array.sub(action,state)
		  in findTerm(term,row,default)
		  end
	val goto = fn ({goto,...} : table) =>
			fn (a as (STATE state,nonterm)) =>
			  case findNonterm(nonterm,Array.sub(goto,state))
			  of SOME state => state
			   | NONE => raise (Goto a)
	val initialState = fn ({initialState,...} : table) => initialState
	val mkLrTable = fn {actions,gotos,initialState,numStates,numRules} =>
	     ({action=actions,goto=gotos,
	       states=numStates,
	       rules=numRules,
               initialState=initialState} : table)
end;
(* functor Join creates a user parser by putting together a Lexer structure,
   an LrValues structure, and a polymorphic parser structure.  Note that
   the Lexer and LrValues structure must share the type pos (i.e. the type
   of line numbers), the type svalues for semantic values, and the type
   of tokens.
*)

functor Join(structure Lex : LEXER
	     structure ParserData: PARSER_DATA
	     structure LrParser : LR_PARSER
	     sharing ParserData.LrTable = LrParser.LrTable
	     sharing ParserData.Token = LrParser.Token
	     sharing type Lex.UserDeclarations.svalue = ParserData.svalue
	     sharing type Lex.UserDeclarations.pos = ParserData.pos
	     sharing type Lex.UserDeclarations.token = ParserData.Token.token)
		 : PARSER =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream
 
    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue
    val makeLexer = LrParser.Stream.streamify o Lex.makeLexer
    val parse = fn (lookahead,lexer,error,arg) =>
	(fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
	        lexer=lexer,
		lookahead=lookahead,
		saction = ParserData.Actions.actions,
		arg=arg,
		void= ParserData.Actions.void,
	        ec = {is_keyword = ParserData.EC.is_keyword,
		      noShift = ParserData.EC.noShift,
		      preferred_subst = ParserData.EC.preferred_subst,
		      preferred_insert= ParserData.EC.preferred_insert,
		      errtermvalue = ParserData.EC.errtermvalue,
		      error=error,
		      showTerminal = ParserData.EC.showTerminal,
		      terms = ParserData.EC.terms}}
      )
     val sameToken = Token.sameToken
end
(* functor JoinWithArg creates a variant of the parser structure produced 
   above.  In this case, the makeLexer take an additional argument before
   yielding a value of type unit -> (svalue,pos) token
 *)

functor JoinWithArg(structure Lex : ARG_LEXER
	     structure ParserData: PARSER_DATA
	     structure LrParser : LR_PARSER
	     sharing ParserData.LrTable = LrParser.LrTable
	     sharing ParserData.Token = LrParser.Token
	     sharing type Lex.UserDeclarations.svalue = ParserData.svalue
	     sharing type Lex.UserDeclarations.pos = ParserData.pos
	     sharing type Lex.UserDeclarations.token = ParserData.Token.token) : ARG_PARSER  =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream
    structure Parse_support = Lex.UserDeclarations.Parse_support

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue

    val makeLexer = fn s => fn arg =>
		 LrParser.Stream.streamify (Lex.makeLexer s arg)
    val parse = fn (lookahead,lexer,error,arg) =>
	(fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
	        lexer=lexer,
		lookahead=lookahead,
		saction = ParserData.Actions.actions,
		arg=arg,
		void= ParserData.Actions.void,
	        ec = {is_keyword = ParserData.EC.is_keyword,
		      noShift = ParserData.EC.noShift,
		      preferred_subst = ParserData.EC.preferred_subst,
		      preferred_insert= ParserData.EC.preferred_insert,
		      errtermvalue = ParserData.EC.errtermvalue,
		      error=error,
		      showTerminal = ParserData.EC.showTerminal,
		      terms = ParserData.EC.terms}}
      )
    val sameToken = Token.sameToken
end;
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* drt (12/15/89) -- the functor should be used during development work,
   but it is wastes space in the release version.
   
functor ParserGen(structure LrTable : LR_TABLE
		  structure Stream : STREAM) : LR_PARSER =
*)

abstraction LrParser : LR_PARSER =
 struct
     val print = fn s => output(std_out,s)
     val println = fn s => (print s; print "\n")
     structure LrTable = LrTable
     structure Stream = Stream
     structure Token : TOKEN =
	struct
	    structure LrTable = LrTable
	    datatype ('a,'b) token = TOKEN of LrTable.term * ('a * 'b * 'b)
	    val sameToken = fn (TOKEN (t,_),TOKEN(t',_)) => t=t'
	end
     

     open LrTable 
     open Token

     val DEBUG = false
     exception ParseError

      type ('a,'b) elem = (state * ('a * 'b * 'b))
      type ('a,'b) stack = ('a,'b) elem list

      val showState = fn (STATE s) => ("STATE " ^ (makestring s))

      fun printStack(stack: ('a,'b) elem list, n: int) =
         case stack
           of (state, _) :: rest =>
                 (print("          " ^ makestring n ^ ": ");
                  println(showState state);
                  printStack(rest, n+1)
                 )
            | nil => ()

      val parse = fn {arg : 'a,
		      table : LrTable.table,
		      lexer : ('_b,'_c) token Stream.stream,
		      saction : int * '_c * ('_b,'_c) stack * 'a ->
				nonterm * ('_b * '_c * '_c) * ('_b,'_c) stack,
		      void : '_b,
		      ec = {is_keyword,preferred_subst,
			    preferred_insert,errtermvalue,showTerminal,
			    error,terms,noShift},
		      lookahead} =>
 let fun prAction(stack as (state, _) :: _, 
		  next as (TOKEN (term,_),_), action) =
             (println "Parse: state stack:";
              printStack(stack, 0);
              print("       state="
                         ^ showState state	
                         ^ " next="
                         ^ showTerminal term
                         ^ " action="
                        );
              case action
                of SHIFT s => println ("SHIFT " ^ showState s)
                 | REDUCE i => println ("REDUCE " ^ (makestring i))
                 | ERROR => println "ERROR"
		 | ACCEPT => println "ACCEPT";
              action)
        | prAction (_,_,action) = action

      val action = LrTable.action table
      val goto = LrTable.goto table

      fun parseStep(next as (TOKEN (terminal, value as (_,leftPos,_)),lexer) :
			('_b,'_c) token * ('_b,'_c) token Stream.stream,
		    stack as (state,_) :: _ : ('_b ,'_c) stack) =
         case (if DEBUG then prAction(stack, next,action(state, terminal))
               else action(state, terminal))
              of SHIFT s => parseStep(Stream.get lexer, (s,value) :: stack)
               | REDUCE i =>
		    let val (nonterm,value,stack as (state,_) :: _ ) =
					 saction(i,leftPos,stack,arg)
		    in parseStep(next,(goto(state,nonterm),value)::stack)
		    end
               | ERROR => let val (_,leftPos,rightPos) = value
		          in error("syntax error\n",leftPos,rightPos);
			     raise ParseError
			  end
  	       | ACCEPT => let val (_,(topvalue,_,_)) :: _ = stack
			       val (token,restLexer) = next
			   in (topvalue,Stream.cons(token,lexer))
			   end
      val next as (TOKEN (terminal,(_,leftPos,_)),_) = Stream.get lexer
   in parseStep(next,[(initialState table,(void,leftPos,leftPos))])
   end
end;

(* drt (12/15/89) -- this needs to be used only when the parsing engine
  (the code above) is functorized.  

structure LrParser = ParserGen(structure LrTable = LrTable
			     structure Stream = Stream);
*)
