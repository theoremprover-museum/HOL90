(* ========================================================================= *)
(*  FILE          : parse.sml                                                *)
(*  DESCRIPTION   : Code for use in parsing Hoare triples.                   *)
(*                                                                           *)
(*  AUTHOR        : Konrad Slind, TUMunchen                                  *)
(*  DATE          : March 1993                                               *)
(* ========================================================================= *)


(* System.system "sed_hol_yak"; *)
use "hol_yak.sig" ; use "hol_lex.sml"; use "hol_yak.sml";

open Core; (* open up all of the HOL 0/1 Core - could be replaced by more *)
           (* explicit opens to avoid endless recompilation of libraries  *)
           (* during system development                                   *)

structure Table = holLrValsFun(structure Token = LrParser.Token
                               structure Parse_support = Parse_support)
structure Lex = HOL_LEX(structure Tokens=Table.Tokens
                        structure Parse_support=Parse_support)

structure P=JoinWithArg(structure ParserData=Table.ParserData
                        structure Lex=Lex
                        structure LrParser = LrParser)

fun PARSE_ERR{function,message} = HOL_ERR{origin_structure = "Parse",
					  origin_function = function,
					  message = message}

local
fun T [] ol ml = (ol, rev ml) |
    T ((ANTIQUOTE  x)::rst) ol ml = T rst (ol^"^") (x::ml) |
    T ((QUOTE s)::rst) ol ml = T rst (ol^s) ml
in
fun format (q:'a frag list) = T q "" []
end;

fun error (s,_,_) = (output(std_out,("HOL parser error: "^s^"\n"));
                     raise PARSE_ERR{function = "first pass of parsing",
				     message = s});

(* Performs the first pass, parsing into preterms. *)
fun p (ol_frag_list:Term.term frag list) =
   let val _ = Term.Type.reset_type_num()
       val (s,antiq_list) = format ol_frag_list
       val strm = open_string s
       val lexer = P.makeLexer(fn _ => input_line strm) 
                              (ref antiq_list : Term.term list ref)
       val (res,_) = P.parse(0,lexer,error,())
   in res
   end;

(* trans_term : "s", " ... x ..."  -->  "\s. ... s `x` ..." *)

(*
fun is_upper_case s = 
   let val A = ordof("A",0)
       val Z = ordof("Z",0)
       fun f i = let val letter = ordof(s,i)
                 in (letter>=A) andalso (letter<=Z) andalso f(i+1)
                 end
   in f 0 handle _ => true
   end;
*)

(* Ignores variables found in antiquotes! Crap! - need Preterm to be open! *)
local
open Parse_support.Preterm (* not good enough *)
fun frees(v as Var _) free_list = 
      if (mem v free_list) then free_list else v::free_list
  | frees(Comb{Rator, Rand}) free_list = frees Rand (frees Rator free_list)
  | frees(Abs{Body,...}) free_list = frees Body free_list
  | frees(Constrained(M,_)) free_list = frees M free_list
  | frees _ free_list = free_list
in
fun free_prevars tm = frees tm []
end;

fun trans_term s tm =
   let exception FAIL
       fun opr t = 
         let val {Name,Ty} = dest_const t
         in if (Lexis.is_string_literal Name 
                andalso (Ty = mk_type{Tyop = "string",Args = []}))
            then {t |-> mk_comb{Rator=s, Rand=t}}
            else FAIL
         end

       val subst_list = mapfilter opr 
          (find_terms "is_string_literal o is_constant" tm)
   in 
   mk_abs{Bvar=s, Body=subst subst_list tm}
   end
   handle _ => raise PARSE_ERR{function = "trans_term", 
                               message = "unable to thread state"};

fun thread ?????

fun hoare_term_parser frag_list =
  (Globals.in_type_spec := NONE;
   case (p frag_list)
     of (Parse_support.PTM ptm) => 
                Preterm.typecheck_cleanup
                  (Preterm.typecheck (thread_state ptm))
      | _ => raise PARSE_ERR{function = "term_parser",
			     message = "Not a term."});

fun % frag_list _ = hoare_term_parser frag_list;

Globals.term_pp_prefix := "%"; Globals.term_pp_suffix := "";
(* Examples *)
p `{| T |} R := X {|T|}`;

p `{| T |}
          R := X;
          Q := 0;
          assert {|( R = X) /\ (Q = 0) |};
          while Y <= R do
              invariant{| X = R + Y * Q |};
              R := R - Y;
              Q := Q + 1
          done
   {| R < Y /\ (X = R + Y * Q) |}`;

p` [| 0 < Y |]
        R := X;
        Q := 0;
        assert{|0 < Y /\ (R = X) /\ (Q = 0)|};
        while Y <= R do 
           invariant{|0 < Y /\ (X = R + Y * Q)|}; 
           variant{|R|};
           R := R - Y;
           Q := Q + 1
        done
   [| (X = R + Y * Q) /\ R < Y |]`;

