structure Hol1 = 
struct
structure Globals = Globals
structure Exception = Exception
structure Lib = Lib
structure Base_logic = Base_logic
structure Term_io = Term_io
structure Drule = Drule
structure Conv = Conv
structure Tactical = Tactical
structure Rewrite = Rewrite
structure Thm_cont = Thm_cont
structure Tactic = Tactic
structure Taut_thms = Taut_thms
structure Resolve = Resolve
structure Type_def_support = Type_def_support
structure Induct_then = Induct_then
structure Prim_rec = Prim_rec
end;

open Hol1

open Save_hol
open Prim_rec
open Induct_then
open Type_def_support
open Resolve
open Taut_thms
open Tactic
open Thm_cont
  infix THEN_TCL 
  infix ORELSE_TCL
open Rewrite
open Tactical
  infix THEN
  infix THENL
  infix ORELSE
open Conv
  infix THENC
  infix ORELSEC
open Drule

open Term_io
   open Parse
   open Hol_pp

open Base_logic
   open Bool
   open Exists
   open Min

   open Const_def
   open Type_def
   open Const_spec

   open Install
   open Add_to_sml
   open Library
   open Theory
   open Thm
   open Net
   open Dsyntax
   open Match
   open Term
   open Type

open Save_hol
open Lib
  infix 3 ##
open Exception
open Globals;
