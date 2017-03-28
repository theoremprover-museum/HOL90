(*========================================================================
 * $Id: core.sml,v 1.1.4.3 1997/10/05 21:11:17 kxs Exp $
 *
 * FILE: core.sml
 * AUTHOR: Donald Syme
 *
 * The Core structure contains everything in levels 0 and 1 of the system.
 *
 * This structure may or may not be permanent.  It is used to avoid having to
 * explicitly open lots and lots of structures in the HOL libraries,
 * but the downside of this is that if any of the signatures in the
 * core system change, this will make all the libraries recompile - bummer.
 * Explicit opening is better, but it can take a long time to work out
 * which structures need opening when given a source code file
 * which relies on them all being open at the top level.
 *=======================================================================*)

structure Core = struct

(* hol0 *)

open Abbrev;
open Exception;
open Parse
open Hol_pp

open boolThry
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

open Lib
  infix 3 ##
open Globals;


(* hol0/1 *)
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

datatype frag = datatype Portable.frag;

end;