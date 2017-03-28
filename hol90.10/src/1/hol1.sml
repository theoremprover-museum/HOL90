(*========================================================================
 * $Id: hol1.sml,v 1.2.2.1.2.3 1997/10/05 21:10:59 kxs Exp $
 *
 * FILE: hol1.sml
 * AUTHOR: Donald Syme
 *
 * This file contains meta-meta-level things that happen at the end of
 * level 1 of the HOL system.  Meta-meta-level things that affect the
 * ML environment and which usually can't be separately compiled by a
 * separate compilation facility like CM.) .  In particular this includes:
 *	- Installs pretty printers
 *	- Opening structures at the top level
 *	- Declaring type abbreviations
 * 	- Deleting structures/signatures/functors for garbage collecting.
 *=======================================================================*)

(*-----------------------------------------------------------------------
 * Install the pretty printers for:
 *	rewrites
 *---------------------------------------------------------------------- *)

val _ = Portable.PrettyPrint.install_pp 
             ["Rewrite","rewrites"] "Rewrite.pp_rewrites" Rewrite.pp_rewrites;

(*-----------------------------------------------------------------------
 * Open the structures at the top level and declare the appropriate infixes
 * at the top level.
 *---------------------------------------------------------------------- *)
open CoreHol
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

   open Parse
   open Hol_pp

(*open Base_logic*)
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
(*   open Net *)
  open Dsyntax 
   open Match
   open Term
   open Type

open Lib
  infix 3 ##
open Exception
open Globals;


(*-----------------------------------------------------------------------
 * Wipe out functors and signatures for GC.
 *---------------------------------------------------------------------- *)

signature EMPTY = sig end;
signature Drule1_sig = EMPTY;
signature Drule2_sig = EMPTY;
signature Drule3_sig = EMPTY;
signature Drule_sig = EMPTY;
signature Induct_then_sig = EMPTY;
signature Prim_rec_sig = EMPTY;
signature Resolve_sig = EMPTY;
signature Rewrite_sig = EMPTY;
signature Tactic_sig = EMPTY;
signature Tactical_sig = EMPTY;
signature Taut_thms_sig = EMPTY;
signature Thm_cont_sig = EMPTY;
signature Type_def_support_sig = EMPTY;
