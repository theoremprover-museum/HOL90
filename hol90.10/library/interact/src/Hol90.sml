(*========================================================================
 * $Id: core.sml,v 1.1 1995/10/31 15:07:40 drs1004 Exp $
 *
 * FILE: top.sml
 * AUTHOR: Donald Syme
 *
 * The Hol90 structure contains everything in the old HOL system. It is 
 * used as a convenient way to open everything up for working.
 *
 *=======================================================================*)

structure Hol90 = struct

(* hol0 *)

open Abbrev;
open Exception;
open Parse
open CoreHol;
open Hol_pp

open boolThry
open Exists
open Min

open Const_def
open Type_def
open Const_spec

(* open Install *)
open Add_to_sml
(* open Library *)
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

(* hol 2 *)
open Num_conv;
open Let_conv; 
open Num_induct;
open Rec_type_support; 


(* hol 3 *)
open Goalstack; 
open Implicit; 
open Define_type;
(* open Sys_lib; *)
open Rsyntax; 

open Help;

(* Define a prettyprinter installer and set fixities.  *)
local
   fun top_pp_thm ppstrm th =  
      ( Portable.PrettyPrint.begin_block ppstrm
          Portable.PrettyPrint.CONSISTENT 0;
       CoreHol.Thm.pp_thm ppstrm th; 
        Portable.PrettyPrint.end_block ppstrm)
in
fun pp_on() =
 ( Portable.PrettyPrint.install_pp
         ["CoreHol","Type","hol_type"] 
	 "Hol_pp.pp_self_parsing_type"
	 CoreHol.Hol_pp.pp_self_parsing_type;

   Portable.PrettyPrint.install_pp
         ["CoreHol","Term","term"] 
	 "Hol_pp.pp_self_parsing_term"
	 CoreHol.Hol_pp.pp_self_parsing_term;

   Portable.PrettyPrint.install_pp ["CoreHol","Thm","thm"] "it" top_pp_thm;

   Portable.PrettyPrint.install_pp 
             ["Rewrite","rewrites"] "Rewrite.pp_rewrites" Rewrite.pp_rewrites;

   Portable.PrettyPrint.install_pp ["Goalstack","goalstack"]
       "Goalstack.pp_goalstack" Goalstack.pp_goalstack; 

    Portable.PrettyPrint.install_pp ["Goalstack","proofs"]
      "Goalstack.pp_proofs" Goalstack.pp_proofs
  )
end;

end;

