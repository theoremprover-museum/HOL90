(*========================================================================
 * $Id: hol3.sml,v 1.1.2.1.2.2 1997/10/05 21:11:30 kxs Exp $
 *
 * FILE: hol2.sml
 * AUTHOR: Donald Syme
 *
 * This file contains meta-meta-level things that happen at the end of
 * level 2 of the HOL system.  Meta-meta-level things that affect the
 * ML environment and which usually can't be separately compiled by a
 * separate compilation facility like CM.) .  In particular this includes:
 *	- Installs pretty printers
 *	- Opening structures at the top level
 *	- Declaring type abbreviations
 * 	- Deleting structures/signatures/functors for garbage collecting.
 *=======================================================================*)

(*-----------------------------------------------------------------------
 * Install the pretty printers for:
 *	goalstack
 *	proofs
 *---------------------------------------------------------------------- *)

PP.install_pp ["Goalstack","goalstack"]
   "Goalstack.pp_goalstack" Goalstack.pp_goalstack; 
PP.install_pp ["Goalstack","proofs"]
   "Goalstack.pp_proofs" Goalstack.pp_proofs;

(*-----------------------------------------------------------------------
 * Open the structures at the top level and declare the appropriate infixes
 * at the top level.
 *---------------------------------------------------------------------- *)


open Goalstack; 
open Implicit; 
open Define_type;
open Sys_lib;
open Rsyntax; 

Install.install (!Globals.HOLdir); 

datatype frag = datatype Portable.frag;

(*-----------------------------------------------------------------------
 * Wipe out functors and signatures for GC.
 *---------------------------------------------------------------------- *)

signature EMPTY = sig end;
signature Define_type_sig = EMPTY;
signature Goalstack_sig = EMPTY;
signature Psyntax_sig = EMPTY;
signature Rsyntax_sig = EMPTY;
signature Sys_lib_sig = EMPTY;
