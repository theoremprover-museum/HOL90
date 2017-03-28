(*========================================================================
 * $Id: hol2.sml,v 1.1 1995/10/31 15:07:05 drs1004 Exp $
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
 *---------------------------------------------------------------------- *)

(*-----------------------------------------------------------------------
 * Open the structures at the top level and declare the appropriate infixes
 * at the top level.
 *---------------------------------------------------------------------- *)

open Num_conv;
open Let_conv; 
open Num_induct;
open Rec_type_support; 

(*-----------------------------------------------------------------------
 * Wipe out functors and signatures for GC.
 *---------------------------------------------------------------------- *)

signature EMPTY = sig end;
signature Let_conv_sig = EMPTY;
signature Num_conv_sig = EMPTY;
signature Num_induct_sig = EMPTY;
signature Rec_type_support_sig = EMPTY;

