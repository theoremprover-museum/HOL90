(*========================================================================
 * $Id: hol0.sml,v 1.1.2.1.2.2 1997/07/10 20:23:21 kxs Exp $
 *
 * FILE: hol0.sml
 * AUTHOR: Donald Syme
 *
 * This file contains meta-meta-level things that happen at the end of
 * level 0 of the HOL system.  Meta-meta-level things that affect the
 * ML environment and which usually can't be separately compiled by a
 * separate compilation facility like CM.) .  In particular this includes:
 *	- Installs pretty printers
 *	- Opening structures at the top level
 *	- Declaring type abbreviations
 * 	- Deleting structures/signatures/functors for garbage collecting.
 *
 * IMPORTANT NOTE:
 *	Do *not* assume this file has been executed when writing code
 * in levels 1, 2 and 3.  You may assume it has been executed when writing
 * theories that get processed between levels 0 and 1.
 *=======================================================================*)

(*-----------------------------------------------------------------------
 * Install the pretty printers for:
 *	thm
 *	hol_type
 *	lib
 *	term
 *---------------------------------------------------------------------- *)

local
   fun top_pp_thm ppstrm th =  
      ( Portable.PrettyPrint.begin_block ppstrm
          Portable.PrettyPrint.CONSISTENT 0;
       CoreHol.Thm.pp_thm ppstrm th; 
        Portable.PrettyPrint.end_block ppstrm)
in
   val it = top_pp_thm
end;
val _ = Portable.PrettyPrint.install_pp ["CoreHol","Thm","thm"] "it" it;

val _ = Portable.PrettyPrint.install_pp
         ["CoreHol","Type","hol_type"] 
	 "CoreHol.Hol_pp.pp_self_parsing_type"
	 CoreHol.Hol_pp.pp_self_parsing_type;
val _ = Portable.PrettyPrint.install_pp
         ["CoreHol","Term","term"] 
	 "CoreHol.Hol_pp.pp_self_parsing_term"
	 CoreHol.Hol_pp.pp_self_parsing_term;
val _ = Portable.PrettyPrint.install_pp
         ["Library","lib"] 
	 "Library.pp_library"
	 Library.pp_library;

(*-----------------------------------------------------------------------
 * Open the structures at the top level and declare the appropriate infixes
 * at the top level.
 *
 * NOTE: This is done mostly in 1/hol1.sml
 *---------------------------------------------------------------------- *)

open Abbrev;
open Exception;

(*-----------------------------------------------------------------------
 * Wipe out functors and signatures for GC.
 *---------------------------------------------------------------------- *)

structure EMPTY = struct end;
functor CACHE() = EMPTY;
functor CONST_DEF() = EMPTY;
functor CONST_SPEC() = EMPTY;
functor DSYNTAX() = EMPTY;
functor EXISTS_DEF() = EMPTY;
functor HOL_LEX() = EMPTY;
functor HOL_PP() = EMPTY;
functor HolLrValsFun() = EMPTY;
functor INSTALL() = EMPTY;
functor MATCH() = EMPTY;
functor NET() = EMPTY;
functor PARSE_SUPPORT() = EMPTY;
functor PRETERM() = EMPTY;
functor TERM() = EMPTY;
functor THM() = EMPTY;
functor THY_LEX() = EMPTY;
functor THY_PARSE() = EMPTY;
functor THY_PP() = EMPTY;
functor thyLrValsFun() = EMPTY;
functor TYPE_DEF() = EMPTY;
functor UID() = EMPTY;
