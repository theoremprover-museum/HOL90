(* =====================================================================
 * FILE          : mk_HOL.sml                                            
 * DESCRIPTION   : Make HOL theory by combining other theories.		 
 *                                                                       
 * AUTHORS       : Donald Syme, University of Cambridge               
 * DATE          : 95.10.21
 * ID            : $Id: mk_HOL.sml,v 1.1 1995/10/31 14:01:02 drs1004 Exp $
 * ===================================================================== *)


load_theory "rec_type";
new_theory "HOL";
new_parent "one";
new_parent "sum";
new_parent "restr_binder";

export_theory ();
