(* =====================================================================
 * FILE         : mk_BASIC_HOL.sml                                            
 * DESCRIPTION  : Make BASIC_HOL theory by combining other theories.
 *                                                                       
 * AUTHORS      : Donald Syme, University of Cambridge               
 * DATE         : 95.10.21
 * ID           : $Id: mk_BASIC_HOL.sml,v 1.1.4.1 1997/07/11 16:37:26 kxs Exp $
 * ===================================================================== *)

load_theory"pair";
new_theory "BASIC_HOL";
 new_parent "num";
export_theory ();
