(*========================================================================
 * ld_BASIC_HOL.sml
 *
 * Loader file for the BASIC_HOL theory.  Could be remade automatically.
 *
 * The idea of this file is that if a structure depends
 * on having the BASIC_HOL theory loaded, then it should go "open BASIC_HOL"
 * at the top of the structure.  A compilation manager like CM will
 * then tell that this file needs to be loaded first.  This is the
 * only way of expressing such a dependency in CM.
 *
 * It may be better if each theory in BASIC_HOL had its
 * own structure.  Then a structure utilising one of the theories would
 * have "open Pair" or "open Num" in its header.   The dependencies are 
 * thus recorded at a finer grain.  But it hardly seems worth it.
 *
 * In the future the signature of this structure may be expanded to
 * include structures for the theories that are in BASIC_HOL. 
 *
 * This file may be loaded multiple times without detriment.
 *======================================================================*)

structure BASIC_HOL : sig end = struct
   open CoreHol;
   open Theory;
   open Lib;
   val _ = if (current_theory() <> "") andalso
              (mem "BASIC_HOL" (current_theory() :: ancestry "-"))
           then () 
  	   else load_theory "BASIC_HOL";


   (*-----------------------------------------------------------------
    * hmmm... kind of a strange place to have these, but it makes sense
    *   in a way.                                              DRS
    *----------------------------------------------------------------- *)

   val _ = Globals.assert_nums_defined(); 

   val pair_rewrites = map (theorem "pair") ["PAIR","FST","SND"] 
   val _ = Rewrite.add_implicit_rewrites pair_rewrites

end;



