(*========================================================================
 * ld_HOL.sml
 *
 * Loader file for the HOL theory.  Could be remade automatically.
 *
 * The idea of this file is that if a structure depends
 * on having the HOL theory loaded, then it should go "open HOL"
 * at the top of the structure.  A compilation manager like CM will
 * then tell that this file needs to be loaded first.  This is the
 * only way of expressing such a dependency in CM.
 *
 * This file may be loaded multiple times without detriment.
 *
 * See also ld_BASIC_HOL.sml for more discussion on files of this sort.
 *======================================================================*)

structure HOL :sig end = struct
   open CoreHol;
   open Theory;
   open Lib;
   open BASIC_HOL;

   val _ = if (current_theory() <> "") andalso
              (mem "HOL" (current_theory() :: ancestry "-"))
           then () 
  	   else load_theory "HOL";
end;



