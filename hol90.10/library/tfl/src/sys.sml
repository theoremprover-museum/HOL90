(* Build the HOL version of Tfl *)

(*---------------------------------------------------------------------------
 *          Build TFL functor 
 *---------------------------------------------------------------------------*)

(* Hiding of constructors *)
use"mask.sig";
use"mask.sml";

(* The specifications - these are independent of any system *)
use "utils.sig";
use "usyntax.sig";
use "rules.sig";
use "thry.sig";
use "thms.sig";
use "tfl.sig";

(*----------------------------------------------------------------------------
 * Compile the TFL functor - this is defined totally in terms of the 
 * above interfaces.
 *---------------------------------------------------------------------------*)

use "tfl.sml";

(*----------------------------------------------------------------------------
 *      Supply implementations
 *---------------------------------------------------------------------------*)
use "utils.sml";
use "usyntax.sml";
use "rw.sig"; use "rw.sml";
use "thms.sml";
use"rules.sml";
use"hol_datatype.sig"; use"hol_datatype.sml";
use "thry.sml";

(*---------------------------------------------------------------------------
 *      Link the system and specialize for HOL 
 *---------------------------------------------------------------------------*)

val _ = load_library_in_place arith_lib;
use"Q.sig"; use"Q.sml";
use"post.sml";

(*---------------------------------------------------------------------------
 *      Dump the system
 *---------------------------------------------------------------------------*)

val _ = PP.install_pp ["RW","simpls"] "" RW.pp_simpls;
open HOL_Tfl;
open RW;
val use = Lib.interpret;
infix 4 |->;
val Term = Parse.term_parser;
val Type = Parse.type_parser;
save_hol"HEAP";
