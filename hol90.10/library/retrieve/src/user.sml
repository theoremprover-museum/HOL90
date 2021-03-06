(****************************************************************************)
(* FILE          : user.sml                                                 *)
(* DESCRIPTION   : Some useful user-level functions for theorem retrieval.  *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 1989                                                     *)
(*                                                                          *)
(* TRANSLATED BY : D.R.Syme                                                 *)
(* DATE          : 1995                                                     *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 17th November 1995                                       *)
(****************************************************************************)

structure RetrieveUser : RETRIEVE_USER =
struct

type term = CoreHol.Term.term;

local

open Exception Lib RetrieveStruct RetrieveName RetrieveMatching RetrieveSearch;

fun failwith_message function message =
   raise HOL_ERR{origin_structure = "RetrieveUser",
                 origin_function = function,
                 message = message};

in

(*--------------------------------------------------------------------------*)
(* Abbreviation for `find_theorems'.                                        *)
(*--------------------------------------------------------------------------*)

val FT = find_theorems;

(*--------------------------------------------------------------------------*)
(* Abbreviation for `continue_search'.                                      *)
(*--------------------------------------------------------------------------*)

val CS = continue_search;

(*--------------------------------------------------------------------------*)
(* run_search : searchstep -> foundthm list                                 *)
(*                                                                          *)
(* Function to complete a stepwise search in one step.                      *)
(*                                                                          *)
(* This function repeatedly attempts to continue a search, until this fails *)
(* because there are no more theories to search. When this happens, the     *)
(* list of theorems found during the search is extracted and returned as    *)
(* result.                                                                  *)
(*--------------------------------------------------------------------------*)

fun run_search srchstp =
   run_search (continue_search srchstp) handle HOL_ERR _ => show_step srchstp;

(*--------------------------------------------------------------------------*)
(* full_search : thmpattern -> source -> foundthm list                      *)
(*                                                                          *)
(* Function to perform a search in a single step.                           *)
(*                                                                          *)
(* Given a pattern and a source, this function searches the source in one   *)
(* step, and returns a list of theorems which match the pattern.            *)
(*--------------------------------------------------------------------------*)

fun full_search thmp src = run_search (find_theorems thmp src);

(*--------------------------------------------------------------------------*)
(* search_until_find : searchstep -> searchstep                             *)
(*                                                                          *)
(* Function to continue a search until a match is found.                    *)
(*                                                                          *)
(* If the found theorem list of the searchstep given is empty, the search   *)
(* is continued. The evaluation will fail if no theorems are found before   *)
(* the list of theories to search is exhausted.                             *)
(*--------------------------------------------------------------------------*)

fun search_until_find srchstp =
   if (null o show_step) srchstp
   then (search_until_find o continue_search) srchstp
   else srchstp;

(*--------------------------------------------------------------------------*)
(* search_n_theories : int -> searchstep -> searchstep                      *)
(*                                                                          *)
(* Function to continue with a search for a number of steps.                *)
(*                                                                          *)
(* If n is greater than zero, and the end of the search has not been        *)
(* reached, the search is continued.                                        *)
(*--------------------------------------------------------------------------*)

fun search_n_theories n srchstp =
   if (n < 1)
   then srchstp
   else case srchstp
        of Endofsearch _ => srchstp
         | Step _ => search_n_theories (n - 1) (continue_search srchstp);

(*--------------------------------------------------------------------------*)
(* search_n_until_find : int -> searchstep -> searchstep                    *)
(*                                                                          *)
(* Function to continue with a search for a number of steps, or until a     *)
(* theorem is found.                                                        *)
(*                                                                          *)
(* If n is greater than zero, and the searchstep given does not contain any *)
(* theorems, the search is continued.                                       *)
(*--------------------------------------------------------------------------*)

fun search_n_until_find n srchstp =
   if (n > 0) andalso ((null o show_step) srchstp)
   then search_n_until_find (n - 1) (continue_search srchstp)
   else srchstp;

(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* ancestors_excluding : string list -> string list -> searchpath           *)
(*                                                                          *)
(* Function to allow a user to set up a constructor equivalent to           *)
(* `Ancestors' but with the a default value for the exclusion list.         *)
(*--------------------------------------------------------------------------*)

fun ancestors_excluding exclusions ancestors =
   Ancestors (ancestors,exclusions);

(*--------------------------------------------------------------------------*)
(* Ancestry : string list -> searchpath                                     *)
(*                                                                          *)
(* `Ancestry' is an example of the use of `ancestors_excluding' and is      *)
(* likely to be the most useful default exclusion.                          *)
(*--------------------------------------------------------------------------*)

val Ancestry = ancestors_excluding ["HOL"];

(*--------------------------------------------------------------------------*)
(* List_from : searchstep -> source                                         *)
(*                                                                          *)
(* Function to make a `source' of the form `List ...' from a `searchstep'.  *)
(*                                                                          *)
(* The `foundthm list' is extracted from the `searchstep', and then `List'  *)
(* is applied to it.                                                        *)
(*--------------------------------------------------------------------------*)

val List_from = List o show_step;

(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* kind : thmkind -> thmpattern                                             *)
(* thryname : string -> thmpattern                                          *)
(* thmname : string -> thmpattern                                           *)
(* conc : term -> thmpattern                                                *)
(* hypP : term list -> thmpattern                                           *)
(* hypF : term list -> thmpattern                                           *)
(* side : side_condition -> thmpattern                                      *)
(*                                                                          *)
(* Functions which can be used in place of certain `thmpattern'             *)
(* constructors, so that the arguments can be given as the representing     *)
(* types of abstract types rather than as the abstract types themselves.    *)
(*                                                                          *)
(* `kind' and `side' are only included for consistency.                     *)
(*--------------------------------------------------------------------------*)

val kind = Kind
and thryname = Thryname o autonamepattern
and thmname = Thmname o autonamepattern
and conc = Conc o autotermpattern
and hypP = HypP o (map autotermpattern)
and hypF = HypF o (map autotermpattern)
and side = Side;

(*--------------------------------------------------------------------------*)
(* BigAnd : thmpattern list -> thmpattern                                   *)
(*                                                                          *)
(* `BigAnd' is an additional thmpattern constructor, useful when large      *)
(* numbers of thmpatterns are to be ANDed together.                         *)
(*--------------------------------------------------------------------------*)

fun BigAnd [] = failwith_message "BigAnd" "null list prohibited"
  | BigAnd (thmp::thmps) =
   if (null thmps)
   then thmp
   else Andalso (thmp,BigAnd thmps);

(*--------------------------------------------------------------------------*)
(* BigOr : thmpattern list -> thmpattern                                    *)
(*                                                                          *)
(* `BigOr' is an additional thmpattern constructor, useful when large       *)
(* numbers of thmpatterns are to be ORed together.                          *)
(*--------------------------------------------------------------------------*)

fun BigOr [] = failwith_message "BigOr" "null list prohibited"
  | BigOr (thmp::thmps) =
   if (null thmps)
   then thmp
   else Orelse (thmp,BigOr thmps);

end;

end; (* RetrieveUser *)
