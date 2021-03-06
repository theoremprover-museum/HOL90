(****************************************************************************)
(* FILE          : retrieve.sml                                             *)
(* DESCRIPTION   : Top-level structure for theorem retrieval.               *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 28th September 1995                                      *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 29th September 1995                                      *)
(****************************************************************************)

structure Retrieve =
struct

exception NO_MATCH = RetrieveExceptions.NO_MATCH;

type foundthm = RetrieveMatching.foundthm;
type searchpath = RetrieveSearch.searchpath;
type source = RetrieveSearch.source;
type searchstep = RetrieveSearch.searchstep;
type thmkind = RetrieveMatching.thmkind;
type thmpattern = RetrieveMatching.thmpattern;

val Ancestors = RetrieveSearch.Ancestors;
val ancestors_excluding = RetrieveUser.ancestors_excluding;
val Ancestry = RetrieveUser.Ancestry;
val Andalso = RetrieveMatching.Andalso;
val Any = RetrieveMatching.Any;
val Axiom = RetrieveMatching.Axiom;
val BigAnd = RetrieveUser.BigAnd;
val BigOr = RetrieveUser.BigOr;
val conc = RetrieveUser.conc;
val contains = RetrieveSidecond.contains;
val continue_search = RetrieveSearch.continue_search;
val CS = RetrieveUser.CS;
val Definition = RetrieveMatching.Definition;
val display_search = RetrieveSearch.display_search;
val Endofsearch = RetrieveSearch.Endofsearch;
val find_theorems = RetrieveSearch.find_theorems;
val FT = RetrieveUser.FT;
val full_search = RetrieveUser.full_search;
val has_body = RetrieveSidecond.has_body;
val hypF = RetrieveUser.hypF;
val hypP = RetrieveUser.hypP;
val kind = RetrieveUser.kind;
val List = RetrieveSearch.List;
val List_from = RetrieveUser.List_from;
val matches = RetrieveSidecond.matches;
val None = RetrieveMatching.None;
val Not = RetrieveMatching.Not;
val Orelse = RetrieveMatching.Orelse;
val Paths = RetrieveSearch.Paths;
val run_search = RetrieveUser.run_search;
val search_n_theories = RetrieveUser.search_n_theories;
val search_n_until_find = RetrieveUser.search_n_until_find;
val search_until_find = RetrieveUser.search_until_find;
val show_step = RetrieveSearch.show_step;
val Step = RetrieveSearch.Step;
val test1term = RetrieveSidecond.test1term;
val test1type = RetrieveSidecond.test1type;
val test2terms = RetrieveSidecond.test2terms;
val test2types = RetrieveSidecond.test2types;
val Theorem = RetrieveMatching.Theorem;
val Theory = RetrieveSearch.Theory;
val thmname = RetrieveUser.thmname;
val thryname = RetrieveUser.thryname;
val Where = RetrieveMatching.Where;

(*--------------------------------------------------------------------------*)
(* Infix declarations to make construction of theorem patterns nicer.       *)
(*--------------------------------------------------------------------------*)

infix Andalso;
infix Orelse;
infix Where;

infix contains;
infix matches;
infix has_body;

end;
