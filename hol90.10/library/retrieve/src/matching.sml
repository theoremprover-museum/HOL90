(****************************************************************************)
(* FILE          : matching.sml                                             *)
(* DESCRIPTION   : Matching theorems.                                       *)
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

structure RetrieveMatching : RETRIEVE_MATCHING =
struct

type thm = CoreHol.Thm.thm;

local

open Exception Lib CoreHol;
open RetrieveExceptions RetrieveStruct RetrieveName;

fun failwith_message function message =
   raise HOL_ERR{origin_structure = "RetrieveMatching",
                 origin_function = function,
                 message = message};

in

(*--------------------------------------------------------------------------*)
(* Datatype for the three different kinds of theorem.                       *)
(*--------------------------------------------------------------------------*)

datatype thmkind = Axiom | Definition | Theorem;

(*--------------------------------------------------------------------------*)
(* Datatype for a full representation of a theorem.                         *)
(*                                                                          *)
(* The first string is for the theory name. The second is for the theorem   *)
(* name.                                                                    *)
(*--------------------------------------------------------------------------*)

type foundthm = thmkind * string * string * Thm.thm;

(*--------------------------------------------------------------------------*)
(* Datatype for representing theorem patterns.                              *)
(*                                                                          *)
(* The first seven constructors generate representations for theorem        *)
(* patterns. The rest combine or modify such representations.               *)
(*                                                                          *)
(* Any' and None' added by D.R.Syme, 1995.                                  *)
(*--------------------------------------------------------------------------*)

datatype thmpattern_rep = Any'
                        | None'
                        | Kind' of thmkind
                        | Thryname' of namepattern
                        | Thmname' of namepattern
                        | Conc' of termpattern
                        | HypP' of termpattern list
                        | HypF' of termpattern list
                        | Side' of side_condition
                        | Andalso' of thmpattern_rep * thmpattern_rep
                        | Orelse' of thmpattern_rep * thmpattern_rep
                        | Not' of thmpattern_rep
                        | Where' of thmpattern_rep * thmpattern_rep;

(*==========================================================================*)
(* Abstract datatype for theorem patterns.                                  *)
(*                                                                          *)
(* There are two types of theorem pattern clause.                           *)
(*                                                                          *)
(* There are main clauses, in which tests are performed on a foundthm. All  *)
(* of the constructors are allowed in this type of clause, though in        *)
(* principle, side-condition tests should not be. Side-condition tests      *)
(* within main clauses are re-interpreted as follows:                       *)
(*                                                                          *)
(*    Side <side-condition>                                                 *)
(*                                                                          *)
(* is interpreted as                                                        *)
(*                                                                          *)
(*    (Conc (autotermpattern `conc:bool`)) Where (Side <side-condition>)    *)
(*                                                                          *)
(* This only makes sense if <side-condition> tests `conc`.                  *)
(*                                                                          *)
(* Only `Side', `Andalso', `Orelse', and `Not' constructors are permitted   *)
(* within a side-condition clause.                                          *)
(*                                                                          *)
(* `Where' is used to link these two types of clause. Its first argument is *)
(* a main clause. Its second argument is a side-condition clause. Note that *)
(* `Where' cannot occur within a side-condition clause.                     *)
(*                                                                          *)
(* All of these constraints are imposed by the abstract datatype, which     *)
(* uses the type `thmpattern_rep' as its representing type.                 *)
(*==========================================================================*)

datatype thmpattern = ThmPattern of thmpattern_rep;

(*--------------------------------------------------------------------------*)
(* The following auxiliary matching functions should be local to the type   *)
(* definition. Hence, they are hidden from the user.                        *)
(*--------------------------------------------------------------------------*)

local

val conc_var =
   Term.mk_var {Name = "conc",Ty = Type.mk_type {Args = [],Tyop = "bool"}};

(*--------------------------------------------------------------------------*)
(* andalsofn : (unit -> result_of_match) ->                                 *)
(*             (unit -> result_of_match) ->                                 *)
(*             (unit -> result_of_match)                                    *)
(*                                                                          *)
(* This function is used for ANDing two `result_of_matches' together.       *)
(*                                                                          *)
(* The first argument is applied to (). If the result is `Nomatch', then    *)
(* the result of the whole evaluation is `Nomatch'. If not, the second      *)
(* argument is treated similarly. If both the arguments contain matchings,  *)
(* the function attempts to join the two `heads'. If this succeeds, the     *)
(* result becomes the `head' of the combined `result_of_match'. If not, the *)
(* result is discarded.                                                     *)
(*                                                                          *)
(* The rest of the `result_of_match' is (when required) obtained by calling *)
(* `andalsofn' recursively, firstly on the original first argument and the  *)
(* `tail' of the second, and then on the tail of the first and the original *)
(* second argument. The two resulting `result_of_matches' are appended      *)
(* using `approms'.                                                         *)
(*                                                                          *)
(* The overall effect of this is to combine a `list' of n matchings with a  *)
(* `list' of m matchings to form a `list' of all the possible combinations  *)
(* of matchings which can be joined successfully (maximum length n * m).    *)
(*--------------------------------------------------------------------------*)

fun andalsofn rom1fn rom2fn () =
   case (rom1fn ())
   of Nomatch => Nomatch
    | Match (m1,romfn1) =>
      (case (rom2fn ())
       of Nomatch => Nomatch
        | Match (m2,romfn2) =>
          let val rest =
                 approms (andalsofn rom1fn romfn2) (andalsofn romfn1 rom2fn)
          in  Match (join_matchings m1 m2,rest) handle NO_MATCH => rest ()
          end);

(*--------------------------------------------------------------------------*)
(* notfn : (unit -> result_of_match) -> (unit -> result_of_match)           *)
(*                                                                          *)
(* This function simply negates a `result_of_match', discarding any         *)
(* matchings, since they make no sense when negated. `Not' can therefore be *)
(* very destructive.                                                        *)
(*--------------------------------------------------------------------------*)

fun notfn rom1fn () =
   case (rom1fn ())
   of Nomatch => Match_null
    | Match _ => Nomatch;

(*--------------------------------------------------------------------------*)
(* sidematch : thmpattern_rep -> matching -> unit -> result_of_match        *)
(*                                                                          *)
(* This function is used for processing side-condition clauses, given an    *)
(* environment which consists of a single matching. All side-condition      *)
(* tests within the clause are applied to this matching.                    *)
(*                                                                          *)
(* Tests on the foundthm itself are prohibited (there is no foundthm        *)
(* available to test). This means that the first six cases for theorem      *)
(* patterns all cause failures.                                             *)
(*                                                                          *)
(* If the side-condition clause is simply a side-condition, the             *)
(* side-condition is applied to the environment. If the test succeeds, the  *)
(* result is passed back up. If not, `Nomatch' is passed back up.           *)
(*                                                                          *)
(* `Andalso', `Orelse' and `Not' cause `sidematch' to be called             *)
(* recursively, and the results of these calls are processed further by     *)
(* subsidiary functions. `Where' is prohibited within side-condition        *)
(* clauses.                                                                 *)
(*                                                                          *)
(* The failures due to illegal constructor use should never occur because   *)
(* the abstract datatype will prevent such constructions.                   *)
(*--------------------------------------------------------------------------*)

fun sidematch thmp_rep env () =
   case thmp_rep
   of Kind' _ => failwith_message "sidematch" "illegal use of Kind"
    | Thryname' _ => failwith_message "sidematch" "illegal use of Thryname"
    | Thmname' _ => failwith_message "sidematch" "illegal use of Thmname"
    | Conc' _ => failwith_message "sidematch" "illegal use of Conc"
    | HypP' _ => failwith_message "sidematch" "illegal use of HypP"
    | HypF' _ => failwith_message "sidematch" "illegal use of HypF"
    | Any' => Match_null
    | None' => Nomatch
    | Side' x => (x env handle NO_MATCH => Nomatch)
    | Andalso' (x,y) => andalsofn (sidematch x env) (sidematch y env) ()
    | Orelse' (x,y) => approms (sidematch x env) (sidematch y env) ()
    | Not' x => notfn (sidematch x env) ()
    | Where' _ => failwith_message "sidematch" "illegal use of Where";

(*--------------------------------------------------------------------------*)
(* wherefn : thmpattern_rep ->                                              *)
(*           (unit -> result_of_match) ->                                   *)
(*           (unit -> result_of_match)                                      *)
(*                                                                          *)
(* This function is used for handling side-condition clauses.               *)
(*                                                                          *)
(* It passes each matching in the `result_of_match' it is given to the      *)
(* theorem pattern. The matchings are passed in turn as environments. The   *)
(* evaluation proceeds only as far as is necessary, but the potential to    *)
(* continue it is retained.                                                 *)
(*                                                                          *)
(* `sidematch' is used to test the theorem pattern under each of the        *)
(* environments. It returns a `result_of_match'. Only those matchings       *)
(* consistent with the environment should be retained. That is, any         *)
(* wildcard which appears in the environment as well as in the matching     *)
(* should match to the same object in both cases. `andalsofn' is used to    *)
(* perform this checking.                                                   *)
(*                                                                          *)
(* The `result_of_matches' generated for each environment are appended      *)
(* using `approms'.                                                         *)
(*--------------------------------------------------------------------------*)

fun wherefn thmp_rep rom1fn () =
   case (rom1fn ())
   of Nomatch => Nomatch
    | Match (m,romfn) =>
      approms (andalsofn (fn () => Match (m,fn () => Nomatch))
                  (sidematch thmp_rep m))
         (wherefn thmp_rep romfn) ();

(*--------------------------------------------------------------------------*)
(* kindfn : thmkind -> foundthm -> (unit -> result_of_match)                *)
(*                                                                          *)
(* This function tests the kind of a found theorem.                         *)
(*--------------------------------------------------------------------------*)

fun kindfn knd (fthm : foundthm) () = bool_to_rom (knd = #1 fthm);

(*--------------------------------------------------------------------------*)
(* thrynamefn : namepattern -> foundthm -> (unit -> result_of_match)        *)
(*                                                                          *)
(* This function uses a `namepattern' to test the name of the theory to     *)
(* which a found theorem belongs.                                           *)
(*--------------------------------------------------------------------------*)

fun thrynamefn nmp (fthm : foundthm) () =
   bool_to_rom (namematch nmp (#2 fthm));

(*--------------------------------------------------------------------------*)
(* thmnamefn : namepattern -> foundthm -> (unit -> result_of_match)         *)
(*                                                                          *)
(* This function uses a `namepattern' to test the name of a found theorem.  *)
(*--------------------------------------------------------------------------*)

fun thmnamefn nmp (fthm : foundthm) () = bool_to_rom (namematch nmp (#3 fthm));

(*--------------------------------------------------------------------------*)
(* concfn : termpattern -> foundthm -> (unit -> result_of_match)            *)
(*                                                                          *)
(* This function tests the conclusion of a found theorem against a          *)
(* termpattern.                                                             *)
(*                                                                          *)
(* The conclusion is extracted and then matched against the termpattern.    *)
(* If the match succeeds, the matching is made into a `result_of_match'.    *)
(* Otherwise, `Nomatch' is returned as the `result_of_match'.               *)
(*--------------------------------------------------------------------------*)

fun concfn patt (fthm : foundthm) () =
   Match (make_matching patt (Thm.concl (#4 fthm)),fn () => Nomatch)
   handle NO_MATCH => Nomatch;

(*--------------------------------------------------------------------------*)
(* hypfn : termpattern list -> term list -> (unit -> result_of_match)       *)
(*                                                                          *)
(* This function tests a list of termpatterns against a list of hypotheses. *)
(*                                                                          *)
(* The result is a `result_of_match'. A subsidiary function is used to      *)
(* allow backtracking.                                                      *)
(*                                                                          *)
(* `hypmatch' takes four arguments plus a null argument to provide `lazy'   *)
(* evaluation. The first argument is an accumulated matching for the        *)
(* wildcards bound so far. The second argument is a list of hypotheses left *)
(* unmatched. This has to be remembered while the various ways of matching  *)
(* them are attempted. The third argument is the list of patterns not yet   *)
(* matched. The fourth argument is the list of hypotheses which have not    *)
(* yet been tried against the head of the pattern list.                     *)
(*                                                                          *)
(* When the pattern list is empty, the accumulated matching is made into a  *)
(* `result_of_match', and returned as result. If the list of hypotheses     *)
(* runs out before the patterns, `Nomatch' is returned.                     *)
(*                                                                          *)
(* If the head of the pattern list matches the head of the hypothesis list, *)
(* and the resulting matching is consistent with the accumulated matching,  *)
(* the head of the hypothesis list is removed from the previous level's     *)
(* list and `hypmatch' is called recursively to attempt a new level of      *)
(* match. Any other ways of matching are found as described below, and are  *)
(* appended to the result of this call.                                     *)
(*                                                                          *)
(* Any other ways of matching are found by a recursive call to `hypmatch'   *)
(* with all of the original arguments except that the fourth argument is    *)
(* the tail of the original list. The result of this call becomes the       *)
(* result of the original call if the head of the pattern list did not      *)
(* match the head of the hypothesis list.                                   *)
(*--------------------------------------------------------------------------*)

fun hypfn pattl hypl () =
   let fun hypmatch m prevtl [] _ () = Match (m,fn () => Nomatch)
         | hypmatch m prevtl _ [] () = Nomatch
         | hypmatch m prevtl (pl as p::ps) (terml as term::terms) () =
          let val rest = hypmatch m prevtl pl terms
          in  let val newm = join_matchings m (make_matching p term)
                  val newtl = filter (fn x => not (x = term)) prevtl
              in  approms (hypmatch newm newtl ps newtl) rest ()
              end
              handle NO_MATCH => rest ()
          end
   in  hypmatch null_matching hypl pattl hypl ()
   end;

(*--------------------------------------------------------------------------*)
(* hypPfn : termpattern list -> foundthm -> (unit -> result_of_match)       *)
(*                                                                          *)
(* This function tests the hypotheses of a found theorem against a list of  *)
(* termpatterns. Not all of the hypotheses need to be matched for the match *)
(* to succeed.                                                              *)
(*                                                                          *)
(* The list of hypotheses is extracted from the found theorem. If there are *)
(* more termpatterns than hypotheses, `Nomatch' is returned. Otherwise,     *)
(* `hypfn' is used to test the termpatterns against the hypotheses.         *)
(*--------------------------------------------------------------------------*)

fun hypPfn pattl (fthm : foundthm) () =
   let val hypl = Thm.hyp (#4 fthm)
   in  if (length pattl > length hypl)
       then Nomatch
       else hypfn pattl hypl ()
   end;

(*--------------------------------------------------------------------------*)
(* hypFfn : termpattern list -> foundthm -> (unit -> result_of_match)       *)
(*                                                                          *)
(* This function tests the hypotheses of a found theorem against a list of  *)
(* termpatterns. All of the hypotheses need to be matched for the match to  *)
(* succeed.                                                                 *)
(*                                                                          *)
(* The list of hypotheses is extracted from the found theorem. If there are *)
(* the same number of termpatterns as there are hypotheses, `hypfn' is used *)
(* to test the termpatterns against the hypotheses. Otherwise, `Nomatch' is *)
(* returned.                                                                *)
(*--------------------------------------------------------------------------*)

fun hypFfn pattl (fthm : foundthm) () =
   let val hypl = Thm.hyp (#4 fthm)
   in  if (length pattl = length hypl)
       then hypfn pattl hypl ()
       else Nomatch
   end;

(*--------------------------------------------------------------------------*)
(* mainmatch : thmpattern_rep -> foundthm -> unit -> result_of_match        *)
(*                                                                          *)
(* This function is used for processing main clauses of theorem patterns,   *)
(* given a foundthm to match against. For the first six cases of clause     *)
(* type, auxiliary functions are called. Note that these and `mainmatch'    *)
(* itself are lazy. That is they require a null argument before they        *)
(* actually perform any computation.                                        *)
(*                                                                          *)
(* Side-condition clauses are re-interpreted when they occur within a main  *)
(* clause, as described at the beginning of this abstract type definition.  *)
(*                                                                          *)
(* `Andalso' and `Orelse' call `mainmatch' recursively on their two         *)
(* arguments and use subsidiary functions to combine the results. `Not'     *)
(* calls `mainmatch' on its argument and then calls a subsidiary function   *)
(* to process the result. `Where' calls `mainmatch' on its first argument,  *)
(* and then passes the result along with its second argument to a function  *)
(* which deals with the side-condition clause.                              *)
(*--------------------------------------------------------------------------*)

fun mainmatch thmp_rep fthm () =
   case thmp_rep
   of Any' => Match_null
    | None' => Nomatch
    | Kind' x => kindfn x fthm ()
    | Thryname' x => thrynamefn x fthm ()
    | Thmname' x => thmnamefn x fthm ()
    | Conc' x => concfn x fthm ()
    | HypP' x => hypPfn x fthm ()
    | HypF' x => hypFfn x fthm ()
    | Side' _ =>
      mainmatch (Where' ((Conc' o autotermpattern) conc_var,thmp_rep)) fthm ()
    | Andalso' (x,y) => andalsofn (mainmatch x fthm) (mainmatch y fthm) ()
    | Orelse' (x,y) => approms (mainmatch x fthm) (mainmatch y fthm) ()
    | Not' x => notfn (mainmatch x fthm) ()
    | Where' (x,y) => wherefn y (mainmatch x fthm) ();

in

(*--------------------------------------------------------------------------*)
(* Any : thmpattern                                                         *)
(* None : thmpattern                                                        *)
(* Kind : thmkind -> thmpattern                                             *)
(* Thryname : namepattern -> thmpattern                                     *)
(* Thmname : namepattern -> thmpattern                                      *)
(* Conc : termpattern -> thmpattern                                         *)
(* HypP : termpattern list -> thmpattern                                    *)
(* HypF : termpattern list -> thmpattern                                    *)
(* Side : side_condition -> thmpattern                                      *)
(* Andalso : (thmpattern * thmpattern) -> thmpattern                        *)
(* Orelse : (thmpattern * thmpattern) -> thmpattern                         *)
(* Not : thmpattern -> thmpattern                                           *)
(*--------------------------------------------------------------------------*)

val Any = ThmPattern Any';
val None = ThmPattern None';
val Kind = ThmPattern o Kind';
val Thryname = ThmPattern o Thryname';
val Thmname = ThmPattern o Thmname';
val Conc = ThmPattern o Conc';
val HypP = ThmPattern o HypP';
val HypF = ThmPattern o HypF';
val Side = ThmPattern o Side';

fun Andalso (ThmPattern thmp1,ThmPattern thmp2) =
   ThmPattern (Andalso' (thmp1,thmp2));

fun Orelse (ThmPattern thmp1,ThmPattern thmp2) =
   ThmPattern (Orelse' (thmp1,thmp2));

fun Not (ThmPattern thmp) = ThmPattern (Not' thmp);

(*--------------------------------------------------------------------------*)
(* is_legal_sidecond : thmpattern_rep -> bool                               *)
(*                                                                          *)
(* Function to check that a side-condition clause is legal.                 *)
(*--------------------------------------------------------------------------*)

fun bad_side_condition () = failwith_message "Where" "bad side-condition";

fun is_legal_sidecond (Kind' _) = bad_side_condition ()
  | is_legal_sidecond (Thryname' _) = bad_side_condition ()
  | is_legal_sidecond (Thmname' _) = bad_side_condition ()
  | is_legal_sidecond (Conc' _) = bad_side_condition ()
  | is_legal_sidecond (HypP' _) = bad_side_condition ()
  | is_legal_sidecond (HypF' _) = bad_side_condition ()
  | is_legal_sidecond Any' = bad_side_condition ()
  | is_legal_sidecond None' = bad_side_condition ()
  | is_legal_sidecond (Side' _) = true
  | is_legal_sidecond (Andalso' (thmp_rep1,thmp_rep2)) =
   (is_legal_sidecond thmp_rep1) andalso (is_legal_sidecond thmp_rep2)
  | is_legal_sidecond (Orelse' (thmp_rep1,thmp_rep2)) =
   (is_legal_sidecond thmp_rep1) andalso (is_legal_sidecond thmp_rep2)
  | is_legal_sidecond (Not' thmp_rep1) = is_legal_sidecond thmp_rep1
  | is_legal_sidecond (Where' _) = bad_side_condition ();

(*--------------------------------------------------------------------------*)
(* Where : (thmpattern * thmpattern) -> thmpattern                          *)
(*                                                                          *)
(* The function `is_legal_sidecond' either returns `true' or fails. The     *)
(* failure which occurs in the body of `Where' if `is_legal_sidecond'       *)
(* returns false is therefore unnecessary.                                  *)
(*--------------------------------------------------------------------------*)

fun Where (ThmPattern thmp1,ThmPattern thmp2) =
   if (is_legal_sidecond thmp2)
   then ThmPattern (Where' (thmp1,thmp2))
   else bad_side_condition ();

(*--------------------------------------------------------------------------*)
(* thmmatch : thmpattern -> foundthm -> bool                                *)
(*                                                                          *)
(* Function to test a theorem pattern against a foundthm.                   *)
(*                                                                          *)
(* It calls `mainmatch' to attempt the matching. `mainmatch' returns a      *)
(* `result_of_match', which `thmmatch' converts to a Boolean value.         *)
(*--------------------------------------------------------------------------*)

fun thmmatch (ThmPattern thmp) fthm = rom_to_bool (mainmatch thmp fthm ());

end;

(*--------------------------------------------------------------------------*)
(* thmfilter : thmpattern -> foundthm list -> foundthm list                 *)
(*                                                                          *)
(* Function to filter a list of theorems using a theorem pattern.           *)
(*--------------------------------------------------------------------------*)

val thmfilter = filter o thmmatch;

end;

end; (* RetrieveMatching *)
