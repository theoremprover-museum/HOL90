(****************************************************************************)
(* FILE          : struct.sml                                               *)
(* DESCRIPTION   : Matching the structure of HOL types and terms.           *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 1989                                                     *)
(*                                                                          *)
(* TRANSLATED BY : D.R.Syme                                                 *)
(* DATE          : 1995                                                     *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 29th September 1995                                      *)
(****************************************************************************)

structure RetrieveStruct : RETRIEVE_STRUCT =
struct

local

open RetrieveExceptions RetrieveExtract;

fun failwith_message function message =
   raise HOL_ERR{origin_structure = "RetrieveStruct",
                 origin_function = function,
                 message = message};

fun failwith function = failwith_message function "";

(*--------------------------------------------------------------------------*)
(* merge : (''a * ''b) list -> (''a * ''b) list -> (''a * ''b) list         *)
(*                                                                          *)
(* Function to merge two association lists, failing if the lists are        *)
(* inconsistent.                                                            *)
(*                                                                          *)
(* The first element of the pair at the head of l2 is looked-up in l1. If   *)
(* the second element of the pair obtained is equal to the second element   *)
(* of the pair at the head of l2, then the head of l2 is discarded.         *)
(* Otherwise, the merge fails. If the look-up in l1 fails, the head of l2   *)
(* is retained.                                                             *)
(*--------------------------------------------------------------------------*)

fun merge l1 l2 =
   if (null l2)
   then l1
   else (let val p = assoc (fst (hd l2)) l1
         in  if (p = snd (hd l2))
             then (merge l1 (tl l2))
             else failwith "merge"
         end
         handle NOT_FOUND => ((hd l2)::(merge l1 (tl l2))));

(*--------------------------------------------------------------------------*)
(* join : (term * term) list * (hol_type * hol_type) list ->                *)
(*        (term * term) list * (hol_type * hol_type) list ->                *)
(*        (term * term) list * (hol_type * hol_type) list                   *)
(*                                                                          *)
(* Function to merge two `match' lists.                                     *)
(*--------------------------------------------------------------------------*)

fun join (avtl,attl) (bvtl,bttl) =
   (merge avtl bvtl,merge attl bttl) handle HOL_ERR _ => raise NO_MATCH;

(*--------------------------------------------------------------------------*)
(* remove_bv : term ->                                                      *)
(*             (term * term) list * (hol_type * hol_type) list ->           *)
(*             (term * term) list * (hol_type * hol_type) list              *)
(*                                                                          *)
(* Function to remove a bound variable from a `match' list.                 *)
(*                                                                          *)
(* Any pairs in the variable-term association list which have the bound     *)
(* variable as their first element are filtered out.                        *)
(*--------------------------------------------------------------------------*)

fun remove_bv bv (vtl,ttl) = (filter (fn x => not (fst x = bv)) vtl,ttl);

(*--------------------------------------------------------------------------*)
(* match_type : hol_type -> hol_type -> (hol_type * hol_type) list          *)
(*                                                                          *)
(* Function for matching two types.                                         *)
(*                                                                          *)
(* The first type given, p, must be the more general.                       *)
(*                                                                          *)
(* If p is a simple polymorphic type (i.e. one containing no constructors)  *)
(* then it can match any type. A single item association list is            *)
(* constructed from the two types in such a case.                           *)
(*                                                                          *)
(* If p is not a simple type, it is split up into a constructor and a list  *)
(* of simpler types. An attempt is made to split t, also. If this fails,    *)
(* then no match can be made. If the constructors obtained from p and t are *)
(* different then the match must fail. The lists of simpler types obtained  *)
(* from decomposing p and t are converted to a list of pairs, the match     *)
(* failing if the original lists were not of the same length. The function  *)
(* is then applied recursively to each pair of the new list, and the        *)
(* results are merged. If merging fails, the whole match fails.             *)
(*--------------------------------------------------------------------------*)

fun match_type p t =
   if (Type.is_vartype p)
   then [(p,t)]
   else let val {Tyop = pc,Args = ptypl} = Type.dest_type p
            and {Tyop = tc,Args = ttypl} =
               Type.dest_type t handle HOL_ERR _ => raise NO_MATCH
        in  if (pc = tc)
            then itlist merge
                    (map (fn (x,y) => match_type x y) (zip ptypl ttypl)) []
                 handle HOL_ERR _ => raise NO_MATCH
            else raise NO_MATCH
        end;

(*--------------------------------------------------------------------------*)
(* match_term                                                               *)
(*    : term -> term -> (term * term) list * (hol_type * hol_type) list     *)
(*                                                                          *)
(* Function for matching two terms.                                         *)
(*                                                                          *)
(* The first term given, p, must be the more general.                       *)
(*                                                                          *)
(* The function consists of four cases.                                     *)
(*                                                                          *)
(* p is a constant. If t is not a constant, the match fails. If the names   *)
(* of p and t are different, the match fails. Constants cannot be           *)
(* wildcards, so only the types need adding to the `match' list. One might  *)
(* think the match should fail if the types are different, but this is not  *)
(* the case. Consider the `=' function, for instance. The types must match, *)
(* however.                                                                 *)
(*                                                                          *)
(* p is a variable. A variable can match any term, provided its type can be *)
(* matched to that of the term.                                             *)
(*                                                                          *)
(* p is an abstraction. An abstraction can only match another abstraction.  *)
(* p and t are decomposed into their bound variables and bodies. The bound  *)
(* variables are matched to obtain the type matchings. The bodies are also  *)
(* matched. The resultant matchings are then merged, and the bound variable *)
(* is then removed from the variable-term list to allow for renaming of     *)
(* bound variables. Note that the merge has to be done before the           *)
(* bound variable is removed to ensure the bound variables correspond in    *)
(* the body.                                                                *)
(*                                                                          *)
(* p is a combination. A combination can only match another combination.    *)
(* p and t are decomposed into their rators and rands. The two rators are   *)
(* matched against each other. The two rands are matched. Then the          *)
(* resulting `match' lists are merged.                                      *)
(*--------------------------------------------------------------------------*)

fun match_term p t =
   case (Term.dest_term p)
   of CONST {Name = pname,Ty = _} =>
      if (pname = #Name (Term.dest_const t) handle HOL_ERR _ => false)
      then ([],match_type (Term.type_of p) (Term.type_of t))
      else raise NO_MATCH
    | VAR _ => ([(p,t)],match_type (Term.type_of p) (Term.type_of t))
    | LAMB {Bvar = pbv,Body = pbody} =>
      let val {Bvar = tbv,Body = tbody} =
             Term.dest_abs t handle HOL_ERR _ => raise NO_MATCH
      in  remove_bv pbv (join (match_term pbv tbv) (match_term pbody tbody))
      end
    | COMB {Rator = prator,Rand = prand} =>
      let val {Rator = trator,Rand = trand} =
             Term.dest_comb t handle HOL_ERR _ => raise NO_MATCH
      in  join (match_term prator trator) (match_term prand trand)
      end;

(*--------------------------------------------------------------------------*)
(* match_internal_type                                                      *)
(*    : term -> term -> (term * term) list * (hol_type * hol_type) list     *)
(*                                                                          *)
(* Function to match a term pattern inside a term.                          *)
(*                                                                          *)
(* The function applies match_term to the pattern and the term. If this     *)
(* fails the function is called recursively on any possible sub-terms of    *)
(* the term. If all these attempts to match fail, the whole evaluation      *)
(* fails.                                                                   *)
(*--------------------------------------------------------------------------*)

fun match_internal_term p t =
   match_term p t
   handle NO_MATCH =>
   (match_internal_term p (Term.rator t handle HOL_ERR _ => raise NO_MATCH))
   handle NO_MATCH =>
   (match_internal_term p (Term.rand t handle HOL_ERR _ => raise NO_MATCH))
   handle NO_MATCH =>
   (match_internal_term p
      (#Body (Term.dest_abs t handle HOL_ERR _ => raise NO_MATCH)))
   handle NO_MATCH => raise NO_MATCH;

in

(*==========================================================================*)
(* Datatype for wildcard variables to be used in pattern matching.          *)
(*==========================================================================*)

datatype wildvar = Wildvar of Term.term;

(*--------------------------------------------------------------------------*)
(* show_wildvar : wildvar -> term                                           *)
(*                                                                          *)
(* Function to convert a wildvar into a term.                               *)
(*--------------------------------------------------------------------------*)

fun show_wildvar (Wildvar w) = w;

(*--------------------------------------------------------------------------*)
(* make_wildvar : term -> wildvar                                           *)
(*                                                                          *)
(* Function to make a wildvar from a term. The term must be a variable.     *)
(*--------------------------------------------------------------------------*)

fun make_wildvar t =
   if (Term.is_var t)
   then Wildvar t
   else failwith_message "wildvar" "term is not a variable";

(*--------------------------------------------------------------------------*)
(* wildvarlist : term list -> wildvar list                                  *)
(*                                                                          *)
(* Function to make a list of wildvars out of a list of terms.              *)
(*--------------------------------------------------------------------------*)

val wildvarlist = map make_wildvar;

(*==========================================================================*)
(* Datatype for wildcard types to be used in pattern matching.              *)
(*==========================================================================*)

datatype wildtype = Wildtype of Type.hol_type;

(*--------------------------------------------------------------------------*)
(* show_wildtype : wildtype -> hol_type                                     *)
(*                                                                          *)
(* Function to convert a wildtype into a hol_type.                          *)
(*--------------------------------------------------------------------------*)

fun show_wildtype (Wildtype w) = w;

(*--------------------------------------------------------------------------*)
(* make_wildtype : hol_type -> wildtype                                     *)
(*                                                                          *)
(* Function to make a wildtype from a hol_type.                             *)
(* The type must be a `primitive' polymorphic type.                         *)
(*--------------------------------------------------------------------------*)

fun make_wildtype t =
   if (Type.is_vartype t)
   then Wildtype t
   else failwith_message "wildtype" "type is not polymorphic";

(*--------------------------------------------------------------------------*)
(* wildtypelist : hol_type list -> wildtype list                            *)
(*                                                                          *)
(* Function to make a list of wildtypes out of a list of types.             *)
(*--------------------------------------------------------------------------*)

val wildtypelist = map make_wildtype;

(*==========================================================================*)
(* Datatype for patterns used to match terms.                               *)
(*==========================================================================*)

datatype termpattern =
   TermPattern of (Term.term * wildvar list * wildtype list);

(*--------------------------------------------------------------------------*)
(* show_termpattern : termpattern -> (term * wildvar list * wildtype list)  *)
(*                                                                          *)
(* Function to convert a termpattern to its representing type.              *)
(*--------------------------------------------------------------------------*)

fun show_termpattern (TermPattern p) = p;

(*--------------------------------------------------------------------------*)
(* make_termpattern : (term * wildvar list * wildtype list) -> termpattern  *)
(*                                                                          *)
(* Function to make a termpattern from a term, a list of wildcard variables *)
(* and a list of wildcard types.                                            *)
(*--------------------------------------------------------------------------*)

fun make_termpattern (tm,wvl,wtl) =
   let (* Convert wildcard variables to their representing variables *)

       val varl = map show_wildvar wvl

       (* Convert wildcard types to their representing type *)

       and typl = map show_wildtype wtl

   in  (* Form a termpattern if and only if the lists of wildcard variables *)
       (* and wildcard types are sets (i.e. contain no repetitions) and all *)
       (* the wildcard variables specified are free variables in tm and all *)
       (* the wildcard types specified are `primitive' polymorphic types    *)
       (* occurring in tm.                                                  *)

       if (RetrieveSets.no_rep varl) then
          if (RetrieveSets.no_rep typl) then
             if (RetrieveSets.is_subset (get_freevars tm) varl) then
                if (RetrieveSets.is_subset (get_primvartypes tm) typl) then
                   TermPattern (tm,wvl,wtl)
                else failwith_message "make_termpattern" "wildtype not in term"
             else failwith_message "make_termpattern" "wildvar not in term"
          else failwith_message "make_termpattern" "duplicate wildtype"
       else failwith_message "make_termpattern" "duplicate wildvar"
   end;

(*--------------------------------------------------------------------------*)
(* show_full_termpattern                                                    *)
(*    : termpattern -> (term * term list * hol_type list)                   *)
(*                                                                          *)
(* Function to convert a termpattern into its representing type, and the    *)
(* wildvars and wildtypes within that to their representing types.          *)
(* So, function makes all of a termpattern visible.                         *)
(*--------------------------------------------------------------------------*)

fun show_full_termpattern p =
   let val (tm,wvl,wtl) = show_termpattern p
   in  (tm,(map show_wildvar wvl),(map show_wildtype wtl))
   end;

(*--------------------------------------------------------------------------*)
(* make_full_termpattern                                                    *)
(*    : (term * term list * hol_type list) -> termpattern                   *)
(*                                                                          *)
(* Function to make a termpattern from a term, a list of terms, and a list  *)
(* of types. The term represents the pattern. The list of terms represents  *)
(* the variables which are to be taken as wildcards, and the list of types  *)
(* represents the `primitive' polymorphic types which are to be taken as    *)
(* wildcards.                                                               *)
(*--------------------------------------------------------------------------*)

fun make_full_termpattern (tm,terml,typel) =
   make_termpattern (tm,wildvarlist terml,wildtypelist typel);

(*--------------------------------------------------------------------------*)
(* autotermpattern : term -> termpattern                                    *)
(*                                                                          *)
(* Function to make a termpattern out of a term by using the free variables *)
(* in the term as wildvars and the `primitive' polymorphic types as         *)
(* wildtypes.                                                               *)
(*--------------------------------------------------------------------------*)

fun autotermpattern t =
   make_full_termpattern (t,get_freevars t,get_primvartypes t);

(*==========================================================================*)
(* Datatype for the result of matching a termpattern against a term.        *)
(*==========================================================================*)

datatype matching =
   Matching of (wildvar * Term.term) list * (wildtype * Type.hol_type) list;

(*--------------------------------------------------------------------------*)
(* show_matching                                                            *)
(*    : matching -> ((wildvar * term) list * (wildtype * hol_type) list)    *)
(*                                                                          *)
(* Function to convert a matching to its representing type.                 *)
(*--------------------------------------------------------------------------*)

fun show_matching (Matching m) = m;

(*--------------------------------------------------------------------------*)
(* null_matching : matching                                                 *)
(*                                                                          *)
(* A matching with no bindings.                                             *)
(*--------------------------------------------------------------------------*)

val null_matching = Matching ([],[]);

(*--------------------------------------------------------------------------*)
(* make_matching : termpattern -> term -> matching                          *)
(*                                                                          *)
(* Function to form a matching from a termpattern and a term.               *)
(*--------------------------------------------------------------------------*)

fun make_matching p t =
   let (* Extract low-level components of termpattern *)

       val (tm,varl,typl) = show_full_termpattern p

       (* Use `match_term' to attempt a matching of the template tm against *)
       (* the term t. If this fails, `make_matching' fails. If it succeeds  *)
       (* the (term * term) list * (hol_type * hol_type) list returned by   *)
       (* `match_term' is bound to the pair (vpl,tpl) for further           *)
       (* analysis/processing.                                              *)

       val (vpl,tpl) = match_term tm t

       (* The (term * term) list component returned by `match_term' is a    *)
       (* list of pairs such that the first element of the pair is a        *)
       (* variable in tm, and the second element of the pair is the term in *)
       (* t that the variable has been matched to.                          *)
       (*                                                                   *)
       (* Bound-variables in tm do not appear in the result of              *)
       (* `match_term'. Some of the variables which do appear may not have  *)
       (* been specified as wildvars. The match must fail if such a         *)
       (* variable does not (when its type has been instantiated) match     *)
       (* itself in the list returned by `match_term'. The                  *)
       (* (hol_type * hol_type) list, returned by `match_term' is used to   *)
       (* perform the instantiation.                                        *)
       (*                                                                   *)
       (* Types are dealt with similarly, except that there is no           *)
       (* equivalent action to instantiation.                               *)
       (*                                                                   *)
       (* The matching we are trying to construct should look like the      *)
       (* result of `match_term' except that the variables and types from   *)
       (* tm should be converted to wildcards, and only those of them that  *)
       (* appear as wildcards in the termpattern should be included.        *)
       (*                                                                   *)
       (* Now we know what we are trying to achieve, let us define some     *)
       (* functions to help us.                                             *)
       (*                                                                   *)
       (* f is used to convert the term or type which is representing a     *)
       (* wildcard into the appropriate wildcard type.                      *)

       fun f w (a,b) = ((w a),b)

       (* `instant_type' instantiates the type of a variable using a        *)
       (* (hol_type * hol_type) list in which the first element of each     *)
       (* pair is a `primitive' type. The embedded function `change_type'   *)
       (* does the real work. `instant_type' splits the variable into its   *)
       (* name and type, applies `change_type' to the type, and then        *)
       (* reconstructs the variable using the new type.                     *)

       fun instant_type ttl v =
          let (* `change_type' instantiates a type. If the type is          *)
              (* `primitive', it is looked-up in the instantiation list. If *)
              (* found, the corresponding instance is returned. If not the  *)
              (* type itself is returned. If the type is not `primitive',   *)
              (* it is decomposed into a constructor and a list of simpler  *)
              (* types. Each of the latter are then instantiated, and the   *)
              (* type is reconstructed.                                     *)

              fun change_type ttl typ =
                 if (is_primtype typ)
                 then assoc typ ttl handle NOT_FOUND => typ
                 else let val {Tyop = s,Args = l} = Type.dest_type typ
                      in  Type.mk_type
                             {Tyop = s,Args = map (change_type ttl) l}
                      end
          in  let val {Name = s,Ty = t} = Term.dest_var v
              in  Term.mk_var {Name = s,Ty = change_type ttl t}
              end
          end

       (* `build' filters its last argument removing any pairs whose first  *)
       (* element is not in xs. If lf applied to the first element of such  *)
       (* a pair is not equal to the second element of the pair, then the   *)
       (* match being performed is failed.                                  *)
       (*                                                                   *)
       (* `build' is used to build a matching from a `match' list and a     *)
       (* wildcard list. Any variable or type in the `match' list but not   *)
       (* in the wildcard list must match itself (allowing for type         *)
       (* instantiation - hence the need for lf), and will not be included  *)
       (* in the result.                                                    *)

       fun build lf xs [] = []
         | build lf xs ((xx as (x1,x2))::xxs) =
          if (mem x1 xs)
          then xx::(build lf xs xxs)
          else if (lf x1 = x2)
               then build lf xs xxs
               else raise NO_MATCH

   in  (* Note : assumes all variables which could be wildvars appear in    *)
       (*        the matching returned by `match_term'.                     *)

       Matching (map (f make_wildvar) (build (instant_type tpl) varl vpl),
                 map (f make_wildtype) (build (fn x => x) typl tpl))

   end;

(*--------------------------------------------------------------------------*)
(* join_matchings : matching -> matching -> matching                        *)
(*                                                                          *)
(* Function to combine two (consistent) matchings into a single matching.   *)
(*                                                                          *)
(* Split the two matchings into wildvar and wildtype `match' lists. Merge   *)
(* the two resulting wildvar lists and the two resulting wildtype lists.    *)
(* If either merge fails, the match fails.                                  *)
(*--------------------------------------------------------------------------*)

fun join_matchings (Matching m) (Matching n) =
   let val (mwvl,mwtl) = m
       and (nwvl,nwtl) = n
   in  Matching (merge mwvl nwvl,merge mwtl nwtl)
   end
   handle HOL_ERR _ => raise NO_MATCH;

(*--------------------------------------------------------------------------*)
(* show_full_matching                                                       *)
(*    : matching -> ((term * term) list * (hol_type * hol_type) list)       *)
(*                                                                          *)
(* Function to convert a matching into its representing type, and the       *)
(* wildvars and wildtypes within that to their representing types.          *)
(* So, function makes all of a matching visible.                            *)
(*--------------------------------------------------------------------------*)

fun show_full_matching m =
   let val (wvl,wtl) = show_matching m
       fun f (w,t) = (show_wildvar w,t)
       fun g (w,t) = (show_wildtype w,t)
   in  (map f wvl,map g wtl)
   end;

(*--------------------------------------------------------------------------*)
(* match_of_var : matching -> wildvar -> term                               *)
(*                                                                          *)
(* Function to lookup a wildvar in a matching, and return the term to which *)
(* it is bound.                                                             *)
(*--------------------------------------------------------------------------*)

fun match_of_var m wv =
   (assoc wv o fst o show_matching) m
   handle NOT_FOUND =>
   failwith_message "match_of_var" "unknown wildvar (variable)";

(*--------------------------------------------------------------------------*)
(* match_of_type : matching -> wildtype -> hol_type                         *)
(*                                                                          *)
(* Function to lookup a wildtype in a matching, and return the type to      *)
(* which it is bound.                                                       *)
(*--------------------------------------------------------------------------*)

fun match_of_type m wt =
   (assoc wt o snd o show_matching) m
   handle NOT_FOUND =>
   failwith_message "match_of_type" "unknown wildtype (polymorphic type)";

(*==========================================================================*)
(* Datatype for lazy evaluation of alternate matchings.                     *)
(*                                                                          *)
(* Nomatch means there is no way to match.                                  *)
(* Match means there is at least one way to match, and specifies the        *)
(* matching (which may be null). The second element of the pair is a        *)
(* function to generate any other matchings if they exist.                  *)
(*==========================================================================*)

datatype result_of_match = Nomatch
                         | Match of matching * (unit -> result_of_match);

(*--------------------------------------------------------------------------*)
(* Abbreviation for a result_of_match which is a match with no bindings.    *)
(*--------------------------------------------------------------------------*)

val Match_null = Match (null_matching,fn () => Nomatch);

(*--------------------------------------------------------------------------*)
(* approms : (unit -> result_of_match) ->                                   *)
(*           (unit -> result_of_match) ->                                   *)
(*           (unit -> result_of_match)                                      *)
(*                                                                          *)
(* Function to append two lazy lists (`result_of_matches').                 *)
(*                                                                          *)
(* `approms' appends two `result_of_matches' which are essentially just     *)
(* lazy lists of matchings. The result must be kept as lazy as possible.    *)
(* This function is also used to OR two `result_of_matches', since this     *)
(* operation corresponds exactly to appending them.                         *)
(*                                                                          *)
(* The arguments to `approms' are actually functions from unit to a         *)
(* `result_of_match', so that as little evaluation as necessary is done.    *)
(*                                                                          *)
(* The function is defined in an analogous way to `append' on lists.        *)
(*--------------------------------------------------------------------------*)

fun approms rom1fn rom2fn () =
   case (rom1fn ())
   of Nomatch => rom2fn ()
    | Match (m,romfn) => Match (m,approms romfn rom2fn);

(*--------------------------------------------------------------------------*)
(* bool_to_rom : bool -> result_of_match                                    *)
(*                                                                          *)
(* Function to convert a Boolean value to a result_of_match.                *)
(*--------------------------------------------------------------------------*)

fun bool_to_rom true = Match_null
  | bool_to_rom false = Nomatch;

(*--------------------------------------------------------------------------*)
(* rom_to_bool : result_of_match -> bool                                    *)
(*                                                                          *)
(* Function to convert a result_of_match to a Boolean value.                *)
(*                                                                          *)
(* Note that information may be thrown away in this process.                *)
(*--------------------------------------------------------------------------*)

fun rom_to_bool (Match _) = true
  | rom_to_bool Nomatch = false;

(*==========================================================================*)
(* Abbreviation for the type representing side-conditions.                  *)
(*                                                                          *)
(* When applied to a matching, a side-condition performs tests on the       *)
(* bindings in the matching, and returns a `lazy list' of any successful    *)
(* new bindings.                                                            *)
(*==========================================================================*)

type side_condition = matching -> result_of_match;

end;

end; (* RetrieveStruct *)
