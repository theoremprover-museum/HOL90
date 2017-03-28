(*--------------------------------------------------------------------------*)
(*                  Copyright (c) Jim Grundy 1992                           *)
(*                  All rights reserved                                     *)
(*                                                                          *)
(* Jim Grundy, hereafter referred to as `the Author', retains the copyright *)
(* and all other legal rights to the Software contained in this file,       *)
(* hereafter referred to as `the Software'.                                 *)
(*                                                                          *)
(* The Software is made available free of charge on an `as is' basis. No    *)
(* guarantee, either express or implied, of maintenance, reliability,       *)
(* merchantability or suitability for any purpose is made by the Author.    *)
(*                                                                          *)
(* The user is granted the right to make personal or internal use of the    *)
(* Software provided that both:                                             *)
(* 1. The Software is not used for commercial gain.                         *)
(* 2. The user shall not hold the Author liable for any consequences        *)
(*    arising from use of the Software.                                     *)
(*                                                                          *)
(* The user is granted the right to further distribute the Software         *)
(* provided that both:                                                      *)
(* 1. The Software and this statement of rights are not modified.           *)
(* 2. The Software does not form part or the whole of a system distributed  *)
(*    for commercial gain.                                                  *)
(*                                                                          *)
(* The user is granted the right to modify the Software for personal or     *)
(* internal use provided that all of the following conditions are observed: *)
(* 1. The user does not distribute the modified software.                   *)
(* 2. The modified software is not used for commercial gain.                *)
(* 3. The Author retains all rights to the modified software.               *)
(*                                                                          *)
(* Anyone seeking a licence to use this software for commercial purposes is *)
(* invited to contact the Author.                                           *)
(*--------------------------------------------------------------------------*)
(*==========================================================================*)
(* CONTENTS: reflexivity, transitivity, strengh and window rules tables.    *)
(*==========================================================================*)
(*$Id: rules.sml,v 4.1 1994/09/10 03:42:51 jim Exp $*)

structure Rules :
    sig
        datatype path_elt = RATOR | RAND | BODY
        type path
        val traverse : path -> term -> term
	val boundin : path -> term -> term list
        type window_rule
        type rule_id
        val store_rule  : window_rule -> rule_id
        val search_rule : path -> (window_rule * rule_id) list
        val kill_rule : rule_id -> unit
    end =

struct

(* A path is a list made up of RATOR, RAND AND BODY.                        *)
(* Paths are used to denote a particular subterm within a term.             *)
datatype path_elt = RATOR | RAND | BODY;

type path = path_elt list;

(* The function traverse takes a path and returns a function from           *)
(*   a term to the selected subterm.                                        *)
local
    fun translate RATOR = rator
     |  translate RAND  = rand
     |  translate BODY  = body
in
    fun traverse p = rev_itlist (curry (op o)) (map translate p) I
end;

(* Find those variable bound in a path.				    	    *)
fun boundin []           _ = []
 |  boundin (RATOR::ps) tm = boundin ps (rator tm)
 |  boundin (RAND::ps)  tm = boundin ps (rand tm)
 |  boundin (BODY::ps)  tm = (bndvar tm)::(boundin ps (body tm))

(* A window rule is composed of the following components:                   *)
(*   A path which describes the subterm which is to be the focus of the     *)
(*       child window as a funtion of the focus of the parent.              *)
(*   Funtions from the focus of the parent window to the following:         *)
(*       A boolean indicating whether this rule is valid for use on the     *)
(*           focus.                                                         *)
(*       Functions from the relation the user wishes to preserve in the     *)
(*           parent window to:                                              *)
(*           The relationship that will be preserved in the child window.   *)
(*           The relationship that will be preserved in the parent window.  *)
(*       The set of new hypotheses for the parent window.		    *)
(*       A function from the theorem generated by the child window to one   *)
(*           relavent to the parent.                                        *)
type window_rule =  (   path
                    *   (term -> bool)
                    *   (term -> term -> term)
                    *   (term -> term -> term)
                    *   (term -> (thm list))
                    *   (term -> (thm -> thm))
                    );

(* Create and maintain a table of rules for opening at various positions    *)
(*   in a term.                                                             *)
(* The rules are stored in tree of assignable variables which is keyed      *)
(*   off the path.                                                          *)
(* The rules are stored along with a unique identifier.  This identifier    *)
(*    also tels us the relative age of the rules. The smaller the id, the   *)
(*    longer the rule has been in the system.                               *)

type rule_id = int;

datatype tree =
    TREE of ((window_rule * rule_id) list ref) * ((path_elt * tree) list ref);

fun new_tree () =
    let val new_value = ref ([]:(window_rule * rule_id) list)
        and new_kids = ref ([]:(path_elt * tree) list)
    in
        TREE(new_value,new_kids)
    end;
     
fun plant (TREE (value,kids)) (trail:path) rule id =
    if null trail then
        value := (rule,id)::(!value)
    else
        let val (t::ts) = trail in
        let val chosen_kid = assoc t (!kids)
                handle _ => 
                    let val new_kid = new_tree () in
                        kids := (t,new_kid)::(!kids);
                        new_kid
                    end
        in
            plant chosen_kid ts rule id
        end end;

fun harvest (TREE(value,kids)) (trail:path) =
    if null trail then
        !value
    else
        let val (t::ts) = trail in
            append ((harvest (assoc t (!kids)) ts) handle _ => []) (!value)
        end;

fun purge (TREE(value,kids)) id = 
    (
        map (C purge id o snd) (!kids);
        value := filter (fn (_,rid) => not (rid = id)) (!value)
    );

val rule_tree = new_tree ();
val next_id = ref 0;

fun store_rule r =
    let val id = !next_id in
        plant rule_tree (#1 r) r id;
        next_id := id + 1;
        id
    end;

val search_rule = harvest rule_tree;
val kill_rule = purge rule_tree;

end;

open Rules;
