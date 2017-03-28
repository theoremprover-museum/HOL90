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
(* CONTENTS: the core functional window inference system                    *)
(*==========================================================================*)
(*$Id: win.sml,v 4.1 1994/09/10 03:42:51 jim Exp $*)

structure Win :

sig
    datatype win_path = FOCUS_PATH of path | CONTEXT_PATH of (term * path)
    type win_stack
    val create_stack : window -> win_stack
    val top_window : win_stack -> window
    val top_path : win_stack -> win_path
    val depth_stack : win_stack -> int
    val bad_conjectures : win_stack -> term list
    val CONTEXT_LIST :
        (thm list -> win_stack -> win_stack) -> win_stack -> win_stack
    val ADD_SUPPOSE : goal -> win_stack -> win_stack
    val ADD_THEOREM : thm -> win_stack -> win_stack
    val TRANSFORM_WIN : thm -> win_stack -> win_stack
    val CONJECTURE : term -> win_stack -> win_stack
    val MATCH_TRANSFORM_WIN : thm -> win_stack -> win_stack
    val CONVERT_WIN : conv -> win_stack -> win_stack
    val RULE_WIN : (thm -> thm) -> win_stack -> win_stack
    val THM_RULE_WIN : (thm -> thm) -> win_stack -> win_stack
    val FOC_RULE_WIN : (term -> thm) -> win_stack -> win_stack
    val TACTIC_WIN : tactic -> win_stack -> win_stack
    val GEN_REWRITE_WIN :
	(conv -> conv) -> rewrites -> thm list -> win_stack -> win_stack
    val PURE_REWRITE_WIN : thm list -> win_stack -> win_stack
    val REWRITE_WIN : thm list -> win_stack -> win_stack
    val PURE_ONCE_REWRITE_WIN : thm list -> win_stack -> win_stack
    val ONCE_REWRITE_WIN : thm list -> win_stack -> win_stack
    val PURE_ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
    val ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
    val PURE_ONCE_ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
    val ONCE_ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
    val FILTER_PURE_ASM_REWRITE_WIN :
        (term -> bool) -> thm list -> win_stack -> win_stack
    val FILTER_ASM_REWRITE_WIN :
        (term -> bool) -> thm list -> win_stack -> win_stack
    val FILTER_PURE_ONCE_ASM_REWRITE_WIN :
        (term -> bool) -> thm list -> win_stack -> win_stack
    val FILTER_ONCE_ASM_REWRITE_WIN :
        (term -> bool) -> thm list -> win_stack -> win_stack
    val OPEN_WIN : path -> win_stack -> win_stack
    val OPEN_CONTEXT : term * path -> win_stack -> win_stack
    val ESTABLISH : term -> win_stack -> win_stack
    val CLOSE_WIN : win_stack -> win_stack
    val UNDO_WIN : win_stack -> win_stack
end

=

struct

(* Windows are either opened on a subterm of the focus, or on a subterm of  *)
(* the context.                                                             *)
datatype win_path = FOCUS_PATH of path | CONTEXT_PATH of (term * path);

(* A new datatype describes a stack of windows.                             *)
(* The base of the stack is a window.  New windows are linked onto the      *)
(* stack together with a close function.   When a window is closed, it      *)
(* is removed from the top of the stack and used together with the close    *)
(* function to transform the window below.                                  *)
datatype win_stack = BASE of window
                   | LINK of window
                           * (window -> (window -> window))
                           * win_path
                           * win_stack;

(* Create a new window stack containing window w.                           *)
fun create_stack w = BASE w;

(* The window on top of the stack.                                          *)
fun top_window (LINK (w,_,_,_)) = w
 |  top_window (BASE w) = w;

(* Removes the top window from the stack.                                   *)
fun pop_window (LINK (_,_,_,s)) = s
 |  pop_window (BASE _) = WIN_ERR{function="pop_window",message="stack bottom"};

(* Open a new window, requires a path, the new window, and a basis function.*)
fun open_window p (w,f) s = LINK (w,f,p,s);

(* Apply some transformation to the top window of the stack.                *)
fun change_window f (LINK (w,c,p,s)) = LINK (f w,c,p,s)
 |  change_window f (BASE w) = BASE (f w);

(* Removes the top window and transforms the one below.                     *)
fun close_window (LINK (w,c,_,s)) = change_window (c w) s
 |  close_window (BASE _) =
        WIN_ERR{function="close_window",message="stack bottom"};

(* The current depth of the stack.                                          *)
fun depth_stack (LINK (_,_,_,s)) = 1 + depth_stack s
 |  depth_stack (BASE _) = 1;

(* The path that the window on top of the stack was opened on.              *)
fun top_path (LINK (_,_,p,_)) = p
 |  top_path (BASE _) = WIN_ERR{function="top_path",message="stack bottom"};


(* The conjectures which are used in the top window and are not valid       *)
(*   in the window below.                                                   *)
fun bad_conjectures s =
    let val topwin = top_window s in
    let val bnds = bound topwin
        and  usedcnjs = used_conjectures topwin
    in
        if (depth_stack s) > 1 then
            let val winbelow =
                    transfer_sups_thms topwin (top_window (pop_window s)) in
            let val hypsbelow = all_hypotheses winbelow 
                and lemsbelow = lemmas winbelow 
                and cnjsbelow = conjectures winbelow in
            let val availbelow = hypsbelow@lemsbelow@cnjsbelow
            in
                (filter (not o (C term_mem availbelow)) usedcnjs)
                @
                (filter (fn c => exists (C mem bnds) (free_vars c)) usedcnjs)
            end end end
        else usedcnjs
    end end;

(* Transforms a function that takes a list of theorems and transforms a     *)
(* window stack, to one that uses the context of the top window.            *)
fun CONTEXT_LIST (f:thm list -> win_stack -> win_stack) s =
    f (map ASSUME (context (top_window s))) s;

(* Next we convert some of the functions from WinCore to work with stacks.  *)

val ADD_SUPPOSE = change_window o add_suppose
and ADD_THEOREM = change_window o add_theorem
and TRANSFORM_WIN = change_window o transform_win
and CONJECTURE = change_window o conjecture
and MATCH_TRANSFORM_WIN = change_window o match_transform_win
and CONVERT_WIN = change_window o convert_win
and RULE_WIN = change_window o rule_win
and THM_RULE_WIN = change_window o thm_rule_win
and FOC_RULE_WIN = change_window o foc_rule_win
and TACTIC_WIN = change_window o tactic_win;

(* Functions for rewriting the window.                                      *)
fun GEN_REWRITE_WIN rewrite_fun built_in_rewrites =
    let val REWL_CONV = GEN_REWRITE_CONV rewrite_fun built_in_rewrites in
        CONVERT_WIN o REWL_CONV
    end;

(* Basic rewriting functions.                                               *)
val PURE_REWRITE_WIN = GEN_REWRITE_WIN TOP_DEPTH_CONV empty_rewrites
and PURE_ONCE_REWRITE_WIN = GEN_REWRITE_WIN ONCE_DEPTH_CONV empty_rewrites
and REWRITE_WIN = GEN_REWRITE_WIN TOP_DEPTH_CONV (base_rewrites())
and ONCE_REWRITE_WIN = GEN_REWRITE_WIN ONCE_DEPTH_CONV (base_rewrites());

(* Assumption rewrite variants.                                             *)
fun PURE_ASM_REWRITE_WIN thl =
    CONTEXT_LIST (fn ctl => PURE_REWRITE_WIN (ctl@thl)) 
and ASM_REWRITE_WIN thl =
    CONTEXT_LIST (fn ctl => REWRITE_WIN (ctl@thl)) 
and PURE_ONCE_ASM_REWRITE_WIN thl =
    CONTEXT_LIST (fn ctl => PURE_ONCE_REWRITE_WIN (ctl@thl)) 
and ONCE_ASM_REWRITE_WIN thl =
    CONTEXT_LIST (fn ctl => ONCE_REWRITE_WIN (ctl@thl));

(* Filtered assumption rewriting.                                           *)
fun FILTER_PURE_ASM_REWRITE_WIN f thl =
    CONTEXT_LIST (fn ctl => PURE_REWRITE_WIN ((filter (f o concl) ctl)@thl)) 
and FILTER_ASM_REWRITE_WIN f thl =
    CONTEXT_LIST (fn ctl => REWRITE_WIN ((filter (f o concl) ctl)@thl)) 
and FILTER_PURE_ONCE_ASM_REWRITE_WIN f thl =
    CONTEXT_LIST
        (fn ctl => PURE_ONCE_REWRITE_WIN ((filter (f o concl) ctl)@thl))
and FILTER_ONCE_ASM_REWRITE_WIN f thl =
    CONTEXT_LIST (fn ctl => ONCE_REWRITE_WIN ((filter (f o concl) ctl)@thl));

(* Return the subwindow and close function required to open a subwindow at  *)
(* the position denoted by `path' in a window.                              *)
(* Finds the _best_ list of window rules to use in order to follow the path.*)
(* One list of rules is _better_ than another if.                           *)
(* 1. The relationship being preserved in the child window is weaker.       *)
(* 2. There are more hypotheses available in the child window.              *)
(* 3. The rules used from the start were more _specific_ to this case.      *)
(*    A rule is more _specific_ than another if.                            *)
(*    1. It follows a longer path.                                          *)
(*    2. It preserves a weaker relationship in the parent.                  *)
(*    3. It preserves a weaker relationship in the child.                   *)
(* 4. The rules used from the start were more recently added to the         *)
(*    database.                                                             *)
local
    fun path_of (p,_,_) = flatten (map (fn (l,_,_,_,_) => l) p)
    fun shorter r1 r2 = prefix (path_of r1) (path_of r2)
    (* Which of two lists of rules is the best *)
    fun better_rules [] [] = false
     |  better_rules ((p1,rp1,rc1,h1,id1:rule_id)::t1) ((p2,rp2,rc2,h2,id2)::t2)
        =
            if (length p1) > (length p2) then true
            else if (length p2) > (length p1) then false
            else (* (length p1) = (length p2) *)
                if is_weaker rp1 rp2  then true
                else if is_weaker rp2 rp1 then false
                else (* the parent relations are equal or uncomparable *)
                    if is_weaker rc1 rc2 then true
                    else if is_weaker rc2 rc1 then false
                    else (* the relations are equal or uncomparable *)
                        if (length h1) > (length h2) then true
                        else if (length h2) > (length h1) then false
                        else (* (length h1) = (length h2) *)
                        if id2 > id1 then true
                        else if id1 > id2 then false
                        else (* c1 = c2 *)
                            better_rules t1 t2
    (* Which is the better of two routes to a focus *)
    fun better_route (r1 as (psl1, w1, _)) (r2 as (psl2, w2, _)) =
        let val rel1  = relation w1
            and rel2  = relation w2
        in
            if is_weaker rel1 rel2 then r1
            else if is_weaker rel2 rel1 then r2
            else (* the relations are equal or uncomparable *)
                let val hyps1 = hypotheses w1
                    and hyps2 = hypotheses w2
                in
                    if (length hyps1) > (length hyps2) then r1
                    else if (length hyps2) > (length hyps1) then r2
                    else (* (length hyps1) = (length hyps2) *)
                        if better_rules psl1 psl2 then r1
                        else r2
                end
        end
    (* Assuming that l is a list of routes sorted by length,                *)
    (* crush_routes l, will delete all but the best rule of each length -   *)
    (* it is not possible to accurately compare routes of differing length. *)
    fun crush_routes [rt] = [rt]
     |  crush_routes (r1::r2::trts) =
            if (path_of r1) = (path_of r2) then
                crush_routes ((better_route r1 r2)::trts)
            else
                r1::(crush_routes (r2::trts))
    (* If l is a list of theorems that contain the assumptions of a window, *)
    (* then (avoid_bnds b l) returns a list of assumptions that preservs as *)
    (* much of the structure of the original list as possible, but avoids   *)
    (* assumptions that contain free variables in b.                        *)
    fun avoid_bnds bnds [] = []
     |  avoid_bnds bnds (t::ts) =
            if null (intersect bnds (thm_free_vars t)) then
                t::(avoid_bnds bnds ts)
            else
                let val (thyps,tconc) = dest_thm t in
                    if (null thyps) orelse (thyps = [tconc]) orelse
                       ((length thyps = 1) andalso (tconc = true_tm))
                    then
                        (avoid_bnds bnds ts)
                    else
                        avoid_bnds bnds
                            (   (ASSUME tconc)::
                                ((map (fn t => ADD_ASSUM t TRUTH) thyps)@ts)
                            )
                end
    (* Graft attempts to join a single window rule onto a route.            *)
    fun graft (step_info,pwin,close) =
        let val pfoc = focus pwin 
            and prel = relation pwin
            and phyps = hyp_thms pwin
            and plems = lemma_thms pwin
            and psups = suppositions pwin
            and pbnds = bound pwin
        in
            fn ((rpth,rapplic,rcrel,rprel,rhyps,rinf),id) => 
                if (rapplic pfoc) andalso (is_weaker prel (rprel pfoc prel))
                then
                    let val nbnds = boundin rpth pfoc in
                    let val cfoc = traverse rpth pfoc
                        and crel = rcrel pfoc prel
                        and cbnds = pbnds @ nbnds in
                    let val chyps =
                            thm_setify ((rhyps pfoc)@(avoid_bnds nbnds phyps))
                        and clems = plems
                        and csups = psups
                    in
                        (   step_info @
                                [(rpth, (rprel pfoc prel), crel, chyps, id)],
                            make_win crel cfoc csups cbnds chyps clems,
                            (fn cwin =>
                                close 
                                    (transform_win 
                                        (rinf pfoc (win_thm cwin))
                                        (transfer_sups_thms cwin pwin)))
                        )
                    end end end
                else
                    fail ()
        end
    (* (best_route p start) finds the best route to p that begins by taking *)
    (* one of the routes in start.                                          *)
    fun best_route pth (prt_rts as (pr::prs)) =
        let val pth_sofar = path_of pr in
            if pth_sofar = pth then
                pr
            else
                let val pth_rem = after pth_sofar pth in
                let val steps =
                        sort shorter
                            (mapfilter (graft pr) (search_rule pth_rem))
                in
                    if null steps then
                        WIN_ERR{function="OPEN_WIN",message=
                            "no applicable rule - please report this bug"}
                    else
                        best_route pth (crush_routes (merge shorter prs steps))
                end end
        end
in
    fun open_win_basis path win =
        let val hyps = hyp_thms win 
            and rel = relation win in
        let val start = [([([],rel,rel,hyps,0)],win,I)] in
        let val (_,subwin,closefn) = best_route path start in
            (subwin,(C (K closefn)))
        end end end
end;

(* Open a subwindow on the selected term.                                   *)
fun OPEN_WIN path stack =
    let val win = top_window stack in
        open_window (FOCUS_PATH path) (open_win_basis path win) stack
    end;

(* Open a window on a selected lemma or hypothesis.                         *)
fun OPEN_CONTEXT (tm, path) stack = 
    let val win = top_window stack in
        if (term_mem tm (context win)) then
            let val subwin1 =
                    make_win imp_tm tm (suppositions win) [] (hyp_thms win)
                        (lemma_thms win) in
            let fun closefn1 w =
                        (add_theorem (UNDISCH (win_thm w))) o
                            (transfer_sups_thms w) in
            let val (subwin2, closefn2) = open_win_basis path subwin1 in
            let fun closefn w = closefn1 (closefn2 w subwin1) in
                open_window (CONTEXT_PATH (tm,path)) (subwin2, closefn) stack
            end end end end
        else
            WIN_ERR{function="OPEN_CONTEX",message="no such term in context"}
    end;

(* Postulate a lemma, or prove a conjecture.                                *)
fun ESTABLISH tm stack = 
    let val win = top_window stack in
    let val (bad_sups,good_sups) =
                partition (fn (_,c) => (c = tm)) (suppositions win) in
    let val subwin =
        make_win pmi_tm tm good_sups [] (hyp_thms win) (lemma_thms win) in
    let fun closefn w =
            if (focus w) = true_tm then
                (itlist add_suppose bad_sups) o
                    (add_theorem (MP (PMI_IMP (win_thm w)) TRUTH)) o
                    (transfer_sups_thms w)
            else
                WIN_ERR{function="ESTABLISH",message="not yet proved"}
    in
        open_window (CONTEXT_PATH (tm,[])) (subwin, closefn) stack
    end end end end;

val CLOSE_WIN = close_window;
val UNDO_WIN = pop_window;

end;
open Win;
