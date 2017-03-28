structure KB_order :KB_order_sig =
struct

open Psyntax;

(* Term orderings *)
fun is_subterm_of t1 t2 =
   if (is_comb t2)
   then exists (fn x => (x=t1) orelse (is_subterm_of t1 x))
               (snd (strip_comb t2))
   else false;


fun perm_cong t1 t2 =
  let val (c1,args1) = strip_comb t1
      and (c2,args2) = strip_comb t2
  in (c1=c2) andalso (exists (fn x => x = args2) (KBlib.permute args1))
  end
  handle _ => false;



(***********************************************************************
 * rpo is true when t1 > t2 under recursive path ordering of Dershowitz.
 * Variables cannot be included in the base ordering, which is a partial
 * ordering.
 ************************************************************************)
exception RPO_ERR;
fun rpo po t1 t2 = 
   if (is_var t1)
   then false
   else if (is_const t1)
        then if (is_const t2)
             then po t1 t2
             else if (is_var t2)
                  then false
                  else if (is_comb t2)
                       then let val (c2,args2) = strip_comb t2
                            in (po t1 c2) andalso (all (rpo po t1) args2)
                            end
                       else raise RPO_ERR
        else if (is_comb t1)
             then if (is_const t2)
                  then let val (c1,_) = strip_comb t1
                       in (po c1 t2) orelse (is_subterm_of t2 t1)
                       end
                  else if (is_var t2)
                     then is_subterm_of t2 t1
                    else 
                    if (is_comb t2)
                    then let val (c1,args1) = strip_comb t1
                             and (c2,args2) = strip_comb t2
                         in (exists (fn x => (rpo po x t2) orelse (x = t2) 
                                             orelse (perm_cong x t2)) args1)
                            orelse
                            (if (c1 = c2)
                             then KBlib.multiset_gt (rpo po) args1 args2
                             else if (po c1 c2) 
                                  then (all (rpo po t1) args2)
                                  else false)
                         end
                    else raise RPO_ERR
             else raise RPO_ERR;


(****************************************************************************
 * The lexicographic recursive path ordering lrpo is true when t1 > t2 
 * under lexicographic version of recursive path ordering. Defined in 
 * Dershowitz' paper on Termination in JSC. Base ordering is assumed to
 *  be a partial order.
 *****************************************************************************)
exception LRPO_ERR;
fun lrpo po t1 t2 = 
   if (is_var t1) then false
   else 
   if (is_const t1)
   then if (is_const t2) then po t1 t2
        else if (is_var t2) then false
             else if (is_comb t2)
                  then let val (c2,args2) = strip_comb t2
                       in (po t1 c2) andalso (all (lrpo po t1) args2)
                       end
                  else raise LRPO_ERR
   else 
   if (is_comb t1)
   then if (is_const t2)
        then let val (c1,_) = strip_comb t1
             in (po c1 t2) orelse (is_subterm_of t2 t1)
             end 
        else if (is_var t2) then is_subterm_of t2 t1
             else if (is_comb t2)
                  then let val (c1,args1) = strip_comb t1
                           and (c2,args2) = strip_comb t2
                     in (exists (fn x => (lrpo po x t2) orelse (x = t2)) args1)
                        orelse 
                        (if (c1 = c2)
                         then (KBlib.lex_gt (lrpo po) args1 args2
                               andalso
                               (all (fn x => lrpo po t1 x) (tl args2)))
                         else if (po c1 c2)
                              then (all (lrpo po t1) args2)
                              else false)
                     end
                  else raise LRPO_ERR
   else raise LRPO_ERR;


(****************************************************************************
 * The recursive path ordering with status
 *****************************************************************************)
exception RPOS_ERR;
fun rpos status po t1 t2 =
   if (is_var t1) then false
   else 
   if (is_const t1)
   then if (is_var t2) then false
        else if (is_const t2) then po t1 t2 
             else if (is_comb t2)
                  then let val (c2,args2) = strip_comb t2
                       in (po t1 c2) andalso (all (rpos status po t1) args2)
                       end
                  else raise RPOS_ERR
   else 
   if (is_comb t1)
   then if (is_var t2) then is_subterm_of t2 t1
        else if (is_const t2)
             then let val (c1,_) = strip_comb t1
                  in (po c1 t2) orelse (is_subterm_of t2 t1)
                  end
             else
             if (is_comb t2)
             then let val (c1,args1) = strip_comb t1
                      and (c2,args2) = strip_comb t2
                  in (exists (fn x => (rpos status po x t2) orelse (x = t2) 
                                      orelse (if (status c1)
                                              then false 
                                              else perm_cong x t2))
                             args1)
                     orelse
                     (if (c1 = c2) 
                      then if (status c1)
                           then (KBlib.lex_gt (rpos status po) args1 args2
                                 andalso
                                 (all (fn x => rpos status po t1 x)(tl args2)))
                           else KBlib.multiset_gt(rpos status po) args1 args2
                      else (po c1 c2 andalso all (rpos status po t1) args2))
                  end
             else raise RPOS_ERR
   else raise RPOS_ERR;

end; (* KB_order *)
