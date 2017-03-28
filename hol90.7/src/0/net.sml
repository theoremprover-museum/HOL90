(* ===================================================================== *)
(* FILE          : net.sml                                               *)
(* DESCRIPTION   : Implementation of term nets, from the group at ICL.   *)
(*                 Thanks! A term net is a database, keyed by terms.     *)
(*                 Term nets were initially implemented by Larry Paulson *)
(*                 for Cambridge LCF.                                    *)
(*                                                                       *)
(* AUTHOR        : Somebody in the ICL group.                            *)
(* DATE          : August 26, 1991                                       *)
(* MODIFIED      : Sept 5, 1992, to use deBruijn representation          *)
(* ===================================================================== *)


functor NET (Term : Term_sig) : Net_sig =
struct
structure Term = Term;

fun NET_ERR{function,message} = HOL_ERR{origin_structure = "Net",
					origin_function = function,
					message = message}

datatype term_label = V | Cnst of string | Cmb | Lam;

fun label_of tm =
   if (Term.is_comb tm)
   then Cmb
   else if (Term.is_abs tm)
        then Lam
        else if (Term.is_const tm)
             then Cnst (#Name(Term.dest_const tm))
             else if ((Term.is_var tm) orelse (Term.is_bvar tm))
                  then V
                  else raise NET_ERR{function = "label_of",
				     message = "not translatable"};

datatype 'a net = NODE of (term_label * 'a net) list | TIP of ('a list)

val empty_net = NODE [];

fun get_edge label =
   let fun get (NODE edges) = 
              (case (assoc1 label edges)
                 of (SOME (_,net)) => net
                  | NONE => empty_net)
         | get (TIP _) = raise NET_ERR{function = "get_edge",
                                       message = "tips have no edges"}
   in get
   end;

fun get_tip_list (TIP L) = L
  | get_tip_list (NODE _) = [];

fun is_empty_node (NODE []) = true
  | is_empty_node _ = false;

fun follow tm net =
   let val var_net = get_edge V net
       val label = label_of tm
       val othernets = 
          case label
            of V => [] 
             | (Cnst _) => [get_edge label net] 
             | Lam => follow (#Body(Term.break_abs tm)) (get_edge label net)
             | Cmb => let val {Rator,Rand} = Term.dest_comb tm
                      in itlist(fn i => fn A => (follow Rator i @ A))
                               (follow Rand (get_edge label net))
                               []
                      end
   in gather (not o is_empty_node) (var_net::othernets)
   end;

fun overwrite (a,b) = 
  let fun over [] = [(a,b)]
        | over ((x,y)::rst) = 
              if (a=x)
              then (a,b)::rst
              else (x,y)::(over rst)
  in over 
  end;


fun net_update elem =
   let 
   fun update deferred tm (net as (NODE edges)) =
        let fun exec_deferred [] net = TIP (elem::get_tip_list net)
              | exec_deferred (h::rst) net = update rst h net
            val label = label_of tm
            val child = get_edge label net
            val new_child = 
              case label
                of V => exec_deferred deferred child 
                 | (Cnst _) => exec_deferred deferred child 
                 | Cmb => let val {Rator, Rand} = Term.dest_comb tm
                          in update (Rator::deferred) Rand child
                          end
                 | Lam => update deferred (#Body(Term.break_abs tm)) child
        in NODE (overwrite (label,new_child) edges)
        end
     | update _ _ (TIP _) = raise NET_ERR{function = "net_update",
                                          message = "can not update a tip"}
   in update
   end

fun enter (tm,elem) net = net_update elem [] tm net;

fun lookup tm net = itlist (fn (TIP L) => (fn A => (L@A))
                             | (NODE _) => I)
                           (follow tm net)
                           [];

end; (* NET *)

