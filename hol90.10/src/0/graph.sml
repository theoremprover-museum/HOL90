(*---------------------------------------------------------------------------
 * Simple implementation of directed graphs. More efficient ones are 
 * certainly possible, but speed hasn't so far been a problem in the 
 * application (representing the HOL theory graph).  Acyclicity is not 
 * enforced here.
 *---------------------------------------------------------------------------*)
signature Node_sig =
    sig
	type node
	val node_name : node -> string
	val node_eq : node -> node -> bool
    end;

	
functor DAG(structure Node : Node_sig) =
struct

open Lib;
type node = Node.node;
type graph_node = { node : node,  parents : node list }
type graph = graph_node list;

fun THEORY_GRAPH_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Theory_graph",
		      origin_function = function,
		      message = message}

val node_eq = node_eq;

val the_graph = ref([]:graph)

fun add_node n ps = the_graph := {node = n, parents = ps}::(!the_graph);

fun graph_assoc n =
   let fun assc ({node,parents}::rst) = 
                if (Node.node_eq n node) then parents else assc rst
         | assc [] = raise NOT_FOUND
   in  assc   end;

fun str_graph_assoc str =
   let fun assc ({node,parents}::rst) = 
                if (str = Node.node_name node) then parents else assc rst
         | assc [] = raise NOT_FOUND
   in assc
   end;

fun parents str = str_graph_assoc str (!the_graph);

fun node_in_graph n = (graph_assoc n (!the_graph); true)
                      handle NOT_FOUND => false;
fun is_ancestor s = can (str_graph_assoc s) (!the_graph);

(* Generally useful. *)
fun insert p f alist =
   let fun ins (a::rst) L =
              if (p a)
              then (rev L)@((f a)::rst)
              else ins rst (a::L)
         | ins [] L = raise NOT_FOUND
   in
   ins alist []
   end;

(* Duplicate parents are union'ed*)
fun add_parent n new_parent = the_graph := 
   insert (fn {node, ...} => Node.node_eq node n) 
          (fn {node,parents} => 
              { node = node, 
                parents = op_union Node.node_eq [new_parent] parents })
          (!the_graph);

fun graph_copy() = !the_graph;
fun replace_graph g = the_graph := g;

fun ancestry str = 
   let val P = str_graph_assoc str (!the_graph)
       fun ances to_see seen = rev_itlist (fn thid => fn A =>
          if (op_mem Node.node_eq thid A)
          then A
          else let val parents = graph_assoc thid (!the_graph)
                                 handle NOT_FOUND => []
               in ances parents (thid::A)
               end)      to_see seen
   in ances P []
   end
   handle NOT_FOUND 
   => raise THEORY_GRAPH_ERR{function = "ancestry",
                    message = quote str^" is not in the theory graph."};


(*---------------------------------------------------------------------------
 * All nodes in the graph that aren't parents.
 *---------------------------------------------------------------------------*)
fun fringe () =
  let val all_parents = map #parents (!the_graph)
      fun is_parent y = exists (Lib.op_mem Node.node_eq y) all_parents
  in 
     filter (not o is_parent) (map #node (!the_graph))
  end;

end; (* DAG *)
