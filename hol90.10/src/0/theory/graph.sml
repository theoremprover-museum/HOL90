(***************************************************************************
 * Simple implementation of directed graphs. More efficient ones are 
 * certainly possible, but speed hasn't so far been a problem in the 
 * application (representing the HOL theory graph).  Acyclicity is not 
 * enforced here.
 *************************************************************************)
signature Node_sig =
    sig
	type node_id
	val node_name : node_id -> string
	val node_eq : node_id -> node_id -> bool
    end;
	
functor DAG((* structure Lib : Lib_sig *)
	    structure Node : Node_sig) =
struct
open Lib;
type node_id = Node.node_id;
type graph_node = { node : node_id,  parents : node_id list }
type graph = graph_node list;

fun THEORY_GRAPH_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Theory_graph",
		      origin_function = function,
		      message = message}


val the_graph = ref([]:graph)

fun add_node n ps = the_graph := {node = n, parents = ps}::(!the_graph);

fun graph_assoc node_id =
   let fun assc ({node,parents}::rst) = 
                if (Node.node_eq node_id node)
                then parents
                else assc rst
         | assc [] = raise NOT_FOUND
   in
   assc
   end;

fun str_graph_assoc str =
   let fun assc ({node,parents}::rst) = 
                if (str = Node.node_name node)
                then parents
                else assc rst
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
fun add_parent node_id new_parent = the_graph := 
   insert (fn {node, ...} => Node.node_eq node node_id) 
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

end; (* DAG *)
