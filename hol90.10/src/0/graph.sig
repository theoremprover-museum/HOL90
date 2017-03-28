signature Theory_graph_sig =
sig
type node
type graph

  val node_eq : node -> node -> bool
  val add_node : node -> node list -> unit
  val node_in_graph : node -> bool
  val is_ancestor : string -> bool
  val add_parent : node -> node  -> unit
  val graph_copy : unit -> graph
  val replace_graph : graph -> unit
  val parents : string -> node list
  val ancestry : string -> node list
  val fringe : unit -> node list

end;
