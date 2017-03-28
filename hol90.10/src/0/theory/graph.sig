signature Theory_graph_sig =
sig
type node_id
type graph
val add_node : node_id -> node_id list -> unit
val node_in_graph : node_id -> bool
val is_ancestor : string -> bool
val add_parent : node_id -> node_id  -> unit
val graph_copy : unit -> graph
val replace_graph : graph -> unit
val parents : string -> node_id list
val ancestry : string -> node_id list
end;
