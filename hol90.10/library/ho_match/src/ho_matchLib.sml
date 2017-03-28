signature ho_matchLib_sig =
sig
 structure Ho_net : Ho_net_sig
 structure Ho_match : Ho_match_sig
 structure Rewrite : Rewrite_sig
 structure Resolve : Resolve_sig
 structure Theorems : Theorems_sig
end;

structure ho_matchLib =
struct
 structure Ho_net = Ho_net
 structure Ho_match = Ho_match
 structure Ho_rewrite = Ho_rewrite
 structure Ho_resolve = Ho_resolve
 structure Theorems = Theorems
end;
