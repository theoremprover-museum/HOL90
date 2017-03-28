signature RETRIEVE_SETS =
sig
   val no_rep : ''a list -> bool
   val remove_rep : ''a list -> ''a list
   val is_subset : ''a list -> ''a list -> bool
end;
