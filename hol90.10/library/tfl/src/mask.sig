signature Mask_sig =
sig
  datatype 'a binding = |-> of ('a * 'a)  (* infix 7 |->; *)
end
