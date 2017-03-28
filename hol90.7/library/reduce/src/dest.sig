signature Dest_sig =
sig
    val dest_op : term -> term -> term list
    val term_of_int : int-> term
    val int_of_term : term -> int
end
