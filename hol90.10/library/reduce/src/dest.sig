signature Dest_sig =
sig

 val dest_op : CoreHol.Term.term -> CoreHol.Term.term -> CoreHol.Term.term list
 val term_of_int : int -> CoreHol.Term.term
 val int_of_term : CoreHol.Term.term -> int
end
