signature Term_coeffs_sig =
sig
 
   val negate_coeffs : (int * ('a * int) list) -> (int * ('a * int) list)
   val merge_coeffs : (int * (string * int) list) ->
                      (int * (string * int) list) ->
                      (int * (string * int) list)
   val lhs_coeffs : (int * ('a * int) list) -> (int * ('a * int) list)
   val rhs_coeffs : (int * ('a * int) list) -> (int * ('a * int) list)
   val diff_of_coeffs :
          ((int * (string * int) list) * (int * (string * int) list)) ->
          ((int * (string * int) list) * (int * (string * int) list))
   val vars_of_coeffs : ('a * (''b * 'c) list) list -> ''b list
   val var_of_prod : CoreHol.Term.term -> string
   val coeffs_of_arith : CoreHol.Term.term -> (int * (string * int) list)
   val coeffs_of_leq : CoreHol.Term.term -> (int * (string * int) list)
   val coeffs_of_leq_set : CoreHol.Term.term -> (int * (string * int)list) list
   val build_arith : int * (string * int) list -> CoreHol.Term.term
   val build_leq : (int * (string * int) list) -> CoreHol.Term.term 
end
