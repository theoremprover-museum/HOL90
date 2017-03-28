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
   val var_of_prod : term -> string
   val coeffs_of_arith : term -> (int * (string * int) list)
   val coeffs_of_leq : term -> (int * (string * int) list)
   val coeffs_of_leq_set : term -> (int * (string * int) list) list
   val build_arith : int * (string * int) list -> term
   val build_leq : (int * (string * int) list) -> term 
end
