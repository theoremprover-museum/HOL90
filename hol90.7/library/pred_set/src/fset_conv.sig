signature Fset_conv_sig =
sig
val FINITE_CONV : conv
val IN_CONV :conv -> conv
val DELETE_CONV :conv -> conv
val UNION_CONV :conv -> conv
val INSERT_CONV :conv -> conv
val IMAGE_CONV :conv -> conv ->conv
end;
