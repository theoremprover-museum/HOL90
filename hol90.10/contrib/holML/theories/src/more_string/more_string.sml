(* File: more_string.sml *)

val _ = load_library_in_place string_lib;

val _ = add_theory_to_sml "more_string";

fun ltstring_CONV s =
    (REWRITE_CONV [ltstring_DEF,empty_str_DEF,first_char_DEF,rest_string_DEF,
		   ltascii_lemma,theorem "ascii" "ASCII_11"]
     THENC
     (DEPTH_CONV string_CONV)) s

