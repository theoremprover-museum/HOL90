signature Sys_lib_sig =
sig
(*
  val prim_hol_lib : lib
  val basic_hol_lib : lib
*)
  val hol_lib : lib

  type lib


  val lite_lib : lib
  val ho_match_lib : lib
  val refute_lib : lib
  val fol_lib : lib
  val tab_lib : lib
  val meson_lib : lib
  val decision_lib : lib
  val reduce_lib : lib
  val arith_lib : lib
  val simp_lib : lib
(*   val automate_lib : lib *)
  val ind_def_new_lib : lib
  val tfl_lib : lib
  val string_lib : lib
  val option_lib : lib
  val num_lib : lib
  val set_lib : lib
  val pred_set_lib : lib
  val unwind_lib : lib
  val hol88_lib : lib
  val ind_def_lib : lib
  val taut_lib : lib
  val utils_lib : lib
  val retrieve_lib : lib
  val group_lib : lib
  val integer_lib : lib
  val abs_theory_lib : lib
  val unity_lib : lib
  val prog_logic_lib : lib
  val pair_lib : lib
  val real_lib : lib
  val wellorder_lib : lib
  val window_lib : lib
  val list_lib : lib
  val res_quan_lib : lib
  val word_lib : lib
  val mutrec_lib : lib
  val nested_rec_lib : lib
end;
