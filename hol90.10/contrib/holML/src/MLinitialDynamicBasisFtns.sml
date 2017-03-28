(* File: MLinitialDynamicBasisFtns.sml *)

(* declare exception names for the exceptions that may be raised by
   APPLYing basvalues (basvalues are Size, Chr, Abs, Div, etc) and
   by such things as failed matches. *)

val Abs_en = --`EXNAME 0`--
val Div_en = --`EXNAME 1`--
val Mod_en = --`EXNAME 2`--
val Prod_en = --`EXNAME 3`--
val Neg_en = --`EXNAME 4`--
val Sum_en = --`EXNAME 5`--
val Diff_en = --`EXNAME 6`--
val Match_en = --`EXNAME 7`--
val Bind_en = --`EXNAME 8`--

fun mk_pack exname = mk_comb{Rator = (--`PACK`--),
			     Rand = mk_comb{Rator = (--`NAMEexval`--),
					    Rand = exname}}

val Abs_pack = mk_pack Abs_en
val Div_pack = mk_pack Div_en
val Mod_pack = mk_pack Mod_en
val Prod_pack = mk_pack Prod_en
val Neg_pack = mk_pack Neg_en
val Sum_pack = mk_pack Sum_en
val Diff_pack = mk_pack Diff_en
val Match_pack = mk_pack Match_en
val Bind_pack = mk_pack Bind_en
