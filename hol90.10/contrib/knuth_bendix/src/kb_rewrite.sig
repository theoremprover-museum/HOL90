signature KB_rewrite_sig =
  sig
    val PSUB_ALL : thm list -> thm -> thm
    val RW_LHS_FULLY : thm list -> thm -> thm
    val RW_RHS_FULLY : thm list -> thm -> thm
  end
