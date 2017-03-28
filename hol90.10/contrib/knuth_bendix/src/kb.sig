signature KB_sig =
  sig
    val kb : (term -> term -> bool) -> thm list -> thm list
    val kb_trace : (term -> term -> bool) -> thm list -> thm list
  end
