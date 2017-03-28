signature KB_order_sig =
  sig
    val lrpo : (term -> term -> bool) -> term -> term -> bool
    val rpo : (term -> term -> bool) -> term -> term -> bool
    val rpos : (term -> bool) -> (term -> term -> bool) -> term -> term -> bool
  end

