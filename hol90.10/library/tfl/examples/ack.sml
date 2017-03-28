(*---------------------------------------------------------------------------
 * Ackermann's function.
 *---------------------------------------------------------------------------*)

new_theory"ackermann";

val ack_def = Rfunction `^pred X ^pred` 
  `(ack (0,n) =  n+1) /\
   (ack (SUC m,0) = ack (m, 1)) /\
   (ack (SUC m, SUC n) = ack (m, ack (SUC m, n)))`;

val ack_eqns = save_thm("ack_eqns", #rules ack_def);
val ack_induction = save_thm("ack_induction", #induction ack_def);


val ack_positive = Q.store_thm("ack_pos",  `!x y. 0 < ack(x,y)`,
REC_INDUCT_TAC ack_induction THEN ONCE_RW_TAC[ack_eqns] 
 THEN RW_TAC[] THEN CONV_TAC ARITH_CONV);


val ack_grows_faster_than_plus = Q.store_thm("ack_grows_faster_than_plus",  
`!x y. x+y < ack(x,y)`,
REC_INDUCT_TAC ack_induction 
 THEN ONCE_RW_TAC[ack_eqns] THEN RW_TAC[] 
 THEN CONV_TAC ARITH_CONV);


html_theory"-";
