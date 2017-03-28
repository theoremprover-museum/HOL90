(* ===================================================================== *)
(* FILE          : num_lib.sig  (Formerly num.sml)                       *)
(* DESCRIPTION   : Signature for useful proof support for :num.          *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* ===================================================================== *)


signature Num_lib_sig = 
sig
val ADD_CONV : conv
val num_EQ_CONV : conv
val EXISTS_LEAST_CONV : conv
val EXISTS_GREATEST_CONV : conv
end;
