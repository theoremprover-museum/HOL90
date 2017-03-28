(***************************** multiple_rec_spec.sig ********************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   20.7.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*  see multiple_rec_spec.DOC                                           *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

signature MULTIPLE_REC_SPEC =
sig

val new_multiple_recursive_specification : 
 {name : string, rec_axiom : thm, def : term} -> thm

end;
