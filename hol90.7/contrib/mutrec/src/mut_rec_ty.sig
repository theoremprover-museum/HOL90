(* =====================================================================*)
(* FILE          : mut_rec_ty.sig                                       *)
(* DESCRIPTION   : signature of theorems returned by MutRecDefFunc      *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter and Myra VanInwegen, based on comments   *)
(*                 by Tom Melham                                        *)
(* DATE          : 92.08.08                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature MutRecDefSig =
    sig
	structure TypeInfo : TypeInfoSig
	val New_Ty_Induct_Thm :thm
        val New_Ty_Uniqueness_Thm :thm
	val New_Ty_Existence_Thm :thm
    end
