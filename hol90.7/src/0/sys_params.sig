(* ===================================================================== *)
(* FILE          : sys_params.sig                                        *)
(* DESCRIPTION   : Signature for the system parameters that need to be   *)
(*                 at building time.                                     *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 29 September, 1992                                    *)
(* ===================================================================== *)

(* Copyright 1992 by AT&T Bell Laboratories *)

signature Sys_params_sig =
sig
    datatype thy_opt = make_binary | make_new_ascii | use_old_ascii
    val theory_file_option : thy_opt
    val HOL_base_directory : string
end
