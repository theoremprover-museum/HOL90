(* ===================================================================== *)
(* FILE          : zip_lib.sml                                           *)
(* DESCRIPTION   : Proof support for :zip, also pair quantifier stuff    *)
(*                                                                       *)
(* AUTHORS       : Paul Loewenstein, Sun Microsystems                    *)
(* DATE          : 93.02.04                                              *)
(* ===================================================================== *)

structure Zip_lib : Zip_lib_sig =
struct

open Rsyntax;

(* Pair destructuring conversions *)

local
val BINDER_CONV = RAND_CONV o ABS_CONV;
val PAIR_FORALL = theorem "zip" "PAIR_FORALL";
val PAIR_EXISTS = theorem "zip" "PAIR_EXISTS";
val EXISTS_Zip = theorem "zip" "EXISTS_Zip";
val FORALL_Zip = theorem "zip" "FORALL_Zip"
in
fun PAIR_FORALL_CONV (var1,var2) tm =
 let
  val {Bvar = s, Body = t} = dest_forall tm;
  val {Tyop = p, Args = types} = dest_type (type_of s)
 in
   if p = "prod" then
    CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (SPEC (mk_abs {Bvar = s, Body = t}) (CONV_RULE
     ((BINDER_CONV o RAND_CONV) (GEN_ALPHA_CONV var1 THENC
      (BINDER_CONV (GEN_ALPHA_CONV var2))))
     (INST_TYPE [{residue = hd types, redex = ==`:'a`==},
        {residue = hd(tl types), redex = ==`:'b`==}] PAIR_FORALL)))
   else raise HOL_ERR {origin_structure = "Zip_lib",
      origin_function = "PAIR_FORALL_CONV",
      message = p}
 end;

fun PAIR_EXISTS_CONV (var1,var2) tm =
 let
  val {Bvar = s, Body = t} = dest_exists tm;
  val {Tyop = p, Args = types} = dest_type (type_of s)
 in
   if p = "prod" then
    CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (SPEC (mk_abs {Bvar = s, Body = t}) (CONV_RULE
     ((BINDER_CONV o RAND_CONV) (GEN_ALPHA_CONV var1 THENC
      (BINDER_CONV (GEN_ALPHA_CONV var2))))
     (INST_TYPE
        [{residue = hd types, redex = ==`:'a`==},
        {residue = hd(tl types), redex = ==`:'b`==}]
         PAIR_EXISTS)))
   else raise HOL_ERR  {origin_structure = "Zip_lib",
      origin_function = "PAIR_EXISTS_CONV",
      message = p}
 end;

fun EXISTS_ZIP_CONV (var1,var2) tm =
 let 
   val {Bvar = s, Body = t} = dest_exists tm;
   val {Tyop = f, Args = ftypes} = dest_type (type_of s);
   val {Tyop = p, Args = types} = dest_type (el 2 ftypes)
 in
     if p = "prod" andalso f = "fun" then
    CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (SPEC (mk_abs {Bvar = s, Body = t}) (CONV_RULE
     ((BINDER_CONV o RAND_CONV) (GEN_ALPHA_CONV var1 THENC
      (BINDER_CONV (GEN_ALPHA_CONV var2))))
     (INST_TYPE
       [{residue = hd ftypes, redex = ==`:'a`==},
        {residue = hd types, redex = ==`:'b`==},
        {residue = hd(tl types), redex = ==`:'c`==}]
    EXISTS_Zip)))
   else raise HOL_ERR {origin_structure = "Zip_lib",
      origin_function = "EXISTS_ZIP_CONV",
      message = p ^ " " ^ f}
 end;

fun FORALL_ZIP_CONV (var1,var2) tm =
 let 
   val {Bvar = s, Body = t} = dest_forall tm;
   val {Tyop = f, Args = ftypes} = dest_type (type_of s);
   val {Tyop = p, Args = types} = dest_type (el 2 ftypes)
 in
     if p = "prod" andalso f = "fun" then
    CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (SPEC (mk_abs {Bvar = s, Body = t}) (CONV_RULE
     ((BINDER_CONV o RAND_CONV) (GEN_ALPHA_CONV var1 THENC
      (BINDER_CONV (GEN_ALPHA_CONV var2))))
     (INST_TYPE
       [{residue = hd ftypes, redex = ==`:'a`==},
        {residue = hd types, redex = ==`:'b`==},
        {residue = hd(tl types), redex = ==`:'c`==}]
    FORALL_Zip)))
   else raise HOL_ERR
     {origin_structure = "Zip_lib",
      origin_function = "FORALL_ZIP_CONV",
      message = p ^ " " ^ f}
 end
end;

end; (* Zip_lib *)
