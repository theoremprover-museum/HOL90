(* ========================================================================= *)
(* Version of the MESON procedure a la PTTP. Various search options.         *)
(* ========================================================================= *)


signature mesonLib_sig =
sig
 type thm
 type tactic

   val depth    : bool ref
   val prefine  : bool ref
   val precheck : bool ref
   val dcutin   : int ref
   val skew     : int ref
   val cache    : bool ref

   val GEN_MESON_TAC : int -> int -> int -> thm list -> tactic
   val MESON_TAC     : thm list -> tactic (* = ASM_EQ_MESON_TAC *)
   val ASM_MESON_TAC : thm list -> tactic

end (* sig *)
