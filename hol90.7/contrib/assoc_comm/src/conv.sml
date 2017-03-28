(* structure AC_Conv : *)

open Rsyntax;

fun AC_CONV_ERR{func,mesg} = 
        HOL_ERR{origin_structure = "AC_CONV",
                origin_function = func,
                message = mesg};

fun front_rev_itlist f =
   let fun rit [] = raise AC_CONV_ERR{func = "AC_MK_COMB",  mesg = "0 args"}
         | rit [_] = raise AC_CONV_ERR{func = "AC_MK_COMB", mesg = "1 arg"}
         | rit (a::rst) = rev_itlist f rst a
   in rit
   end;


fun AC_MK_COMB ac_op =
   let val ac_op_refl = REFL ac_op
   in
   front_rev_itlist (fn th => fn core => MK_COMB(MK_COMB(ac_op_refl, core),th))
   end;

fun is_ac_comb ac_consts tm = 
   mem (rator(rator tm)) ac_consts handle _ => false;

fun strip_ac_comb tm =
   let val {Rator,Rand = r} = dest_comb tm
       val {Rator,Rand = l} = dest_comb Rator
       val lflat = if (is_ac_comb [Rator] l)
                   then snd(strip_ac_comb l)
                   else [l]
       val rflat = if (is_ac_comb [Rator] r)
                   then snd(strip_ac_comb r)
                   else [r]
   in (Rator, lflat@rflat)
   end;

fun AC_SUB_CONV ac_consts conv tm =
   if (is_ac_comb ac_consts tm)
   then let val (ac_op,L) = strip_ac_comb tm
        in AC_MK_COMB ac_op (map (fn tm => conv tm handle _ => REFL tm) L)
        end
   else if (is_comb tm)
        then let val {Rator,Rand} = dest_comb tm
             in MK_COMB(conv Rator, conv Rand)
             end
        else if (is_abs tm)
             then let val {Bvar,Body} = dest_abs tm
                  in ABS Bvar (conv Body)
                  end
             else ALL_CONV tm;

fun DEPTH_CONV ac_consts conv t =
   (AC_SUB_CONV ac_consts (DEPTH_CONV ac_consts conv) THENC (REPEATC conv))
    t;

fun REDEPTH_CONV ac_consts conv t =
   (AC_SUB_CONV ac_consts (REDEPTH_CONV ac_consts conv) THENC
    ((conv THENC (REDEPTH_CONV ac_consts conv)) ORELSEC ALL_CONV))
   t;

fun TOP_DEPTH_CONV ac_consts conv t =
    (REPEATC conv  THENC
     (TRY_CONV
         (CHANGED_CONV (AC_SUB_CONV ac_consts (TOP_DEPTH_CONV ac_consts conv))
          THENC TRY_CONV(conv THENC TOP_DEPTH_CONV ac_consts conv))))
    t;

fun ONCE_DEPTH_CONV ac_consts conv tm =
   (conv ORELSEC (AC_SUB_CONV ac_consts (ONCE_DEPTH_CONV ac_consts conv))) tm;
