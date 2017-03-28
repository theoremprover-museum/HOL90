
(* Create functions that allow us to make terms correspoonding to parts
   of environments. Don't give functions for constructors with no arguments *)

(* syntax functions for MLsval.sml *)

fun mk_SVINT i = mk_comb {Rator = --`SVINT`--, Rand = i}
fun mk_SVSTR s = mk_comb {Rator = --`SVSTR`--, Rand = s}
fun mk_ADDR n = mk_comb {Rator = --`ADDR`--, Rand = n}
fun mk_EXNAME n = mk_comb {Rator = --`EXNAME`--, Rand = n}
fun mk_EXNAMESET s = mk_comb {Rator = --`EXNAMESET`--, Rand = s}

(* syntax functions for MLexconenv.sml *)
fun mk_EXCONENV f= mk_comb {Rator = --`EXCONENV`--, Rand = f}

(* syntax functions for MLenvInput.sml *)
fun mk_SVALval sv = mk_comb {Rator = --`SVALval`--, Rand = sv}
fun mk_BASval b = mk_comb {Rator = --`BASval`--, Rand = b}
fun mk_CONval b = mk_comb {Rator = --`CONval`--, Rand = b}
fun mk_APPCONval c v = list_mk_comb (--`APPCONval`--, [c, v])
fun mk_EXVALval e = mk_comb {Rator = --`EXVALval`--, Rand = e}
fun mk_RECORDval r = mk_comb {Rator = --`RECORDval`--, Rand = r}
fun mk_ADDRval a = mk_comb {Rator = --`ADDRval`--, Rand = a}
fun mk_CLOSUREval c = mk_comb {Rator = --`CLOSUREval`--, Rand = c}
fun mk_RECORD f = mk_comb {Rator = --`RECORD`--, Rand = f}
fun mk_NAMEexval e = mk_comb {Rator = --`NAMEexval`--, Rand = e}
fun mk_NAMEVALexval e v = list_mk_comb (--`NAMEVALexval`--, [e, v])
fun mk_CLOSURE m e v = list_mk_comb (--`CLOSURE`--, [m, e, v])
fun mk_STATE m e = list_mk_comb (--`STATE`--, [m, e])
fun mk_ENV s v e = list_mk_comb (--`ENV`--, [s, v, e])
fun mk_STRENV f = mk_comb {Rator = --`STRENV`--, Rand = f}
fun mk_VARENV f = mk_comb {Rator = --`VARENV`--, Rand = f}

val val_ty = (==`:val`==)
val record_ty = (==`:record`==)
val exval_ty = (==`:exval`==)
val closure_ty = (==`:closure`==)
val env_ty = ==`:env`==;
val strenv_ty = (==`:strenv`==)
val varenv_ty = (==`:varenv`==)
