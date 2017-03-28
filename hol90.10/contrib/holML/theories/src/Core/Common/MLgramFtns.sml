
(* Create functions that allow us to make terms correspoonding to parts
   of ML syntax. Don't give functions for constructors with no arguments *)

fun mk_EXBIND1 ec eo = list_mk_comb (--`EXBIND1`--, [ec, eo])
fun mk_EXBIND2 ec el eo = list_mk_comb (--`EXBIND2`--, [ec, el, eo])

fun mk_SCONatpat sc = mk_comb {Rator = --`SCONatpat`--, Rand = sc}
fun mk_VARatpat v = mk_comb {Rator = --`VARatpat`--, Rand = v}
fun mk_CONatpat c = mk_comb {Rator = --`CONatpat`--, Rand = c}
fun mk_EXCONatpat e = mk_comb {Rator = --`EXCONatpat`--, Rand = e}
fun mk_RECORDatpat p = mk_comb {Rator = --`RECORD`--, Rand = p}
fun mk_PARatpat p = mk_comb {Rator = --`PARatpat`--, Rand = p}
fun mk_PATROW l p pr = list_mk_comb (--`PATROW`--, [l, p, pr])
fun mk_ATPATpat a = mk_comb {Rator = --`ATPATpat`--, Rand = a}
fun mk_CONpat c a = list_mk_comb (--`CONpat`--, [c, a])
fun mk_EXCONpat e a = list_mk_comb (--`EXCONpat`--, [e, a])
fun mk_LAYEREDpat v p = list_mk_comb (--`LAYEREDpat`--, [v, p])

fun mk_SCONatexp sc = mk_comb {Rator = --`SCONatexp`--, Rand = sc}
fun mk_VARatexp v = mk_comb {Rator = --`VARatexp`--, Rand = v}
fun mk_CONatexp c = mk_comb {Rator = --`CONatexp`--, Rand = c}
fun mk_EXCONatexp ec = mk_comb {Rator = --`EXCONatexp`--, Rand = ec}
fun mk_LETatexp d e = list_mk_comb (--`LETatexp`--, [d, e])
fun mk_PARatexp e = mk_comb {Rator = --`PARatexp`--, Rand = e}
fun mk_RECORDatexp e = mk_comb {Rator = --`RECORDatexp`--, Rand = e}
fun mk_EXPROW l e er = list_mk_comb (--`EXPROW`--, [l, e, er])
fun mk_ATEXPexp a = mk_comb {Rator = --`ATEXPexp`--, Rand = a}
fun mk_APPexp e a = list_mk_comb (--`APPexp`--, [e, a])
fun mk_HANDLEexp e m = list_mk_comb (--`HANDLEexp`--, [e, m])
fun mk_RAISEexp e = mk_comb {Rator = --`RAISEexp`--, Rand = e}
fun mk_FNexp m = mk_comb {Rator = --`FNexp`--, Rand = m}
fun mk_MATCH mr m = list_mk_comb (--`MATCH`--, [mr, m])
fun mk_MRULE p e = list_mk_comb (--`MRULE`--, [p, e])
fun mk_VALdec v = mk_comb {Rator = --`VALdec`--, Rand = v}
fun mk_EXCEPTdec e = mk_comb {Rator = --`EXCEPTdec`--, Rand = e}
fun mk_LOCALdec d1 d2 = list_mk_comb (--`LOCALdec`--, [d1, d2])
fun mk_OPENdec l = mk_comb {Rator = --`OPENdec`--, Rand = l}
fun mk_SEQdec d1 d2 = (--`SEQdec`--, d1, d2)
fun mk_PLAINvalbind p e v = list_mk_comb (--`PLAINvalbind`--, [p, e, v])
fun mk_RECvalbind v = mk_comb {Rator = --`RECvalbind`--, Rand = v}

val num_ty = ==`:num`==
val strid_ty = (==`:strid`==)
val var_ty = ==`:var`==
val con_ty = ==`:con`==
val scon_ty = ==`:scon`==
val excon_ty = ==`:excon`==
val label_ty = ==`:label`==
val exbind_ty = (==`:exbind`==)
val atpat_ty = (==`:atpat`==)
val patrow_ty = (==`:patrow`==)
val pat_ty = ==`:pat`==
val atexp_ty = (==`:atexp`==)
val exprow_ty = (==`:exprow`==)
val exp_ty = (==`:exp`==)
val match_ty = ==`:match`==
val mrule_ty = (==`:mrule`==)
val dec_ty = ==`:dec`==;
val valbind_ty = (==`:valbind`==)

fun mk_long_ty ty = mk_type {Tyop = "long", Args = [ty]};
