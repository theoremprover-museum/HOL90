(* File: MLpackFtns.sml *)

fun mk_PACK e = mk_comb {Rator = --`PACK`--, Rand = e}
fun mk_VALvp v = mk_comb {Rator = --`VALvp`--, Rand = v}
fun mk_PACKvp p = mk_comb {Rator = --`PACKvp`--, Rand = p}
fun mk_RECORDrp r = mk_comb {Rator = --`RECORDrp`--, Rand = r}
fun mk_PACKrp p = mk_comb {Rator = --`PACKrp`--, Rand = p}
fun mk_VALvpf v = mk_comb {Rator = --`VALvpf`--, Rand = v}
fun mk_PACKvpf p = mk_comb {Rator = --`PACKvpf`--, Rand = p}
fun mk_ENVep e = mk_comb {Rator = --`ENVep`--, Rand = e}
fun mk_PACKep p = mk_comb {Rator = --`PACKep`--, Rand = p}
fun mk_VARENVvep v = mk_comb {Rator = --`VARENVvep`--, Rand = v}
fun mk_PACKvep p = mk_comb {Rator = --`PACKvep`--, Rand = p}
fun mk_EXCONENVeep e = mk_comb {Rator = --`EXCONENVeep`--, Rand = e}
fun mk_PACKeep p = mk_comb {Rator = --`PACKeep`--, Rand = p}
fun mk_VARENVvef v = mk_comb {Rator = --`VARENVvef`--, Rand = v};

val pack_ty = (==`:pack`==)
val val_pack_ty = (==`:val_pack`==)
val record_pack_ty = (==`:record_pack`==)
val val_pack_fail_ty = (==`:val_pack_fail`==)
val env_pack_ty = (==`:env_pack`==)
val varenv_pack_ty = (==`:varenv_pack`==)
val exconenv_pack_ty = (==`:exconenv_pack`==)
val varenv_fail_ty = (==`:varenv_fail`==)
