(* File: MLexconenvFtns.sml *)

fun insert_into_exconenv {excon, exname, exconenv} =
    mk_comb{Rator =
	      mk_comb{Rator = mk_comb{Rator = (--`insert_into_exconenv`--),
				      Rand = exconenv},
		      Rand = excon},
	    Rand = exname}

fun add_to_exconenv ((ec, en)::more_pairs) ee =
    insert_into_exconenv {excon = ec ,
			exname = en,
			exconenv = add_to_exconenv more_pairs ee}
  | add_to_exconenv [] ee = ee;

val exconenv_ty = (==`:exconenv`==);
