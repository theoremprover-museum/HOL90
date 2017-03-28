(* File: MLvalFtns.sml *)

fun insert_into_record {label, value, record} =
    mk_comb{Rator = mk_comb{Rator = mk_comb{Rator = (--`insert_into_record`--),
					    Rand = record},
			    Rand = label},
	    Rand = value};

(* the stuff at the beginning of the list will overwrite the stuff at 
   the end of the list *)
fun add_to_record ((label, value)::more_pairs) record =
    insert_into_record {label = label ,
			value = value,
			record = add_to_record more_pairs record}
  | add_to_record [] record = record;

fun insert_into_varenv {var, value, varenv} =
    mk_comb{Rator = mk_comb{Rator = mk_comb{Rator = (--`insert_into_varenv`--),
					    Rand = varenv},
			    Rand = var},
	    Rand = value}

fun add_to_varenv ((va, vl)::more_pairs) ve =
    insert_into_varenv {var = va ,
			value = vl,
			varenv = add_to_varenv more_pairs ve}
  | add_to_varenv [] ve = ve;


fun insert_into_strenv {strid, env, strenv} =
    mk_comb{Rator =
	      mk_comb{Rator = mk_comb{Rator = (--`insert_into_strenv`--),
				      Rand = strenv},
		      Rand = strid},
	    Rand = env}

fun add_to_strenv ((strid, env)::more_pairs) se =
    insert_into_strenv {strid = strid ,
			env = env,
			strenv = add_to_strenv more_pairs se}
  | add_to_strenv [] se = se;
