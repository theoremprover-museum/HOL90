(*===========================================================================*)
(*                                                                           *)
(*   FILE:         ineq_conv.sml                                             *)
(*   AUTHORS:      Wim Ploegaerts                                            *)
(*   DATE:         14-6-1990                                                 *)
(*   EDITOR:       Paul Curzon  July 1991                                    *)
(*   DESCRIPTION:  Some conversions for rewriting equalities and             *)
(*                 inequalities of naturals                                  *)
(*   TRANSLATOR:   Paul Curzon   April 1993                                  *)
(*                                                                           *)
(*===========================================================================*)




structure Ineq_conv : Ineq_conv_sig =
struct

fun INEQ_CONV_ERR {function,message} =
               HOL_ERR{origin_structure = "Ineq_conv",
                                           origin_function = function,
                                           message = message};


local
fun PROTECT_GSPEC tml th =
    let val (wl,w) = dest_thm th in
     if is_forall w then
	let val {Bvar = tm, Body = body} = dest_forall w in
	 let val  tm' =  if (mem tm tml) then (genvar (type_of tm)) else tm in
	    PROTECT_GSPEC tml (SPEC tm' th)
         end
        end
     else th
    end


fun PROTECT_PART_MATCH tml  partfn th =
    let val pth = PROTECT_GSPEC tml (GEN_ALL th)
    val pat = partfn(concl pth)
    val matchfn = match_term pat
    in
     (fn tm => INST_TY_TERM (matchfn tm) pth)
    end


fun PROTECT_REWRITE_CONV tml =
     PROTECT_PART_MATCH tml
             (fn t =>
                 (let val {lhs = tm, ...} = dest_eq t
                  in tm end))

val NUM_TRANSLATION_LEQ_EQ = 
          ((GENL [(--`p:num`--),(--`m:num`--),(--`n:num`--)])
                    o SYM o SPEC_ALL)
          (theorem "arithmetic" "LESS_EQ_MONO_ADD_EQ")

val  NUM_TRANSLATION_LESS_EQ = 
          ((GENL [(--`p:num`--),(--`m:num`--),(--`n:num`--)])
                   o SYM o SPEC_ALL) 
          (theorem "arithmetic" "LESS_MONO_ADD_EQ")

val  NUM_TRANSLATION_EQ_EQ = 
          ((GENL [(--`p:num`--),(--`m:num`--),(--`n:num`--)])
                   o SYM o SPEC_ALL)  
          (theorem "arithmetic" "EQ_MONO_ADD_EQ")

in

val (NUM_LESS_EQ_PLUS_CONV, NUM_EQ_PLUS_CONV, NUM_LESS_PLUS_CONV) =

 ((fn t => PROTECT_REWRITE_CONV [] 
			(SPEC t NUM_TRANSLATION_LEQ_EQ))
     handle HOL_ERR _ =>
	raise INEQ_CONV_ERR {function = "NUM_LESS_EQ_PLUS_CONV",
			 message = "Term has incorrect form"},

  (fn t => PROTECT_REWRITE_CONV [] 
			(SPEC t NUM_TRANSLATION_EQ_EQ))
     handle HOL_ERR _ =>
	raise INEQ_CONV_ERR {function = "NUM_EQ_PLUS_CONV",
			 message = "Term has incorrect form"},

  (fn t => PROTECT_REWRITE_CONV [] 
			(SPEC t NUM_TRANSLATION_LESS_EQ))
     handle HOL_ERR _ =>
	raise INEQ_CONV_ERR {function = "NUM_LESS_PLUS_CONV",
			 message = "Term has incorrect form"})
end;



end (* signature Ineq_conv *)
