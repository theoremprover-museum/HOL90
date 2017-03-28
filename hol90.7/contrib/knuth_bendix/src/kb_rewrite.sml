structure KB_rewrite : KB_rewrite_sig =
struct

open Psyntax;

exception NO_SUCCESS;
fun first_success f [] =  raise NO_SUCCESS 
  | first_success f (a::rst) = f a handle _ => first_success f rst;

val global_rewrite_list = ref ([] : (thm*term) list);

(* Does one match *)
fun basic_match ob pat_th = 
   let val tm_subst = fst (match_term (lhs (concl pat_th)) ob)
       and v = genvar (type_of ob)
       val pat_th' = INST tm_subst pat_th
   in
   ( global_rewrite_list := (!global_rewrite_list)@[(pat_th',v)];
     v)
   end;

fun node_match pats ob = first_success (basic_match ob) pats;

fun make_template pats =
   let fun mk_tmp ob =
      (node_match pats ob)
       handle _ => (mk_comb (mk_tmp (rator ob), mk_tmp (rand ob))
                    handle _ =>  ob)
   in
   mk_tmp
   end;

(* Performs one parallel disjoint replacement *)
fun PSUB eq_thms ob_thm = 
   (global_rewrite_list := [];
    let val temp = make_template eq_thms (concl ob_thm)
    in
    SUBST (!global_rewrite_list) temp ob_thm
    end);

fun PSUB_ALL eq_thms ob_thm =
   let val result = ref (PSUB eq_thms ob_thm)
   in
   ( while not (null (!global_rewrite_list))
     do result := PSUB eq_thms (!result);
     !result)
   end;

fun PSUB_CONV eq_thms ob = 
   ( global_rewrite_list := [];
     let val temp = make_template eq_thms ob
     in
     SUBST_CONV (!global_rewrite_list) temp ob
     end);

fun PSUB_ALL_CONV eq_thms ob =
   let val result = ref (PSUB_CONV eq_thms ob)
   in
   ( while not (null (!global_rewrite_list))
     do result := TRANS (!result )
                       (PSUB_CONV eq_thms ((snd o dest_eq o concl) (!result)));
     !result)
   end;

fun RW_LHS_FULLY R th =
   let val (l,r) = dest_eq (concl th)
       val l' = PSUB_ALL_CONV R l
       and v = genvar (type_of l)
   in
   SUBST [(l',v)] (mk_eq (v,r)) th
   end;

fun RW_RHS_FULLY R th =
   let val (l,r) = dest_eq (concl th)
       val r' = PSUB_ALL_CONV R r
       and v = genvar (type_of r)
   in
   SUBST [(r',v)] (mk_eq (l,v)) th
   end;

fun MATCH_SUBST_TAC rewrites =
  let val conv = PSUB_ALL_CONV rewrites
  in
  fn (A,t) => let val th = conv t
                  val (_,right) = dest_eq(concl th)
              in
              if right= (--`T`--) 
              then ([], fn [] => EQ_MP (SYM th) TRUTH)
              else ([A,right], fn [th'] => EQ_MP (SYM th) th')
              end
  end;

end; (* KB_rewrite *)
