(***************************** multiple_rec_spec.sml ********************)
(*                                                                      *)
(* Author: Ingo Schuck, Ralf Reetz                                      *)
(* Date:   5.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*  see multiple_rec_spec.DOC                                           *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:   Integer                                              *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

structure multiple_rec_spec : MULTIPLE_REC_SPEC =
struct

fun new_multiple_recursive_specification
 {name : string, rec_axiom : thm, def : term} =
 let
  (*------------------- utilities ---------------------------------*)
  val serial_no = ref 0

  (*-- new_serial_no --
    Global Input:
     Integer.makestring, serial_no
    Input:
     unit
    Output:
     A string representing a number is returned. For every call, the number 
     returned is increased by 1. For the first call, number 1 is returned.
    Algorithm:
     store the current number returned in serial_no
  *)
  fun new_serial_no () = 
   let
    val _ = (serial_no := (!serial_no) +1)
   in
    Integer.makestring (!serial_no)
   end


  (*-- mk_n_ary_funtype --
    Global Input:
     none
    Input:
     list of hol types [ty1,ty2,...,tyn]
    Output:
     hol type ==`:ty1 -> ty2 -> ... -> tyn
    Algorithm:
     If the list consists of 2 types then use mk_type. Otherwise, use
     recursion. It fails if the supplied length of the list is equal
     1 or 0.
  *)
  fun mk_n_ary_funtype [ty1,ty2] =
   mk_type{Tyop = "fun", Args = [ty1,ty2]}
  | mk_n_ary_funtype (ty::ty_list) =
   mk_type{Tyop = "fun", Args = [ty, mk_n_ary_funtype ty_list]}
  
   
(*----------------------------- here we go --------------------------------*)

  (*--- split 'def' into list of conjuncts. For each conjunct create a ---*)
  (*--- record containing an argumentlist of the function on the left  ---*)
  (*--- side, a list of the produced 'r' variables (see example below) ---*)
  (*--- and the right-handside of the equation:                        ---*)
  val tmp = map (dest_eq) (strip_conj def)
  val tmp = map (fn x => {lhs=snd (strip_comb (#lhs x)),
                          r_l=[], rhs= #rhs x}) tmp

  (*-- get argument type --*)
  val r_type = type_of (hd (#lhs (hd tmp)))


  (*-- col_loop --
    Global Input:
     serial_no, mk_n_ary_funtype
    Input:
     list of the remaining columns
    Output:
     thm list * term for the existance prove
    Algorithm:
     the arguments of the function are treated as a matrix and the
     appropiate theorems needed for rewriting are generated column
     by column (right to left)
  *)
  fun col_loop (rem_col:{lhs:term list, r_l:term list, rhs:term} list) =

  let
  (*-- extraction of the constant in each argument.                     --*)
  (*-- reason: detection of rows whose functionarguments are compatible --*)
   val tmp = map (fn x => {p_list= (rev (tl (rev (#lhs x)))),
                           lhs= #lhs x, rhs= #rhs x, r_l= #r_l x}) rem_col
   val tmp = map (fn x =>
                         {p_list=(map (fn x => fst(strip_comb x)) (#p_list x)),
                          lhs= #lhs x, rhs= #rhs x, r_l= #r_l x}) tmp

   (*- line_loop -
     Global Input:
      serial_no, mk_n_ary_funtype
     Input:
      list of the remaining columns
     Output:
      {lhs:term list, r_l:term list, rhs:term} list * thm list, means a list
      of the now remaining columns and a list of the resulting theorems
     Algorithm:
      group rows with compatible functionarguments and construct the
      corresponding theorems
   *)
   fun line_loop (rem_col: {lhs:term list, p_list:term list, r_l:term list,
                            rhs:term} list) =

   if null rem_col then ([],[])
    else let

     (*----------------- utilities for line_loop ---------------*)
     (*- same_stuff -
       Global Input:
        none
       Input:
        pivot row, list of the remaining columns
       Output:
        list of the remaining columns whose rows have compatible
        functionarguments to the pivot row
       Algorithm:
        trivial
     *)
     fun same_stuff pivot (l: {lhs:term list, p_list:term list, r_l:term list,
                               rhs:term} list) =

     if null l then []
      else
       if ((#p_list (hd l)) = pivot) then
        ({lhs=(#lhs (hd l)), rhs=(#rhs (hd l)), r_l=(#r_l (hd l))} ::
         (same_stuff pivot (tl l)))
        else (same_stuff pivot (tl l))
     (* end same_stuff *)


     (*- del_same_row -
       Global Input:
        none
       Input:
        pivot row, list of the remaining columns
       Output:
        list of the remaining columns without the rows having compatible
        functionarguments to the pivot row
       Algorithm:
        trivial
     *)
     fun del_same_row pivot (l: {lhs:term list, p_list:term list,
                                 r_l:term list, rhs:term} list) =

     if null l then []
      else
       if ((#p_list (hd l)) = pivot) then del_same_row pivot (tl l)
        else (hd l)::del_same_row pivot (tl l)
     (* end del_same_row *)

     val pivot = (#p_list(hd rem_col))
     val fn_name = name ^ (new_serial_no ())


     (*- construct_col -
       Global Input:
        fn_name, mk_n_ary_funtype
       Input:
        list of the remaining columns whose rows have compatible
        functionarguments
       Output:
        term * term, the first term contains the finial construction for the
        current column, current row group; the second term names the resulting
        functionname
       Algorithm:
     *)
     fun construct_col (rem_col:{lhs:term list, r_l:term list, rhs:term} list) =

     if null (#r_l (hd (rem_col))) then  (* first step *)
      let
       val help = (rev (#lhs (hd rem_col)))
       val param_list = hd help :: (flatten
                         (map (fn x => (snd (strip_comb x))) (rev (tl help))))
       val new_rhs = #rhs (hd rem_col)
       val param_type_list = (map type_of param_list) @ [type_of new_rhs]
       val cur_fun = mk_var{Name = fn_name,
                            Ty = (mk_n_ary_funtype param_type_list)}
       val cur_eq = (mk_eq{lhs=list_mk_comb (cur_fun, param_list),
                           rhs=new_rhs})
      in
      if null (tl rem_col) then (cur_eq, cur_fun)
       else
        (mk_conj{conj1=cur_eq,
                 conj2= fst (construct_col (tl rem_col))}, cur_fun)
      end
      else  (* all other steps *)
       let
        val help = (rev (#lhs (hd rem_col)))
        val param_list = ((hd help) :: ( (#r_l (hd rem_col))@
             (flatten (map (fn x => snd(strip_comb x)) (rev (tl help))))))
        val new_rhs = list_mk_comb ((#rhs (hd rem_col)),
                  (#r_l (hd rem_col))@
                  (flatten (map (fn x => snd(strip_comb x)) (rev help))))

        val param_type_list = (map type_of param_list) @ [type_of new_rhs]
        val cur_fun = mk_var{Name = fn_name,
                             Ty = (mk_n_ary_funtype param_type_list)}
        val cur_eq = (mk_eq{lhs=list_mk_comb (cur_fun, param_list),
                            rhs=new_rhs})
       in
       if null (tl rem_col) then (cur_eq, cur_fun)
        else
         (mk_conj{conj1=cur_eq,
                  conj2= fst (construct_col (tl rem_col))}, cur_fun)
      end
     (* end construct_col *)

     val col_construction = construct_col (same_stuff pivot rem_col)
     val new_fn = new_recursive_definition
                   {name      = fn_name,
                    fixity    = Prefix,
                    rec_axiom = rec_axiom,
                    def       = (fst col_construction)}

     val remain_row = line_loop (del_same_row pivot rem_col)
    in
    ({lhs= rev (tl (rev (#lhs (hd rem_col)))),
      r_l= mk_var {Name = name ^ "r" ^ (new_serial_no ()), Ty = r_type} ::
            #r_l (hd rem_col),
      rhs= mk_const (dest_var (snd col_construction))}
     :: (fst remain_row), new_fn :: (snd remain_row) )
    end
   (* end line_loop *)

   val l_l = line_loop tmp

  in
   if null (#lhs (hd (fst l_l))) then (snd l_l, #rhs (hd (fst l_l)))
    else
     let
      val tmp = col_loop (fst l_l)
     in
     (snd l_l @ fst tmp, snd tmp)
     end    
  end
 (* col_loop *)

 val result = col_loop tmp

val tmp = rev (free_vars (--`^def`--))
 in
 new_specification
  {consts  = [{const_name=name,fixity=Prefix}],
   name    = name,
   sat_thm = 
     prove(mk_exists {Bvar=(hd tmp),
                      Body=(list_mk_forall ((tl tmp), (--`^def`--)))},
           EXISTS_TAC (snd result) THEN PURE_REWRITE_TAC (fst result)
           THEN REWRITE_TAC []) }
 end;
(* end new_multiple_recursive_specification *)

end; (* struct *)
