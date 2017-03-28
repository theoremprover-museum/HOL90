signature Ac_term_sig =
  sig
   datatype ac_term = Ac_app of term * ac_term list
                    | Ac_const of term
                    | Ac_var of term
   val pp_ac : Portable.PrettyPrint.ppstream -> ac_term -> unit
   val install_ac_pp: unit -> unit 
   val binary_op_type : term -> hol_type
   val is_comm : thm -> bool
   val is_assoc : thm -> bool
   val std_assoc_form : thm -> thm
   val std_comm_form : thm -> thm
   val mk_ac : term list -> term -> ac_term
   val mk_rigid_ac : term list -> term -> ac_term
   val ac_term_eq : ac_term -> ac_term -> bool
   val ac_vars : ac_term -> ac_term list
   val is_ac_var : ac_term -> bool
   val is_ac_const : ac_term -> bool
   val is_ac : term list -> ac_term -> bool
   val gen_ac_var : hol_type -> ac_term
   val term_leq : term -> term -> bool
   val term_sort : term list -> term list
   val un_ac : term list -> ac_term -> term
  end;



functor AC_TERM(Ac_lib :Ac_lib_sig) : Ac_term_sig = 
struct

open Rsyntax;
fun AC_TERM_ERR{func, mesg} = 
        HOL_ERR{origin_structure = "AC_term",
                origin_function = func,
                message = mesg};

datatype ac_term = Ac_var of term
                 | Ac_const of term
                 | Ac_app of term * ac_term list;

fun pr_list pfun dfun bfun L =
   let fun pr [] = ()
         | pr [i] = pfun i
         | pr (i::rst) = ( pfun i; dfun() ; bfun() ; pr rst )
   in pr L
   end;

fun pp_ac ppstrm ac_tm =
  let val {add_string,add_break,begin_block,end_block,...} = 
              PP.with_ppstream ppstrm
      val ppterm = Hol_pp.pp_term ppstrm
      fun pp (Ac_var tm) = ppterm tm
        | pp (Ac_const tm) = ppterm tm
        | pp (Ac_app(tm,L)) = 
            (begin_block PP.CONSISTENT 1;
             ppterm tm;
             add_string "(";
             begin_block PP.CONSISTENT 0;
             pr_list pp (fn () => add_string",")
                        (fn () => add_break(0,0)) L;
             end_block();
             add_string ")";
             end_block())
  in begin_block PP.CONSISTENT 0;
     pp ac_tm;
     end_block()
  end;


fun install_ac_pp() = 
  Portable.PrettyPrint.install_pp ["Ac_tools","Acu","Ac_term","ac_term"] 
      2 (* Bogus parameter? *) pp_ac;


   
local
fun fail() = raise AC_TERM_ERR{func="strip_binary_op",
                               mesg="wrong type"}
in
fun binary_op_type c = 
   case (dest_type (#Ty (dest_const c)))
     of {Tyop="fun", Args = [ty1,ty2]}
        => (case (dest_type ty2)
              of {Tyop="fun", Args = [ty2a, ty2b]}
                 => if (ty1=ty2a) andalso (ty2a=ty2b)
                    then ty1
                    else fail()
               | _ => fail())
      | _ => fail()
end;


(* Does constant c have a type of the form
 *
 *       ty -> ty -> ty
 ***)
val is_binary_op = can binary_op_type;


(* Does th have the form

       |- x+y = y+x
*)
fun is_comm th = 
   let val {lhs,rhs} = dest_eq (concl th)
       val (c1,[Ll,Lr]) = strip_comb lhs
   in if (is_binary_op c1)
      then let val (c2,[Rl,Rr]) = strip_comb rhs
           in (c1 = c2 andalso Ll = Rr andalso Lr = Rl)
           end
      else false
   end handle _ => false;


(* Does th have the form

       |- (a + b) + c = a + (b + c)
*)
fun is_assoc th = 
   let val {lhs,rhs} = dest_eq (concl th)
       val (c1,[Ll,Lr]) = strip_comb lhs
   in if (is_comb Ll) 
      then let val (c11,[Lll,Llr]) = strip_comb Ll
               val (c2,[Rl,Rr]) = strip_comb rhs
               val (c21,[Rrl,Rrr]) = strip_comb Rr
           in ((is_binary_op c1) andalso 
               (c1 = c11) andalso (c11 = c2) andalso (c2 = c21) andalso
               (Lr = Rrr) andalso (Llr = Rrl) andalso (Lll = Rl))
           end
      else false
   end handle _ => false;
   

fun std_comm_form th = 
   let val th' = SPEC_ALL th
   in if (is_comm th')
      then th'
      else raise AC_TERM_ERR{func = "std_comm_form", 
                             mesg = "Not a commutative theorem"}
   end;

fun std_assoc_form th = 
   let val th' = SPEC_ALL th
   in if (is_assoc th')
      then th'
      else if (is_assoc (SYM th'))
           then (SYM th')
           else raise AC_TERM_ERR{func = "std_assoc_form", 
                                  mesg = "Not an associative theorem"}
   end;

(* Maps from an hol term to an ac_term. Lambda terms not allowed. *)

fun mk_ac ac_consts =
   let fun elevate_wrt f trm = 
        if (is_comb trm) 
        then let val (g,args) = strip_comb trm
             in if (f = g)
                then flatten (map (elevate_wrt f) args)
                else [mk trm]
             end
        else if (is_var trm)
             then [Ac_var trm]
             else if (is_const trm)
                  then [Ac_const trm]
                  else raise AC_TERM_ERR{func="mk_ac",
                                         mesg="abstractions not allowed"}
   and mk tm = 
         if (is_comb tm) 
         then let val (f,args) = strip_comb tm
              in Ac_app(f, if (mem f ac_consts) 
                           then flatten (map (elevate_wrt f) args)
                           else map mk args)
              end
         else if (is_var tm)
              then Ac_var tm
              else if (is_const tm)
                   then Ac_const tm
                   else raise AC_TERM_ERR{func = "mk_ac", 
                                          mesg = "abstractions not allowed"}
   in mk
   end;

fun mk_rigid_ac ac_consts =
   let fun elevate_wrt f trm = 
        if (is_comb trm) 
        then let val (g,args) = strip_comb trm
             in if (f = g)
                then flatten (map (elevate_wrt f) args)
                else [mk_ac trm]
             end
        else if (is_const trm orelse is_var trm)
             then [Ac_const trm]
             else raise AC_TERM_ERR{func="mk_rigid_ac", 
                                    mesg="abstractions not allowed"}
   and mk_ac tm = 
         if (is_comb tm) 
         then let val (f,args) = strip_comb tm
              in if (mem f ac_consts) 
                 then Ac_app(f, flatten (map (elevate_wrt f) args))
                 else Ac_app(f, map mk_ac args)
              end
         else if (is_const tm orelse is_var tm)
              then Ac_const tm
              else raise AC_TERM_ERR{func="mk_rigid_ac", 
                                     mesg="abstractions not allowed"}
   in mk_ac
   end;


(* - val a = mk_ac `((a * (b * c)) + ((p * q) * r) + c)`
     and b = mk_ac `((q * (p * r)) + c + ((c * b) * a))`;
   - ac_term_eq a b;
   val it = true : bool
*)
fun ac_term_eq (Ac_app(c1,args1)) (Ac_app(c2,args2)) =
	       (c1 = c2) andalso (Ac_lib.op_multiset_eq ac_term_eq args1 args2)
  | ac_term_eq t1 t2 = (t1 = t2);

fun ac_vars (v as Ac_var _) = [v]
  | ac_vars (Ac_const _) = []
  | ac_vars (Ac_app(_,args)) = mk_set(flatten(map ac_vars args));

fun is_ac_var (Ac_var _) = true
  | is_ac_var _ = false;

fun is_ac_const (Ac_const _) = true
  | is_ac_const _ = false;

fun is_ac ac_consts (Ac_app(c,_)) = mem c ac_consts
  | is_ac _ _ = false;

fun gen_ac_var ty = Ac_var (genvar ty);

fun term_leq t1 t2 = aconv t1 t2 orelse term_lt t1 t2;
val term_sort = sort term_leq;


(* Maps from an ac_term to a hol term. *)

fun un_ac ac_consts =
   let fun un (Ac_var a) = a
         | un (Ac_const a) = a
         | un (Ac_app(_,[])) = raise AC_TERM_ERR{func = "un_ac.[]", mesg = ""}
         | un (Ac_app(f, args)) = 
             let val args' = term_sort(map un args)
             in if (mem f ac_consts)
                then let val args'' = rev args'
                     in itlist (fn x => fn y => list_mk_comb(f,[x,y]))
                               (rev(tl args'')) (hd args'')
                     end
                else list_mk_comb(f, args')
             end
   in un
   end;

end; (* AC_TERM *)
