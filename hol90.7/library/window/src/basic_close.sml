(*--------------------------------------------------------------------------*)
(*                  Copyright (c) Jim Grundy 1992                           *)
(*                  All rights reserved                                     *)
(*                                                                          *)
(* Jim Grundy, hereafter referred to as `the Author', retains the copyright *)
(* and all other legal rights to the Software contained in this file,       *)
(* hereafter referred to as `the Software'.                                 *)
(*                                                                          *)
(* The Software is made available free of charge on an `as is' basis. No    *)
(* guarantee, either express or implied, of maintenance, reliability,       *)
(* merchantability or suitability for any purpose is made by the Author.    *)
(*                                                                          *)
(* The user is granted the right to make personal or internal use of the    *)
(* Software provided that both:                                             *)
(* 1. The Software is not used for commercial gain.                         *)
(* 2. The user shall not hold the Author liable for any consequences        *)
(*    arising from use of the Software.                                     *)
(*                                                                          *)
(* The user is granted the right to further distribute the Software         *)
(* provided that both:                                                      *)
(* 1. The Software and this statement of rights are not modified.           *)
(* 2. The Software does not form part or the whole of a system distributed  *)
(*    for commercial gain.                                                  *)
(*                                                                          *)
(* The user is granted the right to modify the Software for personal or     *)
(* internal use provided that all of the following conditions are observed: *)
(* 1. The user does not distribute the modified software.                   *)
(* 2. The modified software is not used for commercial gain.                *)
(* 3. The Author retains all rights to the modified software.               *)
(*                                                                          *)
(* Anyone seeking a licence to use this software for commercial purposes is *)
(* invited to contact the Author.                                           *)
(*--------------------------------------------------------------------------*)
(*============================================================================*)
(* CONTENTS: generic and basic window inference rules                         *)
(*============================================================================*)
(*$Id: basic_close.sml,v 4.1 1994/09/10 03:42:51 jim Exp slind $*)

structure BasicClose : sig end =

struct

(*      (|- f = g)                                                           *)
(* --------------------  RATOR_CLOSE "f x"                                   *)
(*  (|- (f x) = (g x))                                                       *)
fun RATOR_CLOSE tm th = (AP_THM th (rand tm))
                        handle _ => WIN_ERR{function="RATOR_CLOSE",message=""};

(*      (|- x = y)                                                           *)
(* -------------------- RAND_CLOSE "f x"                                     *)
(*  (|- (f x) = (f y))                                                       *)
fun RAND_CLOSE tm th = (AP_TERM (rator tm) th)
                       handle _ => WIN_ERR{function="RAND_CLOSE",message=""};

(*       (|- t = u)                                                          *)
(* ---------------------- BODY_CLOSE "\x.t"                                  *)
(*  (|- (\x.t) = (\x.u))                                                     *)
fun BODY_CLOSE tm th = (ABS (bndvar tm) th)
                       handle _ => WIN_ERR{function="BODY_CONV",message=""};

val COND1_THM = theorem "window" "COND1_THM";
(*            (A |- B R D)                                                   *)
(* --------------------------------- COND1_CLOSE "A => B | C"                *)
(*  (|- (A => B | C) R (A => D | C)                                          *)
fun COND1_CLOSE tm th =
    let val {cond=a,larm=b,rarm=c} = dest_cond tm
        and d = rand (concl th)
        and r = rator (rator (concl th)) in
    let val x = genvar (type_of b) in
    let val rref =
            GEN x (reflexive (mk_comb{Rator=(mk_comb{Rator=r,Rand=x}),Rand=x}))
    in
        MP (MP (ISPECL [r,a,b,c,d] COND1_THM) rref) (DISCH a th)
    end end end;


val COND2_THM = theorem "window" "COND2_THM";
(*          (~A |- C R D)                                                    *)
(* --------------------------------- COND2_CLOSE "A => B | C"                *)
(*  (|- (A => B | C) R (A => B | D)                                          *)
fun COND2_CLOSE tm th =
    let val {cond=a,larm=b,rarm=c} = dest_cond tm 
        val d = rand (concl th)
        val r = rator (rator (concl th)) in
    let val x = genvar (type_of c) in
    let val rref =
            GEN x (reflexive (mk_comb{Rator=(mk_comb{Rator=r,Rand=x}),Rand=x}))
    in
        MP (MP (ISPECL [r,a,b,c,d] COND2_THM) rref) (DISCH (mk_neg a) th)
    end end end;

val BODY2_THM = theorem "window" "BODY2_THM";

(*        (v = c |- u R t)                                                   *)
(* ----------------------------- BODY2_CLOSE "((\v.u) c)"                    *)
(*  (|- ((\v.u) c) R ((\v.t) c)                                              *)
fun BODY2_CLOSE tm th =
    let val {Rator=vu,Rand=c} = dest_comb tm in
    let val {Bvar=v,Body=u} = dest_abs vu
        and t = rand (concl th)
        and r = rator (rator (concl th)) in
    let val vt = mk_abs{Bvar=v,Body=t} 
    in
        if mem v (flatten (map free_vars (hyp th))) then
            let val t1 = GEN v (DISCH (mk_eq{lhs=v,rhs=c}) th) in
            let val t2 = ISPECL [c,vu,vt,r] BODY2_THM in
            let val t3 =
                CONV_RULE
                    (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
                        (RATOR_CONV (RAND_CONV BETA_CONV)))))))
                    t2 in
            let val t4 =
                CONV_RULE
                    (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
                        (RAND_CONV BETA_CONV))))))
                    t3 in
                MP t4 t1
            end end end end
        else
            let val t1 = BETA_CONV (mk_comb{Rator=mk_abs{Bvar=v,Body=u},Rand=v})
                and t2 = SYM (BETA_CONV (mk_comb{Rator=vt,Rand=v}))
            in
                INST [{redex=c,residue=v}]
                     (transitive (CONJ (transitive (CONJ t1 th)) t2))
            end
    end end end;

val LET_THM = theorem "window" "LET_THM";

(*             (v = c |- u R t)                                              *)
(* ----------------------------------------- LET_CLOSE "let v = c in u"      *)
(*  (|- (let v = c in u) R (let v = c in t)                                  *)
fun LET_CLOSE tm th =
    let val {func=vu,arg=c} = dest_let tm in
    let val {Bvar=v,Body=u} = dest_abs vu
        and t = rand (concl th)
        and r = rator (rator (concl th)) in
    let val vt = mk_abs{Bvar=v,Body=t} in
    let val t1 = GEN v (DISCH (mk_eq{lhs=v,rhs=c}) th) in
    let val t2 = ISPECL [c,vu,vt,r] LET_THM in
    let val t3 = CONV_RULE
                    (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
                    (RATOR_CONV (RAND_CONV BETA_CONV)))))))
                    t2 in
    let val t4 = CONV_RULE
                    (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
                    (RAND_CONV BETA_CONV))))))
                    t3
    in
        MP t4 t1
    end end end end end end end;

(* Put all those rules in the data base.                                     *)

val dummy =
(
store_rule
    (
        [RATOR], 
        is_comb, 
        (fn targ => fn rel =>
            let val ty = type_of (rator targ) in
                mk_const{Name="=",Ty=(fun_type [ty,ty,bool])}
            end),  
        (fn targ => fn rel => mk_const{Name="=",Ty=(type_of rel)}),
        K [], 
        RATOR_CLOSE
    );
store_rule
    (
        [RAND],
        is_comb,
        (fn targ => fn rel =>
            let val ty = type_of (rand targ) in
                mk_const{Name="=",Ty=(fun_type [ty,ty,bool])}
            end),
        (fn targ => fn rel => mk_const{Name="=",Ty=(type_of rel)}),
        K [],
        RAND_CLOSE
    );
store_rule
    (
        [BODY],
        is_abs,
        (fn targ => fn rel => 
            let val ty = ran targ in
                mk_const{Name="=",Ty=(fun_type [ty,ty,bool])}
            end),
        (fn targ => fn rel => mk_const{Name="=",Ty=(type_of rel)}),
        K [],
        BODY_CLOSE
    );
store_rule
    (
        [RATOR,RAND],
        is_cond,
        K I,
        K I,
        (fn tm => SMASH (ASSUME (rand (rator (rator tm))))),
        COND1_CLOSE
    );
store_rule
    (
        [RAND],
        is_cond,
        K I,
        K I,
        (fn tm => SMASH (ASSUME (mk_neg (rand (rator (rator tm)))))),
        COND2_CLOSE
    );
store_rule
    (
        [RATOR,BODY],
        (fn tm => (is_comb tm) andalso (is_abs (rator tm))),
        K I,
        K I,
        (fn tm => 
            let val v = bndvar (rator tm) in
	       [ASSUME (mk_eq{lhs=v,rhs=(rand tm)})]
            end),
        BODY2_CLOSE
    );
store_rule
    (
        [RATOR,RAND,BODY],
        (fn tm => is_let tm),
        K I,
        K I,
        (fn tm => 
            let val {func=vu,arg=c} = (dest_let tm) in
            let val v = (#Bvar (dest_abs vu)) in
                [ASSUME (mk_eq{lhs=v,rhs=c})]
            end end),
        LET_CLOSE
    )
);
end;
