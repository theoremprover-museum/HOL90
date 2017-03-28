signature TRANSLATION =
    sig
        (* HACKERY *)

        val prime_var  : term -> term
        val unprime    : term -> term
        val is_ghost   : string -> bool
        val trans_term : term -> term -> term
        val untrans_term : term -> term
        val TRANS_THM  : thm -> thm

    end

(* ------------------------------------------------------------------------ *)
(*        THIS IS ALL HACKERY, AND I DON'T LIKE IT ONE LITTLE BIT!          *)
(* ------------------------------------------------------------------------ *)

functor Translation () : TRANSLATION =
    struct

   open Rsyntax;

  val butlast = fst o Lib.front_n_back;


  fun SYNTAX_ERR {function,message} = 
      HOL_ERR{origin_structure = "Translation",
	      origin_function = function,
	      message = message}

  exception FAIL

  (* "x"   --->   "`x`"  *)

  fun prime_var tm = 
      mk_const{Name=("\""^((#Name o dest_var) tm)^"\""),Ty=(==`:string`==)}

  (* unprime "`X`"   --->   "X:num" *)

  fun unprime t =
      let val {Name,...} = dest_const t
      in
	  mk_var{Name=implode(butlast(tl(explode Name))),Ty=(==`:num`==)}
      end

(*
   A ghost variable will be one that satisfies the predicate is_ghost.
   This is an assignable predicate; we initialize it to the predicate

      is_lower : tok -> bool   

   which tests whether a token is made up of lower case letters.
*)

  fun is_ghost tok =
      can (map (fn ch => let 
			     val true = (ch >= "a" andalso ch <= "z")
			 in
			     true
			 end)) (explode tok)

  (* trans_term : "s", " ... x ..."  -->  "\s. ... s `x` ..." *)

  fun trans_term s tm =
      (let val NUM = (==`:num`==)
	   val subst_list = 
	       mapfilter
	       (fn t => 
		if (type_of t = NUM) andalso (not(is_ghost(#Name(dest_var t))))
		    then {redex=t, residue=mk_comb{Rator=s, Rand=prime_var t}}
		else raise FAIL)
	       (free_vars tm)
       in 
	   mk_abs{Bvar=s, Body=subst subst_list tm}
       end) handle _ => raise SYNTAX_ERR{function="trans_term",message=""}

  (* untrans_term : "\s. ... s `x` ..."   --->   " ... x ... " *)

  fun untrans_term t =
      (let val {Bvar=s,Body=t1} = dest_abs t
	   fun u_fn t =
	       if (is_const t) orelse (is_var t)
		   then t
	       else if is_comb t
			then 
			    let val {Rator,Rand} = dest_comb t
			    in
				if Rator = s
				    then (unprime Rand)
				else mk_comb{Rator=u_fn Rator,Rand= u_fn Rand}
			    end
		    else if is_abs t
			     then 
				 let val {Bvar,Body} = dest_abs t
				 in
				     mk_abs{Bvar=Bvar,Body= u_fn Body}
				 end
			 else raise FAIL
       in
	   u_fn t1
       end) handle _ => raise SYNTAX_ERR{function="untrans_term",message=""}

(* Test examples:

trans_term (--`s:string->num`--) (--`(X:num=x) /\ (Y:num=y)`--);
trans_term (--`s:string->num`--) (--`(R < Y) /\ (X = R + (Y*Q))`--);     

*)

(* TRANS_THM instantiates a theorem using INST 

     |- ... x ...  -->  |- !s. ... s "x" ..."
*)

  fun TRANS_THM th =
      (let val s = (--`s:string->num`--)
	   val NUM = (==`:num`==)
	   val subst_list = 
	       mapfilter
	       (fn t => 
		if (type_of t = NUM) andalso (not(is_ghost(#Name(dest_var t))))
		    then {redex=t, residue=mk_comb{Rator=s, Rand=prime_var t}}
		else raise FAIL)
	       (free_vars (concl th))
       in 
	   GEN s (INST subst_list th)
       end) handle FAIL => raise SYNTAX_ERR{function="TRANS_THM",message=""}

    end (* Functor Translation() *)

