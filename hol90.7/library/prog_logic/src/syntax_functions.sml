signature SYNTAX = 
    sig

	val dest_LIST    : term -> term list
    
	val dest_spec    : term -> term * term * term
	
	val dest_t_spec  : term -> term * term * term
	
	val dest_assign  : term -> term * term 
	
	val dest_seq     : term -> term * term
	
        val dest_seql    : term -> term list

        val mk_seql      : term list -> term

	val dest_if1     : term -> term * term
	
	val dest_if2     : term -> term * term * term
	
        val dest_while   : term -> term * term

        val dest_assert  : term -> term

        val dest_variant : term -> term

        val dest_invariant  : term -> term

    end;

(* ========================================================================= *)
(*  FILE          : syntax.sml                                               *)
(*  DESCRIPTION   : Code for generating the semantic representation of a     *)
(*                  partial correctness spec. from terms representing the    *)
(*                  concrete syntax.                                         *)
(*                                                                           *)
(*  AUTHOR        : Matthew Morley, University of Edinburgh                  *)
(*  DATE          : January 1993                                             *)
(*  HISTORY       : Specialised to HOL90 from HOL88 prog_lib library.        *)
(* ========================================================================= *)


functor Syntax() : SYNTAX =
  struct

  fun SYNTAX_ERR {function,message} = 
      HOL_ERR{origin_structure = "Syntax",
	      origin_function = function,
	      message = message}

  open Rsyntax;

  exception FAIL;

  (* dest_list "[C1; ... ;Cn]"   --->   ["C1"; ... ;"Cn"] *)

  val dest_LIST = (#els o dest_list)

  (* dest_tuple "(t1,...,tn)"    --->   ["t1";...;"tn"] *)

  fun dest_tuple t =
      (let val {fst,snd} = dest_pair t
       in
	   fst::(dest_tuple snd)
       end) handle _ => [t]

(* ========================================================================= *)
(*   Destructors for terms representing internal syntax                      *)
(* ========================================================================= *)

  (* dest_spec "MK_SPEC(p,c,q)"  --> ("p","c","q") *)

  local val mk_spec = --`MK_SPEC`--
  in
      fun dest_spec tm =
	  let val {Rator,Rand} = dest_comb tm
	      val [p,c,q] = dest_tuple Rand
	  in
	      if (Rator = mk_spec)
		  then (p,c,q)
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_spec",
				   message = "Term not a valid specification"}
  end

  (* dest_assign "MK_ASSIGN(x,e)"    ---> ("x","e") *)

  local val mk_ass = --`MK_ASSIGN`--
  in
      fun dest_assign tm =
	  (let val {Rator,Rand} = dest_comb tm
	       val [x,e] = dest_tuple Rand
	   in
	       if (Rator = mk_ass)
		   then (x,e)
	       else raise FAIL
	   end) 
	       handle _ => raise SYNTAX_ERR{function = "dest_assign",
					    message = "Term not an assignment"}
  end

  (* dest_seq "MK_SEQ(c1,c2)"    --->  ("c1","c2") *)

  local val mk_seq = --`MK_SEQ`--
  in
      fun dest_seq tm =
	  let val {Rator,Rand} = dest_comb tm
	      val [c,c'] = dest_tuple Rand
	  in
	      if (Rator = mk_seq)
		  then (c,c')
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_seq",
				   message = "Term not a command sequence"}
  end

  (* dest_seql "c1;c2; ... ;cn"  --->  ["c1";"c2"; ... ;"cn"] *)

  fun dest_seql t =
      (let val (c,rest) = dest_seq t
       in
	   (dest_seql c) @ (dest_seql rest)
       end) handle _ => [t];

  (* mk_seql ["c1";... ;"cn"]    --->  "c1;(c2; ... ;cn)"  *)

  fun mk_seql l =
      if null l 
	  then raise FAIL
      else if null(tl l)
	       then hd l
	   else (--`MK_SEQ(^(hd l),^(mk_seql(tl l)))`--)

  (* dest_if1 "MK_IF1(b,c)"        --->  ("b","c") *)

  local val mk_if1 = --`MK_IF1`--
  in
      fun dest_if1 tm =
	  let val {Rator,Rand} = dest_comb tm
	      val [b,c] = dest_tuple Rand
	  in
	      if (Rator = mk_if1)
		  then (b,c)
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_if1",
				   message = "Term not a guarded command"}
  end

  (* dest_ife "MK_IF2(b,c,c')"   --->  ("b","c","c'") *)

  local val mk_if2 = --`MK_IF2`--
  in
      fun dest_if2 tm =
	  let val {Rator,Rand} = dest_comb tm
	      val [b,c,c'] = dest_tuple Rand
	  in
	      if (Rator = mk_if2)
		  then (b,c,c')
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_if2",
				   message = "Term not a conditional"}
  end


(* dest_assert "MK_ASSERT p"  -->  "p" *)

  local val mk_ass = --`MK_ASSERT`--
  in
      fun dest_assert tm =
	  let val {Rator,Rand} = dest_comb tm
	  in
	      if (Rator = mk_ass)
		  then Rand
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_assert",
				   message = "Term not an assertion"}
  end

  (* dest_invariant "MK_INVARIANT p"  -->  "p" *)

  local val mk_inv = --`MK_INVARIANT`--
  in
      fun dest_invariant tm =
	  let val {Rator,Rand} = dest_comb tm
	  in
	      if (Rator = mk_inv)
		  then Rand
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_invariant",
				   message = "Term not an invariant"}
  end

  (* dest_variant "MK_VARIANT p"  -->  "p" *)

  local val mk_var = --`MK_VARIANT`--
  in
      fun dest_variant tm =
	  let val {Rator,Rand} = dest_comb tm
	  in
	      if (Rator = mk_var)
		  then Rand
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_variant",
				   message = "Term not a variant"}
  end

  (* dest_while "MK_WHILE(b,c)"  -->  ("b","c") *)

  local val mk_while = --`MK_WHILE`--
  in
      fun dest_while tm =
	  let val {Rator,Rand} = dest_comb tm
	      val [b,c] = dest_tuple Rand
	  in
	      if (Rator = mk_while)
		  then (b,c)
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_while",
				   message = "Term not a while loop"}
  end

(* dest_t_spec "T_SPEC(p,c,q)" --> ("p","c","q") *)

  local val mk_spec = --`T_SPEC`--
  in
      fun dest_t_spec tm =
	  let val {Rator,Rand} = dest_comb tm
	      val [p,c,q] = dest_tuple Rand
	  in
	      if (Rator = mk_spec)
		  then (p,c,q)
	      else raise FAIL
	  end 
      handle _ => raise SYNTAX_ERR{function = "dest_t_spec",
				   message = "Term not a valid specification"}
  end

  end; (* Functor Syntax() *)
