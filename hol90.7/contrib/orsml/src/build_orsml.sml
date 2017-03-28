(* =====================================================================*)
(* FILE          : build_orsml.sml                                      *)
(* DESCRIPTION   : composes the pieces for orsml in hol.                *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter                                          *)
(*                                                                      *)
(* DATE          : 94.08.08                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature orsig = 
   sig

	(* types *)

        type base
        type co_type
	type co

	(* type work *)

	exception Dontunify
	val printtype : co_type -> unit
	val normalize : co_type -> co_type	
	val typeof : co -> co_type
        val tp_print : co_type -> string 
	(* duplicate elimination *)
 	
	exception Badtypebool
	val eq : co * co -> co

	(* object creation *)

        exception Badobject
	val mksetint : int list -> co
	val mksetco : co list -> co
	val mkorsint : int list -> co
	val mkorsco : co list -> co
	val mkprodco : co * co -> co
        val mkintco : int -> co
        val mkboolco : bool -> co
        val mkstringco : string -> co
        val mkbaseco : base -> co 
        val Dup_elim : bool ref 
	val dupelim : co -> co

	(* algebra *)

	exception Badtypecomp
	exception Badtypeproj
	exception Badtypepair
	exception Badtypebang
	exception Badtypeid
	exception Badtyperho
	exception Badtypeflat
	exception Badtypesng
	exception Badtypeunion
	exception Badtypeempty
	exception Badtypemap
	exception Badtypeorrho
	exception Badtypeorflat
	exception Badtypeorunion
	exception Badtypeormap
	exception Badtypeorempty
	exception Badtypealpha
	exception Badtypenormalize
	exception Badtypearith
	exception Badtypecond
        exception Badtypeleq

	val empty : co
        val orempty : co
	val id : co -> co
	val comp : ('a -> 'b) * (co -> 'a) -> co -> 'b
	val p1 : co -> co
	val p2 : co -> co
	val pair : (co -> co) * (co -> co) -> co -> co
	val bang : co -> co
	val sng : co -> co
	val orsng : co -> co
	val union : co * co -> co
	val orunion : co * co -> co
	val orflat : co -> co
	val flat : co -> co
	val emptyset : co -> co
	val emptyorset : co -> co
	val pairwith : co * co -> co
	val orpairwith : co * co -> co
	val smap : (co -> co) -> co -> co
	val orsmap : (co -> co) -> co -> co
	val alpha : co -> co
	val neg : co -> co
	val cond : co * ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
	val plus : co * co -> co
	val mult : co * co -> co
	val monus : co * co -> co
	val gen : co -> co
	val sum : (co -> co) -> co -> co
        val orsum : (co -> co) -> co -> co
	val normal : co -> co
	val normal_form : co -> co
        val normal_entries : co -> co
        val norm : (co -> co) * 'a * (co * 'a -> 'a) 
                * ((co * bool) * 'a -> 'b) -> co -> 'b
	val normal_time : co * (co -> 'a) * ('a * 'a -> bool) 
                        * real -> co * bool
        val exists : (co -> co) -> co -> co * bool
        val apply_unary : (base -> base) -> co -> co
        val apply_binary: (base * base -> base) -> co -> co
	val apply_op2 : (base * base -> base) -> co * co -> co
        val apply : (base list -> base) -> co -> co
 	val apply_test : (base -> bool) -> co -> co
	val leqstring : co * co -> co
        val leqbase : co * co -> co 
	(* structural recursion *)

        structure SR : sig
                         exception Badtypesr 
                         val sr : co * (co * co -> co) -> co -> co
                         val orsr : co * (co * co -> co) -> co -> co
                       end

	(* destruction of objects *)
 
        structure DEST : sig
			     exception Cannotdestroy
			     val co_to_list : co -> co list
			     val co_to_pair : co -> co * co
			     val co_to_int : co -> int
			     val co_to_bool : co -> bool
			     val co_to_base : co -> base 
			     val co_to_string : co -> string
			 end

	(* printing *)

	val printco : co -> unit
	val show : co -> unit
        val pp_co_type : System.PrettyPrint.ppstream -> co_type -> unit
        val pp_co : System.PrettyPrint.ppstream -> co -> unit
        val printer : int -> unit
        val printer_type : int -> unit
        val string_of_co : co -> string 

   end;

structure Orsml:orsig =
    struct
	structure Common = COMMON (structure BTS = HolDbData)
	structure Type = TYPE (Common)
	structure Dupelim = DUPELIM (Common)
	structure SR = STRREC (Common)
	structure DEST = DESTRUCT (Common)
	structure Print = PPRINT (Type)
	structure Make = MAKE (structure Type = Type
			       structure Dupelim = Dupelim)
	structure Algebra = ALGEBRA (Make)
	structure Parser =  PARSER (Make)
	open Print
	    Parser
	    Algebra
	    Algebra.Make
	    Algebra.Make.Dupelim
	    Algebra.Make.Type 
	    Algebra.Make.Type.Common
	    Algebra.Make.Type.Common.BTS

	val _ = Base_symb := "";
	val dupelim = full_remdupl

	structure SR = SR
	structure DEST = DEST
    end; (* structure Orsml:orsig *)



val _ = System.PrettyPrint.install_pp ["Orsml","co"] Orsml.pp_co; 

val _ = System.PrettyPrint.install_pp ["Orsml","co_type"] Orsml.pp_co_type;
