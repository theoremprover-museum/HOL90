(* =====================================================================*)
(* FILE          : hol_db_datatype.sml                                  *)
(* DESCRIPTION   : signature and structure for coercing hol theories    *)
(*                 into nested_relational databases.                    *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter                                          *)
(*                                                                      *)
(* DATE          : 94.08.08                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature HolDbDataSig =
    sig
	datatype hol_theory_data =
	    Type of hol_type
	  | Term of term
	  | Thm of thm
	  | Parent of {thy_name : string, parent : string}
	  | TypeOp of {thy_name : string, tyop :{Name : string, Arity : int}}
	  | Constant of {thy_name : string, constant : term}
	  | Infix of {thy_name : string, constant : term}
	  | Binder of {thy_name : string, constant : term}
	  | Axiom of {thy_name : string, theorem : (string * thm)}
	  | Definition of {thy_name : string, theorem : (string * thm)}
	  | StoredThm of {thy_name : string, theorem :(string * thm)}
        eqtype base
	sharing type base = hol_theory_data
	val eq_base : ''a * ''a -> bool
	val hash_base : 'a -> int
(*	val install_pp : unit -> unit *)
	val leq_base : ''a * ''a -> bool
	val name_base : string
	val pp_base : System.PrettyPrint.ppstream -> hol_theory_data -> unit
	val string_of_base : hol_theory_data -> string
	val theory_to_data : string -> hol_theory_data list
	val parse_base : string -> base
    end


structure HolDbData:HolDbDataSig =
    struct

	datatype hol_theory_data =
	    Type of hol_type
	  | Term of term
	  | Thm of thm
	  | Parent of {thy_name : string, parent : string}
	  | TypeOp of {thy_name : string, tyop :{Name : string, Arity : int}}
	  | Constant of {thy_name : string, constant : term}
	  | Infix of {thy_name : string, constant : term}
	  | Binder of {thy_name : string, constant : term}
	  | Axiom of {thy_name : string, theorem : (string * thm)}
	  | Definition of {thy_name : string, theorem : (string * thm)}
	  | StoredThm of {thy_name : string, theorem :(string * thm)}

	type base = hol_theory_data

	fun leq_base (x, y) = (x = y)

	val name_base = "hol_theory_data"

	val eq_base = (op =)

	fun hash_base x = 0

	local
	open System.PrettyPrint
	fun with_ppstream ppstrm = 
	    {add_string=System.PrettyPrint.add_string ppstrm, 
	     add_break=System.PrettyPrint.add_break ppstrm, 
	     begin_block=System.PrettyPrint.begin_block ppstrm, 
	     end_block=fn () => System.PrettyPrint.end_block ppstrm, 
	     add_newline=fn () => System.PrettyPrint.add_newline ppstrm, 
	     clear_ppstream=fn () =>
	     System.PrettyPrint.clear_ppstream ppstrm, 
	     flush_ppstream=fn () => System.PrettyPrint.flush_ppstream ppstrm}
	in
	fun pp_base ppstrm hol_data =
	let
	    val {add_string,add_break,begin_block,end_block,
		 add_newline,flush_ppstream,...} = with_ppstream ppstrm
	    val bbc = begin_block CONSISTENT
	    val bbi = begin_block INCONSISTENT
	    val eb = end_block
	    val S = add_string 
	    fun lparen() = S "("
	    fun rparen() = S ")"
	    fun lbracket() = S "{"
	    fun rbracket() = S"}"
	    fun string s = S ("\""^s^"\"")
	    fun comma() = S ","
	    fun colon() = S ":"
	    fun label l = S (l^" = ")
	    fun space() = add_break(1,0)
	    fun pp_tm tm = (S (!Globals.term_pp_prefix);S "`";
			    pp_term ppstrm tm;
			    S (!Globals.term_pp_suffix);S "`")
	    fun pp_ty ty = (S (!Globals.type_pp_prefix);S "`";colon();
			    pp_type ppstrm ty (!Globals.max_print_depth);
			    S "`";S (!Globals.type_pp_suffix))
	    fun add_base (Type ty) =
		(bbc 1; S "Type"; space(); lparen(); pp_ty ty; rparen(); eb())
	      | add_base (Term tm) =
		(bbc 1; S "Term"; space(); lparen(); pp_tm tm; rparen(); eb())
	      | add_base (Thm thm) =
		(bbc 1; S "Thm"; space();
		 lparen(); pp_thm ppstrm thm; rparen(); eb())
	      | add_base (Parent {thy_name,parent}) =
		(bbc 1;S "Parent"; space();
		 lbracket();label "parent"; string parent; comma();space();
		 label "thy_name"; string thy_name;rbracket();
		 eb())
	      | add_base (TypeOp {thy_name, tyop = {Name, Arity}}) = 
		(bbc 1;S "TypeOp";
		 lbracket();label "tyop";
		 lbracket();label "Name"; string Name; comma();space();
		 label "Arity"; S(Lib.int_to_string Arity);rbracket();
		 comma();space();
		 label "thy_name"; string thy_name;rbracket();
		 eb())
	      | add_base (Constant {thy_name,constant}) =
		(bbc 1;S "Constant"; lbracket();
		 label "constant"; pp_tm constant; comma(); space();
		 label "thy_name"; string thy_name;
		 rbracket(); eb())
	      | add_base (Binder{thy_name, constant}) =
		(bbc 1;S "Binder"; lbracket();
		 label "constant";pp_tm constant; comma(); space();
		 label "thy_name"; string thy_name;
		 rbracket(); eb())
	      | add_base (Infix{thy_name, constant}) =
		(bbc 1;S "Infix"; lbracket();
		 label "constant";pp_tm constant; comma(); space();
		 label "thy_name"; string thy_name;
		 rbracket(); eb())
	      | add_base (Axiom {thy_name, theorem = (Name, thm)}) =
		(bbc 1;S "Axiom"; lbracket();
		 label "theorem"; lparen();string Name; comma(); space();
		 pp_thm ppstrm thm; rparen(); comma(); space();
		 label "thy_name"; string thy_name;
		 rbracket(); eb())
	      | add_base (Definition {thy_name, theorem = (Name, thm)}) =
		(bbc 1;S "Definition"; lbracket();
		 label "theorem";  lparen();string Name; comma(); space();
		 pp_thm ppstrm thm; rparen(); comma(); space();
		 label "thy_name"; string thy_name;
		 rbracket(); eb())
	      | add_base (StoredThm {thy_name, theorem = (Name, thm)}) =
		(bbc 1;S "StoredThm"; lbracket();
		 label "theorem"; lparen();string Name; comma(); space();
		 pp_thm ppstrm thm; rparen(); comma(); space();
		 label "thy_name"; string thy_name;
		 rbracket(); eb())
	in
		 bbi 0; add_base hol_data; eb()
	end
	end
(*
	fun install_pp () = System.PrettyPrint.install_pp
	          ["HolDbData","hol_theory_data"] pp_base
*)

	val string_of_base = System.PrettyPrint.pp_to_string 70 pp_base

	fun theory_to_data thy =
	   (* {parents = *)
	       map (fn s => Parent{thy_name=thy,parent=s}) (parents thy) @
	   (*  types = *)
	       map (fn s => TypeOp{thy_name=thy,tyop=s}) (types thy) @
	   (*  constants = *)
	       map (fn s => Constant{thy_name=thy,constant=s}) (constants thy)@
	   (*  infixes = *)
	       map (fn s => Infix{thy_name=thy,constant=s}) (infixes thy) @
	   (*  binder = *)
	       map (fn s => Binder{thy_name=thy,constant=s}) (binders thy) @
	   (*  axioms = *)
	       map (fn s => Axiom{thy_name=thy,theorem=s}) (axioms thy) @
	   (*  definitions = *)
	       map (fn s => Definition{thy_name=thy,theorem=s})
	           (definitions thy) @
	   (*  theorems = *)
	       map (fn s => StoredThm{thy_name=thy,theorem=s}) (theorems thy)


	fun parse_base _ = Raise (HOL_ERR{origin_structure = "HolDbData",
					  origin_function = "parse_base",
					  message = "No parser is given."})

    end

