(* ===================================================================== *)
(* FILE          : thy.sml                                               *)
(* DESCRIPTION   : Provides management of logical theories.              *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* REVISION      : July 17, 1997                                         *)
(* ===================================================================== *)


functor THEORY (structure Thm : Thm_sig
                structure Term : Term_sig
                structure Hol_pp : Hol_pp_sig
                structure RawParser : PARSER where type arg = Term.term vector
                structure PPTheory : PPTHeory_sig
                structure Graph : Theory_graph_sig
                  sharing type RawParser.result = Term.term
                  sharing Data.Thm = Thm = NewIO.Thm
                  sharing Thm.Term = Term = Hol_pp.Term
                  sharing type
                    Theory_ops.Theory_graph.node_id = 
                    Theory_ops.Theory_data.theory_id)
            : Theory_sig =
struct
structure Thm = Thm;

open Term;
open Data;
open Lib;
open Exception;
structure String = Portable.String;

fun THEORY_ERR{function,message} =
    HOL_ERR{origin_structure = "Theory",
		      origin_function = function,
		      message = message}

(*---------------------------------------------------------------------------
 * The data in a theory.
 *---------------------------------------------------------------------------*)
structure Uid = UID();

type theory_id = Uid.uid;
val mk_theory_id = Uid.re_mk_uid
val theory_id_name = Uid.name
val theory_id_timestamp = Uid.timestamp
val theory_id_eq = Uid.eq

local val mk_time = Portable.Time.mk_time
in
fun make_thy_id(s,i1,i2) = mk_theory_id
    {name=s,timestamp=mk_time{sec = Lib.string_to_int i1,
                              usec = Lib.string_to_int num2}}
end;

type type_record = {tyc:hol_type, arity :int, theory:string}
type term_record = {const:term, theory:string, place:Thm.Term.fixity};

type theory = { thid : theory_id,
                consistent_with_disk : bool,
                type_constants : type_record list,
                term_constants : term_record list,
                axioms : (string*Thm.thm) list,
                definitions : (string*Thm.thm) list,
                theorems : (string*Thm.thm) list};

(* extraction routines *)
fun theory_id (th:theory) = #thid th
fun theory_consistent_with_disk(th:theory) = (#consistent_with_disk th);
fun thy_types (th:theory) = (#type_constants th);
fun thy_constants (th:theory) = (#term_constants th);
fun theory_axioms (th:theory) = (#axioms th);
fun theory_definitions (th:theory) = (#definitions th);
fun theory_theorems (th:theory) = (#theorems th);

(* Alteration routines *)

fun set_consistency_with_disk b ({thid,consistent_with_disk,
                                  type_constants, term_constants, 
                                  axioms,definitions,theorems}:theory) = 
   {consistent_with_disk = b, thid = thid, 
    type_constants=type_constants,term_constants = term_constants,
    axioms=axioms,definitions = definitions, theorems = theorems};

fun add_type ty ({thid,consistent_with_disk, type_constants, term_constants, 
                  axioms,definitions,theorems}:theory) = 
   {type_constants = ty::type_constants,
    thid = thid, consistent_with_disk=consistent_with_disk, 
    term_constants = term_constants, axioms=axioms,
    definitions = definitions, theorems = theorems};

fun add_term tm ({thid,consistent_with_disk, type_constants, term_constants,
                  axioms,definitions,theorems}:theory) = 
   {term_constants = tm::term_constants,
    thid = thid, consistent_with_disk=consistent_with_disk,
    type_constants = type_constants, axioms=axioms,
    definitions = definitions, theorems = theorems};

local fun check ({axioms,definitions,theorems,...}:theory) s =
        (Lib.assoc s axioms; false)            handle NOT_FOUND
         => ((Lib.assoc s definitions; false)  handle NOT_FOUND
         => ((Lib.assoc s theorems; false)     handle NOT_FOUND => true))
      fun ALREADY_USED_ERR func name = THEORY_ERR{function = func, 
		      message = Lib.quote name^" is already in use as a name"}
in
fun add_axiom (ax as (s,_)) (thry as {thid,consistent_with_disk,
                                      d type_constants, term_constants, 
                                      axioms,definitions,theorems}:theory) = 
   if (check thry s)
   then {axioms = ax::axioms,
         thid = thid, consistent_with_disk = consistent_with_disk, 
         type_constants=type_constants, term_constants=term_constants,
         definitions = definitions, theorems = theorems}
   else raise ALREADY_USED_ERR "add_axiom" s

fun add_definition (def as (s,_)) 
                   (thry as {thid,consistent_with_disk,
                             type_constants, term_constants,axioms,
                             definitions,theorems}:theory) = 
   if (check thry s)
   then {definitions = def::definitions,
         thid = thid, consistent_with_disk = consistent_with_disk, 
         type_constants = type_constants, 
         term_constants = term_constants,axioms = axioms,
         theorems = theorems}
   else raise ALREADY_USED_ERR "add_definition" s

fun add_theorem (th as (s,_)) 
                (thry as {thid,consistent_with_disk,
                          type_constants, term_constants, axioms,
                          definitions,theorems}:theory) = 
   if (check thry s)
   then {theorems = th::theorems,
         thid = thid, consistent_with_disk = consistent_with_disk, 
         type_constants = type_constants, 
         term_constants = term_constants,axioms = axioms,
         definitions = definitions}
   else raise ALREADY_USED_ERR "add_theorem" s
end;


  
(*---------------------------------------------------------------------------
 * Make a fresh theory segment. The timestamp for a theory is its creation 
 * date. 
 *
 * "consistent_with_disk" is set to false because when a theory is created no
 * corresponding file gets created. The file is only created on export. 
 *---------------------------------------------------------------------------*)
fun fresh_theory s:theory =
   { thid = Uid.mk_uid s,
     consistent_with_disk = false,
     type_constants = [],
     term_constants = [],
     axioms = [],
     definitions = [],
     theorems = []}:theory;

(* The initial theory segment *)
val CT = ref (fresh_theory "");
fun the_current_theory() = !CT;
fun make_current thry = (CT := thry);


(*---------------------------------------------------------------------------
 * Adding into the current theory.
 *---------------------------------------------------------------------------*)

local
fun augment_ct f arg = 
   make_current(set_consistency_with_disk false (f arg (the_current_theory())))
in
  val add_parent_to_current_theory = augment_ct add_parent
  val add_type_to_current_theory = augment_ct add_type
  val add_term_to_current_theory = augment_ct add_term
  val add_axiom_to_current_theory = augment_ct add_axiom
  val add_definition_to_current_theory = augment_ct add_definition
  val add_theorem_to_current_theory = augment_ct add_theorem
  fun set_current_theory_disk_consistency b =
         make_current(set_consistency_with_disk b (the_current_theory()))
end;

val current_theory_id = theory_id o the_current_theory;
val current_theory_name = theory_id_name o current_theory_id;
fun draft_mode() = true;

 
(*---------------------------------------------------------------------------
 *            WRITING CONSTANTS 
 *---------------------------------------------------------------------------*)

local
fun write_type_constant {Name,Arity} = 
   if (draft_mode())
   then if (Lexis.allowed_type_constant Name)  
        then if (Type.is_st_type_const Name)
             then raise THEORY_ERR{function = "new_type.write_type_constant", 
                            message = Lib.quote Name^" already in symtab"}
             else let val tyr = {tyc = Type.Tyc Name, arity = Arity,
                                 theory = current_theory_name()}
                  in Type.add_entry tyr;
                     add_type_to_current_theory tyr
                  end
        else raise THEORY_ERR{function = "new_type.write_type_constant",
                      message = Lib.quote Name^" is not an allowed type name"}
   else raise THEORY_ERR{function = "new_type.write_type_constant",
                         message = "not in draft mode"}
in
val new_type = write_type_constant
end;


(*---------------------------------------------------------------------------
 * Add a type to the signature, first checking that it (or something close)
 * is not already there.
 *---------------------------------------------------------------------------*)
fun install_type(s,a,thy) = 
 let val {tyc,arity,theory} = Type.type_decl s 
 in if (a=arity andalso thy=theory}  then ()
     else (Lib.mesg true (String.concat
            ["Attempt to re-declare type ",Lib.quote s,
             ": the signature holds it to have arity ", 
             Lib.int_to_string arity, ", and it was declared in theory ",
             Lib.quote theory, 
              "; \n however, you are attempting to declare it with arity ",
             Lib.int_to_string a, " in the theory ", Lib.quote thy]);
           raise THEORY_ERR{function="install_type",message=""})
 end
 handle (HOL_ERR{origin_structure="Type",origin_function="type_decl",...})
         => Type.add_entry {tyc=Type.Tyc name, arity=arity, theory=thy};

local
fun infixx s ty =
   let val{Tyop="fun", Args=[_,ty2]} = Type.dest_type ty
       val{Tyop="fun", Args=[_,_]}   = Type.dest_type ty2
   in   () end
   handle _ => raise THEORY_ERR {function = s, message = "not an infix type"}
fun binder s ty =
   let val {Tyop="fun", Args=[ty1,_]} = Type.dest_type ty
       val {Tyop="fun", Args=[_,_]}   = Type.dest_type ty1
   in   () end
   handle _ => raise THEORY_ERR {function = s, message = "not a binder type"}
fun write_constant err_str fixity (c as {Name,Ty}) =
 ( case fixity
     of Prefix => ()
      | Binder => binder err_str Ty;
      | Infix prec => 
         (infixx err_str Ty;
          if (prec < 0)
          then raise THEORY_ERR {function = err_str,
                                 message = "precedence must be positive"}
          else ())
   if (Lexis.allowed_term_constant Name) then ()
   else raise THEORY_ERR {function = err_str,
                 message = Lib.quote Name^ " is not an allowed constant name"};
   if (not (draft_mode()))
   then raise THEORY_ERR {function = err_str, message = "not in draft mode"}
   else ();
   if (Term.is_st_term_const Name)
   then raise THEORY_ERR{function = err_str,
                       message = Lib.quote Name^" is already in symbol table"}
   else let val trec = { const = Const c, theory = current_theory_name(),
                         place = fixity }
            val dollared_trec = { const = Const{Name = "$"^Name, Ty=Ty},
                                  theory = current_theory_name(), place=Prefix}
        in (* Add to symtab *)
           Term.add_term_const Term.Defining trec; 
           (* Add to current theory *)
           add_term_to_current_theory trec;
           add_term_to_current_theory dollared_trec
        end)
in
val new_constant = write_constant "new_constant" Prefix
val new_binder = write_constant "new_binder" Binder
fun new_infix{Name,Ty,Prec} = write_constant "new_infix" (Infix Prec) 
                                             {Name=Name,Ty=Ty}
end;

(*---------------------------------------------------------------------------
 * Add a constant to the signature, first checking that it (or something close)
 * is not already there.
 *---------------------------------------------------------------------------*)
fun install_const(s,ty,f,thy) = 
 let val {const,place,theory} = Term.const_decl s 
     val sty = type_of const
 in if (ty=sty andalso thy=theory andalso place=f}  then ()
     else (Lib.mesg true (String.concat
            ["Attempt to re-declare term ",Lib.quote s,
             ": the signature holds it to have type ", 
             Lib.quote(Hol_pp.pp_type sty), " with fixity ", 
             Lib.quote(Term.fixity_to_string place),
             ", and it was declared in theory ",
             Lib.quote theory, 
              "; \n however, you are attempting to declare it with type ",
             Lib.quote(Hol_pp.pp_type ty), " and with fixity ", 
             Lib.quote(Term.fixity_to_string f),
            " in the theory ", Lib.quote thy]);
           raise THEORY_ERR{function="install_const",message=""})
 end
 handle (HOL_ERR{origin_structure="Term",origin_function="const_decl",...})
         => add_term_const Term.Loading
                  {const=Const{Name=s, Ty=ty}, theory=thy, place=f};


(*---------------------------------------------------------------------------
 *     WRITING AXIOMS, DEFINITIONS, AND THEOREMS  
 *---------------------------------------------------------------------------*)
local
fun check_draft_mode s = 
   if (draft_mode()) then () 
   else raise THEORY_ERR{function = s,message = "not in draft mode"};
fun check_bool s tm = 
   if (type_of tm = Type.mk_type{Tyop = "bool", Args = []}) then () 
   else raise THEORY_ERR {function = s,message = "not a formula"};
fun check_name (fname,s) = 
     if (Lexis.ok_thy_index s) then ()
     else raise THEORY_ERR {function = fname,
                            message = Lib.quote s^" not allowed as name"}
fun empty_hyp th = 
   if (Portable.List.null (Thm.hyp th)) then () 
   else raise THEORY_ERR{function = "save_thm",
                         message = "non empty assumption set"}
in
fun new_open_axiom (name,tm) = 
   let val ax = Thm.mk_axiom_thm([],tm)
   in 
     check_name ("new_open_axiom",name);
     check_draft_mode "new_open_axiom";
     check_bool "new_open_axiom" tm;
     add_axiom_to_current_theory(name,ax);
     ax 
   end
fun store_definition(name,tm) =
   ( check_name ("store_definition",name);
     check_draft_mode "store_definition";
     check_bool "store_definition" tm;
     let val def = Thm.mk_definition_thm([],tm)
     in
       add_definition_to_current_theory(name,def);  def
     end
   )
(*---------------------------------------------------------------------------
 * The check_bool is for mk_thm'd things; mk_thm doesn't check that its 
 * args are of type :bool
 *---------------------------------------------------------------------------*)
fun save_thm (name,th) =
   ( check_name ("save_thm",name);
     check_bool "save_thm" (Thm.concl th);
     if (!Globals.allow_theorems_with_assumptions)
     then ()
     else empty_hyp th;
     add_theorem_to_current_theory(name,th);
     th )
end;


(*---------------------------------------------------------------------------
 *        INFORMATION ON CONSTANTS 
 *---------------------------------------------------------------------------*)
val arity = Type.arity_of_type;

val fixity = Term.fixity_of_term
and precedence = Term.prec_of_term;

val is_constant = Term.is_st_term_const
and is_type = Type.is_st_type_const;

val is_binder = Term.is_binder
val is_infix = Term.is_infix

val const_decl = Term.const_decl


(*---------------------------------------------------------------------------
 * The theory graph
 *---------------------------------------------------------------------------*)
structure Graph = 
    DAG(structure Node =
        struct
            type node_id = theory_id
            val node_name = theory_id_name
            val node_eq = Lib.curry theory_id_eq
         end);

(*---------------------------------------------------------------------------
 * Add a theory to the theory graph, first making a few checks. This 
 * operation does not affect the current theory.
 *---------------------------------------------------------------------------*)
fun add_theory (tr,L) =
  let val node = make_thy_id tr
      val parents = map make_thy_id L
      val fringe = Graph.fringe()
  in if Lib.all (fn p => Lib.op_mem Graph.node_eq p fringe) parents
     then Graph.add_node node parents
     else (Lib.mesg true "add_theory: some parents are not in the fringe";
           raise THEORY_ERR{function="add_theory", message=""})
  end;



(*---------------------------------------------------------------------------
 * READING INFORMATION FROM THE CURRENT THEORY
 *---------------------------------------------------------------------------*)
local
val infixed = is_infix o #Name o dest_const
val bindered = is_binder o #Name o dest_const
fun convert_type_recd{tyc=Type.Tyc s, arity, theory} = {Name=s, Arity=arity}
fun convert_term_recd{const,theory,place} = const
fun grab_item style name alist =
   case (Lib.assoc1 name alist)
     of (SOME (_,th)) => th
      | NONE => raise THEORY_ERR{function = style,
                     message = "couldn't find "^style^" named "^Lib.quote name}
in
fun parents "-" = map theory_id_name(Graph.fringe()) 
  | parents str = map theory_id_name(Graph.parents str) handle NOT_FOUND
                  => raise THEORY_ERR{function = "parents",
                              message = Lib.quote str^" not in theory graph."}
val types = map convert_type_recd o thy_types o current_theory
val constants = map convert_term_recd o thy_constants o current_theory
val infixes = Lib.gather infixed o constants
val binders = Lib.gather bindered o constants
val axioms = theory_axioms o current_theory
and definitions = theory_definitions o current_theory
and theorems = theory_theorems o current_theory
end;

fun ancestry "-" = map theory_id_name (Graph.ancestry (current_theory_name()))
  | ancestry s = map theory_id_name (Graph.ancestry s);


(*---------------------------------------------------------------------------
 * Printing theories out as structures and signatures.
 *---------------------------------------------------------------------------*)
fun theory_out f {name,style} ostrm =
 let val ppstrm = PP.mk_ppstream{consumer = Portable.outputc ostrm,
                      linewidth=78, flush = fn () => Portable.flush_out ostrm}
 in f ppstrm handle e 
    => (Portable.output(Portable.std_out,Portable.String.concat
          ["Failure while writing ",style," for theory: ",name,"!\n"]);
        Portable.close_out ostrm
        raise e);
    PP.flush_ppstream ppstrm;
    Portable.close_out ostrm
 end;
    

fun export_theory() = 
  if theory_consistent_with_disk(the_current_theory())
  then Lib.say ("\nTheory "^Lib.quote(current_theory_name())^" already \
                    \consistent with disk, hence not exported.\n")
  else
  let val concat = Portable.String.concat
      val thry =    {name = name,
                  parents = Graph.fringe(),
                    types = types(),
                constants = constants(),
                   axioms = axioms (),
              definitions = definitions(),
                 theorems = theorems ()}
      val ostrm1 = Portable.open_out(concat["./",name,".sig"])
      val ostrm2 = Portable.open_out(concat["./",name,".sml"])
  in
   theory_out (fn ppstrm => NewIO.pp_theory_sig ppstrm thry)
              {name = name, style = "signature"} ostrm1;
   theory_out (fn ppstrm => NewIO.pp_theory_struct ppstrm thry)
              {name = name, style = "structure"} ostrm2;
   Lib.say ("\nTheory "^Lib.quote(current_theory_name())^" exported.\n");
  end;


(*---------------------------------------------------------------------------
 *    THEORY OPERATIONS 
 *---------------------------------------------------------------------------*)

local fun check str =
      if (mem str (current_theory_name()::ancestry"-"))
      then raise THEORY_ERR{function = "new_theory",
			 message = "theory: "^Lib.quote str^" already exists."}
   else if Lexis.ok_identifier str then ()
        else raise THEORY_ERR{function = "new_theory",
       message = "proposed theory name "^Lib.quote str^" is not an identifier"}
in
fun new_theory "min" = 
       ( make_current(fresh_theory "min");
         Theory_graph.add_node (current_theory_id()) [];
         Lib.say ("\nTheory "^Lib.quote "min"^" declared.\n")
       )
  | new_theory str =
       ( check str;
         Lib.say ("\nDeclaring theory "^Lib.quote str^".\n");
         export_theory();
         let val p = current_theory_id()
         in  make_current(fresh_theory str);
             Graph.add_node p (Graph.fringe())
         end
       )
end;

val current_theory = current_theory_name;

local val std_out = Portable.std_out
      val output = Portable.output
      val flush_out = Portable.flush_out
      val concat = Portable.String.concat
in 
fun loadLibThry libname thyname =
  let val thy_dir = concat[!Globals.HOLdir, "library/", libname, "/theories/",
                           SysParams.theory_file_type, "/"]
      val () = if (Lib.mem thy_dir (!Globals.theory_path)) then ()
                else Lib.cons_path thy_dir Globals.theory_path
  in
  if (Lib.mem thyname (current_theory()::ancestry"-")) 
      then (output(std_out, concat 
             ["Theory ", Lib.quote thyname, " is already present.\n"]);
            flush_out std_out)
      else if draft_mode() 
            then Lib.try new_parent thyname
           else Lib.try load_theory thyname
  end
end;


local fun error (s,_,_) = 
    raise HOL_ERR{origin_structure = "",
                  origin_function="Raw term parser",  message=s}
in
fun raw_term_parser tbl [QUOTE s] =
   let val strm = Portable.open_string s
       val lexer = RawParser.makeLexer (fn _ => Portable.input_line strm)
       val (res,_) = RawParser.parse(0,lexer,error,tbl)
   in res
   end
end;



(* Print a theory *)


val CONSISTENT = PP.CONSISTENT
val INCONSISTENT = PP.INCONSISTENT;

fun pp_theory ppstrm({thid,consistent_with_disk,type_constants,
                      term_constants,axioms,definitions,theorems,...}:theory) =
   let val {add_string,add_break,begin_block,end_block,
            add_newline,flush_ppstream,...} = PP.with_ppstream ppstrm
       fun vblock(header, ob_pr, obs) =
             ( begin_block CONSISTENT 4;
               add_string (header^":");
               add_newline();
               PP.pr_list ob_pr (fn () => ()) add_newline obs;
               end_block();
               add_newline();
               add_newline())
       val theory_name = Uid.name thid
       val parental_units = parents theory_name
       val pp_type = Hol_pp.pp_type ppstrm
       fun is_dollared s = (String.ordof(s,0) = String.ordof("$",0))
       val pp_thm = Thm.pp_thm ppstrm
       fun pr_thm (heading, ths) =
          vblock(heading, (fn (s,th) => 
            (begin_block CONSISTENT 0; add_string s; add_break(1,0);
                pp_thm th; end_block())),  ths)
       fun pp_consistency b = 
          if theory_id_eq(thid, theory_id(the_current_theory()))
          then add_string ("Theory "^(Lib.quote theory_name)^" is "^
                          (if b then "consistent" else "inconsistent")^
                          " with disk.\n")
          else ()
   in begin_block CONSISTENT 0;
        add_string ("Theory: "^theory_name);
        add_newline(); 
        add_newline()
        ;
        vblock ("Parents",(fn id => add_string (Uid.name id)), parental_units)
        ;
        vblock ("Type constants", 
                (fn({tyc,arity,theory})
                 => (pp_type tyc;
                     add_string (" "^Lib.int_to_string arity))),
                (rev type_constants))
        ;
        vblock ("Term constants", 
                (fn({const,place,theory})
                 => let val {Name,Ty} = Thm.Term.dest_const const
                    in begin_block CONSISTENT 0;
                       add_string (Name^" ");
                       add_string ("("^Term.fixity_to_string place^")");
                       add_break(3,0);
                       add_string ":";
                       pp_type Ty;
                       end_block()
                    end),
                Lib.gather(fn {const,place,theory} =>
			   not (is_dollared 
				(#Name(Thm.Term.dest_const const))))
                          (rev term_constants))
        ;
        pr_thm ("Axioms", rev axioms);
        pr_thm ("Definitions", rev definitions);
        pr_thm ("Theorems", rev theorems);
        pp_consistency consistent_with_disk;
      end_block();
      flush_ppstream()
   end;


(*fun print_theory_to_outstream {outstream, theory} =
    let	val def_Cons = PP.defaultConsumer()
	val consumer = {consumer = Portable.outputc outstream,
			flush = #flush def_Cons,
			linewidth = #linewidth def_Cons}
	val _ = pp_theory (PP.mk_ppstream consumer)
	                  (Theory_ops.grab_ances_theory theory)
	val _ = Portable.flush_out outstream
    in outstream end

fun print_theory_to_file {file, theory} =
    let val outfile = Portable.open_out file
    in Portable.close_out (print_theory_to_outstream {outstream = outfile,
					     theory = theory})
    end
*)
fun print_theory () = 
   pp_theory (PP.mk_ppstream(PP.defaultConsumer()))
             (current_theory())

end; (* THEORY *)
