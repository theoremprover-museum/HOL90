(* ===================================================================== *)
(* FILE          : theory.sml                                            *)
(* DESCRIPTION   : Provides management of logical theories.              *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


functor THEORY (structure Thm : Thm_sig
                structure Term : Term_sig
                structure Globals : Globals_sig
                structure Hol_pp : Hol_pp_sig
                structure Theory_ops : Theory_ops_sig
                sharing
                  Theory_ops.Theory_data.Thm = Thm
                sharing
                  Thm.Term = Term = Hol_pp.Term
                sharing type
                  Theory_ops.Theory_graph.node_id = 
                  Theory_ops.Theory_data.theory_id
                sharing type
                  Theory_ops.Theory_cache.key = string)
            : Theory_sig =
struct
structure Thm = Thm;

open Term;
open Theory_ops;
open Theory_data;
open Lib;
open Exception;

fun THEORY_ERR{function,message} =
    HOL_ERR{origin_structure = "Theory",
		      origin_function = function,
		      message = message}

 
(* Adding into the current theory *)

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
fun set_current_theory_draft_mode b =
       make_current(set_draft_mode b (the_current_theory()))
fun set_current_theory_disk_consistency b =
       make_current(set_consistency_with_disk b (the_current_theory()))
end;

val draft_mode = Theory_data.theory_draft_mode o the_current_theory
val current_theory_id = theory_id o the_current_theory;
val current_theory_name = theory_id_name o current_theory_id;

(* WRITING CONSTANTS *)

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


local
fun infixx s ty =
   let val{Tyop = "fun", Args = [_,ty2]} = Type.dest_type ty
       val{Tyop = "fun", Args = [_,_]} = Type.dest_type ty2
   in   ()
   end
   handle _ => raise THEORY_ERR {function = s, message = "not an infix type"}
fun binder s ty =
   let val {Tyop = "fun", Args = [ty1,_]} = Type.dest_type ty
       val {Tyop = "fun", Args = [_,_]} = Type.dest_type ty1
   in   ()
   end
   handle _ => raise THEORY_ERR {function = s, message = "not a binder type"}
fun write_constant err_str fixity (c as {Name,Ty}) =
 ( case fixity
     of Prefix => ()
      | (Infix prec) => 
         (infixx err_str Ty;
          if (prec < 0)
          then raise THEORY_ERR {function = err_str,
                                 message = "precedence must be positive"}
          else ())
      | Binder => binder err_str Ty;

   if (Lexis.allowed_term_constant Name)
   then ()
   else raise THEORY_ERR {function = err_str,
                 message = Lib.quote Name^ " is not an allowed constant name"};
   if (not (draft_mode()))
   then raise THEORY_ERR {function = err_str,
			  message = "not in draft mode"}
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


(* WRITING AXIOMS, DEFINITIONS, AND THEOREMS  *)
local
fun check_draft_mode s = 
   if (draft_mode())
   then () 
   else raise THEORY_ERR{function = s,message = "not in draft mode"};
fun check_bool s tm = 
   if (type_of tm = Type.mk_type{Tyop = "bool", Args = []}) 
   then () 
   else raise THEORY_ERR {function = s,message = "not a formula"};
fun check_name (fname,s) = 
     if (Lexis.ok_thy_index s) then ()
     else raise THEORY_ERR {function = fname,
                            message = Lib.quote s^" not allowed as name"}
fun empty_hyp th = 
   if (Portable.List.null (Thm.hyp th)) 
   then () 
   else raise THEORY_ERR{function = "save_thm",
                         message = "non empty assumption set"}
(* change genvar'ed names to normal names *)
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


(* INFORMATION ON CONSTANTS *)
val arity = Type.arity_of_type;

val fixity = Term.fixity_of_term
and precedence = Term.prec_of_term;

val is_constant = Term.is_st_term_const
and is_type = Type.is_st_type_const;

val is_binder = Term.is_binder
val is_infix = Term.is_infix

val const_decl = Term.const_decl


(* READING INFORMATION FROM A THEORY *)
local
val infixed = is_infix o #Name o Thm.Term.dest_const
val bindered = is_binder o #Name o Thm.Term.dest_const
fun convert_from_type_record{tyc = Type.Tyc name, arity, theory} = 
           {Name = name, Arity = arity}
fun convert_from_term_record({const,theory,place}) = const
fun grab_item style name alist =
   case (Lib.assoc1 name alist)
     of (SOME (_,th)) => th
      | NONE => raise THEORY_ERR{function = style,
                     message = "couldn't find "^style^" named "^Lib.quote name}
in
fun parents "-" = parents (current_theory_name())
  | parents str = map theory_id_name(Theory_graph.parents str)
                  handle NOT_FOUND
                  => raise THEORY_ERR{function = "parents",
                              message = Lib.quote str^" not in theory graph."}
val types = map convert_from_type_record o 
            theory_type_constants o Theory_ops.grab_ances_theory
val constants = map convert_from_term_record o 
                theory_term_constants o Theory_ops.grab_ances_theory
val infixes = Lib.gather infixed o constants
and binders = Lib.gather bindered o constants
val axioms = theory_axioms o Theory_ops.grab_ances_theory
and definitions = theory_definitions o Theory_ops.grab_ances_theory
and theorems = theory_theorems o Theory_ops.grab_ances_theory
fun axiom thry_str name = grab_item "axiom" name (axioms thry_str)
and definition thry name = grab_item "definition" name (definitions thry)
and theorem thry_str name = grab_item "theorem" name (theorems thry_str)
end;

fun print_theory_to_outstream {outstream, theory} =
    let	val def_Cons = PP.defaultConsumer()
	val consumer = {consumer = Portable.outputc outstream,
			flush = #flush def_Cons,
			linewidth = #linewidth def_Cons}
	val _ = Theory_data.pp_theory (PP.mk_ppstream consumer)
	                              (Theory_ops.grab_ances_theory theory)
	val _ = Portable.flush_out outstream
    in outstream end

fun print_theory_to_file {file, theory} =
    let val outfile = Portable.open_out file
    in Portable.close_out (print_theory_to_outstream {outstream = outfile,
					     theory = theory})
    end


fun print_theory s = 
   Theory_data.pp_theory (PP.mk_ppstream(PP.defaultConsumer()))
                         (Theory_ops.grab_ances_theory s)

fun ancestry "-" = ancestry(current_theory_name())
  | ancestry s = map Theory_data.theory_id_name (Theory_graph.ancestry s);


(* THEORY OPERATIONS *)

fun new_parent "" = raise THEORY_ERR{function = "new_parent",
                                     message = "empty theory name not allowed"}
  | new_parent "-" = raise THEORY_ERR{function = "new_parent",
                        message= "\"-\" denotes current theory; a theory \
                                 \ cannot be a parent of itself"}
  | new_parent str =
    if (draft_mode())
    then if (str = current_theory_name())
         then raise THEORY_ERR{function = "new_parent",
                               message = "self-parenting is not allowed"}
         else if (Lib.mem str (ancestry "-"))
            then ()
          else 
       Theory_ops.perform_atomic_theory_op
       (fn () =>
        let val {data = hol_sig,...} = Theory_io.get_hol_sig_by_name
                                         (!Globals.theory_path) str
            val {thid,...} = Theory_io.dest_hol_sig hol_sig
        in
           Theory_ops.install_new_parent (current_theory_name(),hol_sig)
           handle HOL_ERR{origin_function = function,message,...}
           => raise THEORY_ERR
                    {function = "new_parent.install_new_parent."^function,
                     message = message}
           ;
           add_parent_to_current_theory thid
           ;
           Theory_graph.add_parent (current_theory_id()) thid
        end)
    else raise THEORY_ERR{function = "new_parent",message="not in draft mode"};


local
fun check str =
   if (mem str (current_theory_name()::ancestry"-"))
   then raise THEORY_ERR{function = "new_theoryn",
			 message = "theory: "^Lib.quote str^" already exists."}
   else 
   if Lexis.ok_identifier str
   then ()
   else raise THEORY_ERR{function = "new_theory",
      message = "proposed theory name "^Lib.quote str^" is not an identifier"}
in
fun new_theory "" = raise THEORY_ERR{function = "new_theory",
                                     message = "empty theory name not allowed"}
  | new_theory "-" = raise THEORY_ERR{function = "new_theory",
                 message = Lib.quote"-"^" is not allowed as a new theory name"}
  | new_theory "min" = 
       ( make_current(fresh_theory "min");
         Theory_graph.add_node (current_theory_id()) [];
         Lib.say ("\nTheory "^Lib.quote "min"^" declared.\n")
       )
  | new_theory str =
       ( check str;
         Lib.say ("\nDeclaring theory "^Lib.quote str^".\n");
         Theory_ops.export_theory();
         let val p = current_theory_id()
         in  make_current(fresh_theory str);
             add_parent_to_current_theory p;
             Theory_graph.add_node (current_theory_id()) [p]
         end
       )
end;



fun close_theory() = 
   ( set_current_theory_draft_mode false;
     Lib.say ("\nTheory "^Lib.quote(current_theory_name())^" closed.\n"));


fun print_load_message s thry_str= 
   let val info_str = if (s = "load_theory") then "Loading" else "Extending"
   in Lib.say ("\n"^info_str^" theory "^Lib.quote thry_str^"\n")
   end;


(* Brings a an entire theory in, not just the hol_sig.  *)
fun haul_in str load_or_extend =
   (print_load_message load_or_extend str;
    if (str = "min")  (* only when reusing theory files *)
    then ()
    else Theory_ops.export_theory();     (* May have stored a thm *)
    Theory_data.make_current             (* Make the leap *)
       (Theory_ops.perform_atomic_theory_op
           (fn () => (Theory_ops.goto_theory str (current_theory_id()))));
    set_current_theory_draft_mode (load_or_extend = "extend_theory"))


(*---------------------------------------------------------------------------
 * load_theory is a "goto" statement in the theory graph. But you can 
 * only prove theorems when you get there. Not allowed to load a parent.
 *---------------------------------------------------------------------------*)
fun load_theory "" = raise THEORY_ERR{function = "load_theory",
			      message = "empty theory name not allowed"}
  | load_theory "-" = raise THEORY_ERR{function = "load_theory",
             message = "\"-\" denotes current theory. You are already there."}
  | load_theory str =
      if (draft_mode())
      then raise THEORY_ERR{function = "load_theory",
                            message = "no theory is the descendant of a draft"}
      else if (str = current_theory_name())
           then raise THEORY_ERR{function = "load_theory",
				 message = "cannot load self"}
           else haul_in str "load_theory";

(*---------------------------------------------------------------------------
 * extend_theory is a "goto" statement in the theory graph. You can 
 * do anything you want when you get there.
 *---------------------------------------------------------------------------*)
fun extend_theory "" = raise THEORY_ERR{function = "extend_theory",
                                     message = "empty theory name not allowed"}
  | extend_theory "-" = extend_theory (current_theory_name())
  | extend_theory str =
      if (draft_mode())
      then raise THEORY_ERR{function = "extend_theory",
                            message = "no theory is the descendant of a draft"}
      else if (str = current_theory_name())
           then (Lib.say ("\nExtending theory "^Lib.quote str^"\n");
                 set_current_theory_draft_mode true)
           else haul_in str "extend_theory";


val draft_mode = Theory_data.theory_draft_mode o the_current_theory
val current_theory = current_theory_name;

val export_theory = Theory_ops.export_theory;
val close = Theory_ops.close;

val delete_theory_from_cache = Theory_cache.delete_object_from_cache;
val delete_cache = Theory_cache.delete_cache;
val theories_in_cache = Theory_cache.objects_in_cache;

val perform_atomic_theory_op = Theory_ops.perform_atomic_theory_op;


(*---------------------------------------------------------------------------
 * HTML view of a theory. Assumes that "-" has already been expanded, since
 * "-.html" is hard for Unix commands like "rm" to deal with
 *---------------------------------------------------------------------------*)
fun theory_to_html ppstrm theory_name =
   let val {parents,type_constants,term_constants,axioms,definitions,theorems}
            = {parents = parents theory_name,
               type_constants = types theory_name,
               term_constants = constants theory_name,
               axioms = axioms theory_name,
               definitions = definitions theory_name,
               theorems = theorems theory_name}
       val {add_string,add_break,begin_block,end_block,
            add_newline,flush_ppstream,...} = PP.with_ppstream ppstrm
       fun is_dollared s = (Portable.String.ordof(s,0) 
                            = Portable.String.ordof("$",0))
       fun strong s = (add_string"<STRONG>"; add_string s; 
                       add_string"</STRONG>")
       fun title s = add_string("<H1>"^s^"</H1>");
       fun link (l,s) = (add_string("<A HREF = "^Lib.quote l^">");
                         strong s;
                         add_string"</A>")
       fun HR() = (add_newline();add_string"<HR>";add_newline());

       fun vblock(header, ob_pr, obs) =
             ( begin_block PP.CONSISTENT 4;
               title header;
               add_newline();
               add_string"<UL>"; add_newline();
               PP.pr_list (fn x => (add_string"<LI>"; ob_pr x))
                          (fn () => ()) add_newline obs;
               add_newline();
               add_string"</UL>";
               end_block();
               add_newline();
               add_newline())

       fun dl_block(header, ob_pr, obs) =
             ( begin_block PP.CONSISTENT 0;
               title header;
               add_newline();
               add_string"<DL>"; add_newline();
               PP.pr_list 
                (fn (x,ob) => 
                     (begin_block PP.CONSISTENT 0;
                      add_string"<DT>"; strong x; add_newline();
                      add_string"<DD>"; add_newline();
                      ob_pr ob;
                      end_block()))
                (fn () => ()) add_newline obs;
               add_newline();
               add_string"</DL>";
               end_block();
               add_newline();
               add_newline())

       val pp_type = Hol_pp.pp_type ppstrm
       fun fixity_to_string(Thm.Term.Infix i)  = "Infix "^(Lib.int_to_string i)
         | fixity_to_string Thm.Term.Prefix = "Prefix"
         | fixity_to_string Thm.Term.Binder = "Binder"
       val pp_thm = Thm.pp_thm ppstrm
       fun pr_thm (heading, ths) = dl_block(heading, 
           (fn th => (begin_block PP.CONSISTENT 0;
                      add_string"<PRE>";
                      add_newline();
                      pp_thm th;
                      add_newline();
                      add_string"</PRE>";
                      add_newline();
                      end_block())),    ths)
   in begin_block PP.CONSISTENT 0;
         add_string("<TITLE>Theory: "^theory_name^"</TITLE>");
         add_newline();
         add_string("<H1>Theory: "^theory_name^"</H1>");
         add_newline()
         ;
         vblock ("Parents", (fn n => link(n^".html",n)), parents)
         ; HR();
         vblock ("Types", 
                 (fn {Name,Arity} => (strong Name; 
                            add_string("(Arity = "^
				       Lib.int_to_string Arity^")"))),
                 (rev type_constants))
         ; HR();
         let val consts = gather (not o is_dollared o #Name o Term.dest_const)
                                 (rev term_constants)
             val binders = gather (is_binder o #Name o Term.dest_const) consts
             val infixes = gather (is_infix  o #Name o Term.dest_const) consts
         in vblock("Constants", (fn const => 
                let val {Name,Ty} = Term.dest_const const
                    val place = (fixity_to_string o fixity) Name
                in begin_block PP.CONSISTENT 0;
                   strong Name;
                   add_string"<EM>";
                   add_string ":";
                   pp_type Ty ~1;
                   add_string"</EM>";
                   end_block()
                end),     consts)
            ;
            if (Portable.List.null infixes) 
            then ()
            else vblock("Infixes", (fn const => 
                  let val {Name,...} = Term.dest_const const
                      val infix_str = case(fixity Name) 
                                      of (Infix i) => Lib.int_to_string i
                             | _ => raise THEORY_ERR{function="theory_to_html",
                                         message = "Non-infix in infix block"}
                  in begin_block PP.CONSISTENT 0;
                     strong (Name^"{");
                     add_string("fixity = "^infix_str);
                     strong"}";
                     end_block()
                  end),     infixes)
            ;
            if (Portable.List.null binders)
            then ()
            else vblock("Binders", (fn const => 
              let val {Name,...} = Term.dest_const const
              in begin_block PP.CONSISTENT 0;
                 strong Name;
                 end_block()
              end),     binders)
         end
         ; HR();
         pr_thm ("Axioms", rev axioms)
         ; HR()
         ;
         pr_thm ("Definitions", rev definitions)
         ; HR()
         ;
         pr_thm ("Theorems", rev theorems);
         HR();
       end_block()
   end;

fun html_theory s = 
   let val name = (case s of "-" => current_theory_name() |    _ => s)
       val ostrm = Portable.open_out (name^".html")
       val consumer = PP.mk_consumer
                       {consumer = Portable.outputc ostrm,
                        linewidth = 78,
                        flush = fn () => Portable.flush_out ostrm}
   in
     PP.with_pp consumer (Lib.C theory_to_html name) 
     handle e => (Portable.close_out ostrm; raise e);
     Portable.close_out ostrm
   end;


local val std_out = Portable.std_out
      val output = Portable.output
      val flush_out = Portable.flush_out
      val concat = Portable.String.concat
in 
fun loadLibThry libname thyname =
  let val thy_dir = concat[!Globals.HOLdir, "library/", libname, "/theories/",
                           SysParams.theory_file_type, "/"]
      val () = if (Lib.mem thy_dir (!Globals.theory_path))
                then ()
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

end; (* THEORY *)

