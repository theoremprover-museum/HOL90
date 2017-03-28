functor THEORY_DATA(structure Thm : Thm_sig
                    structure Hol_pp : Hol_pp_sig
                    structure Globals : Globals_sig
                    sharing
                      Thm.Term = Hol_pp.Term): Theory_data_sig =
struct
structure Thm = Thm;
structure Term = Thm.Term;
structure Type = Term.Type;

structure Uid = UID();

fun THEORY_DATA_ERR{function,message} =
      HOL_ERR{origin_structure = "Theory_data",
	      origin_function = function,
	      message = message}

type theory_id = Uid.uid;
val mk_theory_id = Uid.re_mk_uid
val theory_id_name = Uid.name
val theory_id_timestamp = Uid.timestamp
val theory_id_eq = Uid.eq

type type_record = {tyc:Thm.Term.Type.hol_type, arity :int, theory:string}
type term_record = {const:Thm.Term.term, theory:string, place:Thm.Term.fixity};

type theory = { thid : theory_id,
                in_draft_mode : bool,
                consistent_with_disk : bool,
                parents : theory_id list,
                type_constants : type_record list,
                term_constants : term_record list,
                axioms : (string*Thm.thm) list,
                definitions : (string*Thm.thm) list,
                theorems : (string*Thm.thm) list};

(* extraction routines *)
fun theory_id (th:theory) = #thid th
fun theory_draft_mode (th:theory) = (#in_draft_mode th);
fun theory_consistent_with_disk(th:theory) = (#consistent_with_disk th);
fun theory_parents (th:theory) = (#parents th);
fun theory_type_constants (th:theory) = (#type_constants th);
fun theory_term_constants (th:theory) = (#term_constants th);
fun theory_axioms (th:theory) = (#axioms th);
fun theory_definitions (th:theory) = (#definitions th);
fun theory_theorems (th:theory) = (#theorems th);

   
(* construction routines *)

(* mk_theory is used when an existing theory is brought in from disk.
   Therefore, we don't want to be in draft mode, and we are consistent 
   with disk.
*)
fun mk_theory theory_id =
   { thid = theory_id,
     in_draft_mode = false,
     consistent_with_disk = true,
     parents = [],
     type_constants = [],
     term_constants = [],
     axioms = [],
     definitions = [],
     theorems = []}:theory;

(* Notice that the timestamp for a theory is its creation date. If
   it was the time when last closed, then I could keep track of when 
   extend_theory gets done. But then I would have to do something
   about updating the timestamps of descendent theories.

   consistent_with_disk is set to false because when a theory is created no
   corresponding file gets created. The file is only created on export. 
*)
fun fresh_theory s:theory =
   { thid = Uid.mk_uid s,
     in_draft_mode = true,
     consistent_with_disk = false,
     parents = [],
     type_constants = [],
     term_constants = [],
     axioms = [],
     definitions = [],
     theorems = []}:theory;

(* The initial theory *)
val CT = ref (fresh_theory "");
fun the_current_theory() = !CT;
fun make_current thry = (CT := thry);


(* Alteration routines *)
fun set_draft_mode b ({thid,in_draft_mode,consistent_with_disk,
                       parents,type_constants, term_constants,
                       axioms,definitions,theorems}:theory) = 
   {in_draft_mode = b,
    thid = thid, consistent_with_disk=consistent_with_disk,
    parents = parents, type_constants=type_constants,
    term_constants = term_constants, axioms=axioms,
    definitions = definitions, theorems = theorems};

(* This needs some explaining. When the system is built, the CT is a null
   theory (the "Ur" theory, if you will). It shouldn't be in draft mode,
   because if we are re-using existing theory files, then we will do a
   "load_theory" on "min", but this will fail because you can't do a
   load_theory in draft_mode.
*)
val _ = CT := set_draft_mode false (!CT)

fun set_consistency_with_disk b ({thid,in_draft_mode,consistent_with_disk,
                                  parents,type_constants, term_constants, 
                                  axioms,definitions,theorems}:theory) = 
   {consistent_with_disk = b,
    thid = thid, in_draft_mode = in_draft_mode,parents = parents, 
    type_constants=type_constants,term_constants = term_constants,
    axioms=axioms,definitions = definitions, theorems = theorems};

fun add_parent pid ({thid,in_draft_mode,consistent_with_disk,parents,
                     type_constants, term_constants, axioms,definitions,
                     theorems}:theory) = 
   {parents = Lib.op_union (curry theory_id_eq) [pid] parents, 
    thid = thid, in_draft_mode = in_draft_mode,
    consistent_with_disk = consistent_with_disk,
    type_constants=type_constants,term_constants = term_constants,
    axioms=axioms,definitions = definitions, theorems = theorems};


fun add_type ty ({thid,in_draft_mode,consistent_with_disk,parents,
                  type_constants, term_constants, axioms,definitions,
                   theorems}:theory) = 
   {type_constants = ty::type_constants,
    thid = thid, in_draft_mode = in_draft_mode, 
    consistent_with_disk = consistent_with_disk, parents = parents,
    term_constants = term_constants, axioms=axioms,
    definitions = definitions, theorems = theorems};

fun add_term tm ({thid,in_draft_mode,consistent_with_disk,parents,
                  type_constants, term_constants, axioms,definitions,
                  theorems}:theory) = 
   {term_constants = tm::term_constants,
    thid = thid, in_draft_mode = in_draft_mode, 
    consistent_with_disk = consistent_with_disk, parents = parents,
    type_constants = type_constants, axioms=axioms,
    definitions = definitions, theorems = theorems};

local
(* This check ensures that theory bindings are single valued. *)
fun check ({axioms,definitions,theorems,...}:theory) s =
   (assoc s axioms; false)
   handle NOT_FOUND
    => ((assoc s definitions; false)
         handle NOT_FOUND
         => ((assoc s theorems; false)
             handle NOT_FOUND => true))
fun ALREADY_USED_ERR func name =
      THEORY_DATA_ERR{function = func, 
		      message = Lib.quote name^" is already in use as a name"};
in
fun add_axiom (ax as (s,_)) (thry as {thid,in_draft_mode,consistent_with_disk,
                                      parents, type_constants, term_constants, 
                                      axioms,definitions,theorems}:theory) = 
   if (check thry s)
   then {axioms = ax::axioms,
         thid = thid, in_draft_mode = in_draft_mode, 
         consistent_with_disk = consistent_with_disk, 
         parents = parents,type_constants = type_constants, 
         term_constants = term_constants,definitions = definitions,
         theorems = theorems}
   else raise ALREADY_USED_ERR "add_axiom" s

fun add_definition (def as (s,_)) 
                   (thry as {thid,in_draft_mode,consistent_with_disk,parents,
                             type_constants, term_constants,axioms,
                             definitions,theorems}:theory) = 
   if (check thry s)
   then {definitions = def::definitions,
         thid = thid, in_draft_mode = in_draft_mode, 
         consistent_with_disk = consistent_with_disk, 
         parents = parents,type_constants = type_constants, 
         term_constants = term_constants,axioms = axioms,
         theorems = theorems}
   else raise ALREADY_USED_ERR "add_definition" s

fun add_theorem (th as (s,_)) 
                (thry as {thid,in_draft_mode,consistent_with_disk,parents,
                          type_constants, term_constants, axioms,
                          definitions,theorems}:theory) = 
   if (check thry s)
   then {theorems = th::theorems,
         thid = thid, in_draft_mode = in_draft_mode, 
         consistent_with_disk = consistent_with_disk, 
         parents = parents,type_constants = type_constants, 
         term_constants = term_constants,axioms = axioms,
         definitions = definitions}
   else raise ALREADY_USED_ERR "add_theorem" s
end;


(* This is part of how delete_thm would be implemented, but its specification
 * would require unappealing work - for instance you could delete a theorem
 * from an ancestor and then the specification requires that the change
 * be reflected in the disk representation of that ancestor. But how do you 
 * know where it is? Writing occurs at the head of the theory path, which has 
 * probably changed. Maybe change the specification to refer to only the 
 * current theory. Or just forget it altogether.
 * fun op_remove_once eq_func item =
 *    let val eq_item = eq_func item
 *        fun remv [] = []
 *          | remv (a::rst) = 
 *                if (eq_item a) 
 *                then rst
 *                else (a::remv rst)
 *    in remv
 *    end;
 * 
 * 
 * fun delete_theorem s (thry as {thid,in_draft_mode,consistent_with_disk,
 *                                parents, type_constants, term_constants, 
 *                                axioms,definitions,theorems}:theory) = 
 *    {theorems = op_remove_once (fn (str,_) => (str = s)) theorems,
 *     thid = thid, in_draft_mode = in_draft_mode, 
 *     consistent_with_disk = consistent_with_disk, 
 *     parents = parents,type_constants = type_constants, 
 *     term_constants = term_constants,axioms = axioms,
 *     definitions = definitions}
*)


(* Print a theory *)


val CONSISTENT = PP.CONSISTENT
val INCONSISTENT = PP.INCONSISTENT;

fun pp_theory ppstrm({thid,consistent_with_disk,parents,type_constants,
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
       val pp_type = Hol_pp.pp_type ppstrm
       fun is_dollared s = (ordof(s,0) = ordof("$",0))
       fun fixity_to_string(Thm.Term.Infix i)  = "Infix "^(Lib.int_to_string i)
         | fixity_to_string Thm.Term.Prefix = "Prefix"
         | fixity_to_string Thm.Term.Binder = "Binder"
       val pp_thm = Thm.pp_thm ppstrm
       fun pr_thm (heading, ths) =
          vblock(heading, (fn (s,th) => (begin_block CONSISTENT 0;
                                         add_string s;
                                         add_break(1,0);
                                         pp_thm th;
                                         end_block())),  ths)
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
        vblock ("Parents",(fn id => add_string (Uid.name id)), parents)
        ;
        vblock ("Type constants", 
                (fn({tyc,arity,theory})
                 => (pp_type tyc 1;
                     add_string (" "^int_to_string arity))),
                (rev type_constants))
        ;
        vblock ("Term constants", 
                (fn({const,place,theory})
                 => let val {Name,Ty} = Thm.Term.dest_const const
                    in begin_block CONSISTENT 0;
                       add_string (Name^" ");
                       add_string ("("^fixity_to_string place^")");
                       add_break(3,0);
                       add_string ":";
                       pp_type Ty ~1;
                       end_block()
                    end),
                gather(fn {const,place,theory} =>
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

end; (* THEORY_DATA *)
