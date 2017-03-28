signature Goalstack_sig =
  sig
    type term
    type thm
    type tactic
    type goal
    type goalstack
    type proofs

    structure Functional :
    sig
      (* Starting a proof *)
      val set_goal : goal -> goalstack
      val add : goalstack -> proofs -> proofs

      (* Undo *)
      val backup : goalstack -> goalstack
      val set_backup : int -> goalstack -> goalstack
      val restart   : goalstack -> goalstack
      val drop : proofs -> proofs

      (* Applying a tactic to a goal *)
      val expandf : Abbrev.tactic -> goalstack -> goalstack

      (* Seeing what the state of the proof manager is *)
      val current_goalstack : proofs -> goalstack
      val top_thm : goalstack -> thm
      val initial_goal : goalstack -> goal
      val top_goal  : goalstack -> goal
      val top_goals : goalstack -> goal list

      (* Switch focus to a different subgoal (or proof attempt) *)
      val rotate : int -> goalstack -> goalstack
      val rotate_proofs : int -> proofs -> proofs

    end

    (*----------------------------------------------------------------------
     * The "functions" here maintain a reference to an element of the 
     * proofs type. For example, "set_goal" silently modifies the 
     * current proofs to have the new goalstack as the focus of
     * subsequent operations. For purely functional operations, i.e., 
     * where no hidden state is being maintained, use the "Functional" 
     * structure above.
     *-----------------------------------------------------------------------*)
    structure Implicit :
    sig
      (* Starting a proof *)
      val set_goal : goal -> proofs
      val g : term Portable.frag list -> proofs
      val add : goalstack -> proofs

      (* Undo *)
      val backup : unit -> goalstack
      val b : unit -> goalstack
      val set_backup : int -> unit
      val restart : unit -> goalstack
      val drop : unit -> proofs

      (* Applying a tactic to the current goal *)
      val expandf : Abbrev.tactic -> goalstack
      val expand : Abbrev.tactic -> goalstack
      val e : Abbrev.tactic -> goalstack

      (* Seeing what the state of the proof manager is *)
      val top_thm : unit -> thm
      val initial_goal : unit -> goal
      val top_goal  : unit -> goal
      val top_goals : unit -> goal list
      val p : unit -> goalstack
      val status : unit -> proofs

      (* Switch focus to a different subgoal (or proof attempt) *)
      val rotate : int -> goalstack
      val rotate_proofs : int -> proofs
      val r : int -> goalstack
      val R : int -> proofs
    end

    (* Switch to a different prettyprinter for all goals *)
    val set_goal_pp :(PP.ppstream -> goal -> unit)
                       -> (PP.ppstream -> goal -> unit)
    (* Standard system prettyprinter for goals *)
    val std_goal_pp : (PP.ppstream -> goal -> unit)

    (* Prettyprinters for the state of the proof manager *)
    val pp_goalstack : PP.ppstream -> goalstack -> unit
    val pp_proofs : PP.ppstream -> proofs -> unit
  end
