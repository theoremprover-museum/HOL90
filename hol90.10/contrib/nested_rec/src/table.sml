(* =====================================================================*)
(* FILE          : table.sml                                            *)
(* DESCRIPTION   : Functor for creating quick lookup tables.            *)
(*                 It's undefined what happens if we enter the same     *)
(*                 index but different entries                          *)
(*                                                                      *)
(* AUTHOR        : Healfdene Goguen, University of Edinburgh            *)
(* DATE          : 92.08.01                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

functor TableFunc (structure Entry : EntrySig) : TableSig =
	struct
		structure Entry = Entry

		datatype 'a table_entry = InTable of 'a
					| NotFound

		type 'a table = (Entry.index * 'a) list

		val empty = []

		fun enter {key, entry, table = []} = [(key, entry)]
		  | enter {key, entry, table = (key', entry')::l} =
			case Entry.compare key key' of
				  Entry.Equal => ((key, entry)::l)
				| Entry.Less => (key, entry)::(key', entry')::l
				| Entry.Grt =>
					(key', entry')::
						(enter {key = key,
							entry = entry,
							table = l})

		fun lookup {key, table = []} = NotFound
		  | lookup {key, table = (key', entry')::l} =
			case Entry.compare key key' of
				  Entry.Equal => InTable entry'
				| Entry.Less => NotFound
				| Entry.Grt => lookup {key = key, table = l}

		fun elts l = map (fn (_, b) => b) l
	end;
