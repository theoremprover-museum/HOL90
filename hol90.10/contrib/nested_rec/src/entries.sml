(* =====================================================================*)
(* FILE          : entries.sml                                          *)
(* DESCRIPTION   : Some structure for specfic kinds of lookup tables.   *)
(*                                                                      *)
(* AUTHOR        : Healfdene Goguen, University of Edinburgh            *)
(* DATE          : 92.08.01                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

structure StringEntry : EntrySig =
	struct
		datatype rel = Equal | Less | Grt
		type index = string
		fun compare (s:string) (s':string) =
			if s = s' then Equal
			else if s < s' then Less
			else Grt
	end;
structure StringTable = TableFunc (structure Entry = StringEntry);

structure TypeEntry =
    struct
	datatype rel = Equal | Less | Grt
	type index = hol_type
	fun get_type t =
	    Type.dest_type t handle HOL_ERR _ =>
		{Tyop = Type.dest_vartype t, Args = []}
	fun compare t t' =
	    if t = t' then Equal
	    else
		let
		    val {Tyop = Tyop_t, Args = Args_t} = get_type t
		    val {Tyop = Tyop_t', Args = Args_t'} = get_type t'
		in
		    if Tyop_t < Tyop_t' then Less
		    else if Tyop_t' < Tyop_t then Grt
		    else
			compare_args Args_t Args_t'
		end
	and compare_args [] [] = Equal
	  | compare_args [] (_::_) = Less
	  | compare_args (_::_) [] = Grt
	  | compare_args (a::l) (a'::l') =
		case compare a a' of
		      Equal => compare_args l l'
		    | Less => Less
		    | Grt => Grt
    end
structure TypeTable = TableFunc (structure Entry = TypeEntry)
