signature RETRIEVE_NAME =
sig
   type wildchar
   val show_wildchar : wildchar -> string
   val make_wildchar : string -> wildchar

   type namepattern
   val show_namepattern : namepattern -> string * wildchar * wildchar
   val make_namepattern : string * wildchar * wildchar -> namepattern
   val show_full_namepattern : namepattern -> string * string * string
   val make_full_namepattern : string * string * string -> namepattern
   val autonamepattern : string -> namepattern
   val namematch : namepattern -> string -> bool
end;
