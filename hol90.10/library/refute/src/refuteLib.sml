structure refuteLib 
   : sig structure AC : AC_sig
         structure Canon : Canon_sig
     end =
struct
  structure AC = AC
  structure Canon = Canon
end;
