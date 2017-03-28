(*---------------------------------------------------------------------------
 * Provides a way to allow constructor names to be rebound.
 *---------------------------------------------------------------------------*)
structure MutrecMask 
         : sig type foo 
               val Domain : foo 
           end =
struct
  datatype foo = Domain | Range;
end;
