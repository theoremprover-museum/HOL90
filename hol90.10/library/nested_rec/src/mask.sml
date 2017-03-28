(*---------------------------------------------------------------------------
 * Provides a way to allow constructor names to be rebound.
 *---------------------------------------------------------------------------*)
structure NestedRecMask 
         : sig type foo 
               val Domain : foo 
               val Range : foo
           end =
struct
  datatype foo = Domain | Range;
end;
