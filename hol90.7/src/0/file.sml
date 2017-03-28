functor FILE (Lib : Lib_sig) : File_sig =
struct

fun FILE_ERR{function,message} = HOL_ERR{origin_structure = "File",
                                         origin_function = function,
                                         message = message};

fun found_but_unable_to_read s = Lib.say 
 ("\nfound "^Lib.quote s^" but couldn't read it successfully: continuing\n");

fun get_file_by_name{reader : instream -> 'a,
                     suffix : string} (paths : string list) name =
   let val ending = name^suffix
       fun find [] = raise FILE_ERR{function = "get_file_by_name",
                             message = "unable to get the file "^quote ending}
         | find (prefix::rst) =
            let val pname = prefix^ending
            in if (file_exists_for_reading pname)
               then let val istrm = open_in pname
                        val data = reader istrm 
                                   handle e => (close_in istrm; 
                                                found_but_unable_to_read pname;
                                                raise e)
                        val _ = close_in istrm
                    in {data = data, path = prefix}
                    end handle e => find rst
               else find rst
            end
   in find paths
   end;




fun get_file_by_key {reader : instream -> 'a,
                     suffix : string,
                     eq : ('b * 'b) -> bool,
                     key_of : 'a -> 'b,
                     name_of : 'b -> string} (paths :string list) (key :'b) =
   let val ending = (name_of key)^suffix
       fun find [] = raise FILE_ERR{function = "get_file_by_key",
                       message = "unable to get the file "^Lib.quote ending}
         | find (prefix::rst) =
            let val pname = prefix^ending
            in
            if (file_exists_for_reading pname)
            then let val istrm = open_in pname
                     val data = reader istrm
                                handle e => (close_in istrm; 
                                             found_but_unable_to_read pname;
                                             raise e)
                     val _ = close_in istrm
                 in
                 if eq(key_of data, key)
                 then {data = data, path = prefix}
                 else find rst
                 end handle e => find rst
            else find rst
            end
   in find paths
   end;


end; (* FILE *)
