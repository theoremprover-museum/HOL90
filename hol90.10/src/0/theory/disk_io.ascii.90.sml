(*---------------------------------------------------------------------------
 *  Makes parsers and prettyprinters for ".holsig" and ".thms" files.
 *---------------------------------------------------------------------------*)

functor DISK_IO_ASCII(structure Regime : Regime_sig
                      structure Thy_pp : Thy_pp_sig
                      structure Thms_parse : PARSER
                      structure Holsig_parse : PARSER
                      sharing 
                         Regime.Theory_data.Thm.Term = Thy_pp.Term
                      sharing type
                         Thms_parse.result = Regime.hol_thms
                      sharing type
                         Holsig_parse.result = Regime.hol_sig
                      sharing type
                         Thms_parse.arg = Holsig_parse.arg = unit)
       :Disk_io_sig =
struct
structure Regime = Regime;

fun DISK_IO_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Disk_io",
		      origin_function = function,
		      message = message}

type hol_sig = Regime.hol_sig
type hol_thms = Regime.hol_thms;

(* Parsing theory files *)
fun holsig_error (s,_,_) = 
   (Portable.output(Portable.std_out,"holsig parser error: "^s^"\n");
    raise DISK_IO_ERR{function = "parse_holsig", message = s});

fun read_hol_sig istrm =
   let val lexer = Holsig_parse.makeLexer(fn _ => Portable.input_line istrm) 
       val (res,_) = Holsig_parse.parse(0,lexer,holsig_error,())
   in
   res
   end;

fun thms_error (s,_,_) = 
   (Portable.output(Portable.std_out,("thms parser error: "^s^"\n"));
    raise DISK_IO_ERR{function = "parse_thms", message = s});

fun read_hol_thms istrm =
   let val lexer = Thms_parse.makeLexer(fn _ => Portable.input_line istrm) 
       val (res,_) = Thms_parse.parse(0,lexer,thms_error,())
   in
   res
   end;

fun write_hol_sig(ostm, hsig) =
   let val {thid,parents,type_constants,term_constants} = 
               Regime.dest_hol_sig hsig
       val ppstrm = PP.mk_ppstream
	               {linewidth=70,consumer=Portable.outputc ostm,
                        flush=fn() => Portable.flush_out ostm}
       val {add_string,add_break,begin_block,end_block,
            add_newline,flush_ppstream,...} = PP.with_ppstream ppstrm
       val pp_type_rep = Thy_pp.pp_type_rep ppstrm
       val bbc = begin_block PP.CONSISTENT
       val bbi = begin_block PP.INCONSISTENT
       val eb = end_block
       val S = add_string 
       fun lparen() = S "("
       fun rparen() = S ")"
       fun comma() = S ","
       fun quote() = S "`"
       fun lbracket() = S "["
       fun rbracket() = S "]"
       fun lbrace() = S "{"
       fun rbrace() = S "}"
       fun space() = add_break(1,0)
       val nl = add_newline
       fun pr_sml_list f L = 
          ( bbc 1;lbracket();PP.pr_list f comma space L;rbracket();eb())
       fun thid_to_string thid = 
          let val n = Regime.Theory_data.theory_id_name thid
              and {sec,usec} =
		  Portable.Time.dest_time
		  (Regime.Theory_data.theory_id_timestamp thid)
          in
            bbi 1;
            lparen();S n;comma();space();
	    S (Lib.int_to_string sec);comma();space();
            S (Lib.int_to_string usec);rparen();
            eb()
          end
       fun add_thid thid =
          ( bbc 0;S "thid =";space();thid_to_string thid;eb())
       fun add_parents thid_list = 
          ( bbc 0;S "parents =";space();pr_sml_list thid_to_string thid_list;
            eb())
       local
       open Regime.Theory_data
       in
       fun add_type_constant({tyc,arity,theory}) =
          let val {Tyop,Args=[]} = Thm.Term.Type.dest_type tyc
          in
            bbi 1;lparen();S Tyop;comma();S(Lib.int_to_string arity);rparen();
            eb()
          end
          handle _ => raise DISK_IO_ERR{function = "add_type_constant",
                                        message = "Not a type constant"}
       end
       fun add_type_constants tyclist = 
          ( bbc 0;S "types =";space();pr_sml_list add_type_constant tyclist;
            eb())
       local
       open Regime.Theory_data
       fun fixity_to_string Thm.Term.Binder = "Binder"
         | fixity_to_string (Thm.Term.Infix i) = "Infix "^(Lib.int_to_string i)
         | fixity_to_string Thm.Term.Prefix = "Prefix"
       in
       fun add_term_constant({const,theory,place}) =
          let val {Name,Ty} = Thm.Term.dest_const const
          in
            bbc 1;
            lbrace();
              bbc 0;S "name =";space();lparen();S Name;rparen();comma();eb();
              space();
              bbc 0;S "ty ="; space();pp_type_rep Ty;comma();eb();
              space();
              bbc 0;S"fixity =";space();S(fixity_to_string place);eb();
            rbrace();
            eb()
          end
       end    
       local
       open Regime.Theory_data
       val ascii_dollar = Portable.String.ordof("$",0)
       fun is_dollared s = (Portable.String.ordof(s,0) = ascii_dollar)
       fun keeper{const,theory,place} = 
             not(is_dollared (#Name(Thm.Term.dest_const const)))
       fun plist [] = ()
         | plist [a] = add_term_constant a
         | plist (a::rst) = (add_term_constant a; comma(); space(); plist rst)
       in
       fun add_term_constants symtab_record_list =
          (bbc 0;S "constants =";space();
           bbc 1;lbracket();
	   plist(Lib.gather keeper symtab_record_list);rbracket();
           eb();eb())
       end
   in
     bbc 0;
     add_thid thid;
     nl();
     add_parents parents;
     nl();
     add_type_constants type_constants;
     nl();
     add_term_constants term_constants;
     nl();
     eb();
     flush_ppstream()
   end;


fun write_hol_thms (ostm, hthms) = 
   let val {thid, axioms, definitions, theorems} = Regime.dest_hol_thms hthms
       val ppstrm = PP.mk_ppstream{linewidth=70,consumer=Portable.outputc ostm,
                                   flush=fn () => Portable.flush_out ostm}
       val {add_string,add_break,begin_block,end_block,
            add_newline,flush_ppstream,...} = PP.with_ppstream ppstrm
       val bbc = begin_block PP.CONSISTENT
       val bbi = begin_block PP.INCONSISTENT
       val eb = end_block
       val S = add_string 
       fun lparen() = S "("
       fun rparen() = S ")"
       fun comma() = S ","
       fun quote() = S "`"
       fun lbracket() = S "["
       fun rbracket() = S "]"
       fun space() = add_break(1,0)
       val nl = add_newline
       fun thid_to_string thid = 
          let val n = Regime.Theory_data.theory_id_name thid
              and {sec,usec} =
		  Portable.Time.dest_time
                  (Regime.Theory_data.theory_id_timestamp thid)
          in
            bbi 1;
            lparen();S n;comma();space();
	    S (Lib.int_to_string sec);comma();space();
            S (Lib.int_to_string usec);rparen();
            eb()
          end
       fun add_thid thid =
          ( bbc 0;S "thid =";space();thid_to_string thid;eb())
       fun add_term tm =
          ( bbc 0;quote(); Thy_pp.pp_term ppstrm tm; quote();eb())
       fun pr_sml_list f L = 
          ( bbc 1;
            lbracket();
            PP.pr_list f comma space L;
            rbracket();
            eb()
          )
       fun add_thm (s,th) =
         ( bbc 1;
           lparen();
           lparen(); S s; rparen();
           comma();space();
           let val (H,C) = Regime.Theory_data.Thm.dest_thm th
           in pr_sml_list add_term H; 
              comma();
              space();
              add_term C
           end;
           rparen();
           eb()
         )
      fun add_thm_ob s L = 
         ( bbc 0;
           S (s^" =");
           space();
           pr_sml_list add_thm L;
           eb()
         )
   in
     bbc 0;
     add_thid thid;
     nl();

     add_thm_ob "axioms" axioms;
     nl();

     add_thm_ob "definitions" definitions;
     nl();

     add_thm_ob "theorems" theorems;
     nl();
     flush_ppstream()
   end;
  
end; (* DISK_IO_ASCII *)
