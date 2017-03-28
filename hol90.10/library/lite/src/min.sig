
signature Classical_sig = 
sig

    structure Equal : Equal_sig
    local open Equal open Thm open Term open Type Tactic in

   (* --------------------------------------------------------------------
    * Classical Axioms and basic rules 
    * --------------------------------------------------------------------*)

   val ETA_AX : thm              
   val ETA_CONV : conv
   val FUN_EQ_THM : thm          
   val EXT : thm -> thm
   val SELECT_UNIQUE : thm        
   val SELECT_THM : thm           
   val SELECT_AX : thm
   val SELECT_ELIM : thm -> term * thm -> thm
   val SELECT_RULE : thm -> thm
   val SELECT_INTRO : thm -> thm
   val SELECT_CONV : conv
   val SELECT_REFL : thm
   val select_cid : tmcid
   val mk_select : term * term -> term
   val dest_select : term -> term * term
   val is_select : term -> bool
   val BOOL_CASES_AX : thm        
   val BOOL_SPLIT : thm        
   val CCONTR : term -> thm -> thm
   val CONTRAPOS_CONV : conv

   (* --------------------------------------------------------------------
    * Specification and Type Definition
    * --------------------------------------------------------------------*)
   val gen_type_definition : thm -> (tycid * tmcid * tmcid * thm)
   val gen_specification : int -> thm -> (tmcid list * thm)
   val new_type_definition : string -> string * string -> thm -> (tycid * tmcid * tmcid * thm)
   val new_specification : string list -> thm -> (tmcid list * thm)
   val simple_new_specification : thm -> (tmcid list * thm)

   (* --------------------------------------------------------------------
    * Tautology Checker and Tactics
    * --------------------------------------------------------------------*)

   val TAUT : term -> thm
   val TAUT_CONV : conv
   val TAUT_TAC : tactic

   val ASM_CASES_TAC : term -> tactic
   val BOOL_CASES_TAC : term -> tactic
   (* --------------------------------------------------------------------
    * Clasical Theorems
    * --------------------------------------------------------------------*)

   val IMP_F_EQ_F : thm 
   val NOT_IMP : thm    
   val NOT_CLAUSES : thm
   val OR_CONG :thm 
   val IMP_CONG : thm            
   val AND_CONG : thm 
   val AND_IMP_INTRO : thm
   val OR_IMP_THM : thm          

   val RIGHT_OR_OVER_AND : thm   
   val DE_MORGAN_THM : thm        
   val RIGHT_AND_OVER_OR :thm 
   val LEFT_AND_OVER_OR : thm     
   val LEFT_OR_OVER_AND : thm 

   val EQ_EXPAND : thm           
   val EQ_EXT : thm              
   val EQ_ELIM_THM : thm 

   val LEFT_FORALL_OR_THM : thm  
   val NOT_EXISTS_THM : thm      
   val RIGHT_FORALL_OR_THM : thm 
   val EXCLUDED_MIDDLE : thm     
   val LEFT_OR_FORALL_THM : thm  
   val RIGHT_IMP_EXISTS_THM : thm 
   val EXISTS_THM : thm           
   val EXISTS_NOT_THM : thm       
   val SKOLEM_THM : thm           
   val LEFT_IMP_FORALL_THM : thm 
   val IMP_DISJ_THM : thm        
   val LEFT_EXISTS_IMP_THM : thm 
   val FORALL_NOT_THM : thm      
   val NOT_FORALL_THM : thm      
   val RIGHT_OR_FORALL_THM : thm 
   val UNIQUE_SKOLEM_ALT : thm 
   val SELECT_REFL_2 : thm     
   val RIGHT_EXISTS_IMP_THM : thm 
   val UNIQUE_SKOLEM_THM : thm    

   (* --------------------------------------------------------------------
    * Conditional
    * --------------------------------------------------------------------*)

   val COND_DEF : thm 
   val cond_cid : tmcid
   val mk_cond : term * term * term -> term
   val dest_cond : term -> term * term * term
   val is_cond : term -> bool
   val MONO_COND : thm    
   val COND_RATOR : thm           
   val COND_EXPAND : thm          
   val COND_CASES_TAC : tactic
   val COND_CLAUSES : thm        
   val COND_RAND : thm           
   val COND_ELIM_CONV : conv
   val COND_ELIM_THM : thm       
   val COND_CONG : thm 
   val COND_ID : thm  
   val COND_ABS : thm         
   val COND_BOOL_CLAUSES : thm         

   val theorems : (string * thm) list

   end;

end (* sig *)





