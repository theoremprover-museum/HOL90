new_theory"test";

val hol_datatype = Hol_datatype.hol_datatype;

hol_datatype `Size = B | W | L`;

hol_datatype `DataRegister 
              = RegD0
              | RegD1
              | RegD2
              | RegD3
              | RegD4
              | RegD5
              | RegD6
              | RegD7`;

hol_datatype `AddressRegister
              = RegA0
              | RegA1
              | RegA2
              | RegA3
              | RegA4
              | RegA5
              | RegA6
              | RegA7`;


hol_datatype `DataOrAddressRegister 
              = data of DataRegister
              | address of AddressRegister`;

hol_datatype `Condition 
              = HI   
              | LS 
              | CC 
              | CS 
              | NE 
              | EQ 
              | VC 
              | VS 
              | PL 
              | MI 
              | GE 
              | LT 
              | GT 
              | LE`;


val TYPE = ty_antiq o Type;

val Integer = TYPE`:num`;
val Location = TYPE`:^Integer`;
val ImmediateAddressing = TYPE`:^Integer`;
val DirectAddressing    = TYPE`:DataOrAddressRegister`;
val IndirectAddressing  = TYPE`:AddressRegister`;
val PostIncrementAddressing  = TYPE`:AddressRegister`;
val PreDecrementAddressing   = TYPE`:AddressRegister`;
val IndirectWithDisplacement = TYPE`:^Integer # AddressRegister`;
val IndirectWithIndex = TYPE`:^Integer
                              #AddressRegister
                              #DataOrAddressRegister
                              #Size`;

val AbsoluteAddressing = TYPE`:^Integer`;
val PCwithDisplacement = TYPE`:^Integer`;
val PCwithIndex = TYPE`:^Integer # DataOrAddressRegister # Size`;


hol_datatype `AddressingMode 
              = immediate of ^ImmediateAddressing 
              | direct of ^DirectAddressing 
              | indirect of ^IndirectAddressing
              | postinc of ^PostIncrementAddressing 
              | predec of ^PreDecrementAddressing
              | indirectdisp of ^IndirectWithDisplacement
              | indirectindex of ^IndirectWithIndex
              | absolute of ^AbsoluteAddressing
              | pcdisp of ^PCwithDisplacement
              | pcindex of ^PCwithIndex`;


hol_datatype `M68kInstruction 
    = ABCD of AddressingMode => AddressingMode
    | ADD of Size => AddressingMode => AddressingMode
    | ADDA of Size => AddressingMode => AddressRegister 
    | ADDI of Size => ^ImmediateAddressing => AddressingMode 
    | ADDQ of Size => ^ImmediateAddressing => AddressingMode 
    | ADDX of Size => AddressingMode => AddressingMode 
    | AND of Size => AddressingMode => AddressingMode  
    | ANDI of Size => ^ImmediateAddressing => AddressingMode  
    | ANDItoCCR of ^ImmediateAddressing
    | ANDItoSR of ^ImmediateAddressing 
    | ASL of Size => AddressingMode => DataRegister 
    | ASLW of AddressingMode 
    | ASR of Size => AddressingMode => DataRegister 
    | ASRW of AddressingMode
    | Bcc of Condition => Size => ^Location 
    | BTST of Size => AddressingMode => AddressingMode 
    | BCHG of Size => AddressingMode => AddressingMode 
    | BCLR of Size => AddressingMode => AddressingMode 
    | BSET of Size => AddressingMode => AddressingMode  
    | BRA of Size => ^Location  
    | BSR of Size => ^Location  
    | CHK of AddressingMode => DataRegister  
    | CLR of Size => AddressingMode  
    | CMP of Size => AddressingMode => DataRegister  
    | CMPA of Size => AddressingMode => AddressRegister  
    | CMPI of Size => ^ImmediateAddressing => AddressingMode  
    | CMPM of Size => ^PostIncrementAddressing => ^PreDecrementAddressing  
    | DBT of DataRegister => ^Location  
    | DBF of DataRegister => ^Location  
    | DBcc of Condition => DataRegister => ^Location
    | DIVS of AddressingMode => DataRegister  
    | DIVU of AddressingMode => DataRegister  
    | EOR of Size => DataRegister => AddressingMode  
    | EORI of Size => ^ImmediateAddressing => AddressingMode 
    | EORItoCCR of ^ImmediateAddressing 
    | EORItoSR of ^ImmediateAddressing  
    | EXG of DataOrAddressRegister => DataOrAddressRegister  
    | EXT of Size => DataRegister  
    | ILLEGAL
    | JMP of AddressingMode
    | JSR of AddressingMode
    | LEA of AddressingMode => AddressRegister 
    | LINK of AddressRegister => ^ImmediateAddressing  
    | LSL of Size => AddressingMode => DataRegister 
    | LSLW of AddressingMode 
    | LSR of Size => AddressingMode => DataRegister  
    | LSRW of AddressingMode 
    | MOVE of Size => AddressingMode => AddressingMode  
    | MOVEtoCCR of AddressingMode
    | MOVEtoSR of AddressingMode 
    | MOVEfromSR of AddressingMode 
    | MOVEtoUSP of AddressingMode 
    | MOVEfromUSP of AddressingMode 
    | MOVEA of Size => AddressingMode => AddressRegister  
    | MOVEMto of Size => AddressingMode => DataOrAddressRegister list  
    | MOVEMfrom of Size => DataOrAddressRegister list => AddressingMode  
    | MOVEP of Size => AddressingMode => AddressingMode  
    | MOVEQ of ^ImmediateAddressing => DataRegister 
    | MULS of AddressingMode => DataRegister 
    | MULU of AddressingMode => DataRegister  
    | NBCD of AddressingMode 
    | NEG of Size => AddressingMode  
    | NEGX of Size => AddressingMode  
    | NOP 
    | NOT of Size => AddressingMode  
    | OR of Size => AddressingMode => AddressingMode  
    | ORI of Size => ^ImmediateAddressing => AddressingMode  
    | ORItoCCR of ^ImmediateAddressing  
    | ORItoSR of ^ImmediateAddressing  
    | PEA of AddressingMode 
    | RESET
    | ROL of Size => AddressingMode => DataRegister  
    | ROLW of AddressingMode 
    | ROR of Size => AddressingMode => DataRegister  
    | RORW of AddressingMode
    | ROXL of Size => AddressingMode => DataRegister  
    | ROXLW of AddressingMode 
    | ROXR of Size => AddressingMode => DataRegister  
    | ROXRW of AddressingMode
    | RTE  
    | RTR 
    | RTS 
    | SBCD of AddressingMode => AddressingMode 
    | ST of AddressingMode 
    | SF of AddressingMode 
    | Scc of Condition => AddressingMode
    | STOP of ^ImmediateAddressing  
    | SUB of Size => AddressingMode => AddressingMode 
    | SUBA of Size => AddressingMode => AddressingMode  
    | SUBI of Size => ^ImmediateAddressing => AddressingMode  
    | SUBQ of Size => ^ImmediateAddressing => AddressingMode  
    | SUBX of Size => AddressingMode => AddressingMode 
    | SWAP of DataRegister 
    | TAS of AddressingMode 
    | TRAP of ^Integer 
    | TRAPV
    | TST of Size => AddressingMode  
    | UNLK of AddressRegister`;
