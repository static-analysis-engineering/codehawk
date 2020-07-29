(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:
 
   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.
  
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

(* chlib *)
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

(* ================================================================ Cfg loops === *)

class type cfg_loops_int =
object
  method get_loop_levels: doubleword_int -> doubleword_int list

  method toPretty: pretty_t
end

(* ================================================================== Operand === *)

type asm_operand_kind_t =
  | Flag of eflag_t
  | Reg of cpureg_t
  | FpuReg of int
  | ControlReg of int
  | DebugReg of int
  | MmReg of int
  | XmmReg of int
  | SegReg of segment_t
  | IndReg of cpureg_t * numerical_t
  | SegIndReg of segment_t * cpureg_t * numerical_t
  | ScaledIndReg of cpureg_t option * cpureg_t option * int * numerical_t
  | DoubleReg of cpureg_t * cpureg_t
  | Imm of immediate_int
  | Absolute of doubleword_int
  | SegAbsolute of segment_t * doubleword_int
  | DummyOp

type operand_mode_t = RD | WR | RW | AD  (* AD : address *)

(* Operand data

   An operand may be the source of data that is passed to a function later. If this
   is the case is_function_argument is true and get_function_argument returns the
   address of the call instruction that uses the argument and the index number of 
   the argument (starting at 1).
*)

class type operand_int =
object ('a)

  (* comparison *)
  method equal: 'a -> bool

  (* actions *)
  method set_function_argument: ctxt_iaddress_t -> int -> unit
  method reset_function_argument: unit

  (* converters *)
  method to_byte_operand: 'a
  method to_word_operand: 'a
  method sign_extend: int -> 'a

  (* accessors *)
  method size: int
  method get_kind             : asm_operand_kind_t
  method get_mode             : operand_mode_t
  method get_cpureg           : cpureg_t                     (* raises Invocation_error *)
  method get_absolute_address : doubleword_int               (* raises Invocation_error *)
  method get_immediate_value  : immediate_int                (* raises Invocation_error *)
  method get_function_argument: ctxt_iaddress_t * int        (* raises Invocation_error *)
  method get_esp_offset       : numerical_t                  (* raises Invocation_error *)

  method get_jump_table_target: (numerical_t * register_t)     (* raises Invocation_error *)
  method get_address_registers: cpureg_t list
  method get_indirect_register: cpureg_t
  method get_indirect_register_offset: numerical_t

  (* converters *)
  method to_address          : floc_int -> xpr_t
  method to_value            : floc_int -> xpr_t
  method to_variable         : floc_int -> variable_t        (* raises Invocation_error *)
  method to_expr             : ?unsigned:bool -> floc_int -> xpr_t
  method to_lhs              : ?size:int -> floc_int -> variable_t * cmd_t list  (* raises Invocation_error *)

  (* predicates *)
  method is_register         : bool
  method is_seg_register     : bool
  method is_memory_access    : bool
  method is_absolute_address : bool
  method is_immediate_value  : bool
  method is_function_argument: bool
  method is_esp_offset       : bool
  method is_indirect_register: bool

  method is_read             : bool
  method is_write            : bool

  method is_zero             : bool
  method has_one_bit_set     : bool

  method is_jump_table_target: bool

  (* xml *)
  method write_xml: xml_element_int -> floc_int -> unit

  (* printing *)
  method toString: string
  method toPretty: pretty_t

end

(* ============================================================== X86 opcodes === *)

type not_code_t = JumpTable of jumptable_int | DataBlock of data_block_int

type condition_code_t =
| CcOverflow             (* OF = 1 *)
| CcNotOverflow          (* OF = 0 *)
| CcCarry                (* CF = 1 *)
| CcNotCarry             (* CF = 0 *)
| CcZero                 (* ZF = 1 *)
| CcNotZero              (* ZF = 0 *)
| CcBelowEqual           (* CF = 1 or  ZF = 1 *)
| CcAbove                (* CF = 0 and ZF = 0 *)
| CcSign                 (* SF = 1 *)
| CcNotSign              (* SF = 0 *)
| CcParityEven           (* PF = 1 *)
| CcParityOdd            (* PF = 0 *)
| CcLess                 (* SF != OF *)
| CcGreaterEqual         (* SF = OF *)
| CcLessEqual            (* ZF = 1 or  SF != OF *)
| CcGreater              (* ZF = 0 and SF = OF *)

type opcode_t =
    
(* Misc *)
  | Arpl of operand_int * operand_int           (* adjust RPL Field of segment selector *)
  | BreakPoint                                  (*          call to interrupt procedure *)
  | UndefinedInstruction
  | Pause     
  | Halt     
  | InterruptReturn of bool
  | ConvertLongToDouble of operand_int * operand_int
  | ConvertWordToDoubleword of operand_int * operand_int
  | EmptyMmx
  | FlushCacheLine of operand_int
  | Cpuid
  | LoadFlags
  | StoreFlags
  | PopFlags
  | PushFlags
  | SetALC                                     (*       set al on carry, undocumented *)
  | Wait
  | SysCall                                    (*                    fast system call *)
  | LinuxSystemCall of operand_int             (*    linux system call with id in eax *)
  | SysEnter                                   (* fast call to system level function  *)
  | SysExit                                    (*   fast return from fast system call *)
  | SysReturn                                  (*        return from fast system call *)
  | TableLookupTranslation
  | Ldmxcsr of operand_int                     (*                 load mxcsr register *)
  | Stmxcsr of operand_int                     (*          store mxcsr register state *)
  | Prefetch of string * operand_int           (*           prefetch data into caches *)
  | XGetBV                                     (*     get value from control register *)
  | ReadTimeStampCounter                       (*             read time stamp counter *)
  | MiscOp of string
  | MultiByteNop of int
  | StoreIDTR of operand_int             (* store interrupt descriptor table register *)
      
(* Setting / Scanning bits *)      
  | BitTestComplement of operand_int * operand_int (*           bit test and complement *)
  | BitTestReset  of operand_int * operand_int  (*                   bit test and reset *)
  | BitTestAndSet of operand_int * operand_int  (*                     bit test and set *)
  | BitTest of operand_int * operand_int        (*                             bit test *)
  | BitScanForward of operand_int * operand_int (*                     bit scan forward *)
  | BitScanReverse of operand_int * operand_int (*                     bit scan reverse *)

(* Stack operations *)
  | Pop of int * operand_int
  | Push of int * operand_int
  | PushRegisters
  | PopRegisters
	
(* Arithmetic operations *)
  | Add of operand_int * operand_int
  | XAdd of operand_int * operand_int
  | AddCarry of operand_int * operand_int
  | Sub of operand_int * operand_int
  | SubBorrow of operand_int * operand_int
  | Div of  int * operand_int * operand_int * operand_int * operand_int  (*  unsigned divide *)
  | IDiv of int * operand_int * operand_int * operand_int * operand_int  (*    signed divide *)
  | Mul of  int * operand_int * operand_int * operand_int   (*             unsigned multiply *)
  | IMul of int * operand_int * operand_int * operand_int   (*               signed multiply *)
  | Increment of operand_int
  | Decrement of operand_int
	
(* Randomize *)
  | RdRandomize of operand_int                             (*            randomize register *)
	
(* Control flow *)
  | DirectCall of operand_int
  | IndirectCall of operand_int
  | DirectJmp of operand_int
  | IndirectJmp of operand_int
  | DirectLoop of operand_int
  | Ret of int option
  | BndRet of int option     (* used in MPX mode *)         
  | RepzRet
  | Enter of (operand_int * operand_int)
  | Leave
  
(* Floating point operations *)
  | Finit of bool                                  (*      initialize floating point unit *)
  | Fclex of bool                                  (*                    clear exceptions *)
  | Fbstp of operand_int                           (*                           store bcd *)
  
  | FLoadConstant of string * string        (*    load floating point constant into ST(0) *)
  | FLoad of bool * int * operand_int       (* load operand (with given width) into ST(0) *)
  | FLoadState of string * int * operand_int (*      load fpu status information into fpu *)
  | FStore of bool * bool * int * operand_int                  (* store ST(0) into memory *)
  | FStoreState of string * bool * int * operand_int      (* store fpu status information *)
  | FSaveState of bool * operand_int                                    (* save fpu state *)
  | FRestoreState of operand_int                                     (* restore fpu state *)
  | FStackOp of string * string                                     (* operation on ST(0) *)
  | FXSave of operand_int                                           (* save x87 fpu state *)
  | FXRestore of operand_int                                     (* restore x87 fpu state *)

  | Fadd  of bool * bool * int * operand_int * operand_int 
  | Fsub  of bool * bool * int * operand_int * operand_int 
  | Fsubr of bool * bool * int * operand_int * operand_int 
  | Fmul  of bool * bool * int * operand_int * operand_int 
  | Fdiv  of bool * bool * int * operand_int * operand_int 
  | Fdivr of bool * bool * int * operand_int * operand_int 

  | Fcom  of int * bool * int * operand_int                     (* floating point comparison *)
  | Fucom of int * operand_int                        (* unordered floating point comparison *)
  | Fcomi of bool * bool * operand_int              (* floating point comparison, set eflags *)
  | Fxch of operand_int                                       (* exchange operand with ST(0) *)

  | FXmmMove of string * bool * bool * operand_int * operand_int
  | FXmmOp of string * bool * bool * operand_int * operand_int 
  | FXmmOpEx of string * bool * bool * operand_int * operand_int * operand_int
  | FXmmCompare of bool * bool * operand_int * operand_int * operand_int
  | FConvert of bool * string * string * operand_int * operand_int

(* Conditional jumps *)
  | Jecxz of operand_int
  | Jcc of condition_code_t * operand_int

(* Conditional moves *)
  | CMovcc of condition_code_t * int * operand_int * operand_int
  
(* Comparison *)
  | Cmp of operand_int * operand_int
  | CmpExchange of int * operand_int * operand_int
  | CmpExchange8B of operand_int * operand_int * operand_int
  
(* Move *) 
  | Lea of operand_int * operand_int
  | Mov of int * operand_int * operand_int
  | Movdw of int * operand_int * operand_int
  | Movzx of int * operand_int * operand_int
  | Movsx of int * operand_int * operand_int
  | Movnt of bool * int * operand_int * operand_int
  | Movdq of bool * operand_int * operand_int
  | Xchg of operand_int * operand_int
  | BSwap of operand_int

(* BCD operations *)
  | AAA                                         (*       ASCII adjust ax after addition *)
  | AAD of operand_int                          (*      ASCII adjust ax before division *) 
  | AAM of operand_int                          (*       ASCII adjust ax after multiply *)
  | AAS                                         (*    ASCII adjust al after subtraction *)
  | DAA                                         (*     Decimal adjust al after addition *)
  | DAS                                         (*  Decimal adjust al after subtraction *)
  
(* Logical operations *)
  | LogicalAnd of operand_int * operand_int
  | LogicalOr of operand_int * operand_int
  | OnesComplementNegate of operand_int
  | TwosComplementNegate of operand_int
  | Test of operand_int * operand_int
  | Xor of operand_int * operand_int
  
(* Shift operations *)
  | Sar of operand_int * operand_int             (*                       signed divide *)
  | Shr of operand_int * operand_int             (*                     unsigned divide *)
  | Shl of operand_int * operand_int             (*                            multiply *) 
  | Shrd of operand_int * operand_int * operand_int (*     double precision shift right *)
  | Shld of operand_int * operand_int * operand_int (*      double precision shift left *)
  | Ror of operand_int * operand_int             (*           rotate 32 bits right once *)
  | Rol of operand_int * operand_int             (*            rotate 32 bits left once *)
  | Rcr of operand_int * operand_int             (*                rotate 33 bits right *)
  | Rcl of operand_int * operand_int             (*                 rotate 33 bits left *)

(* String operations *)
  | Cmps of int * operand_int * operand_int      (*                     compare strings *)
  | Movs of int * operand_int * operand_int * operand_int * operand_int  (* move data from string to string *)
  | Scas of int * operand_int                    (*                         scan string *)
  | Stos of int * operand_int * operand_int * operand_int * operand_int  (* store string: dst, src, edi, df *)
  | Lods of int * operand_int                    (*                           load word *)
  
(* Rep instructions *)
  | RepIns of int * operand_int
  | RepOuts of int * operand_int
  | RepLods of int * operand_int
  | RepStos of int * operand_int
  | RepNeStos of int * operand_int
  | RepMovs of int * operand_int * operand_int
  | RepNeMovs of int * operand_int * operand_int
  | RepECmps of int * operand_int * operand_int
  | RepNeCmps of int * operand_int * operand_int
  | RepEScas of int * operand_int
  | RepNeScas of int * operand_int

  (* Instructions on packed data *)
  | PackedOp of string * int * operand_int  * operand_int
  | PackedAdd of bool * bool * int * operand_int * operand_int
  | PackedSubtract of bool * bool * int * operand_int * operand_int
  | PackedMultiply of string * operand_int * operand_int
  | PackedCompare of string * int * operand_int * operand_int
  | PackedCompareString of bool * bool * operand_int * operand_int * operand_int
                                                          (* explicit/implicit, index/mask *)
  | PackedRoundScalarDouble of operand_int * operand_int * operand_int
  | PackedShift of string * int * operand_int * operand_int
  | PackedShuffle of string * operand_int * operand_int * operand_int option
  | PackedExtract of int * operand_int * operand_int * operand_int
  | PackedInsert  of int * operand_int * operand_int * operand_int 
  | PackedAlignRight of operand_int * operand_int * operand_int
  | PackedConvert of string * operand_int * operand_int
  | Unpack of string * int * operand_int * operand_int 

(* Advanced Vector Extension (AVX) instructions *)
  | VZeroAll 
  | VMovdq of bool * operand_int * operand_int 
  | VPackedOp of string * int * operand_int  * operand_int * operand_int
  | VPackedAdd of bool * bool * int * operand_int * operand_int * operand_int
  | VPackedShift of string * int * operand_int * operand_int * operand_int
  | VPackedShuffle of string * operand_int * operand_int * operand_int option
  | VPackedAlignRight of operand_int * operand_int * operand_int * operand_int

(* Set bits *)
  | ClearCF                                 (*                     clear carry flag *)
  | ComplementCF                            (*                complement carry flag *)
  | SetCF                                   (*                       set carry flag *)
  | SetDF                                   (*                   set direction flag *)
  | ClearDF                                 (*                 clear direction flag *)
  | ClearInterruptFlag
  | SetInterruptFlag
  | ClearTaskSwitchedFlag

  | Setcc of condition_code_t * operand_int

(* I/O instructions *)
  | InputFromPort of int * operand_int * operand_int
  | OutputToPort of int * operand_int * operand_int
  | InputStringFromPort of int * operand_int
  | OutputStringToPort of int * operand_int 

(* Extended instruction opcodes for cryptographic functions *)
  | XStoreRng
  | XCrypt of string
  
(* AES encryption *)
  | AESDecrypt of operand_int * operand_int
  | AESDecryptLast of operand_int * operand_int
  | AESEncrypt of operand_int * operand_int
  | AESEncryptLast of operand_int * operand_int
  | AESInvMix of operand_int * operand_int
  | AESKeyGenAssist of operand_int * operand_int * operand_int

(* Meta *)
  | CfNop of int * string                      (* cfg obfuscation without effect *)
  | CfJmp of operand_int * int * string        (* cfg obfuscation with resulting jump *)
  | JumpTableEntry of operand_int
  | OpInvalid                                  (* inside an instruction *)
  | Unknown                                    (* instruction not recognized *)
  | InconsistentInstr of string                (* inconsistent instruction at failure on input *)
  | NotCode of not_code_t option               (* start (Some b) or inside (None) a data block *)

(* ===================================================== X86 Opcode Dictionary == *)

class type x86dictionary_int =
  object

    method index_opkind: asm_operand_kind_t -> int
    method index_operand: operand_int -> int
    method index_opcode: opcode_t -> int
    method index_bytestring: string -> int
    method index_opcode_text: string -> int

    method write_xml_opcode: ?tag:string -> xml_element_int -> opcode_t -> unit
    method write_xml_bytestring: ?tag:string -> xml_element_int -> string -> unit
    method write_xml_opcode_text: ?tag:string -> xml_element_int -> string -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end
  
(* ================================================= Predefined call semantics == *)

class type predefined_callsemantics_int =
object

  (* accessors *)
  method get_name: string                          (* name of the function *)
  method get_md5hash: string             (* md5 hash of hex representation *)
  method get_annotation: floc_int -> pretty_t        (* printed annotation *)
  method get_commands: floc_int -> cmd_t list                      (* chif *)
  method get_parametercount: int             (* number of stack parameters *)
  method get_instrcount: int                     (* number of instructions *)
  method get_description: string           (* description of functionality *)
  method get_call_target:
           doubleword_int -> call_target_info_int   (* type of call target *)

  (* printing *)
  method toPretty: pretty_t
end

type patternrhs_t = 
| PConstantValue of numerical_t
| PRegister of cpureg_t
| PArgument of int
| PGlobalVar of doubleword_int
| PUnknown

type regexpattern_t = {
  regex_s: Str.regexp ;
  regex_f: doubleword_int -> string -> string -> predefined_callsemantics_int option
}

(* ===================================================== Assembly instruction === *)

class type assembly_instruction_int =
object
  (* setters *)
  method set_block_entry: unit
  method set_inlined_call: unit

  (* accessors *)
  method get_address: doubleword_int
  method get_opcode : opcode_t
  method get_instruction_bytes: string
  method get_bytes_ashexstring: string
  method get_non_code_block   : not_code_t

  (* predicates *)
  method is_valid_instruction: bool
  method is_block_entry      : bool
  method is_inlined_call     : bool
  method is_direct_call      : bool
  method is_unknown          : bool
  method is_not_code         : bool
  method is_non_code_block   : bool
  method is_nop              : bool
  method is_esp_manipulating : floc_int -> bool

  (* printing *)
  method toString: string
  method toPretty: pretty_t

  (* xml *)
  method write_xml  : xml_element_int -> unit

end

(* ==================================================== Assembly instructions === *)

class type assembly_instructions_int =
object

  (* setters *)
  method set: int -> assembly_instruction_int -> unit
  method set_not_code: data_block_int list -> unit
  method set_jumptables: jumptable_int list -> unit

  (* accessors *)
  method length: int
  method at_index  :            int -> assembly_instruction_int
  method at_address: doubleword_int -> assembly_instruction_int
  method get_next_valid_instruction_address: doubleword_int -> doubleword_int
  method get_code_addresses_rev:
           ?low:doubleword_int -> ?high:doubleword_int -> unit -> doubleword_int list
  method get_num_instructions: int
  method get_num_unknown_instructions: int
  method get_data_blocks: data_block_int list
  method get_opcode_stats: (string * int) list
  method get_opcode_group_stats: (string * int) list
  method get_jumptable: doubleword_int -> jumptable_int option

  (* iterators *)
  method iteri: (int -> assembly_instruction_int -> unit) -> unit
  method itera: (doubleword_int -> assembly_instruction_int -> unit) -> unit (* provide virtual address *)

  (* predicates *)
  method is_in_code_range          : doubleword_int -> bool
  method is_code_address           : doubleword_int -> bool
  method has_next_valid_instruction: doubleword_int -> bool

  (* printing *)
  method toString: ?filter:(assembly_instruction_int -> bool) -> unit -> string
  method toPretty: pretty_t

end

(* ========================================= Assembly instruction annotations === *)

type assembly_instruction_annotation_type_t =
  | LibraryCall of string
  | ApplicationCall of doubleword_int
  | Call
  | Assignment
  | FunctionArgument
  | Jump of doubleword_int
  | Return
  | RepInstruction
  | NotModeled
  | NoAnnotation

class type assembly_instruction_annotation_int =
object
  (* accessors *)
  method get_annotation_type: assembly_instruction_annotation_type_t

  (* printing *)
  method toPretty : pretty_t
end

(* =========================================================== Assembly block === *)

class type assembly_block_int =
object

  (* accessors *)
  method get_faddr         : doubleword_int
  method get_location      : location_int
  method get_context       : context_t list
  method get_context_string: ctxt_iaddress_t
  method get_first_address : doubleword_int
  method get_last_address  : doubleword_int
  method get_instructions  : assembly_instruction_int list
  method get_instructions_rev: assembly_instruction_int list
  method get_successors    : ctxt_iaddress_t list
  method get_instruction   : doubleword_int -> assembly_instruction_int
  method get_instruction_count: int
  method get_bytes_ashexstring: string

  (* predicates *)
  method includes_instruction_address: doubleword_int -> bool
  method is_returning: bool

  (* iterators *)
  method itera : ?low:doubleword_int -> ?high:doubleword_int -> ?reverse:bool -> 
    (ctxt_iaddress_t -> assembly_instruction_int -> unit) -> unit

  (* xml *)
  method write_xml   : xml_element_int -> unit
  method to_xml      : cfg_loops_int -> xml_element_int

  (* printing *)
  method toString: string
  method toPretty: pretty_t
  method to_annotated_pretty: pretty_t
end

(* ======================================================== Assembly function === *)

class type assembly_function_int =
object

  (* accessors *)
  method get_address : doubleword_int
  method get_blocks  : assembly_block_int list
  method get_block   : ctxt_iaddress_t -> assembly_block_int
  method get_block_count      : int
  method get_instruction_count: int
  method get_stack_adjustment     : int option
  method get_dll_stub             : string * string
  method get_bytes_ashexstring    : string
  method get_function_md5         : string
    
  method get_num_conditional_instructions: int * int * int   

  method get_num_indirect_calls   : int * int           (* calls, resolved *)

  (* iterators *)
  method iter : (assembly_block_int -> unit) -> unit
  method itera: (ctxt_iaddress_t -> assembly_block_int -> unit) -> unit
  method iteri: (doubleword_int -> ctxt_iaddress_t -> assembly_instruction_int -> unit) -> unit
  method iter_calls: (ctxt_iaddress_t -> floc_int -> unit) -> unit

  method populate_callgraph: callgraph_int -> unit

  (* predicates *)
  method is_complete: bool
  method includes_instruction_address: doubleword_int -> bool
  method is_nonreturning : bool
  method is_dll_stub : bool
  method can_be_inlined: bool

  (* saving *)
  method write_xml  : xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t
  method to_annotated_pretty: pretty_t

end

(* ======================================================= Assembly functions === *)

class type assembly_functions_int =
object

  (* reset *)
  method reset: unit

  (* setters *)
  method add_function    : assembly_function_int -> unit
  method replace_function: assembly_function_int -> unit
  method add_functions_by_preamble: doubleword_int list

  (* accessors *)
  method get_callgraph       : callgraph_int
  method get_num_functions   : int
  method get_num_complete_functions       : int
  method get_num_basic_blocks             : int
  method get_num_conditional_instructions : int * int * int
  method get_num_indirect_calls           : int * int
  method get_function_coverage            : int * int * int (* coverage, overlap, multiplicity *)

  method get_functions                  : assembly_function_int list
  method get_application_functions      : assembly_function_int list
  method get_statically_linked_functions: assembly_function_int list
  method get_function : dw_index_t -> assembly_function_int
  method get_function_by_address: doubleword_int -> assembly_function_int
  method get_containing_function: doubleword_int -> doubleword_int

  method get_function_stats    : ((int * int) list * assembly_function_int list)
  method get_opcode_stats      : (string * int) list
  method get_opcode_group_stats: (string * int) list

  (* iterators *)
  method iter : (assembly_function_int -> unit) -> unit
  method itera: (doubleword_int -> assembly_function_int -> unit) -> unit
  method bottom_up_itera: (doubleword_int -> assembly_function_int -> unit) -> unit
  method top_down_itera : (doubleword_int -> assembly_function_int -> unit) -> unit

  (* predicates *)
  method has_function_by_address     : doubleword_int -> bool
  method includes_instruction_address: doubleword_int -> bool

  (* printing *)
  method dark_matter_to_string : string
  method duplicates_to_string  : string

end

(* ================================================================== Code pc === *)

class type code_pc_int =
object
  (* accessors *)
  method get_next_instruction      : ctxt_iaddress_t * assembly_instruction_int
  method get_block_successors      : ctxt_iaddress_t list
  method get_block_successor       : ctxt_iaddress_t 
  method get_false_branch_successor: ctxt_iaddress_t
  method get_true_branch_successor : ctxt_iaddress_t

  (* predicates *)
  method has_more_instructions: bool
end

(* ============================================================== CHIF system === *)

class type chif_system_int =
object
  (* reset *)
  method reset: unit

  (* setters *)
  method add_procedure: procedure_int -> unit

  (* accessors *)
  method get_system: system_int
  method get_procedure_names: symbol_t list
  method get_procedure : symbol_t -> procedure_int
  method get_procedure_by_index  : dw_index_t -> procedure_int
  method get_procedure_by_address: doubleword_int -> procedure_int
  method get_procedure_count: int
  method get_procedure_locations: symbol_t -> (symbol_t * symbol_t) list

  (* predicates *)
  method has_procedure: symbol_t -> bool
  method has_procedure_by_index  : dw_index_t -> bool
  method has_procedure_by_address: doubleword_int -> bool
end

(* ================================================== Global variable accesses == *)

class type global_var_accesses_int =
object

  method initialize : unit

  (* accessors *)

  (* returns a list of all global memory accesses organized by global variable *)
  method get_accesses : 
    (doubleword_int * (doubleword_int * (doubleword_int * memaccess_t) list) list) list

  (* returns a list of all global memory accesses performed by a given function *)
  method get_function_accesses:
    doubleword_int -> (doubleword_int * (doubleword_int * memaccess_t) list) list

  (* returns a list of functions that access a particular global variable *)
  method get_gvar_accesses:
    doubleword_int -> (doubleword_int * (doubleword_int * memaccess_t) list) list

end

(* ======================================================= Disassembly metrics === *)

class type disassembly_metrics_int =
object
  method collect  : unit
  method write_xml: xml_element_int -> unit
  method toPretty : pretty_t
end

class type disassembly_stats_int =
object
  method collect  : unit
  method write_xml: xml_element_int -> unit
  method toPretty : pretty_t
end

(* =========================================== X86 instruction dictionary === *)

class type x86_opcode_dictionary_int =
  object

    method index_esp_offset: int * interval_t -> int
    method index_instr: assembly_instruction_int -> floc_int -> int

    method get_esp_offset: int -> (int * interval_t)

    method write_xml_esp_offset: ?tag:string -> xml_element_int -> int * interval_t -> unit
    method write_xml_instr:
             ?tag:string -> xml_element_int -> assembly_instruction_int -> floc_int -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end

class type x86_analysis_results_int =
  object

    method record_results: ?save:bool -> assembly_function_int -> unit
    method write_xml: xml_element_int -> unit
    method save: unit

  end
