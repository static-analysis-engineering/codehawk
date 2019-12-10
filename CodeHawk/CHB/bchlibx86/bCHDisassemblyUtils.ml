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

(* =============================================================================
   The implementation in this file is based on the documents:

   Intel 64 and IA-32 Architectures Software Developer's Manual, September 2010
   Volume 2A: Instruction Set Reference, A-M
   Volume 2B: Instruction Set Reference, N-Z
   ============================================================================= *)

(* chlib *)
open CHPretty
open CHNumerical

(* chutil *)
open CHLogger

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStrings
   
(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHX86OpcodeRecords

module FFU = BCHFileFormatUtil

exception InconsistentInstruction of string


(* In some cases it is necessary to push back bytes onto the byte stream
let rewind_byte_string = ref 0

let pushback s current_pos n =
  let ch = IO.input_string s in
  let (ch,pos) = IO.pos_in ch in
  let current_position = current_pos () in
  begin
    skip_bytes (current_position - n) ch ;
    (ch,pos)
  end
*)
		    
let is_call_instruction instr =
  match instr with DirectCall _ | IndirectCall _ -> true | _ -> false

let fall_through instr =
  match instr with
  | DirectJmp _ | IndirectJmp _ | Ret _ | BndRet _ | RepzRet -> false
  | _ -> true

let is_conditional_jump_instruction instr =
  match instr with | Jecxz _ | Jcc _ | DirectLoop _ -> true | _ -> false

let is_unconditional_jump_instruction instr =
  match instr with  DirectJmp _ | IndirectJmp _ -> true  | _ -> false

let is_direct_jump_instruction instr =
  is_conditional_jump_instruction instr
  || (match instr with DirectJmp _ -> true | _ -> false)

let is_jump_instruction instr = 
  is_conditional_jump_instruction instr || is_unconditional_jump_instruction instr

let get_jump_operand opcode =
  match get_operands opcode with
    [ op ] -> op
  | _ -> raise (BCH_failure
		  (LBLOCK [ STR "Instruction is not a jump instruction: " ; 
			    STR (opcode_to_string opcode) ]))

let get_push_imm32_values code =
  Array.fold_right
    (fun instr a ->
      match instr with
	Push (_,op) -> op :: a
      | _ -> a) code []

let allflags = [ OFlag ; CFlag ; ZFlag ; SFlag ; PFlag ]

let flags_used_by_condition (cc:condition_code_t) =
  match cc with
  | CcOverflow    | CcNotOverflow  -> [ OFlag ]
  | CcCarry       | CcNotCarry     -> [ CFlag ]
  | CcZero        | CcNotZero      -> [ ZFlag ]
  | CcBelowEqual  | CcAbove        -> [ CFlag ; ZFlag ]
  | CcSign        | CcNotSign      -> [ SFlag ]
  | CcParityEven  | CcParityOdd    -> [ PFlag ]
  | CcLess        | CcGreaterEqual -> [ SFlag ; OFlag ]
  | CcLessEqual   | CcGreater      -> [ ZFlag ; SFlag ; OFlag ]

let select_byte_reg = function
  | 0 -> Al
  | 1 -> Cl
  | 2 -> Dl
  | 3 -> Bl
  | 4 -> Ah
  | 5 -> Ch
  | 6 -> Dh
  | 7 -> Bh
  | _ -> raise (InconsistentInstruction ("Error in select_byte_reg: reg > 7"))

let select_word_reg = function
  | 0 -> Ax
  | 1 -> Cx
  | 2 -> Dx
  | 3 -> Bx
  | 4 -> Sp
  | 5 -> Bp
  | 6 -> Si
  | 7 -> Di
  | _ -> raise (InconsistentInstruction ("Error in select_word_reg: reg > 7"))

let select_reg = function
  | 0 -> Eax
  | 1 -> Ecx
  | 2 -> Edx
  | 3 -> Ebx
  | 4 -> Esp
  | 5 -> Ebp
  | 6 -> Esi
  | 7 -> Edi 
  | _ -> raise (InconsistentInstruction ( "Error in select_reg: reg > 7"))

let select_word_or_dword_reg (opsize_override:bool) (index:int) =
	if opsize_override then select_word_reg index else select_reg index

let select_seg_reg seg =
  match seg with
  | 0 -> ExtraSegment
  | 1 -> CodeSegment
  | 2 -> StackSegment
  | 3 -> DataSegment
  | 4 -> FSegment
  | 5 -> GSegment
  | _ -> raise (InconsistentInstruction (
    "Error in select_seg_reg: seg_reg > 5.  Value: " ^ (string_of_int seg)))

(* Layout of the SIB byte (Figure 2-1, Table 2-3): 7-6: scale, 5-3: index, 2-0: base *)
let decompose_sib sib =
  let sf  = sib lsr 6 in               (* scale *)
  let bs  = sib mod 8 in               (* base  *)
  let ind = (sib lsr 3) mod 8 in       (* index *)
  let base_reg = select_reg bs in
  let ind_reg = select_reg ind in
  let ind_reg = match ind_reg with Esp -> None | _ -> Some ind_reg in
  let scale = match sf with 
  | 0 -> 1
  | 1 -> 2
  | 2 -> 4
  | 3 -> 8
  | _ -> failwith "Error in decompose_sib: scale factor > 3" in
  (scale,ind_reg,base_reg)

(* Layout: 7:R; 6-3: vvvv (complement); 2-0: Lpp *)
let decompose_avx_lpp avx =
  let r = avx lsr 7 in
  let vv = 15 - ((avx lsr 3) mod 16) in
  let lpp = avx mod 8 in
  (* let _ = pr_debug [ STR "r: " ; INT r ; STR "; vvvv: " ; INT vv ; 
		     STR "; lpp: " ; INT lpp ; NL ] in *)
  (r,vv,lpp)

(* Layout: 7-5: RXB; 4-0: m-mmmmm *)
let decompose_avx_rxb avx =
  let rxb = avx lsr 5 in
  let mmm = avx mod 32 in
  (* let _ = pr_debug [ STR "rxb: " ; INT rxb ; STR "; m-mmmm: " ; INT mmm ; NL ] in *)
  (rxb,mmm)

(* Layout of the ModRM byte (Figure 2-1): 7-6: Mod, 5-3: Reg, 2-0: RM *)
let decompose_modrm modrm =
  let md  = modrm lsr 6 in
  let rm  = modrm mod 8 in
  let reg = (modrm lsr 3) mod 8 in
  (md,reg,rm)

(* Table 2-3, NOTES 1 (MOD: 00): effective address = [ scaled index ] + disp32 *)
let get_scaled_address ch size mode:operand_int =
  let sib = ch#read_byte in
  let (sf,ir,br) = decompose_sib sib in
  let (br,ofs) = match br with 
    Ebp -> (None,ch#read_num_signed_doubleword) | _ -> (Some br,numerical_zero) in
  scaled_register_op br ir sf ofs size mode

(* Table 2-3, NOTES 1 (MOD: 01): effective address = [ scaled index ] + disp8 *)
let get_scaled_disp8_address ch size mode:operand_int =
  let sib = ch#read_byte in
  let ofs = ch#read_num_signed_byte in
  let (sf,ir,br) = decompose_sib sib in
  let br = Some br in
  scaled_register_op br ir sf ofs size mode

let get_scaled_disp16_address ch size mode:operand_int =
  let sib = ch#read_byte in
  let ofs = ch#read_num_signed_word in
  let (sf,ir,br) = decompose_sib sib in
  let br = Some br in
  scaled_register_op br ir sf ofs size mode

(* Table 2-3, NOTES 1 (MOD: 10): effective address = [ scaled index ] + disp32 *)
let get_scaled_disp32_address ch size mode:operand_int =
  let sib = ch#read_byte in
  let ofs = ch#read_num_signed_doubleword in
  let (sf,ir,br) = decompose_sib sib in
  let br = Some br in
  scaled_register_op br ir sf ofs size mode

(* Table 2-2: 32-bit addressing forms with the ModR/M byte *)
let get_rm_sized_operand  ?(addrsize_override=false) ?(seg_override=None)
    ~size ~fp ~mm ~xmm ~md ~rm ~ch mode:operand_int =
  let bz = numerical_zero in
  match md with
  | 0 ->
    begin
      match rm with
      | 0 -> indirect_register_op Eax bz size mode
      | 1 -> indirect_register_op Ecx bz size mode
      | 2 -> 
	begin
	  match seg_override with
	  | Some FSegment -> seg_indirect_register_op FSegment Edx numerical_zero 4 mode
	  | _ -> indirect_register_op Edx bz size mode
	end
      | 3 -> indirect_register_op Ebx bz size mode
      | 4 -> get_scaled_address ch size mode
      | 5 -> let d = ch#read_doubleword in absolute_op d size mode
      | 6 -> 
	begin
	  match (seg_override,addrsize_override) with
	  | (Some FSegment,true) ->    (* special case of addressing used in delphi 5 *)
	    let offset = ch#read_num_signed_word in
	    seg_absolute_op FSegment (numerical_to_doubleword offset) 4 mode
	  | _ -> indirect_register_op Esi bz size mode
	end
      | 7 -> indirect_register_op Edi bz size mode
      | _ -> 
	begin
	  ch_error_log#add "disassembly" 
	    (LBLOCK [ STR "Error in get_rm_sized_operand: md=0, rm > 7 (" ; INT rm ; STR ")" ]) ;
	  raise (Invalid_input ("get_rm_sized_operand" ))
	end  
    end
  | 1 -> 
    begin
      match rm with
      | 0 -> let s = ch#read_num_signed_byte in indirect_register_op Eax s size mode
      | 1 -> let s = ch#read_num_signed_byte in indirect_register_op Ecx s size mode
      | 2 -> let s = ch#read_num_signed_byte in indirect_register_op Edx s size mode
      | 3 -> let s = ch#read_num_signed_byte in indirect_register_op Ebx s size mode
      | 4 -> get_scaled_disp8_address ch size mode
      | 5 -> let s = ch#read_num_signed_byte in indirect_register_op Ebp s size mode
      | 6 -> let s = ch#read_num_signed_byte in indirect_register_op Esi s size mode
      | 7 -> let s = ch#read_num_signed_byte in indirect_register_op Edi s size mode
      | _ -> 
	begin
	  ch_error_log#add "disassembly"
	    (LBLOCK [ STR "Error in get_rm_sized_operand: md=1, rm > 7 (" ; INT rm ; STR ")" ]) ;
	  raise (Invalid_input ("get_rm_sized_operand"))
	end
    end
  | 2 ->
    begin
      match rm with
      | 0 -> let s = ch#read_num_signed_doubleword in indirect_register_op Eax s size mode
      | 1 -> let s = ch#read_num_signed_doubleword in indirect_register_op Ecx s size mode
      | 2 -> let s = ch#read_num_signed_doubleword in indirect_register_op Edx s size mode
      | 3 -> let s = ch#read_num_signed_doubleword in indirect_register_op Ebx s size mode
      | 4 -> if addrsize_override then
	  get_scaled_disp16_address ch size mode
	else
	  get_scaled_disp32_address ch size mode
      | 5 -> let s = ch#read_num_signed_doubleword in indirect_register_op Ebp s size mode
      | 6 -> let s = ch#read_num_signed_doubleword in indirect_register_op Esi s size mode
      | 7 -> let s = ch#read_num_signed_doubleword in indirect_register_op Edi s size mode
      | _ -> 
	begin
	  ch_error_log#add "disassembly"
	    (LBLOCK [ STR "Error in get_rm_sized_operand: md=2, rm > 7 (" ; INT rm ; STR ")" ]) ;
	  raise (Invalid_input ("get_rm_sized_operand"))
	end
    end
  | 3 ->
    begin
      if fp then 
	fpu_register_op rm mode
      else if xmm then
	xmm_register_op rm mode
      else if mm then
	mm_register_op rm mode
      else
	match size with
	| 1 -> register_op (select_byte_reg rm) 1 mode
	| 2 -> register_op (select_word_reg rm) 2 mode
	| 4 -> register_op (select_reg rm) 4 mode
	| 8 -> mm_register_op rm mode
	| 16 -> xmm_register_op rm mode
	| _ -> 
	  begin
	    ch_error_log#add "disassembly"
	      (LBLOCK [ STR "Error in get_rm_sized_operand: md=3, size not equal to 1,2, 4, 8 or 16 (" ;
			INT size ; STR ")" ]) ;
	    raise (Invalid_input ("get_rm_sized_operand"))
	  end
    end
  | _ -> 
    begin
      ch_error_log#add "disassembly"
	(LBLOCK [ STR "Error in get_rm_sized_operand: md not equal to 0,1,2, or 3 (" ; INT md ; STR ")" ]);
      raise (Invalid_input ("get_rm_sized_operand"))
    end


let get_rm_byte_operand ?(addrsize_override=false) md rm ch mode:operand_int = 
  get_rm_sized_operand ~addrsize_override ~size:1 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch mode

let get_rm_word_operand md rm ch mode:operand_int = 
  get_rm_sized_operand ~size:2 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch mode

let get_rm_operand md rm ?(seg_override=None) ?(size=4) ?(floating_point=false) ch mode:operand_int = 
  let op = get_rm_sized_operand ~size ~fp:floating_point ~mm:false ~xmm:false ~md ~rm ~ch mode in
  if op#is_absolute_address then
    match seg_override with
      Some seg -> seg_absolute_op seg op#get_absolute_address 4 mode
    | _ -> op
  else
    op

let get_rm_def_operand opsize_override ?(seg_override=None) md rm ch (mode:operand_mode_t):operand_int  =
  let size = if opsize_override then 2 else 4 in
  let op = get_rm_sized_operand ~size ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch mode in
  if op#is_absolute_address then
    match seg_override with
      Some seg -> seg_absolute_op seg op#get_absolute_address size mode
    | _ -> op
  else
    op

(* returns the two operands encoded in the modrm byte (Figure 2-1):
   1: modrm operand  (ModR/M)
   2: register operand (Reg)                                            *)
let get_modrm_operands ?(seg_override=None) 
    ?(addrsize_override=false) ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = register_op (select_reg reg) 4 m2 in
  let op1 = get_rm_sized_operand ~addrsize_override ~seg_override ~size:4 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_byte_operands ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = register_op (select_byte_reg reg) 1 m2 in
  let op1 = get_rm_sized_operand ~size:1 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_word_operands ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = register_op (select_word_reg reg) 2 m2 in
  let op1 = get_rm_sized_operand ~size:2 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_quadword_operands ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = mm_register_op reg m2 in
  let op1 = get_rm_sized_operand ~size:8 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_double_quadword_operands ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = xmm_register_op reg m2 in
  let op1 = get_rm_sized_operand ~size:16 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_mm_operands ch size m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = mm_register_op reg m2 in
  let op1 = get_rm_sized_operand ~size ~fp:false ~mm:true ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_xmm_operands ch size m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = xmm_register_op reg m2 in
  let op1 = get_rm_sized_operand ~size ~fp:false ~mm:false ~xmm:true ~md ~rm ~ch m1 in
  (op1,op2)

(* modrm: xmm or m:size, reg: mm *)
(* return (mm,reg) *)
let get_modrm_xmm_mm_operands ch size m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = mm_register_op reg m2 in
  let op1  = get_rm_sized_operand ~size ~fp:false ~mm:false ~xmm:true ~md ~rm ~ch m1 in
  (op1,op2)

(* modrm: xmm or m:size, reg: reg *)
let get_modrm_xmm_reg_operands ch size m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = register_op (select_reg reg) 4 m2 in
  let op1 = get_rm_sized_operand ~size ~fp:false ~mm:false ~xmm:true ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_sized_operands ch size1 m1 size2 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op2 = match size2 with
      1 -> register_op (select_byte_reg reg) 1 m2
    | 2 -> register_op (select_word_reg reg) 2 m2
    | 4 -> register_op (select_reg reg) 4 m2
    | 8 -> mm_register_op reg m2
    | 16 -> xmm_register_op reg m2
    | _ ->
      begin
	ch_error_log#add "disassembly"
	  (LBLOCK [ STR "Unexpected operand size: " ; INT size2 ]) ;
	raise (BCH_failure (LBLOCK [ STR "Unexpected operand size: " ; INT size2 ]))
      end in
  let op1 = get_rm_sized_operand ~size:size1 ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

let get_modrm_def_operands opsize_override ?(seg_override=None) ?(addrsize_override=false) 
    ch m1 m2:(operand_int * operand_int) =
  let size = if opsize_override then 2 else 4 in
  let (op1,op2) =
    if opsize_override then 
      get_modrm_word_operands ch m1 m2 
    else 
      get_modrm_operands ~addrsize_override ~seg_override ch m1 m2 in
  let op1 = if op1#is_absolute_address then
      match seg_override with 
	Some seg -> seg_absolute_op seg op1#get_absolute_address size m1 
      | _ -> op1 else op1 in
  (op1, op2)
		
let get_modrm_seg_operands ?(opsize_override=false) ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let size = if opsize_override then 2 else 4 in
  let op2 = seg_register_op (select_seg_reg reg) m2  in
  let op1 = get_rm_sized_operand ~size ~fp:false ~mm:false ~xmm:false ~md ~rm ~ch m1 in
  (op1,op2)

(* the reg field within the ModR/M byte specifies which of the control registers 
   is loaded or read. The 2 bits in the mod field are ignored. The r/m field specifies
   the general-purpose register loaded or read. Attempts to reference CR1, CR5, CR6,
   CR7, and CR9–CR15 result in undefined opcode (#UD) exceptions *)
let get_modrm_cr_operands ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op1 = control_register_op reg m1 in
  let op2 = register_op (select_reg rm) 4 m2 in
  (op1,op2)

let get_modrm_dr_operands ch m1 m2:(operand_int * operand_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let op1 = debug_register_op reg m1 in
  let op2 = register_op (select_reg rm) 4 m2 in
  (op1,op2)


let get_string_reference (floc:floc_int) (xpr:xpr_t) =
  try
    match xpr with
    | XConst (IntConst num) ->
      let address = numerical_to_doubleword num in
      begin
	match FFU.get_string_reference address with
	| Some str ->
	  begin
	    string_table#add_xref address str floc#fa floc#cia ;
            chlog#add "add string" (LBLOCK [ floc#l#toPretty ; STR "; " ; STR str ]) ;
	    Some str
	  end
	| _ -> None
      end
    | XOp (XPlus, [ XVar v ; XConst (IntConst num) ]) ->
      if floc#env#has_initialized_string_value v num#toInt then
	Some (floc#env#get_initialized_string_value v num#toInt)
      else
	None
    | _ -> None
  with
  | _ -> None
