(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHFunctionData
open BCHImmediate
open BCHLibTypes
open BCHSystemInfo
open BCHSystemSettings
open BCHUserProvidedDirections

(* bchlibx86 *)
open BCHLibx86Types

module FFU = BCHFileFormatUtil
module TR = CHTraceResult


let asm_operand_kind_is_equal a1 a2 =
  match (a1,a2) with
  | (Flag f1, Flag f2) -> f1 = f2
  | (Reg r1, Reg r2) -> r1 = r2
  | (FpuReg i1, FpuReg i2) -> i1 = i2
  | (ControlReg i1, ControlReg i2) -> i1 = i2
  | (DebugReg i1, DebugReg i2) -> i1 = i2
  | (MmReg i1, MmReg i2) -> i1 = i2
  | (XmmReg i1, XmmReg i2) -> i1 = i2
  | (SegReg s1, SegReg s2) -> s1 = s2
  | (IndReg (r1,off1), IndReg (r2,off2)) -> r1 = r2 && off1#equal off2
  | (SegIndReg (s1,r1,off1), SegIndReg (s2,r2,off2)) ->
     s1 = s2 && r1 = r2 && off1#equal off2
  | (ScaledIndReg (r1,i1,s1,off1), ScaledIndReg (r2,i2,s2,off2)) ->
    r1 = r2 && i1 = i2 && s1 = s2 && off1#equal off2
  | (DoubleReg (r1a,r1b),DoubleReg (r2a,r2b)) -> r1a = r2a && r1b = r2b
  | (Imm i1, Imm i2) -> i1#equal i2
  | (Absolute d1, Absolute d2) -> d1#equal d2
  | (FarAbsolute (s1, d1), FarAbsolute (s2, d2)) -> s1 = s2 && d1#equal d2
  | (SegAbsolute (s1,d1), SegAbsolute (s2,d2)) -> s1 = s2 && d1#equal d2
  | (DummyOp,DummyOp) -> true
  | _ -> false


let offset_to_string (offset:numerical_t) =
  if offset#is_zero then"" else
    try
      let dw = TR.tget_ok (numerical_to_doubleword offset) in
      if system_info#is_code_address dw then
	if functions_data#is_function_entry_point dw then
	  if functions_data#has_function_name dw then
	    "fp:" ^ (functions_data#get_function dw)#get_function_name
	  else
	    "fp:" ^ dw#to_hex_string
	else
	  match system_info#is_in_data_block dw with
	  | Some db ->
	    let dboffset = TR.tget_ok (dw#subtract db#get_start_address) in
	    "db:" ^ db#get_start_address#to_hex_string
            ^ "[" ^ dboffset#to_hex_string ^ "]"
	  | _ ->
             match system_info#is_in_jumptable dw with
	     | Some jt ->
	        if jt#get_start_address#le dw then
		  let jtoffset = TR.tget_ok (dw#subtract jt#get_start_address) in
		  "jt:" ^ jt#get_start_address#to_hex_string
                  ^ "[" ^ jtoffset#to_hex_string ^ "]"
	        else
		  let jtoffset = TR.tget_ok (jt#get_start_address#subtract dw) in
		  "jt:" ^ jt#get_start_address#to_hex_string
                  ^ "[-" ^ jtoffset#to_hex_string ^ "]"
	     | _ -> "ca:" ^ dw#to_hex_string
      else
	TR.tget_ok (numerical_to_signed_hex_string offset)
    with
    | BCH_failure p ->
       let msg =
         LBLOCK [
             STR "offset_to_string: "; offset#toPretty; STR " ("; p; STR ")"] in
       begin
         ch_error_log#add "illegal offset"  msg;
         "illegal offset(" ^ offset#toString ^ ")"
       end
    | Invalid_argument s ->
       begin
	 ch_error_log#add
           "illegal offset" (LBLOCK [offset#toPretty; STR ": "; STR s]);
	 "illegal offset(" ^ offset#toString ^ ")"
       end


let asm_operand_kind_to_string = function
  | Flag f -> eflag_to_string f
  | Reg reg -> cpureg_to_string reg
  | FpuReg reg -> "%st(" ^ (string_of_int reg) ^ ")"
  | ControlReg reg -> "CR" ^ (string_of_int reg)
  | DebugReg reg -> "DR" ^ (string_of_int reg)
  | MmReg reg -> "%mm" ^ (string_of_int reg)
  | XmmReg reg -> "%xmm" ^ (string_of_int reg)
  | SegReg reg -> segment_to_string reg
  | IndReg (reg,offset) ->
     let offset = offset_to_string offset in
     offset ^ "(" ^ (cpureg_to_asm_string reg) ^ ")"
  | SegIndReg (seg,reg,offset) ->
     let offset = offset_to_string offset in
     (segment_to_string seg) ^ ":" ^ offset ^ "(" ^ (cpureg_to_asm_string reg) ^ ")"
  | ScaledIndReg (base,ind,scale,offset) ->
     let offset = offset_to_string offset in
     offset ^ "(" ^ (cpureg_option_to_string base)
     ^ "," ^ (cpureg_option_to_string ind)
     ^ "," ^ (string_of_int scale) ^ ")"
  | DoubleReg (rh,rl) ->
     (cpureg_to_string rh) ^ ":" ^ (cpureg_to_string rl)
  | Imm imm -> imm#to_hex_string
  | Absolute dw -> dw#to_hex_string
  | FarAbsolute (s, dw) -> dw#to_hex_string ^ " (" ^ (string_of_int s) ^ ")"
  | SegAbsolute (seg, dw) ->
     Printf.sprintf "%s:%s" (segment_to_string seg) dw#to_hex_string
  | DummyOp -> ""


let operand_mode_to_string =
  function RD -> "RD" | WR -> "WR" | RW -> "RW" | AD -> "AD"


class operand_t
        (kind:asm_operand_kind_t)
        (op_size:int)
        (mode:operand_mode_t):operand_int =
object (self:'a)

  val kind = kind
  val op_size = op_size    (* size in bytes *)
  val mode = mode
  val mutable function_argument = None

  method equal (other:'a) =
    asm_operand_kind_is_equal kind other#get_kind && op_size = other#size

  method size = op_size
  method get_kind = kind
  method get_mode = mode

  method set_function_argument (callAddress:ctxt_iaddress_t) (seqNr:int) =
    function_argument <- Some (callAddress, seqNr)

  method reset_function_argument =
    begin
      (match function_argument with
       | Some (callAddress, seqNr) ->
	  chlog#add
            "resetting arguments"
	    (LBLOCK [
                 STR "Resetting argument ";
                 INT seqNr;
                 STR " for function at ";
		 STR callAddress])
       | _ -> ()) ;
      function_argument <- None
    end

  method is_function_argument =
    match function_argument with Some _ -> true | _ -> false

  method get_function_argument =
    match function_argument with
    | Some arg -> arg
    | _ ->
       let msg =
         LBLOCK [
             STR "Operand "; self#toPretty; STR " is not a function argument"] in
       begin
         ch_error_log#add "invocation error" msg;
         raise (BCH_failure msg)
       end

  method get_segment_register = match kind with
    | SegReg s -> s
    | _ ->
       begin
         ch_error_log#add
           "invocation error"
           (LBLOCK [STR "operand#get_segment_register: "; self#toPretty]);
         raise (Invocation_error "operand#get_segment_register")
       end

  method get_absolute_address = match kind with
    | Absolute a -> a
    | FarAbsolute (_, a) -> a
    | _ ->
       begin
         ch_error_log#add
           "invocation error"
	   (LBLOCK [STR "operand#get_absolute_address: "; self#toPretty]);
         raise (Invocation_error "operand#get_absolute_address")
       end

  method get_cpureg = match kind with
    | Reg r -> r
    | _ ->
       let msg = LBLOCK [STR "Not an x86 cpu register: "; self#toPretty] in
       begin
         ch_error_log#add "operand mismatch" msg;
         raise (BCH_failure msg)
       end

  method get_immediate_value =
    match kind with
    | Imm imm -> imm
    | _ ->
       begin
         ch_error_log#add "invocation error"
	   (LBLOCK [STR "operand#get_immediate: "; self#toPretty]);
         raise (Invocation_error "operand#get_immediate")
       end

  method get_esp_offset =
    match kind with
    | IndReg (Esp, offset)
    | ScaledIndReg (None, Some Esp, 1, offset)
    | ScaledIndReg (Some Esp, None, 1, offset) -> offset
    | _ ->
      begin
	ch_error_log#add "invocation error"  (STR "operand#get_esp_offset");
	raise (Invocation_error "operand#get_esp_offset")
      end

  method get_jump_table_target =
    match kind with
    | ScaledIndReg (None, Some reg, 4, offset) -> (offset, (CPURegister reg))
    | _ ->
      begin
	ch_error_log#add "invocation error" (STR "operand#get_jump_table_target");
	raise (Invocation_error "operand#get_jump_table_target")
      end

  method get_address_registers =
    match kind with
    | ScaledIndReg (Some cpureg,None, 1, _)
    | ScaledIndReg (None, Some cpureg,1, _)
    | IndReg (cpureg, _) -> [cpureg]
    | _ -> []

  method to_address (floc:floc_int):xpr_t =
    match kind with
    | Imm _ | Reg _ ->
       begin
	 ch_error_log#add
           "invocation error"
	   (LBLOCK [
                STR "Operand ";
                self#toPretty;
                STR " does not have an address"]);
	 raise (Invocation_error "operand#to_address")
       end
    | ScaledIndReg (Some cpureg, None, _, offset)
    | ScaledIndReg (None, Some cpureg, 1, offset)
    | IndReg (cpureg, offset) ->
      let registerVariable = floc#f#env#mk_cpu_register_variable cpureg in
      if offset#equal numerical_zero then
	XVar registerVariable
      else if offset#gt numerical_zero then
	XOp (XPlus, [ XVar registerVariable ; num_constant_expr offset])
      else
	XOp (XMinus, [XVar registerVariable ; num_constant_expr offset#neg])
    | ScaledIndReg (Some cpureg, Some indexreg, scale, offset) ->
       (* result = cpureg + scale * indexreg + offset *)
      let cpuregVar = floc#f#env#mk_cpu_register_variable cpureg in
      let indexregVar = floc#f#env#mk_cpu_register_variable indexreg in
      let registerSum =
	XOp (XPlus,
             [XVar cpuregVar;
	      XOp (XMult, [int_constant_expr scale ; XVar indexregVar])]) in
      if offset#equal numerical_zero then
	registerSum
      else if offset#gt numerical_zero then
	XOp (XPlus, [registerSum; num_constant_expr offset])
      else
	XOp (XMinus, [registerSum; num_constant_expr offset#neg])
    | _ -> random_constant_expr

  method to_value (floc:floc_int):xpr_t =
    match kind with
    | Imm imm -> num_constant_expr imm#to_numerical
    | Reg register ->
      let var = floc#f#env#mk_cpu_register_variable register in
      if floc#is_constant var then
	num_constant_expr (floc#get_constant var)
      else
	random_constant_expr
    | Absolute address when FFU.is_read_only_address address ->
      begin
	match FFU.get_read_only_initialized_doubleword address with
	  Some value -> num_constant_expr value#to_numerical
	| _ ->
	  random_constant_expr
      end
    | _ -> random_constant_expr

  (* to_variable cases

     ---- immediate ---- error (immediate cannot be a variable)
     |
     ---- register  ---- env#get_register_variable
     |
     ---- absolute address ---- env#get_absolute_memory_variable
     |
     ---- indirect address (needs invariant to resolve)
           |
           ------ constant (absolute address) ----- env#get_absolute_memory_variable
           |
           ------ base, offset ---------- function_environment#get_memory_reference
           |                            |--- env#get_memory_variable
           |
           ------ address_expr ---------- function_environment#get_memory_reference_from_address
           |                            | --- env#get_memory_variable
           |
           ------ no information --- env#get_unknown_memory_variable
  *)
  method to_variable (floc:floc_int):variable_t =
    let env = floc#f#env in
    match kind with
    | Imm _ ->
      begin
	ch_error_log#add
          "invocation error"
	  (LBLOCK [ STR "Immediate cannot be converted to a variable" ]);
	raise (Invocation_error "operand#to_variable")
      end
    | Flag flag -> env#mk_flag_variable (X86Flag flag)
    | Reg register -> env#mk_cpu_register_variable register
    | FpuReg regIndex -> env#mk_fpu_register_variable regIndex
    | ControlReg regIndex -> env#mk_control_register_variable regIndex
    | DebugReg regIndex -> env#mk_debug_register_variable regIndex
    | MmReg regIndex -> env#mk_mmx_register_variable regIndex
    | XmmReg regIndex -> env#mk_xmm_register_variable regIndex
    | DoubleReg (reg1,reg2) -> env#mk_double_register_variable reg1 reg2
    | Absolute address ->
       (match env#mk_global_variable address#to_numerical with
        | Error e ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Absolute address to-variable: ";
                     STR (String.concat "; " e)]))
        | Ok var -> var)
    | FarAbsolute (_, addr) ->
       (match env#mk_global_variable addr#to_numerical with
        | Error e ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "FarAbsolute address to-variable: ";
                     STR (String.concat "; " e)]))
        | Ok var -> var)
    | ScaledIndReg (Some cpureg, None, 1, offset)
    | ScaledIndReg (None, Some cpureg, 1, offset)
    | IndReg (cpureg, offset) ->
      let registerVariable = env#mk_cpu_register_variable cpureg in
      floc#get_memory_variable_1 registerVariable offset

    (* either register can function as base *)
    | ScaledIndReg (Some baseReg, Some indexReg, 1, offset) ->
      let baseVar = env#mk_cpu_register_variable baseReg in
      let indexVar = env#mk_cpu_register_variable indexReg in
      floc#get_memory_variable_2 baseVar indexVar offset

    (* baseReg must be the base *)
    | ScaledIndReg (Some baseReg, Some indexReg, scale, offset) ->
      let baseVar = env#mk_cpu_register_variable baseReg in
      let indexVar = env#mk_cpu_register_variable indexReg in
      floc#get_memory_variable_3 baseVar indexVar scale offset

    | ScaledIndReg (None, Some indexReg, scale, offset) ->
      let indexVar = env#mk_cpu_register_variable indexReg in
      floc#get_memory_variable_4 indexVar scale offset

    | _ ->  env#mk_unknown_memory_variable "operand"

  (* TBD: have to add options for size and zero/sign extend *)
  method to_expr ?(unsigned=false) (floc:floc_int):xpr_t =
    match kind with
    | Imm imm ->
       let imm = if unsigned then imm#to_unsigned else imm in
       num_constant_expr imm#to_numerical
    | Absolute address when FFU.is_read_only_address address ->
       begin
	 match FFU.get_read_only_initialized_doubleword address with
	 | Some value -> num_constant_expr value#to_numerical
	 | _ -> XVar (self#to_variable floc)
       end
    | _ -> XVar (self#to_variable floc)

  method to_lhs ?(_size=4) (floc:floc_int) =
    let env = floc#f#env in
    match kind with
    | Imm _ ->
       begin
	 ch_error_log#add "invocation error" (STR "operand#get_lhs: immediate");
	 raise (Invocation_error "operand#get_lhs")
       end
    | Reg cpureg ->
       let registersClobbered = registers_affected_by cpureg in
       let vars =
         List.map (fun reg ->
	     env#mk_cpu_register_variable reg) registersClobbered in
       (self#to_variable floc, [ ABSTRACT_VARS vars ])
    | DoubleReg (reg1,reg2) ->
       let registerVariable1 = env#mk_cpu_register_variable reg1 in
       let registerVariable2 = env#mk_cpu_register_variable reg2 in
       let cmd = ABSTRACT_VARS [registerVariable1 ; registerVariable2] in
       (self#to_variable floc, [cmd])
    | _ ->
       let v = self#to_variable floc in
       if (v#isTmp || floc#env#is_unknown_memory_variable v)
          && (not system_settings#is_abstract_stackvars_disabled) then
	match kind with
	| IndReg(Esp, _)
	| ScaledIndReg (Some Esp, _, _, _)
	| ScaledIndReg (_, Some Esp, _, _) ->
	  let stackvars = floc#env#get_local_stack_variables in
	  let cmd = ABSTRACT_VARS stackvars in
	  (v, [cmd])
	| _ -> (v, [])
      else
	(v, [])

  method is_esp_offset =
    match kind with
    | IndReg (Esp, _)
    | ScaledIndReg (None, Some Esp, 1, _)
    | ScaledIndReg (Some Esp, None, 1, _) -> true
    | _ -> false

  method is_register = match kind with Reg _ -> true | _ -> false

  method is_seg_register = match kind with SegReg _ -> true | _ -> false

  method is_absolute_address =
    match kind with
    | Absolute _ | FarAbsolute _ -> true
    | _ -> false

  method is_immediate_value = match kind with Imm _ -> true | _ -> false

  method is_indirect_register = match kind with  IndReg _ -> true | _ -> false

  method get_indirect_register =
    match kind with
    | IndReg (reg,_) -> reg
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not an indirect register: "; self#toPretty]))

  method get_indirect_register_offset =
    match kind with
    | IndReg (_, offset) -> offset
    | _ ->
       raise (
           BCH_failure
             (LBLOCK [
                  STR "Operand is not an indirect register: "; self#toPretty]))

  method is_memory_access = match kind with
  | Reg _ | FpuReg _ | MmReg _ | XmmReg _ | SegReg _ | DoubleReg _
  | Imm _ | DummyOp -> false
  | _ -> true

  method is_read  = match mode with RW | RD -> true | _ -> false

  method is_write = match mode with RW | WR -> true | _ -> false

  method is_zero =
    match kind with
    | Imm imm ->
       (match imm#to_int with
        | Some i -> i = 0
        | _ -> false)
    | _ -> false

  method has_one_bit_set =
    match kind with
    | Imm imm ->
       (match imm#to_doubleword with
        | Some dw -> (List.length dw#get_bits_set) = 1
        | _ -> false)
    | _ -> false

  method is_jump_table_target =
    match kind with
    | ScaledIndReg (None, Some _, 4, _) -> true
    | _ -> false

  method to_byte_operand =
    try
      match kind with
      | Reg r -> {< kind = Reg (byte_reg_of_reg r) >}
      | _ -> {< >}
    with
      Invalid_argument _ ->
	begin
	  ch_error_log#add
            "operand"
	    (LBLOCK [
                 self#toPretty;
                 STR ": #to_byte_operand is not a valid operation"]);
	  {< >}
	end

  method to_word_operand =
    match kind with
    | Reg r -> {< kind = Reg (word_reg_of_reg r) >}
    | _ -> {< >}

  method sign_extend (size: int) =
    match kind with
    | Imm imm ->
       let ximm = imm#sign_extend size in
       if Result.is_ok ximm then
         {< kind = Imm (TR.tget_ok ximm) >}
       else
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Sign extension of immediate to size: ";
                   INT size;
                   STR " not supported"]))
    | _ -> {< >}

  method toString =
    match kind with
    | Absolute addr when self#is_read && system_info#is_code_address addr ->
      begin
	match system_info#is_in_data_block addr with
	| Some db ->
	  let dboffset = TR.tget_ok (addr#subtract db#get_start_address) in
	  "dbv:"
          ^ db#get_start_address#to_hex_string
          ^ "["
          ^ dboffset#to_hex_string
          ^ "]"
	| _ -> match system_info#is_in_jumptable addr with
	  | Some jt ->
	    if jt#get_start_address#le addr then
	      let jtoffset = TR.tget_ok (addr#subtract jt#get_start_address) in
	      "jtv:"
              ^ jt#get_start_address#to_hex_string
              ^ "["
              ^ jtoffset#to_hex_string
              ^ "]"
	    else
	      let jtoffset = TR.tget_ok (jt#get_start_address#subtract addr) in
	      "jtv:"
              ^ jt#get_start_address#to_hex_string
              ^ "[-"
              ^ jtoffset#to_hex_string
              ^ "]"
	  | _ -> "cav:" ^ addr#to_hex_string
      end
    | FarAbsolute (s, addr) when self#is_read && system_info#is_code_address addr ->
       "far:" ^ addr#to_hex_string ^ "(" ^ (string_of_int s) ^ ")"
    | _ -> asm_operand_kind_to_string kind

  method write_xml (_node:xml_element_int) (_floc:floc_int) = ()

  method toPretty = STR self#toString

end


let dummy_operand = new operand_t DummyOp 0 RD


let flag_op (flag:eflag_t) (mode:operand_mode_t) =
  new operand_t (Flag flag) 1 mode


let register_op (reg:cpureg_t) (size:int) (mode:operand_mode_t) =
  new operand_t (Reg reg) size mode


let double_register_op
      (reg1:cpureg_t) (reg2:cpureg_t) (size:int) (mode:operand_mode_t) =
  new operand_t (DoubleReg (reg1,reg2)) size mode


let fpu_register_op (i:int) (mode: operand_mode_t) =
  new operand_t (FpuReg i) 8 mode


let mm_register_op  (i:int) (mode: operand_mode_t) =
  new operand_t (MmReg i)  8 mode


let xmm_register_op (i:int) (mode: operand_mode_t) =
  new operand_t (XmmReg i) 16 mode


let seg_register_op (reg:segment_t) (mode: operand_mode_t) =
  new operand_t (SegReg reg) 2 mode


let control_register_op (i:int) (mode: operand_mode_t) =
  new operand_t (ControlReg i) 4 mode


let debug_register_op (i:int) (mode: operand_mode_t) =
  new operand_t (DebugReg i) 4 mode


let indirect_register_op
      (reg:cpureg_t) (offset:numerical_t) (size:int) (mode:operand_mode_t) =
  new operand_t (IndReg (reg,offset)) size mode


let scaled_register_op
      (base:cpureg_t option)
      (index_reg:cpureg_t option)
      (scale:int)
      (offset:numerical_t)
      (size:int)
      (mode:operand_mode_t) =
  new operand_t (ScaledIndReg (base,index_reg,scale,offset)) size mode


let seg_indirect_register_op
      (seg:segment_t) (reg:cpureg_t) (offset:numerical_t) (size:int) =
  new operand_t (SegIndReg (seg,reg,offset)) size


let absolute_op (address:doubleword_int) (size:int) (mode:operand_mode_t) =
  new operand_t (Absolute address) size mode


let ds_esi ?(seg=DataSegment) ?(size=4) (mode: operand_mode_t) =
  if user_provided_directions#are_DS_and_ES_the_same_segment then
    indirect_register_op Esi numerical_zero size mode
  else
    seg_indirect_register_op seg Esi numerical_zero 4 mode


let es_edi ?(seg=ExtraSegment) ?(size=4) (mode: operand_mode_t) =
  if user_provided_directions#are_DS_and_ES_the_same_segment then
    indirect_register_op Edi numerical_zero size mode
  else
    seg_indirect_register_op seg Edi numerical_zero 4 mode


let edx_eax_r (mode: operand_mode_t) = double_register_op Edx Eax 8 mode


let dx_ax_r (mode: operand_mode_t) = double_register_op Dx Ax 4 mode


let esp_deref ?(with_offset=0) (mode:operand_mode_t) =
  indirect_register_op Esp (mkNumerical with_offset) 4 mode


let ebp_deref (mode:operand_mode_t) =
  indirect_register_op Ebp numerical_zero 4 mode


let immediate_op (imm:immediate_int) (size:int) =
  new operand_t (Imm imm) size RD


let seg_absolute_op
      (seg:segment_t) (address:doubleword_int) (size:int) (mode:operand_mode_t) =
  new operand_t (SegAbsolute (seg,address)) size mode


let far_absolute_op
      (sd: int) (addr: doubleword_int) (size: int) (mode: operand_mode_t) =
  new operand_t (FarAbsolute (sd, addr)) size mode


(* Flag operands *)
let oflag_op (mode: operand_mode_t) = flag_op OFlag mode
let cflag_op (mode: operand_mode_t) = flag_op CFlag mode
let zflag_op (mode: operand_mode_t) = flag_op ZFlag mode
let sflag_op (mode: operand_mode_t) = flag_op SFlag mode
let pflag_op (mode: operand_mode_t) = flag_op PFlag mode
let dflag_op (mode: operand_mode_t) = flag_op DFlag mode
let iflag_op (mode: operand_mode_t) = flag_op IFlag mode


(* Register operands *)
let eax_r (mode: operand_mode_t) = register_op Eax 4 mode
let ecx_r (mode: operand_mode_t) = register_op Ecx 4 mode
let edx_r (mode: operand_mode_t) = register_op Edx 4 mode
let ebx_r (mode: operand_mode_t) = register_op Ebx 4 mode
let esp_r (mode: operand_mode_t) = register_op Esp 4 mode
let ebp_r (mode: operand_mode_t) = register_op Ebp 4 mode
let esi_r (mode: operand_mode_t) = register_op Esi 4 mode
let edi_r (mode: operand_mode_t) = register_op Edi 4 mode
let ax_r (mode: operand_mode_t) = register_op Ax 2 mode
let cx_r (mode: operand_mode_t)= register_op Cx 2 mode
let dx_r (mode: operand_mode_t)= register_op Dx 2 mode
let bx_r (mode: operand_mode_t)= register_op Bx 2 mode
let sp_r (mode: operand_mode_t)= register_op Sp 2 mode
let bp_r (mode: operand_mode_t)= register_op Bp 2 mode
let si_r (mode: operand_mode_t)= register_op Si 2 mode
let di_r (mode: operand_mode_t)= register_op Di 2 mode
let al_r (mode: operand_mode_t)= register_op Al 1 mode
let ah_r (mode: operand_mode_t)= register_op Ah 1 mode
let cl_r (mode: operand_mode_t)= register_op Cl 1 mode
let ch_r (mode: operand_mode_t)= register_op Ch 1 mode
let dl_r (mode: operand_mode_t)= register_op Dl 1 mode
let dh_r (mode: operand_mode_t)= register_op Dh 1 mode
let bl_r (mode: operand_mode_t)= register_op Bl 1 mode
let bh_r (mode: operand_mode_t)= register_op Bh 1 mode


let cpureg_r ?(opsize_override=false) (i:int) (mode:operand_mode_t) =
  let reg = match i with
    | 0 -> Eax
    | 1 -> Ecx
    | 2 -> Edx
    | 3 -> Ebx
    | 4 -> Esp
    | 5 -> Ebp
    | 6 -> Esi
    | 7 -> Edi
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Register index not recognized: "; INT i])) in
  let reg = if opsize_override then word_reg_of_reg reg else reg in
  let size = if opsize_override then 2 else 4 in
  register_op reg size mode


let imm0_operand = immediate_op imm0 1
let imm1_operand = immediate_op imm1 1

let read_immediate_signed_byte_operand (ch: pushback_stream_int) =
  immediate_op ch#read_imm_signed_byte 1

let read_immediate_signed_word_operand (ch: pushback_stream_int) =
  immediate_op ch#read_imm_signed_word 2

let read_immediate_signed_doubleword_operand (ch: pushback_stream_int) =
  immediate_op ch#read_imm_signed_doubleword 4

let read_immediate_signed_operand size (ch: pushback_stream_int) =
  immediate_op (ch#read_imm_signed size) size

let read_immediate_unsigned_byte_operand (ch: pushback_stream_int) =
  immediate_op ch#read_imm_unsigned_byte 1

let read_immediate_unsigned_word_operand (ch: pushback_stream_int) =
  immediate_op ch#read_imm_unsigned_word 2

let read_immediate_unsigned_doubleword_operand (ch: pushback_stream_int) =
  immediate_op ch#read_imm_unsigned_doubleword 4

let read_immediate_unsigned_operand (size: int) (ch: pushback_stream_int) =
  immediate_op (ch#read_imm_unsigned size) size


(* read a relative 1-byte jump-target and convert to an
   absolute address using the current position in the code  *)
let read_target8_operand (base:doubleword_int) (ch:pushback_stream_int) =
  try
    let a = ch#read_num_signed_byte in
    let p = mkNumerical ch#pos in
    let offset = p#add a in
    let offsetdw = TR.tget_ok (numerical_to_doubleword offset) in
    absolute_op (base#add offsetdw) 4 RD
  with
  | BCH_failure p ->
     raise (BCH_failure (LBLOCK [STR "read_target8_operand: "; p]))


(* read a relative 4-byte jump-target and convert to an
   absolute address using the current position in the code *)
let read_target32_operand (base:doubleword_int) (ch:pushback_stream_int) =
  try
    let a = ch#read_num_signed_doubleword in
    let p = mkNumerical ch#pos in
    let offset = a#add p in
    let offsetdw = TR.tget_ok (numerical_to_doubleword offset) in
    absolute_op (base#add offsetdw) 4 RD
  with
  | BCH_failure p ->
     raise (BCH_failure (LBLOCK [STR "read_target32_operand: "; p]))
