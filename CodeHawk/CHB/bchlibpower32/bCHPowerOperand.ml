(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023  Aarno Labs LLC

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
open CHLogger
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprXml
open Xsimplify

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
open BCHXmlUtil

(* bchlibelf *)
open BCHELFHeader

(* bchlibpower32 *)
open BCHPowerTypes

module TR = CHTraceResult


(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16
let e63 = e32 * e31
let e64 = e32 * e32


let pwr_operand_mode_to_string (m: pwr_operand_mode_t) =
  match m with
  | RD -> "RD"
  | WR -> "WR"
  | RW -> "RW"
  | NT -> "NT"


let pwr_special_reg_to_string (reg: pwr_special_reg_t) =
  match reg with
  | PowerCR -> "CR"
  | PowerCTR -> "CTR"
  | PowerMSR -> "MSR"
  | PowerLR -> "LR"
  | PowerXER -> "XER"
  | PowerSRR0 -> "SSR0"
  | PowerSRR1 -> "SSR1"
  | PowerCSRR0 -> "CSRR0"
  | PowerCSRR1 -> "CSRR1"
  | PowerDSRR0 -> "DSRR0"
  | PowerDSRR1 -> "DSRR1"
  | PowerMCSRR0 -> "MCSRR0"
  | PowerMCSRR1 -> "MCSRR1"


let pwr_register_field_to_string (f: pwr_register_field_t) =
  match f with
  | PowerCR0 -> "cr0"
  | PowerCR1 -> "cr1"
  | PowerCR2 -> "cr2"
  | PowerCR3 -> "cr3"
  | PowerCR4 -> "cr4"
  | PowerCR5 -> "cr5"
  | PowerCR6 -> "cr6"
  | PowerCR7 -> "cr7"
  | PowerXERSO -> "XER[SO]"
  | PowerXEROV -> "XER[OV]"
  | PowerXERCA -> "XER[CA]"


class pwr_operand_t
        (kind: pwr_operand_kind_t)
        (mode: pwr_operand_mode_t): pwr_operand_int =
object (self)

  method get_kind = kind
  method get_mode = mode

  method is_read =
    match mode with | RW | RD -> true | _ -> false

  method is_write =
    match mode with | RW | WR -> true | _ -> false

  method get_absolute_address =
    match kind with
    | PowerAbsolute dw -> dw
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [self#toPretty; STR " is not an absolute address"]))

  method get_gp_register =
    match kind with
    | PowerGPReg i -> i
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [self#toPretty; STR " is not a general-purpose register"]))

  method get_special_register =
    match kind with
    | PowerSpecialReg r -> r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [self#toPretty; STR " is not a special-purpose register"]))

  method get_register_field =
    match kind with
    | PowerRegisterField f -> f
    | PowerConditionRegisterBit i ->
       (match i / 4 with
        | 0 -> PowerCR0
        | 1 -> PowerCR1
        | 2 -> PowerCR2
        | 3 -> PowerCR3
        | 4 -> PowerCR4
        | 5 -> PowerCR5
        | 6 -> PowerCR6
        | 7 -> PowerCR7
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Unexpected condition register bit value: "; INT i])))
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [self#toPretty; STR " is not a register field"]))

  method get_ind_base_register =
    match kind with
    | PowerIndReg (base, _) -> base
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [self#toPretty; STR " is not an indirect register"]))

  method get_xind_base_register =
    match kind with
    | PowerIndexedIndReg (base, _) -> base
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 self#toPretty; STR " is not an indexed indirect register"]))

  method get_xind_index_register =
    match kind with
    | PowerIndexedIndReg (_, index) -> index
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 self#toPretty; STR " is not an indexed indirect register"]))

  method is_absolute_address =
    match kind with
    | PowerAbsolute _ -> true
    | _ -> false

  method is_gp_register =
    match kind with
    | PowerGPReg _ -> true
    | _ -> false

  method is_sp_register =
    match kind with
    | PowerSpecialReg _ -> true
    | _ -> false

  method is_register_field =
    match kind with
    | PowerRegisterField _ -> true
    | _ -> false

  method is_ind_register =
    match kind with
    | PowerIndReg _ -> true
    | _ -> false

  method is_xind_register =
    match kind with
    | PowerIndexedIndReg _ -> true
    | _ -> false

  method is_default_cr =
    match kind with
    | PowerRegisterField PowerCR0 -> true
    | _ -> false

  method to_variable (floc: floc_int): variable_t =
    let env = floc#f#env in
    match kind with
    | PowerGPReg index ->
       env#mk_pwr_gp_register_variable index
    | PowerSpecialReg reg ->
       env#mk_pwr_sp_register_variable reg
    | PowerRegisterField f ->
       env#mk_pwr_register_field_variable f
    | PowerIndReg (index, offset) ->
       let rvar = env#mk_pwr_gp_register_variable index in
       floc#get_memory_variable_1 rvar offset
    | _ ->
    raise
      (BCH_failure
         (LBLOCK [STR "To_variable not implemented for "; self#toPretty]))
    
  method to_expr (floc: floc_int): xpr_t =
    match kind with
    | PowerImmediate imm -> num_constant_expr imm#to_numerical
    | PowerGPReg _ -> XVar (self#to_variable floc)
    | PowerSpecialReg _ -> XVar (self#to_variable floc)
    | PowerRegisterField _ -> XVar (self#to_variable floc)
    | PowerAbsolute a when elf_header#is_program_address a ->
       num_constant_expr a#to_numerical
    | PowerAbsolute a ->
       begin
         ch_error_log#add
           "absolute address"
           (LBLOCK [STR "Address "; a#toPretty; STR " not found"]);
         num_constant_expr a#to_numerical
       end
    | PowerIndReg _ -> XVar (self#to_variable floc)
    | _ ->
       begin
         ch_error_log#add
           "op#to_expr"
           (LBLOCK [STR "Not implemented for "; self#toPretty]);
         XConst XRandom
       end

  method to_shifted_expr (shift: int): xpr_t =
    match kind with
    | PowerImmediate imm ->
       num_constant_expr (imm#to_numerical#shift_left shift)
    | _ ->
       begin
         ch_error_log#add
           "op#to_shifted_expr"
           (LBLOCK [STR "Only available for immediate: "; self#toPretty]);
         XConst XRandom
       end

  method to_updated_offset_address (floc: floc_int): xpr_t =
    match kind with
    | PowerIndReg (_, offset) ->
       let env = floc#f#env in
       let memoff = num_constant_expr offset in
       let addr = XOp (XPlus, [self#to_address floc; memoff]) in
       floc#inv#rewrite_expr addr env#get_variable_comparator
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not an indirect register-address: ";
                 self#toPretty]))

  method to_numerical =
    match kind with
    | PowerImmediate imm -> imm#to_numerical
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Operand is not an immediate value: "; self#toPretty]))

  method to_lhs (floc: floc_int): (variable_t * cmd_t list) =
    match kind with
    | PowerImmediate _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Immediate cannot be a lhs: "; self#toPretty]))
    | PowerAbsolute _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Absolute address cannot be a lhs: "; self#toPretty]))
    | _ -> (self#to_variable floc, [])

  method to_address (floc: floc_int): xpr_t =
    match kind with
    | PowerIndReg (index, offset) ->
       let env = floc#f#env in
       let memoff = num_constant_expr offset in
       let rvar = env#mk_pwr_gp_register_variable index in
       let addr = XOp (XPlus, [XVar rvar; memoff]) in
       floc#inv#rewrite_expr addr env#get_variable_comparator
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Unable to take address of "; self#toPretty]))

  method toString =
    match kind with
    | PowerGPReg index -> "r" ^ (string_of_int index)
    | PowerSpecialReg reg -> (pwr_special_reg_to_string reg)
    | PowerRegisterField f -> (pwr_register_field_to_string f)
    | PowerConditionRegisterBit i ->
       let c = function
         | 0 -> "lt"
         | 1 -> "gt"
         | 2 -> "eq"
         | _ -> "so" in
       let (crf, b) = (i / 4, i mod 4) in
       if crf = 0 then
         c b
       else
         "4*cr" ^ (string_of_int crf) ^ "+" ^ (c b)
    | PowerImmediate imm -> imm#to_hex_string
    | PowerAbsolute dw -> dw#to_hex_string
    | PowerIndReg (index, offset) ->
       offset#toString ^ "(r" ^ (string_of_int index) ^ ")"
    | PowerIndexedIndReg (base, index) ->
       "r" ^ (string_of_int base) ^ "(r" ^ (string_of_int index) ^ ")"

  method toPretty = STR self#toString

end


let pwr_gp_register_op ~(index: int) ~(mode: pwr_operand_mode_t) =
  new pwr_operand_t (PowerGPReg index) mode


let pwr_special_register_op
      ~(reg:pwr_special_reg_t) ~(mode: pwr_operand_mode_t) =
  new pwr_operand_t (PowerSpecialReg reg) mode


let pwr_register_field_op
      ~(fld:pwr_register_field_t) ~(mode: pwr_operand_mode_t) =
  new pwr_operand_t (PowerRegisterField fld) mode


let pwr_indirect_register_op
      ~(basegpr: int) ~(offset: numerical_t) ~(mode: pwr_operand_mode_t) =
  new pwr_operand_t (PowerIndReg (basegpr, offset)) mode


let pwr_indexed_indirect_register_op
      ~(basegpr: int) ~(offsetgpr: int) ~(mode: pwr_operand_mode_t) =
  new pwr_operand_t (PowerIndexedIndReg (basegpr, offsetgpr)) mode


let pwr_absolute_op (addr: doubleword_int) (mode: pwr_operand_mode_t) =
  if system_info#is_code_address addr then
    new pwr_operand_t (PowerAbsolute addr) mode
  else
    raise
      (BCH_failure
         (LBLOCK [STR "Invalid absolute address: "; addr#toPretty]))


let pwr_immediate_op ~(signed: bool) ~(size: int) ~(imm: numerical_t) =
  let immval =
    if signed then
      match size with
      | 1 -> if imm#geq (mkNumerical e7) then imm#sub (mkNumerical e8) else imm
      | 2 -> if imm#geq (mkNumerical e15) then imm#sub (mkNumerical e16) else imm
      | 4 -> if imm#geq (mkNumerical e31) then imm#sub (mkNumerical e32) else imm
      | 8 -> if imm#geq (mkNumerical e63) then imm#sub (mkNumerical e64) else imm
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Unexpected size in pwr-immediate-op: "; INT size]))
    else
      if imm#geq numerical_zero then
        imm
      else
        match size with
        | 1 -> imm#add (mkNumerical e8)
        | 2 -> imm#add (mkNumerical e16)
        | 4 -> imm#add (mkNumerical e32)
        | 8 -> imm#add (mkNumerical e64)
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Unexpected size in pwr-immediate-op: "; INT size])) in
  let op =
    PowerImmediate (TR.tget_ok (make_immediate signed size immval)) in
  new pwr_operand_t op RD


let pwr_gp_register_op_convert (index: int) =
  if index = 0 then
    pwr_immediate_op ~signed:false ~size:4 ~imm:numerical_zero
  else
    pwr_gp_register_op ~index ~mode:RD


let crbit_op (index: int) ~(mode: pwr_operand_mode_t) =
  new pwr_operand_t (PowerConditionRegisterBit index) mode


let crf_op (index: int) =
  pwr_register_field_op
    ~fld:(match index with
          | 0 -> PowerCR0
          | 1 -> PowerCR1
          | 2 -> PowerCR2
          | 3 -> PowerCR3
          | 4 -> PowerCR4
          | 5 -> PowerCR5
          | 6 -> PowerCR6
          | 7 -> PowerCR7
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Condition register field: ";
                       INT index;
                       STR " is invalid"])))

let crbi_op (index: int) = crf_op (index / 4)


let pwr_cr_field_list (crm: int) ~(mode: pwr_operand_mode_t) =
  let indices =
    let rec aux (pos: int) (v: int) (bits: int list) =
      if pos = 8 then
        bits
      else if v mod 2 = 1 then
        aux (pos + 1) (v lsr 1) (pos :: bits)
      else
        aux (pos + 1) (v lsr 1) bits in
    aux 0 crm [] in
  List.map (fun i -> crf_op i ~mode) indices


let cr0_op = crf_op 0

let cr1_op = crf_op 1

let cr2_op = crf_op 2

let cr3_op = crf_op 3

let cr_op = pwr_special_register_op ~reg:PowerCR

let ctr_op = pwr_special_register_op ~reg:PowerCTR

let lr_op = pwr_special_register_op ~reg:PowerLR

let msr_op = pwr_special_register_op ~reg:PowerMSR

let xer_op = pwr_special_register_op ~reg:PowerXER

let xer_ca_op = pwr_register_field_op ~fld:PowerXERCA

let xer_so_op = pwr_register_field_op ~fld:PowerXERSO

let xer_ov_op = pwr_register_field_op ~fld:PowerXEROV
