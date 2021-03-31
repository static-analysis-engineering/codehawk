(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs, LLC

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

(* bchlibarm32 *)
open BCHARMPseudocode
open BCHARMTypes

   (* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16

let arm_operand_mode_to_string = function RD -> "RD" | WR -> "WR" | RW -> "RW"

let armreg_to_string (r:arm_reg_t) =
  match r with
  | AR0 -> "R0"
  | AR1 -> "R1"
  | AR2 -> "R2"
  | AR3 -> "R3"
  | AR4 -> "R4"
  | AR5 -> "R5"
  | AR6 -> "R6"
  | AR7 -> "R7"
  | AR8 -> "R8"
  | AR9 -> "R9"
  | AR10 -> "R10"
  | AR11 -> "R11"
  | AR12 -> "R12"
  | ARSP -> "SP"
  | ARLR -> "LR"
  | ARPC -> "PC"

let shift_rotate_type_to_string (srt:shift_rotate_type_t) =
  match srt with
  | SRType_LSL -> "LSL"
  | SRType_LSR -> "LSR"
  | SRType_ASR -> "ASR"
  | SRType_ROR -> "ROR"
  | SRType_RRX -> "RRX"

let register_shift_to_string (rs:register_shift_rotate_t) =
  match rs with
  | ARMImmSRT (SRType_ROR,0) -> ""
  | ARMImmSRT (srt,imm) ->
     (shift_rotate_type_to_string srt) ^ " #" ^ (string_of_int imm)
  | ARMRegSRT (srt,reg) ->
     (shift_rotate_type_to_string srt) ^ " " ^ (armreg_to_string reg)

let arm_memory_offset_to_string (offset:arm_memory_offset_t) =
  match offset with
  | ARMImmOffset off -> "#" ^ (string_of_int off)
  | ARMIndexOffset r -> armreg_to_string r
  | ARMShiftedIndexOffset (r,rs) ->
     match rs with
     | ARMImmSRT (SRType_LSL,0) -> armreg_to_string r
     | _ ->
        (armreg_to_string r) ^ "," ^ (register_shift_to_string rs)

    (*
let get_register_shift (shifttype:int) (imm:int):register_shift_t option =
  match (shifttype,imm) with
  | (0,0) -> None
  | (0,n) -> Some (SRType_LSL,n)
  | (1,n) -> Some (SRType_LSR,n)
  | (2,n) -> Some (SRType_ASR,n)
  | (3,0) -> Some (SRType_RRX,0)
  | (3,n) -> Some (SRType_ROR,n)
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [ STR "Unexpected arguments for get_register_shift: ";
                    STR "shifttype: " ; INT shifttype;
                    STR "imm: " ; INT imm ]))
     *)
class arm_operand_t
        (kind:arm_operand_kind_t) (mode:arm_operand_mode_t):arm_operand_int =
object (self:'a)

  method get_kind = kind
  method get_mode = mode

  method get_register =
    match kind with
    | ARMReg r -> r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand is not a register: " ; self#toPretty ]))

  method get_absolute_address =
    match kind with
    | ARMAbsolute dw -> dw
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand is not an absolute address: " ;
                      self#toPretty ]))

  method get_pc_relative_address (va: doubleword_int) =
    match kind with
    | ARMOffsetAddress (ARPC, ARMImmOffset off,isadd, _, _) ->
       if isadd then
         va#add_int (8 + off)
       else
         va#add_int (8 - off)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand is no a pc-relative address: ";
                      self#toPretty ]))

  method to_numerical =
    match kind with
    | ARMImmediate imm -> imm#to_numerical
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand is not an immediate value: " ;
                      self#toPretty ]))

  method to_address (floc:floc_int):xpr_t =
    match kind with
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Cannot take address of immediate operand: " ;
                      self#toPretty ]))

  method to_variable (floc:floc_int):variable_t =
    match kind with
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Not implemented" ]))

  method to_expr (floc:floc_int):xpr_t =
    match kind with
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Not implemented" ]))

  method to_lhs (floc:floc_int) =
    match kind with
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Not implemented" ]))

  method is_register = match kind with ARMReg _ -> true | _ -> false

  method is_register_list = match kind with ARMRegList _ -> true | _ -> false

  method is_read = match mode with RW | RD -> true | _ -> false

  method is_write = match mode with RW | WR -> true | _ -> false

  method is_absolute_address =
    match kind with ARMAbsolute _ -> true | _ -> false

  method is_pc_relative_address =
    match kind with
    | ARMOffsetAddress (ARPC, ARMImmOffset _, _, _, _) -> true
    | _ -> false

  method includes_pc =
    match kind with
    | ARMRegList rl -> List.mem ARPC rl
    | _ -> false

  method toString =
    match kind with
    | ARMReg r -> armreg_to_string r
    | ARMRegList l ->
       "{" ^ String.concat "," (List.map armreg_to_string l) ^ "}"
    | ARMShiftedReg (r,rs) ->
       let pshift = register_shift_to_string rs in
       let pshift = if pshift = "" then "" else "," ^ pshift in
       (armreg_to_string r) ^ pshift
    | ARMRegBitSequence (r,lsb,widthm1) ->
       (armreg_to_string r) ^ ", #" ^ (string_of_int lsb)
       ^ ", #" ^ (string_of_int (widthm1+1))
    | ARMImmediate imm -> "#" ^ imm#to_string
    | ARMAbsolute addr -> addr#to_hex_string
    | ARMMemMultiple (r,n) ->
       (armreg_to_string r) ^ "<" ^ (string_of_int n) ^ ">"
    | ARMOffsetAddress (reg,offset,isadd,iswback,isindex) ->
       let poffset = arm_memory_offset_to_string offset in
       let poffset = if isadd then poffset else "-" ^ poffset in
       (match (iswback,isindex) with
        | (false,false) -> "??[" ^ (armreg_to_string reg) ^ ", " ^ poffset ^ "]"
        | (false,true) -> "[" ^ (armreg_to_string reg) ^ ", " ^ poffset ^ "]"
        | (true,false) -> "[" ^ (armreg_to_string reg) ^ ", " ^ poffset ^ "]!"
        | (true,true) -> "[" ^ (armreg_to_string reg) ^ "], " ^ poffset)

  method toPretty = STR self#toString

end

let arm_register_op (r:arm_reg_t) (mode:arm_operand_mode_t) =
  new arm_operand_t (ARMReg r) mode

let arm_register_list_op (l:arm_reg_t list) (mode:arm_operand_mode_t) =
  new arm_operand_t (ARMRegList l) mode

let mk_arm_imm_shifted_register_op
      (r:arm_reg_t)
      (ty:int)    (* 0 - 3 *)
      (imm:int)
      (mode:arm_operand_mode_t) =
  let (shifttype,shiftamount) = decode_imm_shift ty imm in
  let regshift = ARMImmSRT (shifttype,shiftamount) in
  new arm_operand_t (ARMShiftedReg (r,regshift)) mode

let mk_arm_reg_shifted_register_op
      (r:arm_reg_t)         (* register to be shifted *)
      (ty:int)              (* 0 - 3 *)
      (rs:arm_reg_t)        (* register whose lowest byte controls the shift *)
      (mode:arm_operand_mode_t) =
  let shift = decode_reg_shift ty in
  let regshift = ARMRegSRT (shift,rs) in
  new arm_operand_t (ARMShiftedReg (r,regshift)) mode

let mk_arm_rotated_register_op
      (r:arm_reg_t)
      (rotation:int)
      (mode:arm_operand_mode_t) =
  let regshift = ARMImmSRT (SRType_ROR,rotation) in
  new arm_operand_t (ARMShiftedReg (r,regshift)) mode

let mk_arm_reg_bit_sequence_op
      (r:arm_reg_t)
      (lsb:int)
      (widthm1:int)
      (mode:arm_operand_mode_t) =
  new arm_operand_t (ARMRegBitSequence (r,lsb,widthm1)) mode

let mk_arm_immediate_op (signed:bool) (size:int) (imm:numerical_t) =
    let immval =
      if signed || imm#geq numerical_zero then
        imm
      else
        match size with
        | 1 -> imm#add (mkNumerical e8)
        | 2 -> imm#add (mkNumerical e16)
        | 4 -> imm#add (mkNumerical e32)
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [ STR "Unexpected size in arm-immediate-op: " ;
                          INT size ])) in
    let op = ARMImmediate (make_immediate signed size immval#getNum) in
    new arm_operand_t op RD

let arm_immediate_op (imm:immediate_int) = new arm_operand_t (ARMImmediate imm) RD

let arm_absolute_op (addr:doubleword_int) (mode:arm_operand_mode_t) =
  new arm_operand_t (ARMAbsolute addr) mode

let mk_arm_absolute_target_op
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (imm:int)
      (mode:arm_operand_mode_t) =
  let addr = base#add_int (ch#pos + 4) in
  let tgtaddr = addr#add_int imm in
  arm_absolute_op tgtaddr mode

let mk_arm_offset_address_op
      (reg:arm_reg_t)
      (offset:arm_memory_offset_t)
      ~(isadd:bool)
      ~(iswback:bool)
      ~(isindex:bool) =
  new arm_operand_t (ARMOffsetAddress (reg,offset,isadd,iswback,isindex))

let mk_arm_mem_multiple_op (reg:arm_reg_t) (n:int) =
  new arm_operand_t (ARMMemMultiple (reg,n))
