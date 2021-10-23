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
open BCHARMSumTypeSerializer
open BCHARMTypes


let x2p = xpr_formatter#pr_expr

   (* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16


let arm_operand_mode_to_string = function RD -> "RD" | WR -> "WR" | RW -> "RW"

let dmb_option_to_string = dmb_option_mfts#ts


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


let vfp_datatype_to_string (t: vfp_datatype_t) =
  let stri = string_of_int in
  match t with
  | VfpNone -> ""
  | VfpSize s -> "." ^ (stri s)
  | VfpFloat s -> ".F" ^ (stri s)
  | VfpInt s -> ".I" ^ (stri s)
  | VfpPolynomial s -> ".P" ^ (stri s)
  | VfpSignedInt s -> ".S" ^ (stri s)
  | VfpUnsignedInt s -> ".U" ^ (stri s)


let arm_memory_offset_to_string (offset:arm_memory_offset_t) =
  let p_off off =
    if off = 0 then "" else " (+ " ^ (string_of_int off) ^ ")" in
  match offset with
  | ARMImmOffset off -> "#" ^ (string_of_int off)
  | ARMIndexOffset (r, off) -> (armreg_to_string r) ^ (p_off off)
  | ARMShiftedIndexOffset (r, rs, off) ->
     match rs with
     | ARMImmSRT (SRType_LSL, 0) -> (armreg_to_string r) ^ (p_off off)
     | _ ->
        (armreg_to_string r)
        ^ ","
        ^ (register_shift_to_string rs)
        ^ (p_off off)


class arm_operand_t
        (kind:arm_operand_kind_t) (mode:arm_operand_mode_t):arm_operand_int =
object (self:'a)

  val kind = kind
  val mode = mode

  method get_kind = kind
  method get_mode = mode

  method get_size =
    match kind with
    | ARMReg r -> 4
    | ARMExtensionReg (t, _) ->
       (match t with
        | XSingle -> 4
        | XDouble -> 8
        | XQuad -> 16)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand size not implemented for "; self#toPretty]))

  method get_register =
    match kind with
    | ARMReg r -> r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand is not a register: " ; self#toPretty ]))

  method get_register_count =
    match kind with
    | ARMRegList rl -> List.length rl
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Operand is not a register list: ";
                     self#toPretty]))

  method get_register_list =
    match kind with
    | ARMRegList rl -> rl
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Operand is not a register list: ";
                     self#toPretty]))

  method get_register_op_list: 'a list =
    match kind with
    | ARMRegList rl ->
       List.map (fun r -> {< kind = ARMReg r; mode = mode >}) rl
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not a register list: "; self#toPretty]))

  method get_absolute_address =
    match kind with
    | ARMAbsolute dw -> dw
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not an absolute address: "; self#toPretty ]))

  method get_literal_address =
    match kind with
    | ARMLiteralAddress dw -> dw
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not a literal address: "; self#toPretty]))

  method get_pc_relative_address (va: doubleword_int) (pcoffset: int) =
    match kind with
    | ARMOffsetAddress (ARPC, align, ARMImmOffset off, isadd, _, _) ->
       let va = int_to_doubleword (((va#to_int + pcoffset) / align) * align) in
       if isadd then
         va#add_int off
       else
         va#add_int (-off)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand is not a pc-relative address: ";
                      self#toPretty ]))

  method to_numerical =
    match kind with
    | ARMImmediate imm -> imm#to_numerical
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand is not an immediate value: " ;
                      self#toPretty ]))

  method to_address (floc: floc_int): xpr_t =
    match kind with
    | ARMOffsetAddress (r, align, offset, isadd, iswback, isindex) ->
       let env = floc#f#env in
       let memoff =
         if isindex then
           match (offset, isadd) with
           | (ARMImmOffset i, true) -> int_constant_expr i
           | (ARMImmOffset i, false) -> int_constant_expr (-i)
           | _ -> random_constant_expr
         else
           zero_constant_expr in
       let rvar = env#mk_arm_register_variable r in
       let rvarx =
         if align > 1 then
           let alignx = int_constant_expr align in
           XOp (XMult, [XOp (XDiv, [XVar rvar; alignx]); alignx])
         else
           XVar rvar in
       let addr = XOp (XPlus, [rvarx; memoff]) in
       floc#inv#rewrite_expr addr env#get_variable_comparator
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Address of "; self#toPretty; STR " not yet implemented"]))

  method to_updated_offset_address (floc: floc_int): xpr_t =
    match kind with
    | ARMOffsetAddress (r, align, offset, isadd, iswback, isindex) ->
       let env = floc#f#env in
       if isindex then
         self#to_address floc
       else
         let memoff =
           match (offset, isadd) with
           | (ARMImmOffset i, true) -> int_constant_expr i
           | (ARMImmOffset i, false) -> int_constant_expr (-i)
           | _ -> random_constant_expr in
         let addr = XOp (XPlus, [self#to_address floc; memoff]) in
         floc#inv#rewrite_expr addr env#get_variable_comparator
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not an arm-offset-address: ";
                 self#toPretty]))

  method to_variable (floc:floc_int): variable_t =
    let env = floc#f#env in
    match kind with
    | ARMReg r -> env#mk_arm_register_variable r
    | ARMExtensionReg (t, r) -> env#mk_arm_extension_register_variable t r
    | ARMSpecialReg r ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Semantics of special register ";
                 STR (arm_special_reg_to_string r);
                 STR " should be handled separaly"]))
    | ARMOffsetAddress (r, align, offset, isadd, iswback, isindex) ->
       (match offset with
        | ARMImmOffset _ ->
           let rvar = env#mk_arm_register_variable r in
           let memoff =
             match (offset,isadd) with
             | (ARMImmOffset i, true) -> mkNumerical i
             | (ARMImmOffset i, false) -> (mkNumerical i)#neg
             | _ ->
                raise
                  (BCH_failure
                     (LBLOCK [STR "to_variable: offset not implemented: ";
                              self#toPretty])) in
           floc#get_memory_variable_1 ~align rvar memoff
        | ARMShiftedIndexOffset _ ->
           let rvar = env#mk_arm_register_variable r in
           (match (offset, isadd) with
            | (ARMShiftedIndexOffset (ivar, srt, i), true) ->
               let optscale =
                 match srt with
                 | ARMImmSRT (SRType_LSL, 2) -> Some 4
                 | ARMImmSRT (SRType_LSL, 0) -> Some 1
                 | _ -> None in
               (match optscale with
                | Some scale ->
                   let ivar = env#mk_arm_register_variable ivar in
                   if scale = 1 then
                     let rx =
                       floc#inv#rewrite_expr
                         (XVar rvar) floc#env#get_variable_comparator in
                     let ivax =
                       floc#inv#rewrite_expr
                         (XVar ivar) floc#env#get_variable_comparator in
                     let xoffset = simplify_xpr (XOp (XPlus, [rx; ivax])) in
                     (match xoffset with
                      | XConst (IntConst n) ->
                         floc#env#mk_global_variable n
                      | _ ->
                         let _ =
                           chlog#add
                             "shifted index offset memory variable"
                             (LBLOCK [
                                  self#toPretty;
                                  STR "; rx: ";
                                  x2p rx;
                                  STR ": ivax: ";
                                  x2p ivax]) in
                         env#mk_unknown_memory_variable "operand")
                   else
                     floc#get_memory_variable_3 rvar ivar scale (mkNumerical i)
                | _ ->
                   env#mk_unknown_memory_variable "operand")
            | _ -> env#mk_unknown_memory_variable "operand")
        | _ -> env#mk_unknown_memory_variable "operand")
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, 0)) ->
       env#mk_arm_register_variable r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Operand:to_variable not yet implemented for: ";
                      self#toPretty]))

  method to_multiple_variable (floc:floc_int): variable_t list =
    let env = floc#f#env in
    match kind with
    | ARMRegList rl -> List.map env#mk_arm_register_variable rl
    | ARMMemMultiple (r, n) ->
       let rvar = env#mk_arm_register_variable r in
       let rec loop i l =
         if i = 0 then
           l
         else
           let offset = mkNumerical (i - 1) in
           loop (i - 1) ((floc#get_memory_variable_1 rvar offset) :: l) in
       loop n []
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "to-multiple-variable not applicable: ";
                     self#toPretty]))

  method to_expr (floc:floc_int): xpr_t =
    match kind with
    | ARMImmediate imm ->
       big_int_constant_expr imm#to_big_int
    | ARMFPConstant _ -> XConst XRandom
    | ARMReg _ -> XVar (self#to_variable floc)
    | ARMSpecialReg r ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Semantics of special register ";
                 STR (arm_special_reg_to_string r);
                 STR " should be handled separately"]))
    | ARMExtensionReg _ -> XVar (self#to_variable floc)
    | ARMOffsetAddress _ -> XVar (self#to_variable floc)
    | ARMAbsolute a when elf_header#is_program_address a ->
       num_constant_expr a#to_numerical
    | ARMLiteralAddress a ->
       if elf_header#is_program_address a then
         num_constant_expr (elf_header#get_program_value a)#to_numerical
       else
         begin
           ch_error_log#add
             "literal address not found"
             (LBLOCK [floc#l#toPretty; STR ": "; a#toPretty]);
           XConst (XRandom)
         end
    | ARMAbsolute a ->
       begin
         ch_error_log#add
           "absolute address"
           (LBLOCK [STR "Address "; a#toPretty; STR " not found"]);
         num_constant_expr a#to_numerical
       end
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, 0)) ->
       let env = floc#f#env in
       XVar (env#mk_arm_register_variable r)
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSR, n)) ->
       let env = floc#f#env in
       XOp
         (XShiftrt,
          [XVar (env#mk_arm_register_variable r); int_constant_expr n])
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, n)) ->
       let env = floc#f#env in
       XOp
         (XShiftlt,
          [XVar (env#mk_arm_register_variable r); int_constant_expr n])
    | ARMShiftedReg _ -> XConst (XRandom)
    | ARMRegBitSequence (r,lsb,widthm1) -> XConst (XRandom)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand:to_expr not yet implemented for: ";
                 self#toPretty]))

  method to_multiple_expr (floc:floc_int): xpr_t list =
    match kind with
    | ARMRegList rl ->
       let rlops = self#get_register_op_list in
       List.map (fun op -> op#to_expr floc) rlops
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "to-multiple-expr not applicable: ";
                     self#toPretty]))

  method to_lhs (floc:floc_int) =
    match kind with
    | ARMImmediate _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Immediate cannot be a lhs: ";
                     self#toPretty]))
    | ARMReg _ -> (self#to_variable floc, [])
    | ARMExtensionReg _ -> (self#to_variable floc, [])
    | ARMOffsetAddress _ -> (self#to_variable floc, [])
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Lhs not implemented for "; self#toPretty]))

  method to_multiple_lhs (floc: floc_int) =
    match kind with
    | ARMRegList _
      | ARMMemMultiple _ -> (self#to_multiple_variable floc, [])
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "to_multiple_lhs not available for ";
                     self#toPretty]))

  method is_immediate = match kind with ARMImmediate _ -> true | _ -> false

  method is_register = match kind with ARMReg _ -> true | _ -> false

  method is_special_register =
    match kind with ARMSpecialReg _ -> true | _ -> false

  method is_register_list = match kind with ARMRegList _ -> true | _ -> false

  method is_read = match mode with RW | RD -> true | _ -> false

  method is_write = match mode with RW | WR -> true | _ -> false

  method is_absolute_address =
    match kind with ARMAbsolute _ -> true | _ -> false

  method is_pc_relative_address =
    match kind with
    | ARMOffsetAddress (ARPC, _, ARMImmOffset _, _, _, _) -> true
    | _ -> false

  method includes_pc =
    match kind with
    | ARMRegList rl -> List.mem ARPC rl
    | _ -> false

  method is_offset_address_writeback =
    match kind with
    | ARMOffsetAddress (_, _, _, _, true, _) -> true
    | _ -> false

  method toString =
    match kind with
    | ARMDMBOption o -> dmb_option_to_string o
    | ARMReg r -> armreg_to_string r
    | ARMSpecialReg r -> arm_special_reg_to_string r
    | ARMExtensionReg (t, index) -> arm_extension_reg_to_string t index
    | ARMRegList l ->
       "{" ^ String.concat "," (List.map armreg_to_string l) ^ "}"
    | ARMShiftedReg (r,rs) ->
       let pshift = register_shift_to_string rs in
       let pshift = if pshift = "" then "" else "," ^ pshift in
       (armreg_to_string r) ^ pshift
    | ARMRegBitSequence (r,lsb,widthm1) ->
       (armreg_to_string r) ^ ", #" ^ (string_of_int lsb)
       ^ ", #" ^ (string_of_int (widthm1+1))
    | ARMImmediate imm -> "#" ^ imm#to_hex_string
    | ARMFPConstant x -> "#" ^ (Printf.sprintf "%.1f" x)
    | ARMAbsolute addr -> addr#to_hex_string
    | ARMLiteralAddress addr -> addr#to_hex_string
    | ARMMemMultiple (r,n) ->
       (armreg_to_string r) ^ "<" ^ (string_of_int n) ^ ">"
    | ARMOffsetAddress (reg, align, offset, isadd, iswback, isindex) ->
       let poffset = arm_memory_offset_to_string offset in
       let poffset = if isadd then poffset else "-" ^ poffset in
       (match (iswback, isindex) with
        | (false, false) -> "[" ^ (armreg_to_string reg) ^ ", " ^ poffset ^ "]"
        | (false, true) -> "[" ^ (armreg_to_string reg) ^ ", " ^ poffset ^ "]"
        | (true, true) -> "[" ^ (armreg_to_string reg) ^ ", " ^ poffset ^ "]!"
        | (true, false) -> "[" ^ (armreg_to_string reg) ^ "], " ^ poffset)

  method toPretty = STR self#toString

end

let arm_index_offset ?(offset=0) (r: arm_reg_t) =
  ARMIndexOffset (r, offset)

let arm_shifted_index_offset
      ?(offset=0) (r: arm_reg_t) (sr: register_shift_rotate_t) =
  ARMShiftedIndexOffset (r, sr, offset)

let arm_dmb_option_op (op: dmb_option_t) =
  new arm_operand_t (ARMDMBOption op) RD

let arm_dmb_option_from_int_op (option:int) =
  arm_dmb_option_op (get_dmb_option option)

let arm_register_op (r:arm_reg_t) (mode:arm_operand_mode_t) =
  new arm_operand_t (ARMReg r) mode

let arm_extension_register_op
      (t: arm_extension_reg_type_t) (index: int) (mode: arm_operand_mode_t) =
  new arm_operand_t (ARMExtensionReg (t, index)) mode

let arm_special_register_op (r: arm_special_reg_t) (mode: arm_operand_mode_t) =
  new arm_operand_t (ARMSpecialReg r) mode

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
  if rotation = 0 then
    arm_register_op r mode
  else
    let regshift = ARMImmSRT (SRType_ROR, rotation) in
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

let arm_immediate_op (imm:immediate_int) =
  new arm_operand_t (ARMImmediate imm) RD

let arm_fp_constant_op (c: float) =
  new arm_operand_t (ARMFPConstant c) RD

let arm_absolute_op (addr:doubleword_int) (mode:arm_operand_mode_t) =
  new arm_operand_t (ARMAbsolute addr) mode

let arm_literal_op
      ?(align=4) ?(is_add=true) (pcaddr: doubleword_int) (imm: int) =
  let pcaddr = align_dw pcaddr align in
  let addr =
    if is_add then
      pcaddr#add_int imm
    else
      pcaddr#add_int (-imm) in
  new arm_operand_t (ARMLiteralAddress addr) RD

let mk_arm_absolute_target_op
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (imm:int)
      (mode:arm_operand_mode_t) =
  let addr = base#add_int (ch#pos + 4) in
  let tgtaddr = addr#add_int imm in
  arm_absolute_op tgtaddr mode

let mk_arm_offset_address_op
      ?(align=1)
      (reg:arm_reg_t)
      (offset:arm_memory_offset_t)
      ~(isadd:bool)
      ~(iswback:bool)
      ~(isindex:bool) =
  new arm_operand_t
    (ARMOffsetAddress (reg, align, offset, isadd, iswback, isindex))

let mk_arm_mem_multiple_op (reg:arm_reg_t) (n:int) =
  new arm_operand_t (ARMMemMultiple (reg,n))

let sp_r mode = arm_register_op ARSP mode

let pc_r mode = arm_register_op ARPC mode

let arm_sp_deref ?(with_offset=0) (mode:arm_operand_mode_t) =
  if with_offset >= 0 then
    let offset = ARMImmOffset with_offset in
    mk_arm_offset_address_op
      ARSP offset ~isadd:true ~iswback:false ~isindex:false mode
  else
    let offset = ARMImmOffset (-with_offset) in
    mk_arm_offset_address_op
      ARSP offset ~isadd:false ~iswback:false ~isindex:false mode
