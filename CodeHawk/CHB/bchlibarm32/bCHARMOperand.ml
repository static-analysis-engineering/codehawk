(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs, LLC

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
open BCHBCTypes
open BCHBCTypeUtil
open BCHConstantDefinitions
open BCHCPURegisters
open BCHDoubleword
open BCHFunctionData
open BCHImmediate
open BCHLibTypes
open BCHSystemInfo
open BCHSystemSettings
open BCHUserProvidedDirections

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMPseudocode
open BCHARMSumTypeSerializer
open BCHARMTypes

module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr


let arm_operand_mode_to_string = function RD -> "RD" | WR -> "WR" | RW -> "RW"


let cps_effect_to_string (e: cps_effect_t) =
  match e with
  | Interrupt_NoChange -> ""
  | _ -> cps_effect_mfts#ts e


let interrupt_flags_to_string (i: interrupt_flags_t) =
  match i with
  | IFlag_None -> ""
  | _ -> interrupt_flags_mfts#ts i


let dmb_option_to_string = dmb_option_mfts#ts


let shift_rotate_type_to_string (srt:shift_rotate_type_t) =
  match srt with
  | SRType_LSL -> "LSL"
  | SRType_LSR -> "LSR"
  | SRType_ASR -> "ASR"
  | SRType_ROR -> "ROR"
  | SRType_RRX -> "RRX"


(* Use the same print convention as IDA Pro, e.g., LSR#24:
   - no spance between shift type and shift amount
   - decimal representation of shift amount
 *)
let register_shift_to_string (rs:register_shift_rotate_t) =
  match rs with
  | ARMImmSRT (SRType_ROR, 0) -> ""
  | ARMImmSRT (SRType_LSL, 0) -> ""
  | ARMImmSRT (srt, imm) ->
     (shift_rotate_type_to_string srt) ^ "#" ^ (string_of_int imm)
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


let vfp_datatype_to_btype (t: vfp_datatype_t): btype_t =
  match t with
  | VfpNone -> t_unknown
  | VfpSize s -> t_unknown_int_size s
  | VfpFloat 32 -> t_float
  | VfpFloat 64 -> t_double
  | VfpInt s -> t_unknown_int_size s
  | VfpPolynomial _ -> t_unknown
  | VfpSignedInt 8 -> t_char
  | VfpSignedInt 16 -> t_short
  | VfpSignedInt 32 -> t_int
  | VfpSignedInt 64 -> t_long
  | VfpUnsignedInt 8 -> t_uchar
  | VfpUnsignedInt 16 -> t_ushort
  | VfpUnsignedInt 32 -> t_uint
  | VfpUnsignedInt 64 -> t_ulong
  | _ ->
     let _ = chlog#add "unknown vfp btype" (STR (vfp_datatype_to_string t)) in
     t_unknown


let arm_memory_offset_to_string (offset:arm_memory_offset_t) =
  let p_off off =
    if off = 0 then
      ""
    else if off > 9 then
      Printf.sprintf "#%#x" off
    else if off < -9 then
      Printf.sprintf "#%#x" off
    else
      "#" ^ (string_of_int off) in
  match offset with
  | ARMImmOffset off -> p_off off
  | ARMIndexOffset (r, off) -> (armreg_to_string r)
  | ARMShiftedIndexOffset (r, rs, off) ->
     match rs with
     | ARMImmSRT (SRType_LSL, 0) -> (armreg_to_string r)
     | _ ->
        (armreg_to_string r)
        ^ ","
        ^ (register_shift_to_string rs)
        ^ (p_off off)


let arm_simd_list_element_to_string (e: arm_simd_list_element_t) =
  match e with
  | SIMDReg r -> arm_extension_reg_to_string r
  | SIMDRegElement e -> arm_extension_reg_element_to_string e
  | SIMDRegRepElement e -> arm_extension_reg_rep_element_to_string e


class arm_operand_t
        (kind:arm_operand_kind_t) (mode:arm_operand_mode_t):arm_operand_int =
object (self:'a)

  val kind = kind
  val mode = mode

  method get_kind = kind
  method get_mode = mode

  method get_size =
    match kind with
    | ARMReg _ -> 4
    | ARMDoubleReg _ -> 8
    | ARMWritebackReg _ -> 4
    | ARMExtensionReg r ->
       (match r.armxr_type with
        | XSingle -> 4
        | XDouble -> 8
        | XQuad -> 16)
    | ARMDoubleExtensionReg (r1, r2) ->
       (match (r1.armxr_type, r2.armxr_type) with
        | (XSingle, XSingle) -> 8
        | (XDouble, XDouble) -> 16
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Unexpected combination of extension registers: ";
                     self#toPretty])))
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand size not implemented for "; self#toPretty]))

  method get_register =
    match kind with
    | ARMReg r -> r
    | ARMWritebackReg (_, r, _) -> r
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, 0)) -> r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Operand is not a register: "; self#toPretty]))

  method get_extension_register =
    match kind with
    | ARMExtensionReg r -> r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not an extension register: "; self#toPretty]))

  method get_register_count =
    match kind with
    | ARMRegList rl -> List.length rl
    | ARMExtensionRegList rl -> List.length rl
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

  method get_extension_register_op_list: 'a list =
    match kind with
    | ARMExtensionRegList rl ->
       List.map (fun r -> {< kind = ARMExtensionReg r; mode = mode >}) rl
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not an extension register list: "; self#toPretty]))

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
    | ARMOffsetAddress (ARPC, align, ARMImmOffset off, isadd, _, _, _) ->
       let va =
         TR.tget_ok
           (int_to_doubleword (((va#to_int + pcoffset) / align) * align)) in
       if isadd then
         va#add_int off
       else
         va#add_int (-off)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not a pc-relative address: "; self#toPretty ]))

  method to_register: register_t =
    match kind with
    | ARMReg r -> register_of_arm_register r
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, 0)) -> register_of_arm_register r
    | ARMDoubleReg (r1, r2) -> register_of_arm_double_register r1 r2
    | ARMWritebackReg (_, r, _) -> register_of_arm_register r
    | ARMSpecialReg r -> register_of_arm_special_register r
    | ARMExtensionReg r -> register_of_arm_extension_register r
    | ARMDoubleExtensionReg (r1, r2) ->
       register_of_arm_double_extension_register r1 r2
    | ARMExtensionRegElement e -> register_of_arm_extension_register_element e
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand cannot be converted to a generic register: ";
                 self#toPretty]))

  method to_multiple_register: register_t list =
    match kind with
    | ARMRegList rl -> List.map register_of_arm_register rl
    | ARMExtensionRegList rl -> List.map register_of_arm_extension_register rl
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "to_multiple_register not applicable: "; self#toPretty]))

  method to_numerical =
    match kind with
    | ARMImmediate imm -> imm#to_numerical
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Operand is not an immediate value: " ; self#toPretty]))

  method to_address (floc: floc_int): xpr_t =
    match kind with
    | ARMOffsetAddress (r, align, offset, isadd, iswback, isindex, _) ->
       let env = floc#f#env in
       let memoff =
         if isindex then
           match (offset, isadd) with
           | (ARMImmOffset i, true) -> int_constant_expr i
           | (ARMImmOffset i, false) -> int_constant_expr (-i)
           | (ARMIndexOffset (indexreg, indexoffset), true) ->
              let indexvar = env#mk_arm_register_variable indexreg in
              XOp (XPlus, [XVar indexvar; int_constant_expr indexoffset])
           | (ARMShiftedIndexOffset (indexreg, srt, indexoffset), true) ->
              let indexvar = env#mk_arm_register_variable indexreg in
              let xoffset = int_constant_expr indexoffset in
              (match srt with
               | ARMImmSRT (_, 0)-> XOp (XPlus, [XVar indexvar; xoffset])
               | ARMImmSRT (SRType_LSL, 2) ->
                  let shifted = XOp (XMult, [XVar indexvar; int_constant_expr 4]) in
                  XOp (XPlus, [shifted; xoffset])
               | ARMImmSRT (SRType_ASR, 1) ->
                  let shifted = XOp (XDiv, [XVar indexvar; int_constant_expr 2]) in
                  XOp (XPlus, [shifted; xoffset])
               | ARMImmSRT (SRType_ASR, 2) ->
                  let shifted = XOp (XDiv, [XVar indexvar; int_constant_expr 4]) in
                  XOp (XPlus, [shifted; xoffset])
               | ARMImmSRT (SRType_ASR, 3) ->
                  let shifted = XOp (XDiv, [XVar indexvar; int_constant_expr 8]) in
                  XOp (XPlus, [shifted; xoffset])
               | ARMRegSRT (SRType_LSL, srtreg) ->
                  let shiftvar = env#mk_arm_register_variable srtreg in
                  let shifted = XOp (XLsl, [XVar indexvar; XVar shiftvar]) in
                  XOp (XPlus, [shifted; xoffset])
               | ARMRegSRT (SRType_ASR, srtreg) ->
                  let shiftvar = env#mk_arm_register_variable srtreg in
                  let shifted = XOp (XAsr, [XVar indexvar; XVar shiftvar]) in
                  XOp (XPlus, [shifted; xoffset])
               | _ ->
                  begin
                    (if collect_diagnostics () then
                       ch_diagnostics_log#add
                         "operand#to_address"
                         (LBLOCK [STR "ARMShiftedIndexOffset: "; self#toPretty]));
                    random_constant_expr
                  end)
           | _ ->
              begin
                (if collect_diagnostics () then
                   ch_diagnostics_log#add
                     "operand#to_address"
                     (LBLOCK [STR "memoff: "; self#toPretty]));
                random_constant_expr
              end
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
       (* floc#inv#rewrite_expr addr *)
       simplify_xpr addr
    | ARMLiteralAddress dw -> num_constant_expr dw#to_numerical
    | _ ->
       begin
         (if collect_diagnostics () then
            ch_diagnostics_log#add
              "operand#to_address"
              (LBLOCK [STR "Other address: "; self#toPretty]));
         random_constant_expr
       end

  method to_updated_offset_address (floc: floc_int): xpr_t =
    match kind with
    | ARMOffsetAddress (r, align, offset, isadd, iswback, isindex, _) ->
       if isindex then
         self#to_address floc
       else
         let memoff =
           match (offset, isadd) with
           | (ARMImmOffset i, true) -> int_constant_expr i
           | (ARMImmOffset i, false) -> int_constant_expr (-i)
           | _ -> random_constant_expr in
         let addr = XOp (XPlus, [self#to_address floc; memoff]) in
         floc#inv#rewrite_expr addr
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand is not an arm-offset-address: ";
                 self#toPretty]))

  method to_variable (floc:floc_int): variable_t =
    let env = floc#f#env in
    match kind with
    | ARMReg r | ARMWritebackReg (_, r, _) ->
       env#mk_arm_register_variable r
    | ARMDoubleReg (r1, r2) ->
       env#mk_arm_double_register_variable r1 r2
    | ARMExtensionReg r -> env#mk_arm_extension_register_variable r
    | ARMDoubleExtensionReg (r1, r2) ->
       env#mk_arm_double_extension_register_variable r1 r2
    | ARMSpecialReg r -> env#mk_arm_special_register_variable r
    | ARMLiteralAddress dw ->
       floc#env#mk_global_variable dw#to_numerical
    | ARMOffsetAddress (r, align, offset, isadd, iswback, isindex, size) ->
       let (var, trace) =
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
                       (LBLOCK [
                            STR "to_variable: offset not implemented: ";
                            self#toPretty])) in
             (floc#get_memory_variable_1 ~size ~align rvar memoff,
              [STR "ARMImmOffset"; STR "memory-variable-1"])
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
                       let rx = floc#inv#rewrite_expr (XVar rvar) in
                       let ivax = floc#inv#rewrite_expr (XVar ivar) in
                       let xoffset = simplify_xpr (XOp (XPlus, [rx; ivax])) in
                       (match xoffset with
                        | XConst (IntConst n) ->
                           (floc#env#mk_global_variable ~size n,
                            [STR "ARMShiftedIndexOffset"; STR "explicit"])
                        | XVar v when floc#f#env#is_memory_address_variable v ->
                           (floc#f#env#mk_memory_address_deref_variable v,
                            [STR "ARMShiftedIndexOffset"; STR "memory address"])
                        | _ ->
                           (env#mk_unknown_memory_variable "operand",
                            [STR "ARMShiftedIndexOffset";
                             self#toPretty;
                             STR "; rx: ";
                             x2p rx;
                             STR ": ivax: ";
                             x2p ivax]))
                     else
                       (floc#get_memory_variable_3
                          ~size rvar ivar scale (mkNumerical i),
                        [STR "ARMShiftedIndexOffset";
                         self#toPretty;
                         STR ": ";
                         STR "memory-variable-3"])
                  | _ ->
                     (env#mk_unknown_memory_variable "operand",
                      [STR "ARMShiftedIndexOffset"; STR "no scale"; self#toPretty]))
              | _ ->
                 (env#mk_unknown_memory_variable "operand",
                  [STR "ARMShiftedIndexOffset"; STR "unsupported"; self#toPretty]))
          | _ ->
             (env#mk_unknown_memory_variable "operand",
              [STR "ARMOffsetAddress"; STR "unsupported"; self#toPretty])) in
       let _ =
         if (env#is_unknown_memory_variable var) || var#isTemporary then
           if (List.length trace) > 0 then
             chlog#add
               "unknown memory location"
               (LBLOCK (
                    [floc#l#toPretty; STR ". "]
                    @ [List.hd trace]
                    @ [STR ": "]
                    @ (List.tl trace)))
           else
             chlog#add
               "unknown memory location - no info"
               (LBLOCK [floc#l#toPretty]) in
       var
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, 0)) ->
       env#mk_arm_register_variable r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Operand:to_variable not yet implemented for: ";
                 self#toPretty]))

  method to_multiple_variable (floc:floc_int): variable_t list =
    let env = floc#f#env in
    match kind with
    | ARMRegList rl -> List.map env#mk_arm_register_variable rl
    | ARMExtensionRegList rl ->
       List.map env#mk_arm_extension_register_variable rl
    | ARMMemMultiple (r, _, n, size) ->
       let rvar = env#mk_arm_register_variable r in
       let rec loop i l =
         if i = 0 then
           l
         else
           let offset = mkNumerical ((i - 1) * size) in
           loop (i - 1) ((floc#get_memory_variable_1 rvar offset) :: l) in
       loop n []
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "to-multiple-variable not applicable: ";
                     self#toPretty]))

  method to_expr ?(unsigned=false) (floc:floc_int): xpr_t =
    match kind with
    | ARMImmediate imm ->
       let imm = if unsigned then imm#to_unsigned else imm in
       (match imm#to_doubleword with
        | Some dw ->
           if has_symbolic_address_name dw then
             let name = get_symbolic_address_name dw in
             let var =
               floc#f#env#mk_global_memory_address
                 ~optname:(Some name) imm#to_numerical in
             XVar var
           else
             num_constant_expr imm#to_numerical
        | _ -> num_constant_expr imm#to_numerical)
    | ARMFPConstant _ -> XConst XRandom
    | ARMReg _ | ARMWritebackReg _ -> XVar (self#to_variable floc)
    | ARMDoubleReg _ -> XVar (self#to_variable floc)
    | ARMSpecialReg r -> XVar (self#to_variable floc)
    | ARMExtensionReg _ -> XVar (self#to_variable floc)
    | ARMDoubleExtensionReg _ -> XVar (self#to_variable floc)
    | ARMExtensionRegElement _ -> XConst XRandom
    | ARMOffsetAddress _ -> XVar (self#to_variable floc)
    | ARMAbsolute a when elf_header#is_program_address a ->
       num_constant_expr a#to_numerical
    | ARMLiteralAddress a ->
       if elf_header#is_program_address a then
         let dw = elf_header#get_program_value a in
         if has_symbolic_address_name dw then
           let name = get_symbolic_address_name dw in
           let ty = get_symbolic_address_type_by_name name in
           let var =
             floc#f#env#mk_global_memory_address
               ~optname:(Some name) ~opttype:(Some ty) dw#to_numerical in
           XVar var
         else
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
         (XLsr,
          [XVar (env#mk_arm_register_variable r); int_constant_expr n])
    | ARMShiftedReg (r, ARMImmSRT (SRType_ASR, n)) ->
       let env = floc#f#env in
       XOp
         (XAsr,
          [XVar (env#mk_arm_register_variable r); int_constant_expr n])
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, n)) ->
       let env = floc#f#env in
       XOp
         (XLsl,
          [XVar (env#mk_arm_register_variable r); int_constant_expr n])
    | ARMShiftedReg _ ->
       let _ =
         chlog#add
           "shifted-reg unknown"
           (LBLOCK [self#toPretty]) in
       XConst (XRandom)
    | ARMRegBitSequence (r, lsb, widthm1) ->
       let regvar = XVar (floc#env#mk_arm_register_variable r) in
       (match (lsb, widthm1) with
        | (8, 7) ->
           XOp (XXbyte, [int_constant_expr 1; regvar])
        | _ ->
           let mask = Int.shift_left 1 (widthm1+1) in
           if lsb = 0 then
             XOp (XBAnd, [regvar; int_constant_expr mask])
           else
             let shiftedreg = XOp (XLsr, [regvar; int_constant_expr lsb]) in
             XOp (XBAnd, [shiftedreg; int_constant_expr mask]))
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
       List.map (fun (op: 'a) -> op#to_expr floc) rlops
    | ARMExtensionRegList rl ->
       let rlops = self#get_extension_register_op_list in
       List.map (fun (op: 'a) -> op#to_expr floc) rlops
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "to-multiple-expr not applicable: ";
                 self#toPretty]))

  method to_lhs (floc:floc_int) =
    match kind with
    | ARMImmediate _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Immediate cannot be a lhs: ";
                     self#toPretty]))
    | ARMReg _ | ARMWritebackReg _ -> (self#to_variable floc, [])
    | ARMDoubleReg _ -> (self#to_variable floc, [])
    | ARMExtensionReg _ -> (self#to_variable floc, [])
    | ARMDoubleExtensionReg _ -> (self#to_variable floc, [])
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

  method is_immediate =
    match kind with ARMImmediate _ -> true | _ -> false

  method is_small_immediate =
    match kind with
    | ARMImmediate imm ->
       let num = self#to_numerical in
       (try
          num#toInt >= 0 && num#toInt < 5
        with
        | _ -> false)
    | _ -> false

  method is_register =
    match kind with
    | ARMReg _
      | ARMWritebackReg _ -> true
    | ARMShiftedReg (r, ARMImmSRT (SRType_LSL, 0)) -> true
    | _ -> false

  method is_pc_register =
    match kind with ARMReg ARPC -> true | _ -> false

  method is_double_register =
    match kind with ARMDoubleReg _ -> true | _ -> false

  method is_double_extension_register =
    match kind with ARMDoubleExtensionReg _ -> true | _ -> false

  method is_double_extension_register_list =
    match kind with
    | ARMExtensionRegList rl ->
       (match rl with
        | r :: _ -> (match r.armxr_type with XDouble -> true | _ -> false)
        | _ -> false)
    | _ -> false

  method is_extension_register =
    match kind with
    | ARMExtensionReg _ -> true
    | _ -> false

  method is_writeback_register =
    match kind with ARMWritebackReg _ -> true | _ -> false

  method is_special_register =
    match kind with ARMSpecialReg _ -> true | _ -> false

  method is_APSR_condition_flags =
    match kind with
    | ARMSpecialReg APSR_nzcv -> true
    | _ -> false

  method is_bit_sequence =
    match kind with
    | ARMRegBitSequence _ -> true
    | _ -> false

  method to_btype =
    match kind with
    | ARMRegBitSequence (_, _, widthm1) ->
       (match widthm1 with
        | 7 -> t_uchar
        | 15 -> t_ushort
        | _ -> t_uint)
    | _ -> t_unknown

  method is_register_list =
    match kind with ARMRegList _ -> true | _ -> false

  method is_read = match mode with RW | RD -> true | _ -> false

  method is_write = match mode with RW | WR -> true | _ -> false

  method is_absolute_address =
    match kind with ARMAbsolute _ -> true | _ -> false

  method is_literal_address =
    match kind with ARMLiteralAddress _ -> true | _ -> false

  method is_pc_relative_address =
    match kind with
    | ARMOffsetAddress (ARPC, _, ARMImmOffset _, _, _, _, _) -> true
    | _ -> false

  method includes_pc =
    match kind with
    | ARMRegList rl -> List.mem ARPC rl
    | _ -> false

  method includes_lr =
    match kind with
    | ARMRegList rl -> List.mem ARLR rl
    | _ -> false

  method is_offset_address =
    match kind with ARMOffsetAddress _ -> true | _ -> false

  method is_offset_address_writeback =
    match kind with
    | ARMOffsetAddress (_, _, _, _, true, _, _) -> true
    | _ -> false

  method toString =
    try
      match kind with
      | ARMCPSEffect e -> cps_effect_to_string e
      | ARMInterruptFlags f -> interrupt_flags_to_string f
      | ARMDMBOption o -> dmb_option_to_string o
      | ARMReg r -> armreg_to_string r
      | ARMDoubleReg (r1, r2) ->
         "(" ^ (armreg_to_string r1) ^ ", " ^ (armreg_to_string r2) ^ ")"
      | ARMWritebackReg (issingle, r, _) ->
         (armreg_to_string r) ^ (if issingle then "" else "!")
      | ARMSpecialReg r -> arm_special_reg_to_string r
      | ARMExtensionReg r -> arm_extension_reg_to_string r
      | ARMDoubleExtensionReg (r1, r2) ->
         "("
         ^ (arm_extension_reg_to_string r1)
         ^ ", "
         ^ (arm_extension_reg_to_string r2)
         ^ ")"
      | ARMExtensionRegElement e -> arm_extension_reg_element_to_string e
      | ARMRegList l ->
         "{" ^ String.concat "," (List.map armreg_to_string l) ^ "}"
      | ARMExtensionRegList rl ->
         "{" ^ String.concat "," (List.map arm_extension_reg_to_string rl) ^ "}"
      | ARMShiftedReg (r,rs) ->
         let pshift = register_shift_to_string rs in
         let pshift = if pshift = "" then "" else "," ^ pshift in
         (armreg_to_string r) ^ pshift
      | ARMRegBitSequence (r,lsb,widthm1) ->
         (armreg_to_string r) ^ ", #" ^ (string_of_int lsb)
         ^ ", #" ^ (string_of_int (widthm1+1))
      | ARMImmediate imm -> "#" ^ imm#to_string
      | ARMFPConstant x -> "#" ^ (Printf.sprintf "%.1f" x)
      | ARMAbsolute addr -> addr#to_hex_string
      | ARMLiteralAddress addr -> addr#to_hex_string
      | ARMMemMultiple (r, align, n, size) ->
         let alignment = if align = 0 then "" else ":" ^ (string_of_int align) in
         (armreg_to_string r) ^ "<" ^ (string_of_int n) ^ ">" ^ alignment
      | ARMOffsetAddress (reg, align, offset, isadd, iswback, isindex, size) ->
         let poffset = arm_memory_offset_to_string offset in
         let poffset = if isadd then poffset else "-" ^ poffset in
         let pre_offset = if poffset = "" then "" else "," ^ poffset in
         (match (iswback, isindex) with
          | (false, false) -> "[" ^ (armreg_to_string reg) ^ pre_offset ^ "]"
          | (false, true) -> "[" ^ (armreg_to_string reg) ^ pre_offset ^ "]"
          | (true, true) -> "[" ^ (armreg_to_string reg) ^ pre_offset ^ "]!"
          | (true, false) -> "[" ^ (armreg_to_string reg) ^ "]," ^ poffset)
      | ARMSIMDAddress (base, align, wback) ->
         let palign = if align = 1 then "" else ":" ^ (string_of_int align) in
         let pbase = armreg_to_string base in
         (match wback with
          | SIMDNoWriteback -> "[" ^ pbase ^ palign ^ "]"
          | SIMDBytesTransferred _ -> "[" ^ pbase ^ palign ^ "]!"
          | SIMDAddressOffsetRegister r ->
             "[" ^ pbase ^ palign ^ "], " ^ (armreg_to_string r))
      | ARMSIMDList rl ->
         "{"
         ^ (String.concat "," (List.map arm_simd_list_element_to_string rl))
         ^ "}"
    with
    | BCH_failure p ->
       raise
         (BCH_failure
            (LBLOCK [STR "Error in instruction operand: "; p]))

  method toPretty = STR self#toString

end


let arm_index_offset ?(offset=0) (r: arm_reg_t) =
  ARMIndexOffset (r, offset)


let arm_shifted_index_offset
      ?(offset=0) (r: arm_reg_t) (sr: register_shift_rotate_t) =
  ARMShiftedIndexOffset (r, sr, offset)


let arm_dmb_option_op (op: dmb_option_t) =
  new arm_operand_t (ARMDMBOption op) RD


let arm_dmb_option_from_int_op (option: int) =
  arm_dmb_option_op (get_dmb_option option)


let arm_cps_effect_op (e: cps_effect_t) =
  new arm_operand_t (ARMCPSEffect e) RD


let arm_interrupt_flags_op (f: interrupt_flags_t) =
  new arm_operand_t (ARMInterruptFlags f) RD


let arm_register_op (r: arm_reg_t) (mode: arm_operand_mode_t) =
  new arm_operand_t (ARMReg r) mode


let arm_double_register_op
      (r1: arm_reg_t) (r2: arm_reg_t) (mode: arm_operand_mode_t) =
  new arm_operand_t (ARMDoubleReg (r1, r2)) mode


let arm_writeback_register_op
      ?(issingle = false)
      (r: arm_reg_t)
      (offset: int option)
      (mode: arm_operand_mode_t): arm_operand_int =
  new arm_operand_t (ARMWritebackReg (issingle, r, offset)) mode

let arm_extension_register_op
      (t: arm_extension_reg_type_t) (index: int) (mode: arm_operand_mode_t) =
  let reg = {armxr_type = t; armxr_index = index} in
  new arm_operand_t (ARMExtensionReg reg) mode


let arm_double_extension_register_op
      (t: arm_extension_reg_type_t)
      (index1: int)
      (index2: int)
      (mode: arm_operand_mode_t) =
  let reg1 = {armxr_type = t; armxr_index = index1} in
  let reg2 = {armxr_type = t; armxr_index = index2} in
  new arm_operand_t (ARMDoubleExtensionReg (reg1, reg2)) mode


let arm_extension_register_element_op
      (t: arm_extension_reg_type_t)
      (rindex: int)
      (eindex: int)
      (esize: int)
      (mode: arm_operand_mode_t) =
  let reg = {armxr_type = t; armxr_index = rindex} in
  let elt = {armxr = reg; armxr_elem_index = eindex; armxr_elem_size = esize} in
  new arm_operand_t (ARMExtensionRegElement elt) mode


let arm_special_register_op (r: arm_special_reg_t) (mode: arm_operand_mode_t) =
  new arm_operand_t (ARMSpecialReg r) mode


let arm_register_list_op (l: arm_reg_t list) (mode: arm_operand_mode_t) =
  new arm_operand_t (ARMRegList l) mode


let arm_extension_register_list_op
      (xt: arm_extension_reg_type_t) (d: int) (n: int) (mode: arm_operand_mode_t) =
  let rl =
    let rec aux n l =
      if n = 0 then
        l
      else
        aux (n-1) (((n + d )- 1)::l) in
    aux n [] in
  let rl = List.map (fun i -> {armxr_type = xt; armxr_index = i}) rl in
  new arm_operand_t (ARMExtensionRegList rl) mode


let arm_simd_reg_list_op
      (xt: arm_extension_reg_type_t)
      (indices: int list)
      (mode: arm_operand_mode_t) =
  let rl =
    List.map
      (fun i -> SIMDReg {armxr_type = xt; armxr_index = i}) indices in
  new arm_operand_t (ARMSIMDList rl) mode


let arm_simd_reg_elt_list_op
      (xt: arm_extension_reg_type_t)
      (indices: int list)
      (eindex: int)
      (esize: int)
      (mode: arm_operand_mode_t) =
  let rl =
    List.map
      (fun i ->
        let reg = {armxr_type = xt; armxr_index = i} in
        let indexelem = {
            armxr = reg; armxr_elem_index = eindex; armxr_elem_size = esize} in
        SIMDRegElement indexelem) indices in
  new arm_operand_t (ARMSIMDList rl) mode


let arm_simd_reg_rep_elt_list_op
      (xt: arm_extension_reg_type_t)
      (indices: int list)
      (esize: int)
      (ecount: int)
      (mode: arm_operand_mode_t) =
  let rl =
    List.map
      (fun i ->
        let reg = {armxr_type = xt; armxr_index = i} in
        let repelem = {
            armxrr = reg; armxrr_elem_size = esize; armxrr_elem_count = ecount} in
        SIMDRegRepElement repelem) indices in
  new arm_operand_t (ARMSIMDList rl) mode


let mk_arm_simd_address_op
      (base: arm_reg_t)
      (alignment: int)
      (wback: arm_simd_writeback_t)
      (mode: arm_operand_mode_t) =
  new arm_operand_t (ARMSIMDAddress (base, alignment, wback)) mode


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
        | 1 -> imm#add numerical_e8
        | 2 -> imm#add numerical_e16
        | 4 -> imm#add numerical_e32
        | 8 -> imm#add numerical_e64
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Unexpected size in arm-immediate-op: " ;
                     INT size])) in
    (*    let op =*)
      TR.tmap
        (fun imm ->
          new arm_operand_t (ARMImmediate imm) RD)
        (make_immediate signed size immval)
(* new arm_operand_t op RD *)


let arm_immediate_op (imm:immediate_int) =
  new arm_operand_t (ARMImmediate imm) RD


let arm_fp_constant_op (c: float) =
  new arm_operand_t (ARMFPConstant c) RD


let arm_absolute_op (addr:doubleword_int) (mode:arm_operand_mode_t) =
  new arm_operand_t (ARMAbsolute addr) mode
  (*
  if system_info#is_code_address addr then
    new arm_operand_t (ARMAbsolute addr) mode
  else
    raise (Invalid_argument ("Invalid absolute address: " ^ addr#to_hex_string))
   *)

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
      (base:doubleword_int)
      (imm:int)
      (mode:arm_operand_mode_t) =
  let tgtaddr = base#add_int imm in
  arm_absolute_op tgtaddr mode
  (*
  if system_info#is_code_address tgtaddr then
    arm_absolute_op tgtaddr mode
  else
    raise (Invalid_argument ("Invalid target address: " ^ tgtaddr#to_hex_string))
   *)


let mk_arm_offset_address_op
      ?(align=1)
      ?(size=4)
      (reg:arm_reg_t)
      (offset:arm_memory_offset_t)
      ~(isadd:bool)
      ~(iswback:bool)
      ~(isindex:bool) =
  new arm_operand_t
    (ARMOffsetAddress (reg, align, offset, isadd, iswback, isindex, size))


let mk_arm_mem_multiple_op
      ?(align=0) ?(size=4) (reg:arm_reg_t) (n:int) =
  new arm_operand_t (ARMMemMultiple (reg, align, n, size))


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


let arm_reg_deref ?(with_offset=0) (reg: arm_reg_t) (mode:arm_operand_mode_t) =
  if with_offset >= 0 then
    let offset = ARMImmOffset with_offset in
    mk_arm_offset_address_op
      reg offset ~isadd:true ~iswback:false ~isindex:false mode
  else
    let offset = ARMImmOffset (-with_offset) in
    mk_arm_offset_address_op
      reg offset ~isadd:false ~iswback:false ~isindex:false mode


let equal_register_lists (op1: arm_operand_int) (op2: arm_operand_int): bool =
  if not (op1#is_register_list && op2#is_register_list) then
    false
  else if op1#get_register_count != op2#get_register_count then
    false
  else
    let rl1 = op1#get_register_list in
    let rl2 = op2#get_register_list in
    List.fold_left2 (fun acc r1 r2 -> acc && r1 = r2) true rl1 rl2
