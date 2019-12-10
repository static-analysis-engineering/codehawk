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

(* bchlibmips32 *)
open BCHMIPSTypes

let e8 = 256
let e16 = e8 * e8
let e32 = e16 * e16

let mips_operand_mode_to_string = function RD -> "RD" | WR -> "WR" | RW -> "RW" 



class mips_operand_t (kind:mips_operand_kind_t) (mode:mips_operand_mode_t):mips_operand_int =
object (self:'a)

  method get_kind = kind
  method get_mode = mode

  method get_absolute_address =
    match kind with
    | MIPSAbsolute dw -> dw
    | _ ->
       raise (BCH_failure (LBLOCK [ self#toPretty ; STR " is not an absolute address" ]))

  method to_numerical =
    match kind with
    | MIPSImmediate imm -> imm#to_numerical
    | _ ->
       raise (BCH_failure
                (LBLOCK [ STR "Operand is not an immediate value: " ;
                          self#toPretty ]))

  method to_address (floc:floc_int):xpr_t =
    let env = floc#f#env in
    match kind with
    | MIPSImmediate _ ->
       raise (BCH_failure
                (LBLOCK  [ STR "Cannot take address of immediate operand: " ;
                           self#toPretty ]))
    | MIPSReg _ | MIPSSpecialReg _ | MIPSFPReg _ ->
       raise (BCH_failure
                (LBLOCK [ STR "Cannot take address of register: " ;
                          self#toPretty ]))
    | MIPSIndReg (r,offset) ->
       let v = env#mk_mips_register_variable r in
       XOp (XPlus, [ XVar v ; num_constant_expr offset ])
    | MIPSAbsolute a -> num_constant_expr a#to_numerical

  method to_variable (floc:floc_int):variable_t =
    let env = floc#f#env in
    match kind with
    | MIPSReg MRzero ->
       raise (BCH_failure
                (LBLOCK [ STR "Zero is ignored as destination operand" ]))
    | MIPSReg r -> env#mk_mips_register_variable r
    | MIPSSpecialReg r -> env#mk_mips_special_register_variable r
    | MIPSFPReg index -> env#mk_mips_fp_register_variable index
    | MIPSIndReg (r,offset) ->
       let rvar = env#mk_mips_register_variable r in
       floc#get_memory_variable_1 rvar offset
    | MIPSAbsolute a -> env#mk_global_variable a#to_numerical
    | MIPSImmediate imm ->
       raise (BCH_failure
                (LBLOCK [ STR "Immediate cannot be converted to a variable: " ;
                          imm#toPretty ]))

  method to_expr (floc:floc_int):xpr_t =
    match kind with
    | MIPSImmediate imm -> big_int_constant_expr imm#to_big_int
    | MIPSReg MRzero -> zero_constant_expr
    | _ -> XVar (self#to_variable floc)

  method to_lhs (floc:floc_int) =
    match kind with
    | MIPSImmediate imm ->
       raise (BCH_failure
                (LBLOCK [ STR "Immediate cannot be a lhs: " ; imm#toPretty ]))
    | _ -> (self#to_variable floc, [])

  method is_register = match kind with MIPSReg r -> true | _ -> false
                                                              
  method get_register =
    match kind with
    | MIPSReg r -> r
    | _ ->
       raise (BCH_failure (LBLOCK [ STR "Operand is not a mips register: " ;
                                    self#toPretty ]))

  method is_read  = match mode with RW | RD -> true | _ -> false
  method is_write = match mode with RW | WR -> true | _ -> false

  method is_absolute_address =
    match kind with MIPSAbsolute _ -> true | _ -> false

  method toString =
    match kind with
    | MIPSReg r -> mipsreg_to_string r
    | MIPSFPReg i -> "$f" ^ (string_of_int i)
    | MIPSSpecialReg r -> mips_special_reg_to_string r
    | MIPSIndReg (r,num) ->
       let rbase = "(" ^ (mipsreg_to_string r) ^ ")" in
       if num#equal numerical_zero then
         rbase
       else if num#gt numerical_zero then
         (numerical_to_doubleword num)#to_hex_string ^ rbase
       else
         "-" ^ (numerical_to_doubleword num#neg)#to_hex_string ^ rbase
    | MIPSAbsolute dw -> dw#to_hex_string
    | MIPSImmediate imm -> imm#to_string

  method toPretty = STR self#toString
end

let mips_hi_op (mode:mips_operand_mode_t) =
  new mips_operand_t (MIPSSpecialReg MMHi) mode

let mips_lo_op (mode:mips_operand_mode_t) =
  new mips_operand_t (MIPSSpecialReg MMLo) mode

let mips_register_op (r:mips_reg_t) (mode:mips_operand_mode_t) =
  new mips_operand_t (MIPSReg r) mode

let mips_fp_register_op (i:int) (mode:mips_operand_mode_t) =
  new mips_operand_t (MIPSFPReg i) mode

let mips_indirect_register_op (r:mips_reg_t) (offset:numerical_t) (mode:mips_operand_mode_t) =
  new mips_operand_t (MIPSIndReg (r,offset))  mode

let mips_immediate_op (signed:bool) (size:int) (imm:numerical_t) =
  let immval =
    if signed || imm#geq numerical_zero then
      imm
    else
      match size with
      | 1 -> imm#add (mkNumerical e8)
      | 2 -> imm#add (mkNumerical e16)
      | 4 -> imm#add (mkNumerical e32)
      | _ ->
         raise (BCH_failure (LBLOCK [ STR "Unexpected size in mips-immediate-op: " ;
                                      INT size ])) in
  let op = MIPSImmediate (make_immediate signed size immval#getNum) in
  new mips_operand_t op RD

let mips_absolute_op (addr:doubleword_int) (mode:mips_operand_mode_t) =
  new mips_operand_t (MIPSAbsolute addr) mode


let mk_mips_target_op (ch:pushback_stream_int) (base:doubleword_int) (imm:int) =
  let offset = ch#pos + (4 * imm) in
  mips_absolute_op (base#add_int offset) RD

let mk_mips_absolute_target_op
      ?(delay=0) (ch:pushback_stream_int) (base:doubleword_int) (imm:int) =
  let addr = base#add_int (ch#pos + delay) in
  let addrhigh = (addr#get_high lsr 12) lsl 28 in    (* only works on 64-bit implementation *)
  let tgt = imm lsl 2 in
  let tgtaddr = addrhigh + tgt in
  mips_absolute_op (int_to_doubleword tgtaddr) RD
