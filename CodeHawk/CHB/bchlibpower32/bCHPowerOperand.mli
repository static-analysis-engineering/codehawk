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
open CHPretty
open CHNumerical
open CHLanguage

(* chutil *)
open CHXmlDocument

(* xprlib *)
open Xprt

(* bchlib *)
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerTypes


val power_operand_mode_to_string: power_operand_mode_t -> string

val power_gp_register_op:
  index:int -> mode:power_operand_mode_t -> power_operand_int

val power_gp_register_op_convert: int -> power_operand_int

val power_special_register_op:
  reg:power_special_reg_t
  -> mode:power_operand_mode_t
  -> power_operand_int

val power_register_field_op:
  fld:power_register_field_t
  -> mode:power_operand_mode_t
  -> power_operand_int


(** [power_indirect_register_op ~basegpr ~offset ~mode] returns an operand that
    represents a memory address with the base address location in the GPR with
    index [basegpr] and a constant offset with value [offset] *) 
val power_indirect_register_op:
  basegpr:int
  -> offset:numerical_t
  -> mode:power_operand_mode_t
  -> power_operand_int


(** [power_indexed_indirect_register_op ~basegpr ~offsetgpr ~mode] returns an operand
    that represents a memory address with the base address located in the GPR
    with index [basegpr] and the offset located in the GPR with index
    [offsetgpr] *)
val power_indexed_indirect_register_op:
  basegpr:int
  -> offsetgpr:int
  -> mode:power_operand_mode_t
  -> power_operand_int


(** [power_immediate_op ~signed ~size ~imm] returns a signed or unsigned
    immediate value operand of [size] bytes with unsigned value [imm]

    Note: if the immediate value is requested to be signed, values of [imm]
    that exceed the the maximum value that can be represented by a signed
    integer of the given size are interpreted as negative.
 *)
val power_immediate_op:
  signed:bool (* signed *)
  -> size:int (* size in bytes *)
  -> imm:numerical_t  (* value *)
  -> power_operand_int


(** return an absolute address in operand form *)
val power_absolute_op:
  doubleword_int -> power_operand_mode_t -> power_operand_int


(** return condition register field 0 (CR0) in operand form *)
val cr0_op: mode:power_operand_mode_t -> power_operand_int


(** return condition register field 1 (CR1) in operand form *)
val cr1_op: mode:power_operand_mode_t -> power_operand_int


(** return condition register field 2 (CR2) in operand form *)
val cr2_op: mode:power_operand_mode_t -> power_operand_int


(** return condition register field 3 (CR3) in operand form *)
val cr3_op: mode:power_operand_mode_t -> power_operand_int


(** [crf_op f ~mode] returns condition register field [f] (CR[f]) in
    operand form *)
val crf_op: int -> mode:power_operand_mode_t -> power_operand_int


(** [crbi_op i ~mode] returns condition register field [i / 4] in
    operand form *)
val crbi_op: int -> mode:power_operand_mode_t -> power_operand_int


(** [crbit_op i ~mode] returns condition register bit [i] in operand
    form *)
val crbit_op: int -> mode:power_operand_mode_t -> power_operand_int


(** return the condition register (CR) in operand form *)
val cr_op: mode:power_operand_mode_t -> power_operand_int


(** return the count register (CTR) in operand form *)
val ctr_op: mode:power_operand_mode_t -> power_operand_int


(** return the link register (LR) in operand form *)
val lr_op: mode:power_operand_mode_t -> power_operand_int


(** return the machine state register (MSR) in operand form *)
val msr_op: mode:power_operand_mode_t -> power_operand_int


(** return the integer exception register (XER) in operand form *)
val xer_op: mode:power_operand_mode_t -> power_operand_int


(** return the carry bit in the integer exception register (XER-CA)
    in operand form *)
val xer_ca_op: mode:power_operand_mode_t -> power_operand_int


(** return the summary overflow bit in the integer exception register
    (XER-SO) in operand form *)
val xer_so_op: mode:power_operand_mode_t -> power_operand_int


(** return the overflow bit in the integer exception register (XER-OV)
    in operand form *)
val xer_ov_op: mode:power_operand_mode_t -> power_operand_int
