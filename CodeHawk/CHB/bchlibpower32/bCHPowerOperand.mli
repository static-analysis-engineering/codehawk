(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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


val power_gp_register_op:
  index:int -> mode:power_operand_mode_t -> power_operand_int

val power_special_register_op:
  reg:power_special_reg_t
  -> mode:power_operand_mode_t
  -> power_operand_int

val power_indirect_register_op:
  index:int
  -> offset:numerical_t
  -> mode:power_operand_mode_t
  -> power_operand_int

val power_immediate_op:
  signed:bool (* signed *)
  -> size:int (* size in bytes *)
  -> imm:numerical_t  (* value *)
  -> power_operand_int

val power_absolute_op:
  doubleword_int -> power_operand_mode_t -> power_operand_int
