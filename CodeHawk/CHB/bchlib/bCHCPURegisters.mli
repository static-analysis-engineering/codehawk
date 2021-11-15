(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

val full_reg_of_reg: cpureg_t -> cpureg_t

val full_registers: cpureg_t list

val register_compare  : register_t -> register_t -> int
val register_to_string: register_t -> string
val register_from_string: string -> register_t    (* incomplete *)

(* Utility functions *)
val is_register  : string -> bool

val cpureg_to_string   : cpureg_t -> string
val cpureg_from_string : string -> cpureg_t  (* raises Invalid_argument *)

val mipsreg_to_string : mips_reg_t -> string
val mipsreg_from_string: string -> mips_reg_t
val mips_regular_registers: mips_reg_t list
val mips_temporaries: mips_reg_t list
val get_mipsreg_argument: int -> mips_reg_t

val mips_special_reg_to_string: mips_special_reg_t -> string
val mips_special_reg_from_string: string -> mips_special_reg_t

val armreg_to_string: arm_reg_t -> string
val armreg_from_string: string -> arm_reg_t

val arm_extension_reg_type_to_string: arm_extension_reg_type_t -> string
val arm_extension_reg_to_string: arm_extension_register_t -> string
val arm_extension_reg_element_to_string: arm_extension_register_element_t -> string
val arm_extension_reg_rep_element_to_string:
  arm_extension_register_replicated_element_t -> string

val arm_regular_registers: arm_reg_t list
val get_armreg_argument: int -> arm_reg_t

val arm_special_reg_to_string: arm_special_reg_t -> string
val arm_special_reg_from_string: string -> arm_special_reg_t

val cpureg_to_asm_string  : cpureg_t -> string

val cpureg_option_to_string: cpureg_t option -> string

val segment_to_string: segment_t -> string

val byte_reg_of_reg : cpureg_t -> cpureg_t                (* raises Invalid_argument *)
val word_reg_of_reg : cpureg_t -> cpureg_t                (* raises Invalid_argument *)
val sized_reg_of_reg: cpureg_t -> int -> cpureg_t         (* raises Invalid_argument *)

val index_to_register     : int -> cpureg_t
val index_to_word_register: int -> cpureg_t
val index_to_byte_register: int -> cpureg_t

val registers_affected_by: cpureg_t -> cpureg_t list
val registers_zeroed_by  : cpureg_t -> cpureg_t list
