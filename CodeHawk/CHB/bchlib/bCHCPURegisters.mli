(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes


(** Encapsulation of architecture-specific registers into a generic
    register type*)


(** {1 Conversion functions} *)

(** {2 x86}*)

(** Converts an x86 segment to a generic register.*)
val register_of_segment: segment_t -> register_t

(** Converts a regular x86 cpu register to a generic register.*)
val register_of_cpuregister: cpureg_t -> register_t

(** Converts a combination of two x86 cpu registers to a generic register.*)
val register_of_double_register: cpureg_t -> cpureg_t -> register_t

(** Converts the index of an x86 floating-point register to a generic register.*)
val register_of_floating_point_register_index: int -> register_t

(** Converts the index of an x86 control register to a generic register.*)
val register_of_control_register_index: int -> register_t

(** Converts the index of an x86 debug register to a generic register.*)
val register_of_debug_register_index: int -> register_t

(** Converts the index of an x86 mmx register to a generic register.*)
val register_of_mmx_register_index: int -> register_t

(** Converts the index of an x86 xmm register to a generic register .*)
val register_of_xmm_register_index: int -> register_t


(** {2 MIPS}*)

(** Converts a regular MIPS register to a generic register.*)
val register_of_mips_register: mips_reg_t -> register_t

(** Converts a MIPS special register to a generic register.*)
val register_of_mips_special_register: mips_special_reg_t -> register_t

(** Converts the index of a MIPS floating point register to a generic register.*)
val register_of_mips_floating_point_register_index: int -> register_t


(** {2 ARM}*)

(** Converts a regular ARM register to a generic register.*)
val register_of_arm_register: arm_reg_t -> register_t

(** Converts a combination of two ARM registers to a generic register.*)
val register_of_arm_double_register: arm_reg_t -> arm_reg_t -> register_t

(** Converts an ARM special register to a generic register.*)
val register_of_arm_special_register: arm_special_reg_t -> register_t

(** Converts an ARM extension register to a generic register.*)
val register_of_arm_extension_register: arm_extension_register_t -> register_t

(** Converts a combination of two ARM extension registers to a generic register.*)
val register_of_arm_double_extension_register:
  arm_extension_register_t -> arm_extension_register_t -> register_t

(** Converts an ARM extension register element to a generic register.*)
val register_of_arm_extension_register_element:
  arm_extension_register_element_t -> register_t

(** Converts an ARM extension register replicated element to a generic register.*)
val register_of_arm_extension_register_replicated_element:
  arm_extension_register_replicated_element_t -> register_t


(** {2 Power32}*)

(** Converts the index of a Power general-purpose (GP) register to a generic
    register.*)
val register_of_power_gp_register_index: int -> register_t

(** Converts a Power special-purpose (SP) register to a generic register.*)
val register_of_power_sp_register: pwr_special_reg_t -> register_t

(** Converts a Power control-register (CR) register field to a generic register.*)
val register_of_power_cr_register_field: pwr_register_field_t -> register_t


val full_reg_of_reg: cpureg_t -> cpureg_t
val full_registers: cpureg_t list


(** {1 Construction functions} *)

(** {2 ARM} *)

(** [mk_arm_sp_reg i] returns an ARM single-precision floating point register
    (S<i>)

    raise BCHBasicTypes.BCH_failure if [i] is negative or i is greater than 31.*)
val mk_arm_sp_reg: int -> arm_extension_register_t

(** [mk_arm_dp_reg i] returns an ARM double-precision floating point register
    (D<i>)

    raise BCH_failure if [i] is negative or i is greater than 15.*)
val mk_arm_dp_reg: int -> arm_extension_register_t


(** {1 Access functions} *)

(** {2 ARM} *)

val index_of_arm_extension_reg: arm_extension_register_t -> int


(** {1 Utility functions} *)

(** {2 General}*)

val register_compare: register_t -> register_t -> int

val register_equal: register_t -> register_t -> bool

val is_stackpointer_register: register_t -> bool

val is_register: string -> bool

(** {2 x86}*)

val byte_reg_of_reg : cpureg_t -> cpureg_t       (* raises Invalid_argument *)
val word_reg_of_reg : cpureg_t -> cpureg_t       (* raises Invalid_argument *)
val sized_reg_of_reg: cpureg_t -> int -> cpureg_t  (* raises Invalid_argument *)

val index_to_register: int -> cpureg_t
val index_to_word_register: int -> cpureg_t
val index_to_byte_register: int -> cpureg_t

val registers_affected_by: cpureg_t -> cpureg_t list
val registers_zeroed_by: cpureg_t -> cpureg_t list

(** {2 MIPS}*)

val get_mipsreg_argument: int -> mips_reg_t

(** [mipsreg_to_index r] returns the numerical value of mips register [r]
    as it appears in assembly instructions.*)
val mipsreg_to_index: mips_reg_t -> int

(** [index_to_mipsreg i] returns the mips register that corresponds to the
    numerical value [i] (e.g., [index_to_mipsreg 4] returns [MRa0]).*)
val index_to_mipsreg: int -> mips_reg_t

(** {2 ARM}*)
val get_armreg_argument: int -> arm_reg_t
val get_armreg_float_argument: int -> arm_extension_register_t


(** {1 Collections} *)

(** {2 MIPS}*)

val mips_regular_registers: mips_reg_t list

val mips_temporaries: mips_reg_t list

(** {2 ARM}*)

val arm_temporaries: arm_reg_t list

val arm_regular_registers: arm_reg_t list
val arm_regular_registers_no_pc: arm_reg_t list
val arm_xsingle_extension_registers: arm_extension_register_t list
val arm_xdouble_extension_registers: arm_extension_register_t list

(** {2 Power32}*)

val pwr_special_registers: pwr_special_reg_t list


(** {1 Printing} *)

(** {2 General}*)

val register_to_string: register_t -> string

val register_from_string: string -> register_t    (* incomplete *)


(** {2 x86}*)

val cpureg_to_string : cpureg_t -> string
val cpureg_from_string: string -> cpureg_t  (* raises Invalid_argument *)

val cpureg_to_asm_string: cpureg_t -> string

val cpureg_option_to_string: cpureg_t option -> string

val segment_to_string: segment_t -> string


(** {2 MIPS}*)

val mipsreg_to_string : mips_reg_t -> string
val mipsreg_from_string: string -> mips_reg_t

val mips_special_reg_to_string: mips_special_reg_t -> string
val mips_special_reg_from_string: string -> mips_special_reg_t

(** {2 ARM}*)

val armreg_to_string: arm_reg_t -> string
val armreg_from_string: string -> arm_reg_t

val arm_extension_reg_type_to_string: arm_extension_reg_type_t -> string
val arm_extension_reg_to_string: arm_extension_register_t -> string
val arm_extension_reg_element_to_string: arm_extension_register_element_t -> string
val arm_extension_reg_rep_element_to_string:
  arm_extension_register_replicated_element_t -> string

val arm_special_reg_to_string: arm_special_reg_t -> string
val arm_special_reg_from_string: string -> arm_special_reg_t
