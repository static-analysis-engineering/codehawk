(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs LLC

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
open CHFormatStringParser

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


type arm_argument_state_t =
  { aas_next_core_reg: arm_reg_t option;
    aas_next_core_reg_byteoffset: int;
    aas_next_sp_reg: arm_extension_register_t option;
    aas_next_dp_reg: arm_extension_register_t option;
    aas_next_offset: int option;    (* stack offset *)
    aas_next_position: pld_position_t list;  (* used for struct/array parameters *)
    aas_fp_slots_available: int list
  }

val aas_start_state: arm_argument_state_t

val push_field_pos: arm_argument_state_t -> bfieldinfo_t -> arm_argument_state_t

val pop_pos: arm_argument_state_t -> arm_argument_state_t

val update_field_pos:
  arm_argument_state_t -> bfieldinfo_t -> arm_argument_state_t

val arm_argument_state_equal:
  arm_argument_state_t -> arm_argument_state_t -> bool


val mk_arm_argument_state:
  ?nextreg:arm_reg_t option
  -> ?nextreg_byteoffset:int
  -> ?nextspreg:arm_extension_register_t option
  -> ?nextdpreg:arm_extension_register_t option
  -> ?nextoffset:int option
  -> ?nextpos:pld_position_t list
  -> ?fpslots: int list
  -> unit
  -> arm_argument_state_t


val arm_argument_state_to_string: arm_argument_state_t -> string


(** exposed for unit tests only *)
val get_arm_int_param_next_state:
  int
  -> string
  -> btype_t
  -> arm_argument_state_t
  -> int
  -> (fts_parameter_t * arm_argument_state_t)


(** exposed for unit tests only *)
val get_arm_struct_field_locations:
  bfieldinfo_t
  -> arm_argument_state_t
  -> (parameter_location_t list * arm_argument_state_t)


(** exposed for unit tests only *)
val get_arm_struct_param_next_state:
  int
  -> string
  -> btype_t
  -> arm_argument_state_t
  -> int
  -> (fts_parameter_t * arm_argument_state_t)


val arm_vfp_params: bfunarg_t list -> fts_parameter_t list

val get_arm_format_spec_parameters:
  fts_parameter_t list -> argspec_int list -> fts_parameter_t list
