(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHLanguage
open CHPretty

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types

(* convert little endian sequence of four bytes into doubleword *)
val todw: string -> doubleword_int

(* convert little endian sequence of two bytes into doubleword *)
val tow: string -> doubleword_int

(* convert little endian sequence of four bytes into signed offset *)
val todwoff: string -> int

(* convert byte into signed offset *)
val tooff: string -> int

(* convert byte into unsigned integer *)
val toimm2: string -> int

val intvalue_to_string: int -> string
val regindexstring_to_reg: string -> cpureg_t

val xpr_to_basepretty: xpr_t -> pretty_t

val xpr_to_pretty   : floc_int -> xpr_t -> pretty_t
val xpr_to_fppretty : floc_int -> xpr_t -> pretty_t
val xpr_to_dspretty : floc_int -> xpr_t -> pretty_t
val xpr_to_strpretty: floc_int -> xpr_t -> pretty_t
val xpr_to_hexpretty: floc_int -> xpr_t -> pretty_t

val patternrhs_to_string: patternrhs_t -> string

(** [get_arg argvals n floc] returns the value of the n'th stack argument
    (counting starting from 1) at location [floc] *)
val get_arg: (fts_parameter_t * xpr_t) list -> int -> floc_int -> xpr_t

val get_reg_value: cpureg_t -> floc_int -> xpr_t
val get_gv_value: doubleword_int -> floc_int -> xpr_t
val get_reg_derefvalue: cpureg_t -> int -> floc_int -> xpr_t
val get_x_derefvalue: xpr_t -> int -> floc_int -> xpr_t
val get_patternrhs_value:
  ?args:(fts_parameter_t * xpr_t) list -> patternrhs_t -> floc_int -> xpr_t

val get_var_lhs: int -> floc_int -> (variable_t * cmd_t list)
val get_arg_lhs: int -> floc_int -> (variable_t * cmd_t list)   (* byte offset *)
val get_reg_lhs: cpureg_t -> floc_int -> (variable_t * cmd_t list)
val get_reg_deref_lhs: cpureg_t -> ?size:int -> int -> floc_int -> (variable_t * cmd_t list)
val get_x_deref_lhs: xpr_t -> int -> floc_int -> variable_t
val get_nested_deref_lhs: cpureg_t -> int list -> floc_int -> variable_t

val get_returnaddress_lhs: floc_int -> (variable_t * cmd_t list)
val get_allocavar_lhs: int -> int -> floc_int -> (variable_t * cmd_t list)

val get_return_value: string -> floc_int -> variable_t

val set_functionpointer: string -> floc_int -> xpr_t -> unit

val set_delphi_exception_handler_table: floc_int -> xpr_t -> unit

val get_adjustment_commands: int -> floc_int -> cmd_t list

val get_wrapped_call_commands: floc_int -> floc_int -> cmd_t list

val is_named_app_call: doubleword_int -> int -> string -> bool
val is_named_dll_call: doubleword_int -> int -> string -> bool
val is_named_inlined_call: doubleword_int -> int -> string -> bool
val is_named_lib_call: doubleword_int -> int -> string -> bool

val sometemplate:
  ?msg:pretty_t -> predefined_callsemantics_int -> predefined_callsemantics_int option

val get_fnhashes: string -> (string -> int -> predefined_callsemantics_int) ->
  predefined_callsemantics_int list

val mk_dllfun_semantics: string -> string -> (string -> int -> predefined_callsemantics_int)

val add_dllfun: (string,(string -> int -> predefined_callsemantics_int)) Hashtbl.t ->
  string -> string -> unit

val mk_libfun_semantics:
  string list -> string -> (string -> int -> predefined_callsemantics_int)

val add_libfun: (string,(string -> int -> predefined_callsemantics_int)) Hashtbl.t ->
  string list -> string -> unit

class virtual predefined_callsemantics_base_t:
    string -> int ->
object
  method virtual get_name: string
  method get_md5hash: string
  method get_annotation: floc_int -> pretty_t
  method get_commands: floc_int -> cmd_t list
  method virtual get_parametercount: int
  method get_instrcount: int
  method get_call_target: doubleword_int -> call_target_info_int
  method get_description: string
  method toPretty: pretty_t
end
