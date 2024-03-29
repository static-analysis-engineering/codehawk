(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes

(* bchlibpe *)
open BCHLibPETypes

(* bchlibx86 *)
open BCHLibx86Types


val is_dll_jump_target: doubleword_int -> bool

val is_jni_environment_variable: floc_int -> variable_t -> bool

val disassemble_pe: unit -> bool * pretty_t

val disassemble_sections: pe_section_header_int list -> int

val construct_functions: unit -> unit

val record_call_targets: unit -> unit

val decorate_functions: unit -> unit

val construct_functions_pe: unit -> bool * pretty_t

val trace_function: doubleword_int -> assembly_function_int

val resolve_indirect_calls: assembly_function_int -> unit

val identify_misaligned_functions: pe_section_header_int -> unit
