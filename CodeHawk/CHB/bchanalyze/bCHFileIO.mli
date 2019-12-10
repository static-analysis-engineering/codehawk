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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types


val save_functions_list: unit -> unit
val save_global_state: unit -> unit
val save_system_info: unit -> unit
val save_resultmetrics: xml_element_int -> unit
val save_disassembly_status: unit -> unit
val save_function_asm: assembly_function_int -> unit
val save_x86dictionary: unit -> unit
val save_mips_dictionary: unit -> unit
val save_function_info: function_info_int -> unit
val save_function_variables: function_info_int -> unit
val save_function_type_invariants: function_info_int -> unit
val save_function_invariants: function_info_int -> unit
val save_function_summary: function_info_int -> unit
val save_results_jni_calls: unit -> unit

val load_system_info: unit -> xml_element_int option
val load_x86dictionary: unit -> unit
val load_mips_dictionary: unit -> unit
  
