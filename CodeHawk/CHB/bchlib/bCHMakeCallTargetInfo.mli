(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2020 Henny B. Sipma

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

val mk_unknown_target: unit -> call_target_info_int

val mk_app_target: doubleword_int -> call_target_info_int

val mk_dll_target: string -> string -> call_target_info_int

val mk_so_target: string -> call_target_info_int

val mk_syscall_target: int -> call_target_info_int

val mk_jni_target: int -> call_target_info_int

val mk_virtual_target: function_api_t -> call_target_info_int

val mk_inlined_app_target: doubleword_int -> string -> call_target_info_int  

val mk_static_dll_stub_target:
  doubleword_int -> string -> string -> call_target_info_int

val mk_static_pck_stub_target:
  doubleword_int -> string -> string list -> string -> call_target_info_int

val mk_wrapped_target:
  doubleword_int
  -> function_api_t
  -> call_target_t
  -> (api_parameter_t * bterm_t) list
  -> call_target_info_int

val update_target_api:
  call_target_info_int -> function_api_t -> call_target_info_int


