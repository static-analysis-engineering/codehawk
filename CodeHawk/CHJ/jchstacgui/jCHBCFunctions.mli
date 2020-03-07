(* =============================================================================
   CodeHawk Java Analyzer
   Author: Andrew McGraw and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* chutil *)
open CHDot

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

class type bc_function_int =
  object
    method get_blocks: bc_block_int list
    method get_cfg_dot: dot_graph_int
    method get_annotated_cfg_dot: bool -> dot_graph_int
    method get_max_loop_depth: int
    method get_conditions: (int * string) list
    method get_reflective_calls: (int * opcode_t * pretty_t) list
    method get_pushpop_calls: (int * opcode_t * pretty_t) list
    method get_thread_calls: (int * opcode_t * pretty_t) list
    method get_append_calls: (int * opcode_t * pretty_t) list
    method get_loop_taint: int -> int
    method get_cost: int -> int
    method get_total_cost: int
    method get_loop_levels: int -> symbol_t list

    method has_method_call: string -> int -> bool
    method has_class_call: string -> int -> bool
  end

class type bc_functions_int =
  object
    method get_bc_function: method_info_int -> string  * bc_function_int
    method get_bc_function_by_name: string -> bc_function_int
  end

val bcfunctions: bc_functions_int
