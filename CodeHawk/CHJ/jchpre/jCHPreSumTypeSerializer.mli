(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
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
   
(* jchlib *)
open JCHBasicTypesAPI
   
(* jchpre *)
open JCHPreAPI

val binopcode_serializer      : opcode_t sumtype_string_converter_int
val converteropcode_serializer: opcode_t sumtype_string_converter_int

val variable_type_serializer: variable_type_t sumtype_string_converter_int
val non_virtual_target_type_serializer: non_virtual_target_type_t sumtype_string_converter_int
val call_targets_serializer: call_targets_t sumtype_string_converter_int
  
val taint_origin_type_serializer: taint_origin_type_t sumtype_string_converter_int
val taint_node_type_serializer  : taint_node_type_t sumtype_string_converter_int
  
val bc_basicvalue_serializer : bc_basicvalue_t sumtype_string_converter_int
val bc_objectvalue_serializer: bc_objectvalue_t sumtype_string_converter_int
val bc_action_serializer     : bc_action_t sumtype_string_converter_int
val bc_pattern_serializer    : bc_pattern_t sumtype_string_converter_int
