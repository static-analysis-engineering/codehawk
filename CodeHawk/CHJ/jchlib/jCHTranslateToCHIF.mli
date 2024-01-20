(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny Sipma

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
open CHLanguage

(* jchlib *)
open JCHBasicTypesAPI


val handler_pc_label: int -> string

val get_register_variable: int -> value_type_t -> variable_t

val set_command_pretty_printer:
  (int -> ((code_int,cfg_int) command_t -> pretty_t)) -> unit

val translation_failed : CHUtils.SymbolCollections.set_t

val exception_var : CHLanguage.variable_t ref

val make_exn_info:
  class_name_int
  -> (scope_int -> variable_t -> (code_int, cfg_int) command_t list)
  -> (class_name_int -> catch_info_t) -> exn_info_int

val defaultExnInfo: exn_info_int

val defaultExnInfoFn: method_int -> (int -> exn_info_int list)

val make_stack_variable: int -> int -> variable_type_t -> variable_t

val make_register_variable: int -> variable_type_t -> variable_t

val translate_method :
  proc_filter:(procedure_int -> bool) ->
  simplify:bool ->
  transform:bool ->
  java_method:method_int -> code_set:system_int ->
  ?exn_infos_fn:(int -> exn_info_int list) ->
  ?initialization_cmd:(code_int, cfg_int) command_t -> unit -> unit

val translate_class :
  java_class:java_class_or_interface_int ->
  code_set:system_int ->
  ?proc_filter:(procedure_int -> bool) ->
  ?simplify:bool -> ?transform:bool -> unit -> unit

val make_code_set : symbol_t -> system_int

val get_procname_symbol: class_method_signature_int -> symbol_t

val get_method_stack_layout: system_int -> method_int -> method_stack_layout_int
