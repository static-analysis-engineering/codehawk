(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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
open CHStack
open CHLanguage
open CHAtlas
open CHIterator


class type j_semantics_int =
object
  method stable:
           system_int -> iterator_t -> int -> int -> op_arg_t list -> atlas_t -> unit
  method propagate_fwd:
           system_int -> iterator_t -> int -> int -> op_arg_t list -> atlas_t -> atlas_t
  method propagate_bwd:
           system_int -> iterator_t -> int -> int -> op_arg_t list -> atlas_t -> atlas_t
end


class type j_opsemantics_int =
object
  method i_semantics       : j_semantics_int
  method ii_semantics      : j_semantics_int
  method e_semantics       : j_semantics_int
  method init_semantics    : j_semantics_int
  method exit_semantics    : j_semantics_int
  method exn_exit_semantics: j_semantics_int
end


val j_nop_semantics: j_semantics_int


val j_nop_opsemantics: j_opsemantics_int


val opsemantics:
  ?remove_dead_vars:bool
  -> system_int
  -> symbol_t
  -> j_opsemantics_int
  -> invariant:atlas_t
  -> stable:bool
  -> fwd_direction:bool
  -> context:symbol_t stack_t
  -> operation:operation_t -> atlas_t
