(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* bchlibx86 *)
open BCHLibx86Types


(** [make_assembly_function faddr blocks succs] returns an assembly function
    with function address [faddr], basic blocks [blocks] and successor relation
    [succs] for the basic blocks.*)
val make_assembly_function:
  doubleword_int
  -> assembly_block_int list
  -> (ctxt_iaddress_t * ctxt_iaddress_t) list
  -> assembly_function_int


(** Returns a measure of the precision (not necessarily accuracy) of the
    stack pointer values calculated for this function. The first value in
    the tuple represents the number of locations for which no information
    on the stack pointer is available at all (value is TOP), the second
    value in the tuple represents the number of locations for which a
    range (either lower-bound or upper-bound or both) is calculated, but
    not a single value (hence the value is an interval)

    Note: (0, 0) means the stackpointer is known precisely at all locations
    in this function.
 *)
val get_esp_metrics: assembly_function_int -> (int * int)


(** Returns a measure of the precision (not necessarily accuracy) of the
    memory locations calculated for this function. The values returned
    represent:
    - {b reads}: the number of memory reads
    - {b qreads}: the number of memory reads with location unknown
    - {b writes}: the number of memory writes
    - {b qwrites}: the number of memory writes with location unknown

    Note: (x, 0, y, 0) means the location of all memory locations have a
    calculated (symbolic) value.
 *)
val get_op_metrics:
  assembly_function_int -> function_info_int -> (int * int * int * int)
