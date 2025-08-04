(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2025 Aarno Labs LLC

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

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes


(** The principal access point for commands on and analysis results of an
    assembly instruction.

    It can be used to access various properties about that location, such as
    invariants, call target and call arguments (if the instruction at the location
    is a call instruction), branch target (if the instruction at the location is a
    branch instruction), branch condition (in case of a conditional branch), etc.
 *)


(** [get_floc loc] returns a [floc] object at the location loc, that can be
    used to both retrieve and set properties of the instruction at that location *)
val get_floc : location_int -> floc_int


(** [get_floc_by_address faddr iaddr] returns a [floc] object for the context-free
    instruction address [iaddr] in the function with address [faddr] *)
val get_floc_by_address: doubleword_int -> doubleword_int -> floc_int



(** [get_i_floc floc iaddr] returns a [floc] object for the same function/context
    as [floc], but for the (potentially) different instruction address [iaddr] *)
val get_i_floc:
  floc_int
  -> doubleword_int
  -> floc_int


val default_bterm_evaluator:
  function_info_int -> (fts_parameter_t * xpr_t) list -> bterm_evaluator_int
