(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
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
open CHConstantPropagationNoArrays
open CHLanguage

(* jchlib *)
open JCHCopyPropagationNoArrays


class skip_remover_t :
  object
    method walkBoolExp : boolean_exp_t -> unit
    method walkCmd     : (code_int, cfg_int) command_t -> unit
    method walkCode    : code_int -> unit
    method walkNumExp  : numerical_exp_t -> unit
    method walkSymExp  : symbolic_exp_t -> unit
    method walkVar     : variable_t -> unit
  end

class simplifier_t :
  system_int ->
  object
    method copy_propagation        : copy_propagation_no_arrays_t
    method cst_propagation         : constant_propagation_no_arrays_t
    method remove_skips            : code_int -> unit
    method remove_unused_vars      : procedure_int -> unit
    method remove_useless_commands : procedure_int -> unit
    method simplify_procedure      : procedure_int -> unit
  end
