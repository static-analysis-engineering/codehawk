(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2025 Aarno Labs LLC

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
open CHNumerical

(* xprlib *)
open XprTypes


(** returns the largest constant term in the given expression, taking into
    account the sign. If there are no constant terms, zero is returned.*)
val largest_constant_term : xpr_t -> numerical_t


(** returns the smallest constant term in the given expression, taking into
    account the sign. If there are no constant terms, zero is returned.*)
val smallest_constant_term: xpr_t -> numerical_t

(** returns the smallest constant term in the given expression, while
    wrapping constants larger than 2^31 into negative numbers. The pair
    returned is the term as appearing in the expression and the corresponding
    negative value.
*)
val smallest_wrapped_constant_term: xpr_t -> numerical_t * numerical_t

val normalize_offset_expr: xpr_t -> xpr_t

val normalize_scaled_ivar_expr: xpr_t -> variable_t -> xpr_t option

val vars_as_positive_terms: xpr_t -> variable_t list

(** [get_array_index_offset x size] returns a tuple [(xi, n)] such that
    (1) xi * size + n = x, and
    (2) 0 <= n < size
    if such [xi] and [n] can be found, and None otherwise.

    Note: It is assumed that all variables are part of the index, and that
    the remaining offset is constant (e.g., to be converted into one or
    more levels of field offsets.
*)
val get_array_index_offset: xpr_t -> int -> (xpr_t * xpr_t) option
