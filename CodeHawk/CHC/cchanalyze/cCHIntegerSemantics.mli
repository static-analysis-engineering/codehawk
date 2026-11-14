(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026 Aarno Labs LLC

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

(** Integer semantics for the numerical domains.

    The numerical domains reason over unbounded integers (Z), and the
    expression translator maps C arithmetic to its mathematical counterpart.
    This module provides the corrections that map the mathematical value of
    an integer expression to its C value:

    - unsigned [+], [-], [*] and unary [-]: reduction modulo [2^N]
      (C11 6.2.5p9);
    - unsigned [<<]: reduction modulo [2^N] (C11 6.5.7p4);
    - conversion to an unsigned type: reduction modulo [2^N] (C11 6.3.1.3p2);
    - conversion to a signed type that cannot represent the value:
      implementation-defined (C11 6.3.1.3p3); GCC's documented behavior,
      reduction modulo [2^N] into the target range, is used;
    - conversion to [_Bool]: 0 or 1 (C11 6.3.1.2).

    Signed overflow is undefined behavior and is not corrected. *)

(* chlib *)
open CHLanguage
open CHNumerical

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

(* cchanalyze *)
open CCHAnalysisTypes


(** The correction needed at a site. *)
type correction_t =
  | RangeCorrection of
      numerical_t       (* lo: target range lower bound *)
      * numerical_t     (* hi: target range upper bound *)
      * numerical_t     (* slo: lower bound of the mathematical value *)
      * numerical_t     (* shi: upper bound of the mathematical value *)
  (** Reduction modulo [hi - lo + 1] into [[lo, hi]] of a value in
      [[slo, shi]]; corrections below [lo] or above [hi] that are not possible
      or that are excluded by a proof obligation proven safe are left out
      (i.e., [slo >= lo], [shi <= hi] respectively). *)
  | BoolCorrection of numerical_t   (* slo: lower bound of the value *)


(** [get_correction env context e] returns the correction needed to map the
    mathematical value of [e], evaluated in cfg context [context], to its C
    value, or [None] if the two coincide on every execution.

    A lower (upper) correction is omitted if the primary proof obligation
    for the lower (upper) bound of this operation or conversion in [context]
    has been proven safe (in an earlier round). This is sound: that proof was
    based on invariants computed with corrections at all sites not yet
    proven. It is needed for precision: the relational domains cannot use the
    guards to refute an unneeded correction branch, so the join of the
    branches would lose relations. *)
val get_correction:
  c_environment_int -> program_context_int -> exp -> correction_t option


(** [unsigned_shift_factor e2 ty] returns [2^k] if [ty] is an unsigned
    integer type of width [N] and [e2] is an integer constant [k] with
    [0 <= k < N], so that the mathematical value of [e1 << e2] (of type [ty])
    is [e1 * 2^k]; otherwise [None]. *)
val unsigned_shift_factor: exp -> typ -> numerical_t option


(** [fold_constant c n] is the C value of the site whose mathematical value
    is the constant [n]. *)
val fold_constant: correction_t -> numerical_t -> numerical_t


(** [correction_code env v c] returns the commands that replace the
    mathematical value held in [v] by the C value: a branch with one case for
    the value in range, one for a single wrap around in each direction, and
    one that havocs [v] into the target range for values more than one wrap
    around away. *)
val correction_code:
  c_environment_int -> variable_t -> correction_t -> c_cmd_t list
