(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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

(** Symbols for out-parameter postconditions in the initialization domain.

    A [post-initialized] symbol in the initialized-set (FInitializedSet) of a
    location records that the location was written by a callee as an
    out-parameter postcondition ([initialized( *arg_i)], e.g., from
    [chkc_initializes(i)]), possibly only in the success outcome of the call.

    The success outcome is the complement of the callee's error discriminator
    (its error postcondition on the return value), expressed as a condition on
    the call's function-return-value variable. That variable is assigned only
    by the call, so a condition that holds for its value at a proof-obligation
    location holds for the call that last wrote the location.

    In the error outcome the location keeps the state it had before the call
    (a callee cannot make a location uninitialized). For conditional symbols
    that state is copied at the call into a prior-state (augmentation)
    variable; if the success condition cannot be established, the location is
    still initialized if its prior state was. *)

(* chlib *)
open CHLanguage
open CHPretty


(** Condition on the call's return value under which the postcondition holds. *)
type condition_t =
  | Always                               (** unconditional (no discriminator) *)
  | InRange of int option * int option   (** lb <= rv <= ub; [None] is unbounded *)
  | NotEqual of int                      (** rv <> c *)

type t = {
    pi_callee: string;
    pi_callee_vid: int;
    pi_line: int;          (** line of the call *)
    pi_arg: int;           (** argument index (starting at 1) *)
    pi_rv_index: int;      (** index of the function-return-value variable;
                               -1 if the condition is [Always] *)
    pi_prior_index: int;   (** index of the prior-state variable;
                               -1 if the condition is [Always] *)
    pi_condition: condition_t
  }

val to_symbol: t -> symbol_t

(** [from_symbol s] returns [None] if [s] is not a well-formed
    post-initialized symbol. *)
val from_symbol: symbol_t -> t option

val is_post_initialized_symbol: symbol_t -> bool

(** [success_condition epcs] is the success outcome, given the callee's error
    postconditions [epcs]: [Always] if [epcs] is empty; the complement of a
    single comparison of the return value with a constant otherwise. Returns
    [None] if the error outcome cannot be expressed that way (in that case no
    postcondition is applied at the call). *)
val success_condition: CCHLibTypes.xpredicate_t list -> condition_t option

(** The postcondition [initialized( *arg_i)] the symbol stands for (used to
    record the PostAssumption dependency). *)
val postcondition: t -> CCHLibTypes.xpredicate_t

val condition_to_string: condition_t -> string

val to_pretty: t -> pretty_t
