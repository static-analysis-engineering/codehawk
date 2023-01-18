(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2020 Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs

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
open CHNumericalConstraints

(* chutil *)
open CHTraceResult

(* bchlib *)
open BCHLibTypes


exception BCH_failure of pretty_t

(* raised in cases an internal inconsistency is encountered *)
exception Internal_error of string

(* raised in cases where a partial method is called without checking
   whether the requested data is available. 
   Typical case: calling get_xxxx without first checking has_xxxx.
   In general, when a class has a matching has_xxxx for a get_xxxx
   method, the get_xxxx should be considered partial *)
exception Invocation_error of string

(* raised in cases where the external input does not conform to
   the assumptions made in the program *)
exception Invalid_input of string

(* raised when control flow is found to be altered *)
exception Request_function_retracing


val trerror_record: pretty_t -> string list -> pretty_t


(** [fail_tvalue p r] is [v] if [r] is [Ok v] and raises
    [BCH_failure (p e)] if [r] is [Error e].

    @raise BCH_failure
*)
val fail_tvalue: (string list -> pretty_t) -> 'a traceresult -> 'a


(** [fail_tfold p f r] is [f v] if [r] is [Ok v] and raises
    [BCH_failure (p e)] if [r] is [Error e].

    @raise BCH_failure
*)
val fail_tfold: (string list -> pretty_t) -> ('a -> 'c) -> 'a traceresult -> 'c


(** [fail_titer p f r] is [f v] if [r] is [Ok v] and raises
    [BCH_failure (p e)] if [r] is [Error e].

    @raise BCH_failure
 *)
val fail_titer:
  (string list -> pretty_t) -> ('a -> unit) -> 'a traceresult -> unit


val get_version: unit -> string

val eflag_to_string: eflag_t -> string

val eflag_from_string: string -> eflag_t

val eflag_compare: eflag_t -> eflag_t -> int

val arm_cc_flag_to_string: arm_cc_flag_t -> string

val arm_cc_flag_from_string: string -> arm_cc_flag_t

val arm_cc_flag_compare: arm_cc_flag_t -> arm_cc_flag_t -> int

val flag_to_string: flag_t -> string

val flag_from_string: string -> flag_t

val flag_compare: flag_t -> flag_t -> int


type risk_type_t =
    OutOfBoundsRead
  | OutOfBoundsWrite
  | NullDereference
  | TypeConditionViolation
  | FunctionFailure

val risk_type_to_string: risk_type_t -> string
val risk_type_from_string: string -> risk_type_t

val symbol_to_pretty: symbol_t -> pretty_t
val factor_to_pretty: numerical_factor_t -> pretty_t
val symbol_to_string: symbol_t -> string
val factor_to_string: numerical_factor_t -> string
