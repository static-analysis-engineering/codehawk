(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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

(** Facility to record problems during a run of the analyzer. *)

(* chlib *)
open CHPretty

(* chutil *)
open CHTraceResult


val activate_diagnostics: unit -> unit
val deactivate_diagnostics: unit -> unit
val collect_diagnostics: unit -> bool


class type logger_int =
  object
    method set_max_entry_size: int -> unit
    method add: string -> pretty_t -> unit
    method reset: unit
    method size: int
    method tagsize: string -> int
    method toPretty: pretty_t
  end

type tracelogspec_t = {
    tlogger: logger_int;
    ttag: string;
    tmsg: string
  }

(** Create a new logger object.*)
val mk_logger: unit -> logger_int


(** Default logger used in all analyzers.*)
val chlog: logger_int


(** Default error logger used in all analyzers.*)
val ch_error_log: logger_int


(** Optional logger for information messages.*)
val ch_info_log: logger_int


(** Logger for diagnostic messages; can be activated/deactivated with
    [activate_diagnostics] and [deactivate_diagnostics] respectively;
    [collect_diagnostics] reports it diagnostic logging is active.*)
val ch_diagnostics_log: logger_int


val mk_tracelog_spec:
  ?logger:logger_int -> ?tag:string -> string -> tracelogspec_t


(** [log_tvalue tls ~default] is [v] if [r] is [Ok v] and
    [default] otherwise. If [r] is [Error e], [e] is logged
    according to [tls].*)
val log_tvalue:
  tracelogspec_t -> 'a traceresult -> default:'a -> 'a


(** [log_titer tls f r] is [f v] if [r] is [Ok v] and
    logs [e] if [r] is [Error e] according to [tls].*)
val log_titer:
  tracelogspec_t -> ('a -> unit) -> 'a traceresult -> unit


(** [log_tfold tls ~ok ~error r] is [ok v] if [r] is [Ok v] and
    [error e] if [r] is [Error e]. In addition, if [r] is [Error e],
    [e] is logged according to [tls].*)
val log_tfold:
  tracelogspec_t
  -> ok:('a -> 'c)
  -> error:(string list -> 'c)
  -> 'a traceresult
  -> 'c


(** [log_tfold_default tls f d r] is [f v] if [r] is [Ok v] and
    [d] if [r] is [Error _]. In addition, if [r] is [Error e],
    [e] is logged according [tls].*)
val log_tfold_default:
  tracelogspec_t -> ('a -> 'c) -> 'c -> 'a traceresult -> 'c
