(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(** Utilities to set up an analysis *)

(* chlib *)
open CHDomain
open CHIterator
open CHLanguage
open CHOnlineCodeSet

(* chutil *)
open CHInvStore

class type analysis_setup_int =
  object
    method addDomain : string -> domain_int -> unit
    method addIntervals : unit
    method addLinearEqualities : unit
    method addPolyhedra : unit
    method addStridedIntervals : unit
    method addValueSets : unit
    method analyze_procedure :
      ?do_loop_counters:bool
      -> ?preamble:(code_int, cfg_int) command_t list
      -> ?verbose:bool
      -> system_int
      -> procedure_t
      -> unit
    method analyze_procedure_with_logging :
      ?start_timer:(symbol_t -> unit)
      -> ?end_timer:(symbol_t -> unit)
      -> ?do_loop_counters:bool
      -> ?verbose:bool
      -> system_int
      -> procedure_t
      -> unit
    method analyze_system :
      ?start_timer:(symbol_t -> unit)
      -> ?end_timer:(symbol_t -> unit)
      -> ?proc_filter:(procedure_int -> bool)
      -> ?verbose:bool
      -> ?do_loop_counters:bool
      -> system_int
      -> unit
    method resetDomains : unit
    method setDefaultOpSemantics : invariant_store_int -> (symbol_t -> bool) -> unit
    method setOpSemantics : op_semantics_t -> unit
    method setStrategy : iteration_strategy_t -> unit
  end


val mk_analysis_setup: unit -> analysis_setup_int
