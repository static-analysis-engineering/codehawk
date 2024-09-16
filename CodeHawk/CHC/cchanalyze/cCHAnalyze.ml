(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHCommon
open CHIntervalsDomainNoArrays
open CHLanguage
open CHLinearEqualitiesDomainNoArrays
open CHPEPRBounds
open CHPEPRDomainNoArrays
open CHPEPRTypes
open CHPretty
open CHSymbolicSetsDomainNoArrays
open CHStateSetsDomainNoArrays
open CHTimedSymbolicSetsDomainNoArrays
open CHValueSetsDomainNoArrays

(* chutil *)
open CHAnalysisSetup
open CHLogger
open CHTimingLog

(* cchlib *)
open CCHUtilities

(* cchpre *)
open CCHInvariantFact

(* cchanalyze *)
open CCHAnalysisTypes
open CCHInvariantStore

module H = Hashtbl


let start_time = ref 0.0
let timing_active = ref false
let start_timer () =
  begin
    start_time := Unix.gettimeofday ();
    timing_active := true
  end


let analyze_procedure_with_intervals (proc:procedure_int) (system:system_int)
    (semantics:domain_opsemantics_t) =
  let analysis_setup = mk_analysis_setup () in
  begin
    timing_active := false;
    analysis_setup#addDomain intervals_domain (new intervals_domain_no_arrays_t);
    analysis_setup#setOpSemantics (semantics intervals_domain);
    analysis_setup#analyze_procedure system proc;
    log_info "Interval analysis completed [%s:%d]" __FILE__ __LINE__
  end


let analyze_procedure_with_pepr
      (proc:procedure_int)
      (system:system_int)
      (semantics:domain_opsemantics_t)
      (params:pepr_params_int)
      (timeout:float) =
  let analysis_setup = mk_analysis_setup () in
  begin
    timing_active := false;
    analysis_setup#addDomain
      pepr_domain (mk_pepr_domain_no_arrays params timeout);
    analysis_setup#setOpSemantics (semantics pepr_domain);
    analysis_setup#analyze_procedure system proc;
    log_info "Pepr analysis completed [%s:%d]" __FILE__ __LINE__
  end


let analyze_procedure_with_valuesets (proc:procedure_int) (system:system_int)
    (semantics:domain_opsemantics_t) =
  let analysis_setup = mk_analysis_setup () in
  begin
    timing_active := false;
    analysis_setup#addDomain valueset_domain (new valueset_domain_no_arrays_t);
    analysis_setup#setOpSemantics (semantics valueset_domain);
    analysis_setup#analyze_procedure system proc;
    log_info "Value set analysis completed [%s:%d]" __FILE__ __LINE__
  end


let analyze_procedure_with_linear_equalities
      (proc:procedure_int) (system:system_int)
    (semantics:domain_opsemantics_t) =
  let analysis_setup = mk_analysis_setup () in
  try
    begin
      start_timer ();
      analysis_setup#addDomain
        linear_equalities_domain (new linear_equalities_domain_no_arrays_t);
      analysis_setup#setOpSemantics (semantics linear_equalities_domain);
      analysis_setup#analyze_procedure system proc;
      log_info "Linear equality analysis completed [%s:%d]" __FILE__ __LINE__
    end
  with
  | CHFailure p ->
     begin
       ch_error_log#add
         "error"
         (LBLOCK [STR "Error in linear equalities analysis: "; p]);
       raise
         (CCHFailure (LBLOCK [STR "Error in linear equalities analysis: "; p]))
     end


let analyze_procedure_with_symbolic_sets (proc:procedure_int) (system:system_int)
    (semantics:domain_opsemantics_t) =
  let analysis_setup = mk_analysis_setup () in
  begin
    timing_active := false;
    analysis_setup#addDomain
      symbolic_sets_domain (new symbolic_sets_domain_no_arrays_t);
    analysis_setup#setOpSemantics (semantics symbolic_sets_domain);
    analysis_setup#analyze_procedure system proc;
    log_info "symbolic sets analysis completed [%s:%d]" __FILE__ __LINE__
  end


let analyze_procedure_with_statesets
      (proc:procedure_int) (system:system_int) (semantics:domain_opsemantics_t) =
  let analysis_setup = mk_analysis_setup () in
  let policies =
    [("file",
      [("open", [(new symbol_t "start", new symbol_t "open")]);
        ("close", [(new symbol_t "open", new symbol_t "closed")]);
        ("read", [(new symbol_t "open",  new symbol_t "open")])])] in
  begin
    analysis_setup#addDomain
      "state sets" (new state_sets_domain_no_arrays_t policies);
    analysis_setup#setOpSemantics (semantics "state sets");
    analysis_setup#analyze_procedure system proc
  end


let analyze_procedure_with_sym_pointersets
      (proc:procedure_int) (system:system_int)
      (semantics:domain_opsemantics_t)
      (timeout:float) =
  let analysis_setup = mk_analysis_setup () in
  begin
    timing_active := false;
    analysis_setup#addDomain
      sym_pointersets_domain (new timed_symbolic_sets_domain_no_arrays_t timeout);
    analysis_setup#setOpSemantics (semantics sym_pointersets_domain);
    analysis_setup#analyze_procedure system proc;
    log_info "symbolic pointerset analysis completed [%s:%d]" __FILE__ __LINE__
  end


let analyze_linear_equalities
      _env (system:system_int) (semantics:domain_opsemantics_t)  =
  begin
    c_invariants#reset;
    List.iter (fun procName ->
      let proc = system#getProcedure procName in
      begin
	analyze_procedure_with_linear_equalities proc system semantics
      end) system#getProcedures;
    c_invariants#get_invariants
  end


let analyze_intervals _env (system:system_int) (semantics:domain_opsemantics_t) =
  begin
    c_invariants#reset;
    List.iter (fun procName ->
      let proc = system#getProcedure procName in
      begin
	analyze_procedure_with_intervals proc system semantics
      end) system#getProcedures;
    c_invariants#get_invariants
  end


let analyze_pepr env (system:system_int) (semantics:domain_opsemantics_t) =
  let timeout = 10.0 in
  begin
    c_invariants#reset;
    List.iter (fun procName ->
        let proc = system#getProcedure procName in
        let params = mk_pepr_params env#get_parameters in
        try
          analyze_procedure_with_pepr proc system semantics params timeout
        with
        | CHDomainFailure (d,p) ->
           chlog#add
             ("domain failure of " ^ d)
             (LBLOCK [procName#toPretty; STR ": "; p])
        | CHTimeOut d ->
           chlog#add
             ("domain timeout of " ^ d)
             (LBLOCK [procName#toPretty])) system#getProcedures;
    c_invariants#get_invariants
  end


let analyze_valuesets _env (system:system_int) (semantics:domain_opsemantics_t) =
  begin
    c_invariants#reset;
    List.iter (fun procName ->
      let proc = system#getProcedure procName in
      begin
	analyze_procedure_with_valuesets proc system semantics
      end) system#getProcedures;
    c_invariants#get_invariants
  end

let analyze_symbols _env (system:system_int) (semantics:domain_opsemantics_t) =
  begin
    c_invariants#reset;
    List.iter (fun procName ->
      let proc = system#getProcedure procName in
      begin
	analyze_procedure_with_symbolic_sets proc system semantics
      end) system#getProcedures;
    c_invariants#get_invariants
  end


let analyze_statesets _env (system:system_int) (semantics:domain_opsemantics_t) =
  begin
    c_invariants#reset;
    List.iter (fun procName ->
        let proc = system#getProcedure procName in
        begin
          analyze_procedure_with_statesets proc system semantics
        end) system#getProcedures;
    c_invariants#get_invariants
  end


let analyze_sym_pointersets
      _env (system:system_int) (semantics:domain_opsemantics_t) =
  let timeout = 30.0 in
  begin
    c_invariants#reset;
    List.iter (fun procName ->
        let proc = system#getProcedure procName in
        try
          analyze_procedure_with_sym_pointersets proc system semantics timeout
        with
        |CHTimeOut d ->
          chlog#add
            ("domain timeout of " ^ d)
            (LBLOCK [procName#toPretty])) system#getProcedures;
    c_invariants#get_invariants
  end
