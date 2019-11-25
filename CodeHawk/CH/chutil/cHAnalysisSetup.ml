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
open CHAtlas
open CHCommon
open CHDomain
open CHIntervalsDomainNoArrays
open CHIterator   
open CHLanguage
open CHLinearEqualitiesDomainNoArrays
open CHNumerical
open CHNumericalConstraints   
open CHOnlineCodeSet
open CHPolyhedraDomainNoArrays   
open CHPretty
open CHStridedIntervals
open CHStridedIntervalsDomainNoArrays
open CHValueSetsDomainNoArrays

(* chutil *)
open CHInvStore   
open CHLogger


module LF = CHOnlineCodeSet.LanguageFactory

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


class analysis_setup_t:analysis_setup_int =
object (self : 'a)
 
  val mutable sigma_tests = [] 
  val mutable domains = []
  val mutable init = []
  val mutable strategy = {
    widening = (fun i -> i >= 3, "" );
    narrowing = (fun i -> i >= 3) }

  val mutable op_semantics = 
    fun ~invariant ~stable ~fwd_direction ~context ~operation -> invariant

  method setStrategy strat = 
    strategy <- strat

  (* set the default semantics for OPERATIONs to retrieve the invariant when the
     iteration is stable and store the invariant in the given store with address
     the name of the operation, but only if the name of the operation passes the 
     opname_filter. By default, abstract all variables that are WRITE or READ_WRITE.
   *)
  method setDefaultOpSemantics (store:invariant_store_int) (opname_filter:symbol_t -> bool)  =
    let semantics =
      fun ~invariant ~stable ~fwd_direction ~context ~operation ->
        let _ = 
            if stable && opname_filter operation.op_name then
              store#add_invariant operation.op_name invariant
	    else
	      () in
	let mods = 
            List.filter (fun (_, _, m) -> match m with READ  -> false | _ -> true) operation.op_args in
        let mods_l = List.map (fun (_, v, _) -> v) mods in
    if fwd_direction then 
       invariant#analyzeFwd (ABSTRACT_VARS mods_l) 
    else 
       invariant#analyzeBwd (ABSTRACT_VARS mods_l)
    in
    op_semantics <- semantics

  (* set the semantics for OPERATIONs to the given semantics *)
  method setOpSemantics (s:op_semantics_t) = op_semantics <- s

  (* Clear the domains *)
  method resetDomains = begin domains <- [] ; init <- [] end

  (* Add intervals to the list of domains in the atlas *)
  method addIntervals = 
    if List.mem "intervals" domains then () else
    begin
      init <- ("intervals", new intervals_domain_no_arrays_t) :: init ;
      domains <- "intervals" :: domains
    end

  (* Add valuesets to the list of domains in the atlas *)
  method addValueSets =
    if List.mem "valuesets" domains then () else
    begin
      init <- ("valuesets", new valueset_domain_no_arrays_t) :: init ;
      domains <- "valuesets" :: domains
    end

  (* Add strided intervals to the list of domains in the atlas *)
  method addStridedIntervals = 
    if List.mem "strided_intervals" domains then () else
    begin
      init <- ("strided_intervals", new strided_intervals_domain_no_arrays_t) :: init ;
      domains <- "strided_intervals" :: domains
    end

  (* Add linear equalities to the list of domains in the atlas *)
  method addLinearEqualities =
    if List.mem "karr" domains then () else
    begin
      init <- ("karr", new linear_equalities_domain_no_arrays_t) :: init ;
      domains <- "karr" :: domains
    end

  (* Add polyhedra to the list of domains in the atlas *)
  method addPolyhedra =
    if List.mem "polyhedra" domains then () else
    begin
      init <- ("polyhedra", new polyhedra_domain_no_arrays_t) :: init ;
      domains <- "polyhedra" :: domains
    end

  (* Add the domain with the given name and initial values to the list of domains in the atlas *)
  method addDomain (name:string) (dom:domain_int) =
    if List.mem name domains then () else
    begin
      init <- (name, dom) :: init ;
      domains <- name :: domains
    end

  (* run the iterator on the given procedure with the domains specified  *)
  method analyze_procedure 
      ?(do_loop_counters=false) 
      ?(preamble = [])
      ?(verbose = false)
      system (proc:procedure_t) =
    let iterator = new iterator_t
	~db_enabled:false
	~do_loop_counters:do_loop_counters
	~strategy:strategy
	~op_semantics:op_semantics system in
    let code = LF.mkCode (preamble @ [ CODE (new symbol_t "code", proc#getBody) ]) in
    let _ = iterator#runFwd
	~domains:domains
	~atlas:(new atlas_t ~sigmas:sigma_tests init)
	(CODE (new symbol_t "code", code)) in
      ()

  (* run the iterator on the given procedure with the domains specified;
     catch exceptions and log them in the standard logging facility. 
  *)
  method analyze_procedure_with_logging
      ?(start_timer=fun _ -> ())
      ?(end_timer=fun _ -> ())
      ?(do_loop_counters=false) 
      ?(verbose=false)
      system 
      (proc:procedure_t) =
    let thisname = "cHAnalysisSetup.analysis_setup_t.analyze_procedure" in
    let iterator = new iterator_t
	~db_enabled:false
	~do_loop_counters:do_loop_counters
	~strategy:strategy
	~op_semantics:op_semantics system in
    let _ =
      if verbose then
        pr_debug [ STR "Analyzing " ; proc#getName#toPretty ; NL ]
      else () in
    try
      let _ = start_timer proc#getName in
      let _ =
        iterator#runFwd
	  ~domains:domains
	  ~atlas:(new atlas_t ~sigmas:sigma_tests init)
	  (CODE (new symbol_t "code", proc#getBody)) in
      let _ = end_timer proc#getName in
      ()
    with
    | CHFailure e ->
       let msg =
         LBLOCK [
             STR "type:      " ; STR "CHFailure " ; e ; NL ;
	     STR "procedure: " ; proc#getName#toPretty ; NL ;
	     STR "domains:   " ;
             pretty_print_list domains (fun d -> STR d) "[" ", " "]" ; NL ] in
       chlog#add thisname msg
    | Division_by_zero ->
       let msg =
         LBLOCK [
             STR "type:      " ; STR "Division_by_zero" ; NL ;
	     STR "procedure: " ; proc#getName#toPretty ; NL ;
	     STR "domains:   " ;
             pretty_print_list domains (fun d -> STR d) "[" ", " "]"  ; NL ] in
       chlog#add thisname msg
    | Invalid_argument s ->
       let msg =
         LBLOCK [
             STR "type:      " ; STR "Invalid_argument " ; STR s ; NL ;
	     STR "procedure: " ; proc#getName#toPretty ; NL ;
	     STR "domains:   " ;
             pretty_print_list domains (fun d -> STR d) "[" ", " "]" ; NL ] in 
       chlog#add thisname msg 
       
  (* run the iterator on all procedures in the given system with the domain specified;
     no inlining is performed.
     catch exceptions and log them in the standard logging facility.
   *)
  method analyze_system 
      ?(start_timer=fun _ -> ())
      ?(end_timer=fun _ -> ())
      ?(proc_filter=fun _ -> true) 
      ?(verbose=false)
      ?(do_loop_counters=false) system =
    let thisname = "cHAnalysisSetup.analysis_setup_t.analyze_system" in
    let iterator =
      new iterator_t 
	  ~db_enabled:false
	  ~do_loop_counters:do_loop_counters
	  ~strategy:strategy
	  ~op_semantics:op_semantics system in
    let _ =
      List.iter
	(fun proc ->
	  try
	    let p = system#getProcedure proc in
	    if proc_filter p then
	      let _ =
                if verbose then
                  pr_debug [ STR "Analyzing " ; proc#toPretty ; NL ]
                else
                  () in
	      let _ = start_timer proc in
	      let _ =
                iterator#runFwd
		  ~domains:domains
		  ~atlas:(new atlas_t init)
		  (CODE (new symbol_t "code", p#getBody)) in
	      let _ = end_timer proc in
	      ()
	    else
	      ()
	  with
	  | CHFailure e ->
	     let msg =
               LBLOCK [
                   STR "type:      " ; STR "CHFailure " ; e ; NL ;
		   STR "procedure: " ; proc#toPretty ; NL ;
		   STR "domains:   " ;
                   pretty_print_list domains (fun d -> STR d) "[" ", " "]"; NL ] in
	     chlog#add thisname msg
	  | Division_by_zero ->
	     let msg =
               LBLOCK [
                   STR "type:      " ; STR "Division_by_zero" ; NL ;
		   STR "procedure: " ; proc#toPretty ; NL ;
		   STR "domains:   " ;
                   pretty_print_list domains (fun d -> STR d) "[" ", " "]" ; NL ] in
	     chlog#add thisname msg
	  | Invalid_argument s ->
	     let msg =
               LBLOCK [
                   STR "type:      " ; STR "Invalid_argument " ; STR s ; NL ;
		   STR "procedure: " ; proc#toPretty ; NL ;
		   STR "domains:   " ;
                   pretty_print_list domains (fun d -> STR d) "[" ", " "]" ; NL ] in 
	     chlog#add thisname msg
	  | Failure s ->
	     let msg =
               LBLOCK [
                   STR "type:      " ; STR "Failure " ; STR s ; NL ;
		   STR "procedure: " ; proc#toPretty ; NL ;
		   STR "domains:   " ;
                   pretty_print_list domains (fun d -> STR d) "[" ", " "]" ; NL ] in
	     chlog#add thisname msg
	) system#getProcedures in
    ()
    

end


let mk_analysis_setup () = new analysis_setup_t

