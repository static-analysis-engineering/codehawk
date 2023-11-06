(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023  Aarno Labs LLC

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
open CHAtlas
open CHCommon
open CHDomain
open CHIterator
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues
open CHOnlineCodeSet
open CHSymbolicSets
open CHSymbolicSetsDomainNoArrays
open CHPretty

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchanalyze *)
open BCHAnalyzeProcedure


module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory


class reaching_defs_domain_no_arrays_t =
object (self: 'a)

  inherit non_relational_domain_t

  method private getValue' v =
    let v_value = self#getValue v in
    match v_value#getValue with
    | SYM_SET_VAL i -> i
    | TOP_VAL -> topSymbolicSet
    | _ ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Symbolic set expected. ";
                 v#toPretty;
		 STR ": ";
                 v_value#toPretty]))

  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (SYM_SET_VAL x))

  method special cmd args = {< >}

  method private importValue v =
    new non_relational_domain_value_t (SYM_SET_VAL (v#toSymbolicSet))

  method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
	{< table = table' >}
      in
      match cmd with
      | ABSTRACT_VARS l ->
	 begin
	   self#abstractVariables table' l;
	   default ()
	 end
      | ASSIGN_SYM (x, SYM s) ->
	 self#setValue' table' x (new symbolic_set_t [s]);
	 default ()
      | _ ->
	 default ()

  method private analyzeBwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
	{< table = table' >}
      in
      match cmd with
      | ABSTRACT_VARS l ->
	 begin
	   self#abstractVariables table' l;
	   default ()
	 end
      | ASSIGN_SYM (x, SYM s) ->
	 let x_s = self#getValue' x in
	 let x_s' = x_s#meet (new symbolic_set_t [s]) in
	 if x_s'#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     default ()
	   end
      | _ ->
	 default ()

  method analyzeOperation
           ~(domain_name: string)
           ~(fwd_direction: bool)
           ~(operation: operation_t):'a =
    let name = operation.op_name#getBaseName in
    let table' = table#clone in
    let default () =
      {< table = table' >} in
    let (v, sym) =
      match operation.op_args with
      | [(_, v, WRITE)] ->
         let iaddr = List.hd operation.op_name#getAttributes in
         let sym =
           match name with
           | "def" -> new symbol_t iaddr
           | "clobber" -> new symbol_t ~atts:["clobber"] iaddr
           | s -> new symbol_t ~atts:["?" ^ s ^ "?"] iaddr in
         (v, sym)
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [STR "Error in reachingdefs:analyzeOperation"])) in
    match name with
    | "def" | "clobber" ->
       if fwd_direction then
         begin
           self#setValue' table' v (new symbolic_set_t [sym]);
           default ()
         end
       else
         let v_sym = self#getValue' v in
         let v_sym' = v_sym#meet (new symbolic_set_t [sym]) in
         if v_sym'#isBottom then
           self#mkBottom
         else
           begin
             table'#remove v;
             default ()
           end
    | s ->
       begin
         ch_error_log#add
           "reachingdefs"
           (LBLOCK [STR "Unexpected operation: "; STR s]);
         default ()
       end

end

       
let get_vardefuse (op: CHLanguage.operation_t):(variable_t * symbolic_exp_t) =
  match op.op_args with
  | [("dst", v, WRITE)] ->
     (v, SYM (new symbol_t (List.hd op.op_name#getAttributes)))
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Error in get_vardefuse"]))
                                                 

let opsemantics (domain: string) =
  fun
    ~(invariant: CHAtlas.atlas_t)
    ~(stable: bool)
    ~(fwd_direction: bool)
    ~(context: CHLanguage.symbol_t CHStack.stack_t)
    ~(operation: CHLanguage.operation_t) ->
  match operation.op_name#getBaseName with
  | "invariant" ->
     let _ =
       if stable then
         bb_invariants#add_invariant
           (List.hd (operation.op_name#getAttributes)) domain invariant in
     invariant
  | "def" | "clobber" ->
     let (v, sym) = get_vardefuse operation in
     if fwd_direction then
       invariant#analyzeFwd (ASSIGN_SYM (v, sym))
     else
       invariant#analyzeBwd (ASSIGN_SYM (v, sym))
  | _ -> invariant


let analyze_procedure_with_reaching_defs
      (proc: procedure_int) (system: system_int) =
  let strategy: iteration_strategy_t = {
      widening = (fun _ -> true, ""); narrowing = (fun _ -> true)} in
  let iterator =
    new iterator_t
      ~db_enabled:false
      ~do_loop_counters:false
      ~strategy
      ~op_semantics:(opsemantics "reachingdefs") system in
  let code = LF.mkCode [CODE (new symbol_t "code", proc#getBody)] in
  let init = [("reachingdefs", new reaching_defs_domain_no_arrays_t)] in
  let _ =
    iterator#runFwd
      ~domains:["reachingdefs"]
      ~atlas:(new atlas_t ~sigmas:[] init)
      (CODE (new symbol_t "code", code)) in
  ()


let analyze_procedure_with_flag_reaching_defs
      (proc: procedure_int) (system: system_int) =
  let strategy: iteration_strategy_t = {
      widening = (fun _ -> true, ""); narrowing = (fun _ -> true)} in
  let iterator =
    new iterator_t
      ~db_enabled:false
      ~do_loop_counters:false
      ~strategy
      ~op_semantics:(opsemantics "flagreachingdefs") system in
  let code = LF.mkCode [CODE (new symbol_t "code", proc#getBody)] in
  let init = [("flagreachingdefs", new reaching_defs_domain_no_arrays_t)] in
  let _ =
    iterator#runFwd
      ~domains:["flagreachingdefs"]
      ~atlas:(new atlas_t ~sigmas:[] init)
      (CODE (new symbol_t "code", code)) in
  ()


let extract_reaching_defs
      (finfo: function_info_int)
      (invariants: (string, (string, atlas_t) H.t) H.t) =
  H.iter (fun k v ->
      if H.mem v "reachingdefs" then
        let inv = H.find v "reachingdefs" in
        let domain = inv#getDomain "reachingdefs" in
        let varObserver = domain#observer#getNonRelationalVariableObserver in
        let vars = domain#observer#getObservedVariables in
        List.iter (fun (v: variable_t) ->
            let reachingdefs = (varObserver v)#toSymbolicSet in
            if reachingdefs#isTop then
              ()
            else
              match reachingdefs#getSymbols with
              | SET symbols ->
                 let symbols =
                   List.sort (fun s1 s2 ->
                       Stdlib.compare
                         s1#getBaseName s2#getBaseName) symbols#toList in
                 finfo#fvarinv#add_reaching_def k v symbols
              | _ -> ()) vars) invariants


let extract_flag_reaching_defs
      (finfo: function_info_int)
      (invariants: (string, (string, atlas_t) H.t) H.t) =
  H.iter (fun k v ->
      if H.mem v "flagreachingdefs" then
        let inv = H.find v "flagreachingdefs" in
        let domain = inv#getDomain "flagreachingdefs" in
        let varObserver = domain#observer#getNonRelationalVariableObserver in
        let vars = domain#observer#getObservedVariables in
        List.iter (fun (v: variable_t) ->
            let reachingdefs = (varObserver v)#toSymbolicSet in
            if reachingdefs#isTop then
              ()
            else
              match reachingdefs#getSymbols with
              | SET symbols ->
                 let symbols =
                   List.sort (fun s1 s2 ->
                       Stdlib.compare
                         s1#getBaseName s2#getBaseName) symbols#toList in
                 finfo#fvarinv#add_flag_reaching_def k v symbols
              | _ -> ()) vars) invariants
