(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs LLC

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
open CHConstants
open CHDomain
open CHIterator
open CHLanguage
open CHNumericalConstraints
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues
open CHOnlineCodeSet
open CHPretty
open CHUtils

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHBCTypeUtil
open BCHLibTypes

(* bchanalyze *)
open BCHAnalyzeProcedure


module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory


class btype_constants_domain_no_arrays_t =
object (self: 'a)

  inherit non_relational_domain_t

  method private getValue' (v: variable_t): ordered_symbolic_constant_t =
    let t_value = self#getValue v in
    match t_value#getValue with
    | ORDERED_SYM_CONSTANT_VAL n -> n
    | TOP_VAL -> topOrderedSymbolicConstant
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Ordered symbolic constant expected. ";
                 v#toPretty;
                 STR ": ";
                 t_value#toPretty]))

  method private setValue'
                   (t: non_relational_domain_value_t VariableCollections.table_t)
                   (v: variable_t)
                   (x: ordered_symbolic_constant_t) =
    self#setValue
      t v (new non_relational_domain_value_t (ORDERED_SYM_CONSTANT_VAL x))

  method special (cmd: string) (args: domain_cmd_arg_t list) = {< >}

  method private importValue (v: non_relational_domain_value_t) =
    new non_relational_domain_value_t
      (ORDERED_SYM_CONSTANT_VAL (v#toOrderedSymbolicConstant))

  method importNumericalConstraints (csts: numerical_constraint_t list) = {< >}

  method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
        {< table = table' >} in
      match cmd with
      | ABSTRACT_VARS l ->
         begin
           self#abstractVariables table' l;
           default ()
         end
      | ASSIGN_SYM (x, SYM s) ->
         if s#getBaseName = "t_unknown" then
           begin
             self#abstractVariables table' [x];
             default ()
           end
         else             
           begin
             self#setValue' table' x (mkOrderedSymbolicConstant s);
             default ()
           end
      | ASSIGN_SYM (x, SYM_VAR y) ->
         begin
           self#setValue' table' x (self#getValue' y);
           default ()
         end
      | ASSERT TRUE ->
         default ()
      | ASSERT FALSE ->
         self#mkBottom
      | ASSERT (SUBSET (x, syms)) ->
         begin
           match (self#getValue' x)#getCst with
           | ORDERED_SYM_CST s ->
              if List.exists (fun s' -> s#equal s') syms then
                default ()
              else
                self#mkBottom
           | _ ->
              default ()
         end
      | ASSERT (DISJOINT (x, syms)) ->
         begin
           match (self#getValue' x)#getCst with
           | ORDERED_SYM_CST s ->
              if List.exists (fun s' -> s#equal s') syms then
                self#mkBottom
              else
                default ()
           | _ ->
              default ()
         end
      | _ ->
         default ()

  method private analyzeBwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
        {< table = table' >} in
      match cmd with
      | ABSTRACT_VARS l ->
         begin
           List.iter (fun v -> table'#remove v) l;
           default ()
         end
      | ASSIGN_SYM (x, SYM s) ->
         if s#getBaseName = "t_unknown" then
           begin
             table'#remove x;
             default ()
           end
         else
           let x_c = self#getValue' x in
           let x_c' = x_c#meet (mkOrderedSymbolicConstant s) in
           if x_c'#isBottom then
             self#mkBottom
           else
             begin
               table'#remove x;
               default ()
             end
      | ASSIGN_SYM (x, SYM_VAR y) ->
         let x_c = self#getValue' x in
         let y_c = self#getValue' y in
         let y_c' = y_c#meet x_c in
         if y_c'#isBottom then
           self#mkBottom
         else
           begin
             table'#remove x;
             self#setValue' table' y y_c';
             default ()
           end
      | ASSERT _ ->
         self#analyzeFwd' cmd
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
    match name with
    | "btype-set" ->
       let (v, sym) =
         match operation.op_args with
         | [(_, v, WRITE)] ->
            let typ = List.hd operation.op_name#getAttributes in
            let sym = new symbol_t typ in
            (v, sym)
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [STR "Error in typeConstants:analyzeOperation"])) in
       if fwd_direction then
         if sym#getBaseName = "t_unknown" then
           begin
             self#abstractVariables table' [v];
             default ()
           end
         else
           begin
             self#setValue' table' v (mkOrderedSymbolicConstant sym);
             default ()
           end
       else
         if sym#getBaseName = "t_unknown" then
           begin
             table'#remove v;
             default ()
           end
         else 
           let v_ty = self#getValue' v in
           let v_ty' = v_ty#meet (mkOrderedSymbolicConstant sym) in
           if v_ty'#isBottom then
             self#mkBottom
           else
             begin
               table'#remove v;
               default ()
             end
    | "btype-prop" ->
       let (v1, v2) =
         match operation.op_args with
         | [(_, w, WRITE); (_, r, READ)] -> (w, r)
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [STR "Error in typeConstants:analyzeOperation"])) in
       if fwd_direction then
         begin
           self#setValue' table' v1 (self#getValue' v2);
           default()
         end
       else
         let v1_t = self#getValue' v1 in
         let v2_t = self#getValue' v2 in
         let v2_t' = v2_t#meet v1_t in
         if v2_t'#isBottom then
           self#mkBottom
         else
           begin
             table'#remove v1;
             self#setValue' table' v2 v2_t';
               default ()
           end
    | s ->
       begin
         ch_error_log#add
           "btype domain"
           (LBLOCK [STR "Unexpected operation: "; STR s]);
         default ()
       end
                                          
end
  

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
  | "btype-set" ->
     let (v, sym) =
       match operation.op_args with
       | [(_, v, WRITE)] ->
          let typ = List.hd operation.op_name#getAttributes in
          let sym = new symbol_t typ in
          (v, sym)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "Error in typeConstants:analyzeOperation"])) in
     if fwd_direction then
       invariant#analyzeFwd (ASSIGN_SYM (v, SYM sym))
     else
       invariant#analyzeBwd (ASSIGN_SYM (v, SYM sym))
  | "btype-prop" ->
       let (v1, v2) =
         match operation.op_args with
         | [(_, w, WRITE); (_, r, READ)] -> (w, r)
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [STR "Error in typeConstants:analyzeOperation"])) in
       if fwd_direction then
         invariant#analyzeFwd (ASSIGN_SYM (v1, SYM_VAR v2))
       else
         invariant#analyzeBwd (ASSIGN_SYM (v1, SYM_VAR v2))
  | _ -> invariant


let analyze_procedure_with_btypes
      (proc: procedure_int) (system: system_int) =
  let strategy: iteration_strategy_t = {
      widening = (fun _ -> true, ""); narrowing = (fun _ -> true)} in
  let iterator =
    new iterator_t
      ~db_enabled:false
      ~do_loop_counters:false
      ~strategy
      ~op_semantics:(opsemantics "btypes") system in
  let code = LF.mkCode [CODE (new symbol_t "code", proc#getBody)] in
  let init = [("btypes", new btype_constants_domain_no_arrays_t)] in
  let _ =
    iterator#runFwd
      ~domains:["btypes"]
      ~atlas:(new atlas_t ~sigmas:[] init)
      (CODE (new symbol_t "code", code)) in
  ()


let tconstraints = H.create 5
  

let extract_btypes
      (finfo: function_info_int)
      (invariants: (string, (string, atlas_t) H.t) H.t) =
  H.iter (fun k v ->
      if H.mem v "btypes" then
        let inv = H.find v "btypes" in
        let domain = inv#getDomain "btypes" in
        let varObserver = domain#observer#getNonRelationalVariableObserver in
        let vars = domain#observer#getObservedVariables in
        List.iter (fun (v: variable_t) ->
            let abtype = (varObserver v)#toOrderedSymbolicConstant in
            if abtype#isTop then
              ()
            else
              match abtype#getCst with
              | ORDERED_SYM_CST s ->
                 H.add tconstraints k (v, (btype_concretize))
              (* finfo#ftinv#add_var_fact k v (btype_concretize s) *)
              | _ -> ()) vars) invariants

     
