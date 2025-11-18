(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023-2024 Aarno Labs LLC

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
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHExternalPredicate
open CCHFileContract
open CCHFileEnvironment
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHCheckValid
open CCHInvariantFact
open CCHPOPredicate
open CCHPreTypes
open CCHProofObligation
open CCHProofScaffolding

(* cchanalyze *)
open CCHAnalysisTypes
open CCHCheckImplication
open CCHExpTranslator
open CCHOrakel

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class po_query_t
        (env:c_environment_int)
        (fApi:function_api_int)
        (invio:invariant_io_int)
        (po:proof_obligation_int):po_query_int =
object (self)

  val fenv = env#get_fdecls
  val fname = env#get_functionname
  val context = po#get_context
  val cfgcontext = po#get_context#project_on_cfg
  val xd = env#get_xpr_dictionary
  val callsitemgr =
    (proof_scaffolding#get_spo_manager env#get_functionname )#get_callsite_manager
  val numexp_translator =
    get_num_exp_translator env (get_function_orakel env invio)

  method env: c_environment_int = env

  method fenv: cfundeclarations_int = fenv

  method fname: string = fname

  method get_proof_obligation: proof_obligation_int = po

  method get_api_assumptions: api_assumption_int list =
    fApi#get_api_assumptions

  method private get_ppos_spos: (int list * int list) =
    if po#is_ppo then ([po#index], []) else ([], [po#index])

  method get_function_library_calls: (string * string) list =
    fApi#get_library_calls

  method get_function_direct_callsites: direct_callsite_int list =
    callsitemgr#get_direct_callsites

  method get_function_indirect_callsites: indirect_callsite_int list =
    callsitemgr#get_indirect_callsites

  method get_external_value (e: exp): xpr_t =
    numexp_translator#translate_exp context e

  method get_summary (fname:string): function_summary_t option =
    if file_environment#has_external_header fname then
      let header = file_environment#get_external_header fname in
      if function_summary_library#has_summary header fname then
        Some (function_summary_library#get_summary fname)
      else
        None
    else if function_summary_library#has_builtin_summary fname then
      Some (function_summary_library#get_summary fname)
    else
      None

  method get_postconditions (v:variable_t)
         :(annotated_xpredicate_t list * annotated_xpredicate_t list) =
    self#get_sym_postconditions v#getName

  method get_sym_postconditions (s:symbol_t)
         :(annotated_xpredicate_t list * annotated_xpredicate_t list) =
    if self#env#is_function_return_value_sym s then
      let callee = self#env#get_callsym_callee s in
      match self#get_summary callee.vname with
      | Some fs -> (fs.fs_postconditions, fs.fs_error_postconditions)
      | _ ->
         if file_contract#has_function_contract callee.vname then
           let pcs =
             (file_contract#get_function_contract callee.vname)#get_postconditions in
           let pcs = List.map (fun pc -> (pc, NoAnnotation)) pcs in
           (pcs, [])
         else
           let callcontext = env#get_callsym_context s in
           if proof_scaffolding#has_direct_callsite fname callcontext then
             let directcallsite =
               proof_scaffolding#get_direct_callsite fname callcontext in
             (directcallsite#get_postassumes, [])
           else if proof_scaffolding#has_indirect_callsite fname callcontext then
             let indirectcallsite =
               proof_scaffolding#get_indirect_callsite fname callcontext in
             (indirectcallsite#get_postassumes, [])
           else
             ([], [])
    else
      raise
        (CCHFailure
           (LBLOCK [
                STR "Variable ";
                s#toPretty;
                STR " is not a function return value"]))

  method get_sideeffects (v: variable_t): annotated_xpredicate_t list =
    self#get_sym_sideeffects v#getName

  method get_sym_sideeffects (s: symbol_t): annotated_xpredicate_t list =
    if self#env#is_function_sideeffect_value_sym s then
      let callee = self#env#get_callsym_callee s in
      match self#get_summary callee.vname with
      | Some fs -> fs.fs_sideeffects
      | _ ->
         if file_contract#has_function_contract callee.vname then
           let l =
             (file_contract#get_function_contract callee.vname)#get_sideeffects in
           List.map (fun x -> (x, ExternalCondition callee.vname)) l
         else
           let callcontext = env#get_callsym_context s in
           if proof_scaffolding#has_direct_callsite fname callcontext then
             let directcallsite =
               proof_scaffolding#get_direct_callsite fname callcontext in
             directcallsite#get_postassumes
           else if proof_scaffolding#has_indirect_callsite fname callcontext then
             let indirectcallsite =
               proof_scaffolding#get_indirect_callsite fname callcontext in
             indirectcallsite#get_postassumes
           else
             []
    else
      raise
        (CCHFailure
           (LBLOCK [
                STR "Variable ";
                s#toPretty;
                STR " is not a function side effect value"]))

  method get_tainted_value_origin (v: variable_t): string * varinfo * xpredicate_t =
    if self#env#is_tainted_value v then
      let origin = self#env#get_tainted_value_origin v in
      let callee = self#env#get_callvar_callee origin in
      if self#env#is_function_return_value origin then
        let s = "return value from "  ^ callee.vname ^ " may be tainted: " in
        let (pcs, epcs) = self#get_postconditions origin in
        let r =
          List.fold_left (fun acc (pc, _) ->
              match acc with
              | Some  _ -> acc
              | _ ->
                 match pc with
                 | XTainted _ ->  Some pc
                 | _ -> None) None (pcs @ epcs) in
        match r with
        | Some pc -> (s, callee, pc)
        | _ ->
           raise
             (CCHFailure
                (LBLOCK [
                     STR "No taint postcondition found for: ";
                     STR callee.vname]))
      else
        let s = "side-effect value from " ^ callee.vname ^ " may be tainted: " in
        let sideeffects = self#get_sideeffects origin in
        let r =
          List.fold_left (fun acc (pc, _) ->
              match acc with
              | Some _ -> acc
              | _ ->
                 match pc with
                 | XFormattedInput _
                   | XTainted _ -> Some pc
                 | _ -> None) None sideeffects in
        match r with
        | Some pc -> (s, callee, pc)
        | _ ->
           raise
             (CCHFailure
                (LBLOCK [
                     STR "No taint side effect found for: ";
                     STR callee.vname]))
    else
      raise
        (CCHFailure
             (LBLOCK [STR "Variable is not a tainted value: "; v#toPretty]))

  method get_witness (c:xpr_t) (tvar:variable_t) =
    let logmsg c s  b =
      begin
        chlog#add
          "value constraint witness"
          (LBLOCK [
               STR "constraint: ";
               x2p c;
               STR "; simplified: ";
               x2p s;
               STR "; var: " ;
               tvar#toPretty;
               STR "; bound: ";
               x2p b]);
        None
      end in
    let xget_witness c tvar xlb xub =
      let lsubst = fun v -> if v#equal tvar then xlb else XVar v in
      let usubst = fun v -> if v#equal tvar then xub else XVar v in
      let lc = simplify_xpr (substitute_expr lsubst c) in
      if is_true lc then
        Some xlb
      else
        let uc = simplify_xpr (substitute_expr usubst c) in
        if is_true uc then
          Some xub
        else
          logmsg c lc xlb  in
    if self#env#is_tainted_value tvar then
      match self#env#get_tainted_value_bounds tvar with
      | (Some xlb, Some xub) ->
         xget_witness c tvar xlb xub
      | _ -> None
    else
      None

  method private record_proof_result
                   ?(site: (string * int * string) option = None)
                   (status:po_status_t)
                   (deps:dependencies_t)
                   (expl:string) =
    begin
      po#set_status status;
      po#set_dependencies deps;
      po#set_explanation ~site expl;
      po#set_resolution_timestamp (current_time_to_string ())
    end

  method set_diagnostic
           ?(site: (string * int * string) option = None)
           (msg: string) =
    po#add_diagnostic_msg ~site msg

  method set_key_diagnostic
           ?(site: (string * int * string) option = None)
           (key: string)
           (msg: string) =
    po#add_diagnostic_key_msg ~site key msg

  method set_ref_diagnostic
           ?(site: (string * int * string) option = None) (fname: string) =
    match self#get_summary fname with
    | Some s ->
       begin
         match s.fs_domainref with
         | Some (ref, desc) ->
            po#add_diagnostic_key_msg ~site ("DomainRef:" ^ ref ^ ":" ^ fname) desc
         | _ -> ()
       end
    | _ -> ()

  method set_diagnostic_arg
           ?(site: (string * int * string) option = None)
           (index: int)
           (txt: string) =
    let txt = "[" ^ (string_of_int) index ^ "]:" ^ txt in
    po#add_diagnostic_arg_msg ~site index txt

  method set_exp_diagnostic
           ?(site: (string * int * string) option = None)
           ?(lb=false)
           ?(ub=false)
           (e:exp)
           (s:string) =
    match e with
    | Const (CInt _) -> ()
    | _ ->
       let prefix =
         if lb then "lb-exp" else if ub then "ub-exp" else "exp" in
       self#set_diagnostic ~site ("[" ^ prefix ^  ":" ^ (e2s e) ^ "]: " ^ s)

  method set_diagnostic_invariants (index:int) =
    let invs = List.map (fun inv -> inv#index) (self#get_invariants index) in
    match invs with
    | [] -> ()
    | _ -> po#set_diagnostic_invariants index invs

  method set_diagnostic_call_invariants
           ?(site: (string * int * string) option = None) () =
    let callinvs = self#get_call_invariants in
    let entrysym = env#get_p_entry_sym in
    List.iter (fun inv ->
        match inv#get_fact with
        | NonRelationalFact (v,FInitializedSet l) ->
           begin
             match l with
             | [s] when s#equal entrysym ->
                self#set_diagnostic
                  ~site ("[" ^ v#getName#getBaseName ^ ":calls]:none")
              | _ ->
                 let lst =
                   List.fold_left (fun acc s ->
                       if s#equal entrysym then
                         acc
                       else
                         acc ^ "; " ^ s#getBaseName) "" l in
                 self#set_diagnostic
                   ~site("[" ^ v#getName#getBaseName ^ ":calls]" ^ lst)
            end
        | _ -> ()) callinvs

  method set_all_diagnostic_invariants
           ?(site: (string * int * string) option = None) () =
    let locinv = invio#get_location_invariant cfgcontext in
    let invs = locinv#get_invariants in
    List.iter (fun inv -> po#add_diagnostic_msg ~site (p2s (inv#toPretty))) invs

  method get_init_vinfo_mem_invariants
           (vinfo: varinfo) (offset: offset): invariant_int list =
    let numv = self#env#mk_program_var vinfo NoOffset NUM_VAR_TYPE in
    let ctxtinvs = (invio#get_location_invariant cfgcontext)#get_invariants in
    List.fold_left (fun acc inv ->
        match inv#get_fact with
        | NonRelationalFact (v, _) ->
           if self#env#is_memory_variable v then
             let (memref, memoffset) = self#env#get_memory_variable v in
             (match memref#get_base with
              | CBaseVar base when self#env#is_initial_parameter_value base ->
                 let basevar = self#env#get_initial_value_variable base in
                 if numv#equal basevar
                    && (offset_compare offset memoffset) = 0 then
                   inv :: acc
                 else
                   acc
              | _ -> acc)
           else
             acc
        | _ -> acc) [] ctxtinvs

  method set_init_vinfo_mem_diagnostic_invariants
           ?(site: (string * int * string) option = None)
           (vinfo: varinfo)
           (offset: offset) =
    let invs = self#get_init_vinfo_mem_invariants vinfo offset in
    List.iter (fun inv -> po#add_diagnostic_msg ~site (p2s (inv#toPretty))) invs

  method set_vinfo_diagnostic_invariants
           ?(site: (string * int * string) option = None) (vinfo:varinfo) =
    let vinfovalues = self#get_vinfo_offset_values vinfo in
    List.iter (fun (inv, offset) ->
        po#add_diagnostic_msg
          ~site
          ("["
           ^ vinfo.vname
           ^ "]: "
           ^ (p2s (offset_to_pretty offset))
           ^ ": "
           ^ (p2s (inv#value_to_pretty)))) vinfovalues

  method is_formal = fenv#is_formal

  method private record_unevaluated (x:xpr_t) =
    fApi#add_unevaluated po#get_predicate (xd#index_xpr x)

  method record_safe_result
           ?(site: (string * int * string) option = None)
           (deps: dependencies_t)
           (expl: string) =
    let _ = match deps with
      | DEnvC (_, assumptions) ->
         let (ppos, spos) = self#get_ppos_spos in
         List.iter (fun a ->
             match a with
             | LocalAssumption _pred  -> ()
             | GlobalAssumption xpred ->
                fApi#add_global_assumption ~ppos ~spos xpred
             | PostAssumption (calleevid,xpred) ->
                fApi#add_postcondition_assumption ~ppos ~spos calleevid xpred
             | ApiAssumption pred ->
                ignore (fApi#add_api_assumption ~ppos ~spos pred)
             | GlobalApiAssumption pred ->
                ignore
                  (fApi#add_api_assumption ~isglobal:true ~ppos ~spos pred)
           ) assumptions
      | _ -> () in
    self#record_proof_result ~site Green deps expl

  method record_violation_result
           ?(site: (string * int * string) option = None)
           (deps:dependencies_t)
           (expl:string) =
    self#record_proof_result ~site Red deps expl

  method delegate_to_api
           ?(site: (string * int * string) option = None)
           ?(isfile=false)
           ?(isglobal=false)
           (pred:po_predicate_t)
           (invs:int list): bool =
    let (ppos, spos) = self#get_ppos_spos in
    let apred' = fApi#add_api_assumption ~isfile ~isglobal ~ppos ~spos pred in
    match apred' with
    | Some apred ->
       let deps = DEnvC (invs, [ApiAssumption apred] ) in
       let expl =
         "condition "
         ^ (p2s (po_predicate_to_pretty apred))
         ^ " delegated to api" in
       begin
         self#record_proof_result ~site Green deps expl;
         true
       end
    | _ ->
       begin
         self#set_diagnostic
           ~site
           ("condition " ^ (p2s (po_predicate_to_pretty pred)) ^ " not delegated");
         false
       end

  method mk_global_request (p:xpredicate_t)  =
    let (ppos, spos) = self#get_ppos_spos in
    let _ = fApi#add_global_assumption_request ~ppos ~spos p in
    let expl = "submitted global request for " ^ (p2s (xpredicate_to_pretty p)) in
    self#set_diagnostic expl;

  method mk_postcondition_request (pc:xpredicate_t) (callee:varinfo) =
    let (ppos, spos) = self#get_ppos_spos in
    let _ = fApi#add_postcondition_request ~ppos ~spos callee.vid pc in
    let expl =
      "submitted postrequest for condition "
      ^ (p2s (xpredicate_to_pretty pc))
      ^ " to "
      ^ callee.vname in
    self#set_diagnostic expl

  method add_local_spo
           (loc:location) (ctxt:program_context_int) (p:po_predicate_t) =
    let spomanager = proof_scaffolding#get_spo_manager self#fname in
    spomanager#add_local_spo loc ctxt p

  method get_canonical_fnvar_index (v: variable_t): int =
    if env#is_function_sideeffect_value v || env#is_function_return_value v then
      env#get_variable_manager#get_canonical_fnvar_index v#getName#getSeqNumber
    else
      v#getName#getSeqNumber

  method get_call_invariants: invariant_int list =
    let locinvio = invio#get_location_invariant cfgcontext in
    let invs = locinvio#get_invariants in
    List.fold_left (fun acc inv ->
        match inv#get_fact with
        | NonRelationalFact (v, _) when env#is_call_var v -> inv :: acc
        | _ -> acc) [] invs

  method get_invariants (argindex: int): invariant_int list =
    let id = po#index in
    let locinvio = invio#get_location_invariant cfgcontext in
    let facts = locinvio#get_invariants in
    match facts with
    | [] ->
       begin
         self#set_diagnostic_arg
           argindex
           ("no invariant facts in proof obligation context");
         []
       end
    | _ ->
       let vars =
         List.fold_left (fun acc f ->
             match f#get_fact with
             | NonRelationalFact (v, _i) ->
                if env#check_variable_applies_to_po v ~argindex po#is_ppo id then
                  if List.exists (fun vv -> v#equal vv) acc then
                    acc
                  else
                    v :: acc
                else
                  acc
             | _ -> acc) [] facts in
       match vars with
       | [] ->
          begin
            self#set_diagnostic_arg
              argindex
              "no corresponding variables with non-relational facts";
            []
          end
       | _ ->
          let invs =
            List.fold_left (fun acc v ->
                let invs = locinvio#get_var_invariants v in
                List.fold_left (fun acc1 inv ->
                    if List.exists (fun inv' -> inv#index = inv'#index) acc1 then
                      acc1
                    else
                      inv :: acc1) acc invs) [] vars in
          match invs with
          | [] ->
             begin
               self#set_diagnostic_arg
                 argindex
                 ("none of the variables has associated invariants: "
                  ^ (p2s
                       (pretty_print_list vars (fun v -> v#toPretty) "[" "," "]")));
               []
             end
          | _ -> invs

  method get_invariants_lb (argindex: int): invariant_int list =
    List.sort (fun i1 i2 -> i1#compare_lb i2) (self#get_invariants argindex)

  method get_invariants_ub (argindex: int): invariant_int list =
    List.sort (fun i1 i2 -> i1#compare_ub i2) (self#get_invariants argindex)

  method get_pepr_bounds
           (argindex: int): (invariant_int list * xpr_t list list * xpr_t list list) =
    List.fold_left (fun (invs, lbs, ubs) i ->
        match i#pepr_lower_bound with
        | Some l -> (i::invs, l @ lbs, ubs)
        | _ ->
           match i#pepr_upper_bound with
           | Some l -> (i::invs, lbs, l@ubs)
           | _ -> (invs, lbs, ubs)) ([], [], []) (self#get_invariants argindex)

  method get_parameter_constraints: xpr_t list =
    let pcs =
      (invio#get_location_invariant cfgcontext)#get_parameter_constraints in
    List.fold_left (fun acc pc ->
        match pc#get_fact with
        | ParameterConstraint x -> x :: acc
        | _ -> acc) [] pcs

  method get_values (argindex: int): (int * non_relational_value_t) list =
    let id = po#index in
    let locinvio = invio#get_location_invariant cfgcontext in
    let facts = locinvio#get_invariants in
    let vars = List.fold_left (fun acc f ->
        match f#get_fact with
        | NonRelationalFact (v, _i) ->
           if env#check_variable_applies_to_po v ~argindex po#is_ppo id then
             if List.exists (fun vv -> v#equal vv) acc then
               acc
             else
               v :: acc
           else
             acc
        | _ -> acc) [] facts in
    let facts = List.concat (List.map locinvio#get_var_invariants vars) in
    List.fold_left (fun acc f ->
        match f#get_fact with
        | NonRelationalFact (_v, i) -> (f#index, i) :: acc
        | _ -> acc) [] facts

  method get_exp_invariants (e: exp): invariant_int list =
    match e with
    | Lval (Var (_vname, vid), NoOffset) when vid > 0 ->
       let vinfo = self#env#get_varinfo vid in
       List.fold_left (fun acc (inv, offset) ->
           match offset with
           | NoOffset -> inv :: acc
           | _ -> acc) [] (self#get_vinfo_offset_values vinfo)
    | _ -> []

  method get_exp_value (e:exp):(int list * xpr_t option) =
    match e with
    | CastE (_, e1) -> self#get_exp_value e1
    | Const (CInt (i64,_,_)) ->
       ([], Some (XConst (IntConst (mkNumericalFromInt64 i64))))
    | Lval (Var (_vname, vid), NoOffset) when vid > 0 ->
       let vinfo = self#env#get_varinfo vid in
       let invariants =
         List.fold_left (fun acc (inv,offset) ->
             match offset with
             | NoOffset -> inv :: acc
             | _ -> acc) [] (self#get_vinfo_offset_values vinfo) in
       List.fold_left (fun (invs, acc) inv ->
           match acc with
           | Some _ -> (invs, acc)
           | _ ->
              match inv#expr with
              | Some x -> (inv#index :: invs, Some x)
              | _ -> (invs, acc)) ([], None)  invariants
    | BinOp (op, e1, e2, _ty) ->
       begin
         match (self#get_exp_value e1, self#get_exp_value e2) with
         | ((invs1, Some x1), (invs2, Some x2)) ->
            let x = XOp  (binop_to_xop op, [x1; x2])  in
            let xsimplified = simplify_xpr x in
            begin
              match xsimplified with
              | XConst XRandom | XConst XUnknownInt ->
                 begin
                   self#set_exp_diagnostic e (x2s x);
                   ([],None)
                 end
              | _ ->
                 (invs1 @ invs2, Some xsimplified)
            end
         | ((_, Some x1), _) ->
            begin
              self#set_exp_diagnostic e1 (x2s x1);
              ([], None)
            end
         | (_, ([], Some x2)) ->
            begin
              self#set_exp_diagnostic e2 (x2s x2);
              ([], None)
            end
         | _ -> ([], None)
       end
    | _ -> ([], None)

  method  get_exp_upper_bound_value (e:exp):(int list * xpr_t option) =
    match self#get_exp_value e with
    | (invs, Some v) -> (invs, Some v)
    | _ ->
       match e with
       | CastE (_, e1) -> self#get_exp_upper_bound_value e1
       | Lval (Var (_vname, vid), NoOffset) when vid > 0 ->
          let vinfo = self#env#get_varinfo vid in
          let invariants =
            List.fold_left (fun acc (inv, offset) ->
                match offset with
                | NoOffset -> inv :: acc
                | _ -> acc) [] (self#get_vinfo_offset_values vinfo) in
          List.fold_left (fun (invs, acc) inv ->
              match acc with
              | Some _ -> (invs, acc)
              | _ ->
                 match inv#upper_bound_xpr with
                 | Some x -> (inv#index :: invs, Some x)
                 | _ -> (invs,acc)) ([], None) invariants
       | BinOp (MinusA, e1, (Const (CInt (i64,_,_))),_) ->
          begin
            match self#get_exp_upper_bound_value e1 with
            | (invs,Some x) ->
               let xmin =
                 XOp (XMinus, [x; num_constant_expr (mkNumericalFromInt64 i64)]) in
               let xminsimplified = simplify_xpr xmin in
               (invs,Some xminsimplified)
            | _ -> ([], None)
          end
       | BinOp (BAnd, e1, e2, _ty)
            when is_unsigned_integral_type (type_of_exp fenv e1) ->
          self#get_exp_value e2
       | BinOp (Shiftlt, e1, e2, _ty) ->
          begin
            match (self#get_exp_upper_bound_value e1,
                   self#get_exp_upper_bound_value e2) with
            | ((invs1, Some x1), (invs2, Some x2)) ->
               let x = XOp (XShiftlt, [x1; x2]) in
               let xsimplified = simplify_xpr x in
               begin
                 match xsimplified with
                 | XConst XRandom | XConst XUnknownInt ->
                    begin
                      self#set_exp_diagnostic e (x2s x);
                      ([], None)
                    end
                 | _ ->
                    (invs1 @ invs2, Some xsimplified)
               end
            | ((_,Some x1), _) ->
               begin
                 self#set_exp_diagnostic e1 (x2s x1);
                 ([], None)
               end
            | (_,(_,Some x2)) ->
               begin
                 self#set_exp_diagnostic e2 (x2s x2);
                 ([], None)
               end
            | _ -> ([], None)
          end
       | _ ->
          match get_num_range self#fenv e with
          | (_, Some ub) -> ([], Some (num_constant_expr ub))
          | _ -> ([], None)

  method get_extended_values (argindex: int) (e: exp): invariant_int list =
    let values = self#get_invariants argindex in
    match e with
    | Lval (Var (_vname, vid), NoOffset) when vid > 0  ->
       let vinfo = self#env#get_varinfo vid in
       values @
         (List.fold_left (fun acc (inv, offset) ->
              match offset with
              | NoOffset -> inv :: acc
              | _ -> acc) [] (self#get_vinfo_offset_values vinfo))
    | _ -> values

  method get_ntp_value (e:exp):(invariant_int * numerical_t) option =
    match e with
    | StartOf (Var (_vname, vid), NoOffset)
      | CastE (_, StartOf (Var (_vname,vid), NoOffset)) when vid > 0  ->
       let vinfo = self#env#get_varinfo vid in
       begin
         match vinfo.vtype with
         | TArray (_, Some (Const (CInt (_, _, _))), _) ->
            List.fold_left (fun acc (inv, offset) ->
                match acc with
                | Some _ -> acc
                | _ ->
                   match offset with
                   | Index (Const (CInt (i64, _, _)), NoOffset) ->
                      let index = mkNumericalFromInt64 i64 in
                      begin
                        match inv#expr with
                        | Some (XConst (IntConst n)) when n#equal numerical_zero ->
                           Some (inv, index)
                        | _ -> None
                      end
                   | _ -> None) None (self#get_vinfo_offset_values vinfo)
         | _ -> None
       end
    | _ -> None

  method get_function_return_value_buffer_size
           (v: variable_t): (assumption_type_t list * xpr_t) option =
    let fargs = env#get_callvar_args v in
    let callee = self#env#get_callvar_callee v in
    let (pcs, _) = self#get_postconditions v in
    List.fold_left (fun acc (pc, _) ->
        let deps = [PostAssumption (callee.vid, pc)] in
        match acc with
        | Some _ -> acc
        | _ ->
           match pc with
           | XBuffer (ReturnValue, NumConstant i) ->
              Some (deps,num_constant_expr i)
           | XBuffer (ReturnValue, ArgValue (ParFormal i, ArgNoOffset)) ->
              if (List.length fargs) >= i then
                (match List.nth fargs (i-1) with
                 | Some a -> Some (deps, a)
                 | _ -> None)
              else
                None
           | XBuffer (ReturnValue,
                      ArithmeticExpr (Mult, ArgValue (ParFormal i1, ArgNoOffset),
                                      ArgValue (ParFormal i2, ArgNoOffset))) ->
              if (List.length fargs) >= i1 && (List.length fargs) >= i2 then
                match (List.nth fargs (i1-1), List.nth fargs (i2-1)) with
                | (Some x1,Some x2) ->
                   let x = XOp (XMult, [x1; x2]) in
                   Some (deps,simplify_xpr x)
                | _ ->
                   None
              else
                None
           | _ -> None) None pcs

  method private non_relational_value_to_pretty (nrv:non_relational_value_t) =
    match nrv with
    | FRegionSet syms ->
       non_relational_value_to_pretty (FRegionSet syms)
    | _ -> non_relational_value_to_pretty nrv

  method invariants_to_pretty (values: (int * non_relational_value_t) list) =
    match values with
    | [] -> STR "none"
    | _ ->
       let values =
         List.sort (fun (_,nrv1) (_,nrv2) ->
             non_relational_value_compare nrv1 nrv2) values in
       LBLOCK
         (List.map (fun (_,nrv) ->
              LBLOCK [self#non_relational_value_to_pretty nrv; STR "; "]) values)

  method invariant_values_to_pretty (invs:invariant_int list) =
    LBLOCK
      (List.fold_left (fun acc inv ->
           match inv#get_fact with
           | NonRelationalFact (_,nrv) ->
              (self#non_relational_value_to_pretty nrv) :: (STR "; ") :: acc
           | _ -> acc) [] invs)

  method get_vinfo_offset_values (vinfo:varinfo):(invariant_int * offset) list =
    let facts = (invio#get_location_invariant cfgcontext)#get_invariants in
    List.fold_left (fun acc f ->
        match f#get_fact with
        | NonRelationalFact (v, _i) ->
           begin
             match env#get_vinfo_offset v vinfo with
             | Some offset -> (f, offset) :: acc
             | _ -> acc
           end
        | _ -> acc) [] facts

  method vinfo_values_to_pretty
           (values: (int * offset * non_relational_value_t) list) =
    match values with
    | [] -> STR "none"
    | _ ->
       LBLOCK
         (List.map (fun (_,offset,nrv) ->
              let poffset = match offset with
                | NoOffset -> STR ""
                | _ -> LBLOCK [offset_to_pretty offset; STR ": "] in
              LBLOCK [
                  poffset;
                  self#non_relational_value_to_pretty nrv;
                  STR "; "]) values)

  method remove_null_syms (syms:symbol_t list) =
    let memregmgr = env#get_variable_manager#memregmgr in
    List.filter (fun s ->
        let memreg = memregmgr#get_memory_region s#getSeqNumber in
        not memreg#is_null) syms

  method private get_exp_buffer_index_size
                   (e:exp):(string * xpr_t * xpr_t) option =
    (* return index size and offset (in terms of elements) *)
    try
      match e with
      | CastE (_, StartOf (Var (vname, vid), offset))
        | CastE (_, AddrOf (Var (vname, vid), offset))
        | StartOf (Var (vname, vid), offset)
        | AddrOf (Var (vname, vid), offset) when vid > 0 ->
         begin
           match (env#get_varinfo vid).vtype with
           | TArray (_,Some len, _) ->
              begin
                match offset with
                | NoOffset ->
                   Some (vname,self#e2x len,zero_constant_expr)
                | Index (Const (CInt (i64, _, _)), NoOffset) ->
                   let xoffset = num_constant_expr (mkNumericalFromInt64 i64) in
                   Some (vname, self#e2x len, xoffset)
                | _ -> None
              end
           | _ -> None
         end
      | _ -> None
    with
    | CCHFailure p ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Error in get_exp_buffer_index_size for ";
                 exp_to_pretty e;
                 STR ": ";
                 p]))


  method private get_return_value_buffer_size_info
                   (arg:int) (base:variable_t) (invindex:int) (incr:xpr_t) =
    let optargs_to_string args =
      String.concat
        "," (List.map (fun a -> match a with Some x -> x2s x | _ -> "_") args) in
    let callee = env#get_callvar_callee base in
    let fargs = env#get_callvar_args base in
    let _ =
      self#set_diagnostic_arg arg ("function return value: " ^ callee.vname) in
    let _ =
      self#set_diagnostic_arg
        arg ("function arguments: " ^ optargs_to_string fargs) in
    let (pcs, epcs) = self#get_postconditions base in
    match  (pcs, epcs) with
    | ([],_) ->
       begin
         self#set_diagnostic_arg arg ("no postconditions for " ^ callee.vname);
         None
       end
    | (_,_) ->      (* TBD: check that only error post is Null *)
       List.fold_left (fun accp (pc,_) ->
           match accp with
           | Some _ -> accp
           | _ ->
              match pc with
              | XBuffer (ReturnValue,ArgValue (ParFormal i, ArgNoOffset)) ->
                 let deps =
                   DEnvC ([invindex], [PostAssumption (callee.vid, pc)]) in
                 if (List.length fargs) >= i then
                   match List.nth fargs (i-1) with
                   | Some x -> Some (base#getName#getBaseName, x, incr, deps)
                   | _ -> None
                 else
                   None
              | XBuffer (ReturnValue,
                         ArithmeticExpr (Mult, ArgValue (ParFormal i1,ArgNoOffset),
                                         ArgValue (ParFormal i2,ArgNoOffset))) ->
                 let deps =
                   DEnvC ([invindex], [PostAssumption (callee.vid, pc)]) in
                 if (List.length fargs) >= i1  &&  (List.length fargs) >= i2 then
                   match (List.nth fargs (i1-1), List.nth fargs (i2-1)) with
                   | (Some x1,Some x2) ->
                      let x =  XOp  (XMult, [x1; x2]) in
                      Some (base#getName#getBaseName, simplify_xpr x, incr, deps)
                   | _ -> None
                 else
                   None
              | XBuffer (ReturnValue, NumConstant n) ->
                 let deps =
                   DEnvC ([invindex], [PostAssumption (callee.vid, pc)]) in
                 Some (base#getName#getBaseName, num_constant_expr n, incr,deps)
              | _ -> None) None pcs

  method private get_memaddress_buffer_byte_size_info
                   (arg: int)
                   (base: variable_t)
                   (invindex: int)
                   (incr: xpr_t): (string * xpr_t * xpr_t * dependencies_t) option =
    let memref = env#get_memory_reference base in
    let _ =
      self#set_diagnostic_arg
        arg ("memory address: " ^ base#getName#getBaseName) in
    match memref#get_base with
    | CStackAddress stackvar when env#is_local_variable stackvar ->
       let (vinfo,offset) = env#get_local_variable stackvar in
       begin
         match (vinfo.vtype, offset) with
         | (TArray (t,Some len, _), NoOffset) ->
            let _ =
              self#set_diagnostic_arg
                arg
                ("array variable "
                 ^ vinfo.vname
                 ^ " with size "
                 ^ (x2s (self#e2x len))) in
            let xsize = XOp (XMult, [self#e2x len; size_of_type fenv t]) in
            let _ =
              self#set_diagnostic_arg
                arg
                ("stack variable "
                 ^ vinfo.vname
                 ^ "; size (in bytes): "
                 ^ (x2s xsize)
                 ^ " and offset "
                 ^ (x2s incr)) in
            let deps = DLocal [invindex] in
            Some (vinfo.vname, xsize, incr, deps)
         | (ty,NoOffset) ->
            let tsize = size_of_type fenv ty in
            let _ =
              self#set_diagnostic_arg
                arg
                ("stack variable with type: "
                 ^ (p2s (typ_to_pretty ty))
                 ^ " and size: "
                 ^ (x2s tsize)) in
            let deps = DLocal [invindex] in
            Some (vinfo.vname, tsize, zero_constant_expr, deps)
         | (ty, _) ->
            let _ =
              self#set_diagnostic_arg
                arg
                ("stack variable with type: "
                 ^ (p2s (typ_to_pretty ty))
                 ^ " and offset: "
                 ^ (p2s (offset_to_pretty offset))) in
            None
       end
    | CBaseVar v ->
       begin
         self#set_diagnostic_arg arg ("basevar: " ^ v#getName#getBaseName);
         self#xpr_buffer_offset_size arg invindex (XVar v)
       end
    | CGlobalAddress v ->
       begin
         self#set_diagnostic_arg arg ("global var: " ^ v#getName#getBaseName);
         None
       end
    | _ -> None

  method xpr_buffer_offset_size
           (arg: int)
           (invindex: int)
           (x: xpr_t): (string * xpr_t * xpr_t * dependencies_t) option =
    match x with
    | XVar base when env#is_memory_address base ->
       self#get_memaddress_buffer_byte_size_info
         arg base invindex zero_constant_expr
    | XVar v when env#is_function_return_value v ->
       self#get_return_value_buffer_size_info arg v invindex zero_constant_expr
    | XVar v when self#env#is_initial_global_value v ->
       let gvar = self#env#get_initial_value_variable v in
       self#get_global_variable_buffer invindex gvar
    | XOp (XPlus, [XVar base; incr]) when env#is_memory_address base ->
       self#get_memaddress_buffer_byte_size_info arg base invindex incr
    | _ -> None

  method private get_min_size x1 x2 =
    match (x1,x2) with
    | (XConst (IntConst n1), XConst (IntConst n2)) ->
       if n1#lt n2 then Some x1 else Some x2
    | _ -> None

  method private get_max_size x1 x2 =
    match (x1,x2) with
    | (XConst (IntConst n1), XConst (IntConst n2)) ->
       if n1#gt n2 then Some x1 else Some x2
    | _ -> None

  method private xprlist_buffer_offset_size
                   (arg:int) (invindex:int) (xlst:xpr_t list) =
    match xlst with
    | [] -> None
    | h::tl ->
       match self#xpr_buffer_offset_size arg invindex h with
       | None -> None
       | Some r ->
          List.fold_left (fun acc x ->
              match acc with
              | None -> None
              | Some (aname,asize,aoffset,adeps) ->
                 match self#xpr_buffer_offset_size arg invindex x with
                 | Some (name,xsize,xoffset,deps) ->
                    let name = aname ^ "; " ^ name in
                    let xsize = self#get_min_size asize xsize in
                    let xoffset = self#get_max_size aoffset xoffset in
                    let deps = join_dependencies adeps deps in
                    begin
                      match (xsize,xoffset) with
                      | (Some xsize, Some xoffset) ->
                         Some (name,xsize,xoffset,deps)
                      | _ -> None
                    end
                 | _ -> None) (Some r) tl

  (* returns a conservative value of the remaining size in the buffer, that is,
   * a lower bound on the buffer size and an upper bound on the offset *)
  method get_buffer_offset_size
           (arg:int)
           (typ:typ)
           (e:exp):(string * xpr_t * xpr_t * dependencies_t) option =
    let invs = self#get_invariants arg in
    match self#get_exp_buffer_index_size e with
    | Some (name,indexsize,indexoffset) ->
       let typesize = size_of_type fenv typ in
       let bytesize = simplify_xpr (XOp (XMult, [indexsize; typesize])) in
       let byteoffset = simplify_xpr (XOp (XMult, [indexoffset; typesize])) in
       let deps = DLocal [] in
       Some (name,bytesize,byteoffset,deps)
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv#base_offset_value with
              | Some (_,XVar base,_,Some ub,_)
                   when env#is_function_return_value base ->
                 begin
                   match self#get_return_value_buffer_size_info
                           arg base inv#index (num_constant_expr ub) with
                   | Some r -> Some r
                   | _ ->
                      match inv#upper_bound_xpr with
                      | Some x ->
                         begin
                           match self#xpr_buffer_offset_size arg inv#index x with
                           | Some r -> Some r
                           | _ ->
                              match inv#upper_bound_xpr_alternatives with
                              | None | Some [] -> None
                              | Some l ->
                                 self#xprlist_buffer_offset_size arg inv#index l
                         end
                      | _ ->
                         match inv#upper_bound_xpr_alternatives with
                         | None | Some [] -> None
                         | Some l ->
                            self#xprlist_buffer_offset_size arg inv#index l
                 end
              | _ ->
                 match inv#upper_bound_xpr with
                 | Some x ->
                    begin
                      match self#xpr_buffer_offset_size arg inv#index x with
                      | Some r -> Some r
                      | _ ->
                         match inv#upper_bound_xpr_alternatives with
                         | None | Some [] -> None
                         | Some l ->
                            self#xprlist_buffer_offset_size arg inv#index l
                    end
                 | _ ->
                    match inv#upper_bound_xpr_alternatives with
                    | None | Some [] -> None
                    | Some l ->
                       self#xprlist_buffer_offset_size arg inv#index l) None invs

  method x2global (x:xpr_t):exp option =
    match x with
    | XConst (IntConst n) -> Some (make_constant_exp n)
    | XVar v when env#is_initial_global_value v ->
       (try Some (env#get_global_exp v) with
        | CCHFailure p ->
           begin
             chlog#add
               "global expression"
               (LBLOCK [STR env#get_functionname; STR ": "; p]);
             self#record_unevaluated x;
             None
           end)
    | XOp (op, [x1; x2]) ->
       begin
         match (self#x2global x1, self#x2global x2) with
         | (Some a1,Some a2) ->
            let ty = type_of_exp fenv a1 in
            begin
              match op with
              | XPlus -> Some (BinOp (PlusA, a1, a2, ty))
              | XMinus -> Some (BinOp (MinusA, a1, a2, ty))
              | XMult -> Some (BinOp (Mult, a1, a2, ty))
              | _ -> None
            end
         | _ -> None
       end
    | _ ->
       begin
         self#record_unevaluated x;
         None
       end

  method x2api (x:xpr_t):exp option =
    match x with
    | XConst (IntConst n) -> Some (make_constant_exp n)
    | XVar v
         when env#is_initial_parameter_value v
              || env#is_initial_parameter_deref_value v ->
       (try Some (env#get_parameter_exp v) with
        | CCHFailure p ->
           begin
             chlog#add
               "api expression"
               (LBLOCK [STR env#get_functionname; STR ": "; p]);
             self#record_unevaluated x;
             None
           end)
    | XOp (op, [x1; x2]) ->
       begin
         match (self#x2api x1, self#x2api x2) with
         | (Some a1, Some a2) ->
            let ty1 = type_of_exp fenv a1 in
            let ty2 = type_of_exp fenv a2 in
            begin
              try
                begin
                  match op with
                  | XPlus ->
                     Some (BinOp (PlusA, a1, a2, get_integer_promotion ty1 ty2))
                  | XMinus ->
                     Some (BinOp (MinusA, a1, a2, get_integer_promotion ty1 ty2))
                  | XMult ->
                     Some (BinOp (Mult, a1, a2, get_integer_promotion ty1 ty2))
                  | XDiv ->
                     Some (BinOp (Div, a1, a2, get_integer_promotion ty1 ty2))
                  | XShiftrt -> Some (BinOp (Shiftrt, a1, a2, ty1))
                  | XShiftlt -> Some (BinOp (Shiftlt, a1, a2, ty1))
                  | XLt -> Some (BinOp (Lt, a1, a2, TInt (IBool,[])))
                  | XLe -> Some (BinOp (Le, a1, a2, TInt (IBool,[])))
                  | XGt -> Some (BinOp (Gt, a1, a2, TInt (IBool,[])))
                  | XGe -> Some (BinOp (Ge, a1, a2, TInt (IBool,[])))
                  | _ -> None
                end
              with
              | CCHFailure p ->
                 begin
                   ch_error_log#add
                     "integer promotion"
                     (LBLOCK [
                          STR self#env#get_functionname;
                          STR ": ";
                          typ_to_pretty ty1;
                          STR ", ";
                          typ_to_pretty ty2;
                          STR ": ";
                          p]);
                   None
                 end
              | _ -> None
            end
         | _ -> None
       end
    | _ -> None

  method private x2functionreturn (x:xpr_t):varinfo option =
    match x with
    | XVar v when env#is_function_return_value v ->
       Some (env#get_callvar_callee v)
    | _ -> None

  method e2x (e:exp):xpr_t =
    match get_num_value fenv e with
    | Some i -> num_constant_expr i
    | _ ->
       let _ =
         chlog#add
           "e2x failed"
           (LBLOCK [
                STR fname;
                STR ": ";
                INT po#index;
                STR " -- ";
                exp_to_pretty e]) in
       random_constant_expr

  method is_memory_base_address (base:variable_t) =
    if env#is_function_return_value base then
      let callee = env#get_callvar_callee base in
      match self#get_summary callee.vname with
      | Some fs ->
         List.fold_left (fun accp (post,_) ->
             match accp with
             | Some _ -> accp
             | _ ->
                match post with
                | XNewMemory _ -> Some base#getName#getBaseName
                | _ -> None) None fs.fs_postconditions
      | _ ->
         begin
           chlog#add "no summary" (STR callee.vname);
           None
         end
    else if env#is_memory_address base then
      let memref = env#get_memory_reference base in
      match memref#get_base with
      | CStackAddress stackvar when env#is_local_variable stackvar ->
         let (vinfo, offset) = env#get_local_variable stackvar in
         (match offset with
          | NoOffset -> Some ("stackvar:" ^ vinfo.vname)
          | _ -> None)
      | _ ->
         begin
           chlog#add "memory address - non stack" (STR base#getName#getBaseName);
           None
         end
    else
      begin
        chlog#add "not a memory address" (STR base#getName#getBaseName);
        None
      end

  method is_global_expression (x:xpr_t) =
    match simplify_xpr x with
    | XConst _ -> false
    | _ ->
       match self#x2global x with
       | Some _ -> true
       | _ -> false

  method get_global_expression (x:xpr_t) =
    match self#x2global x with
    | Some e -> e
    | _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Expression ";
                 x2p x;
                 STR " cannot be converted to a global expression"]))

  method is_api_expression (x:xpr_t) =
    match simplify_xpr x with
    | XConst _ -> false
    | XOp (_, [XConst _; XConst _]) -> false
    | _ ->
       match self#x2api x with
       | Some _ -> true
       | _ -> false

  method get_api_expression (x:xpr_t) =
    match self#x2api x with
    | Some e -> e
    | _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Expression ";
                 x2p x;
                 STR " cannot be converted to an api expression"]))

  method is_function_return (x:xpr_t) =
    match self#x2functionreturn x with Some _ -> true | _ -> false

  method get_function_return_callee (x:xpr_t) =
    match self#x2functionreturn x with
    | Some e -> e
    | _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Expression ";
                 x2p x;
                 STR " cannot be converted to a post expression"]))

  method get_num_value (e:exp): numerical_t option = get_num_value fenv e

  method get_gv_lowerbound (name:string):int option =
    if file_contract#has_globalvar_contract name then
      let gvar = file_contract#get_globalvar_contract name in
      gvar#get_lower_bound
    else
      None

  method get_gv_upperbound (name:string):int option =
    if file_contract#has_globalvar_contract name then
      let gvar = file_contract#get_globalvar_contract name in
      gvar#get_upper_bound
    else
      None

  (* return a lower bound xpr *)
  method get_lowerbound_xpr (arg:int) (e:exp):(xpr_t * int list) option =
    match get_num_value fenv e with
    | Some i -> Some (num_constant_expr i,[])
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv#lower_bound_xpr with
              | Some lb -> Some (lb,[inv#index])
              | _ -> None) None (self#get_invariants_lb arg)

  (* return an upper bound xpr *)
  method get_upperbound_xpr (arg:int) (e:exp):(xpr_t * int list) option =
    match get_num_value fenv e with
    | Some i -> Some (num_constant_expr i,[])
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv#upper_bound_xpr with
              | Some ub -> Some (ub,[inv#index])
              | _ -> None) None (self#get_invariants_ub arg)

  (* return an external lower bound exp that can be delegated *)
  method get_elb (e:exp) (v:non_relational_value_t):exp option =
    try
      match get_num_value fenv e with
      | Some i -> Some (make_constant_exp i)
      | _ ->
         match v with
         | FSymbolicExpr x -> self#x2api x
         | FIntervalValue (Some lb, _) -> Some (make_constant_exp lb)
         | _ -> None
    with
    | Failure _ -> None

  method get_eub (e:exp) (v:non_relational_value_t):exp option =
    try
      match get_num_value fenv e with
      | Some i -> Some (make_constant_exp i)
      | _ ->
         match v with
         | FSymbolicExpr x -> self#x2api x
         | FIntervalValue (_, Some ub) -> Some (make_constant_exp ub)
         | _ -> None
    with
    | Failure _ -> None

  method get_evb (e:exp) (v:non_relational_value_t):exp option =
    try
      match get_num_value fenv e with
      | Some i -> Some (make_constant_exp i)
      | _ ->
         match v with
         | FSymbolicExpr x -> self#x2api x
         | FIntervalValue (Some lb, Some ub) when lb#equal ub ->
            Some (make_constant_exp lb)
         | _ -> None
    with
    | Failure _ -> None

  method is_command_line_argument (e:exp) =
    fname = "main" &&
      match e with
      | CastE (_,ee) -> self#is_command_line_argument ee
      | Lval (Mem (BinOp
                     ((PlusPI | IndexPI),
                      Lval (Var (_, vid), NoOffset),
                      Const (CInt (_i64, _, _)), _)),
              NoOffset) when vid > 0  ->
         fenv#is_formal vid && (self#env#get_varinfo vid).vparam = 2
      | _ -> false

  method get_command_line_argument_index (e:exp) =
    if self#is_command_line_argument e then
      match e with
      | CastE (_, ee) -> self#get_command_line_argument_index ee
      | Lval (Mem (BinOp
                     ((PlusPI | IndexPI),
                      Lval (Var (_, _vid), NoOffset),
                      Const (CInt (i64, _, _)), _)), NoOffset) ->
         Int64.to_int i64
      | _ ->
         raise
           (CCHFailure
              (LBLOCK [STR "Internal error in get_command_line_argument_index"]))
    else
      raise
        (CCHFailure
           (LBLOCK [
                STR "expression ";
                exp_to_pretty e;
                STR " is not a command-line argument"]))

  method get_command_line_argument_count: (int * int) option =
    if fname = "main" then
      let locinvio = invio#get_location_invariant cfgcontext in
      let argc = fenv#get_formal 1 in
      let argcvar = self#env#mk_program_var argc NoOffset NUM_VAR_TYPE in
      let facts = List.concat (List.map locinvio#get_var_invariants [argcvar]) in
      let facts =
        List.fold_left (fun acc f ->
            match f#get_fact with
            | NonRelationalFact (_v, i) -> (f#index, i) :: acc
            | _ -> acc) [] facts in
      List.fold_left (fun acc (inv, i) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match i with
             | FIntervalValue (Some lb, Some ub) when lb#equal ub ->
                begin
                  try
                    Some (inv,lb#toInt)
                  with
                    _ ->
                    begin
                      chlog#add
                        "large value"
                        (LBLOCK [STR self#fname; STR ": "; lb#toPretty]);
                      None
                    end
                end
             | _ -> acc) None facts
    else
      None

  method check_command_line_argument
           (e:exp)
           (safemsg:int -> int -> string)
           (vmsg:int -> int -> string)
           (dmsg:int -> string): bool =
    if self#is_command_line_argument e then
      let index = self#get_command_line_argument_index e in
      match self#get_command_line_argument_count with
      | Some (inv, i) ->
         if index < i then
           begin
             self#record_safe_result (DLocal [inv]) (safemsg index i);
             true
           end
         else
           begin
             self#record_violation_result (DLocal [inv]) (vmsg index i);
             true
           end
      | _ ->
         begin
           self#set_diagnostic (dmsg index);
           false
         end
    else
      false

  method check_implied_by_assumptions (p:po_predicate_t) =
    let assumptions =
      List.map (fun a -> a#get_predicate) self#get_api_assumptions in
    check_implied_by_assumptions env assumptions p

  method private get_global_variable_buffer invindex (v:variable_t) =
    if self#env#is_global_variable v then
      let (vinfo,offset) = self#env#get_global_variable v in
      match offset with
      | NoOffset ->
         let predicates =
           List.map (fun a -> a#get_predicate) self#get_api_assumptions in
         List.fold_left (fun acc (pred:po_predicate_t) ->
             match acc with
             | Some _ -> acc
             | _ ->
                match pred with
                | PBuffer (Lval (Var (gname, gvid), NoOffset),
                           Const (CInt (i64,_,_)))
                     when gvid = vinfo.vid ->
                   let xsize = num_constant_expr (mkNumericalFromInt64 i64) in
                   let deps = DEnvC ([invindex],[ApiAssumption pred]) in
                   Some (gname, xsize, zero_constant_expr, deps)
                | _ -> None) None predicates
      | _ -> None
    else
      None

end

let mk_poq = new po_query_t
