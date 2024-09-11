(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHPrettyUtil
   
(* xprlib *)
open XprTypes
   
(* cchlib *)
open CCHBasicTypes
open CCHFileContract
open CCHLibTypes
open CCHTypesToPretty

(* cchpre *)
open CCHMemoryBase
open CCHPOPredicate
open CCHPreTypes
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes

let p2s = pretty_to_string
let e2s e = p2s (exp_to_pretty e)

let cd = CCHDictionary.cdictionary

(* -----------------------------------------------------------------------------
 * The IH guarantees that any region pointed to by an argument is valid memory 
 * at function entry point (checked at the time of the call. Similarly any 
 * region pointed to by a return value from a callee is valid memory at the
 * point where the pointer value is received. For any other address 
 * locations received from outside the proof obligation should be delegated.
 * If the application does not contain any calls to free at all (indicated by
 * global_free) the valid-mem obligation is vacuously valid.
 * Any region pointed to can potentially be freed by any calls that are made
 * after the address is received, which is the reason for checking the effect
 * of any calls made since receiving the pointer value.
 * ----------------------------------------------------------------------------- *)

class valid_mem_checker_t
        (poq:po_query_int)
        (e:exp)
        (invs:invariant_int list)
        (callinvs:invariant_int list) =
object (self)

  val memregmgr = poq#env#get_variable_manager#memregmgr

  method global_free =
    if global_contract#is_nofree then
      let deps = DEnvC ( [], [GlobalAssumption (XPreservesAllMemory)]) in
      let msg = "application does not free any memory" in
      begin
        poq#record_safe_result deps msg;
        true
      end
    else
      false

  method private is_uninterpreted s =
    memregmgr#is_uninterpreted s#getSeqNumber

  method private is_valid s =
    (memregmgr#get_memory_region s#getSeqNumber)#is_valid

  method private plist (l:symbol_t list) =
    pretty_print_list
      l (fun s ->
        LBLOCK [STR (poq#env#get_region_name s#getSeqNumber)]) "[" "," "]"

  method private memref_to_string memref =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

                
  (* ----------------------------- safe ------------------------------------- *)

  method get_calls (v: variable_t) =
    let initsym = poq#env#get_p_entry_sym in
    let match_indicator vv =
      if poq#env#is_augmentation_variable vv then
        let indicator = poq#env#get_indicator vv in
        let vindicator = poq#get_canonical_fnvar_index v in
        vindicator = indicator
      else
        false in
    match callinvs with
    | [] ->
       begin
         poq#set_diagnostic "no call-record invariants found";
         None
       end
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv#get_fact with
              | NonRelationalFact (vv, FInitializedSet l)
                   when v#equal vv || (match_indicator vv) ->
                 begin
                   match l with
                   | [] ->
                      begin
                        poq#set_diagnostic
                          "call-record invariant has been corrupted";
                        None
                      end
                   | [s] when s#equal initsym -> Some []
                   | [s] ->
                      begin
                        poq#set_diagnostic
                          ("unexpected symbol in call-record invariant: "
                           ^ s#getBaseName);
                        None
                      end
                   | l when List.exists (fun s -> s#equal initsym) l ->
                      Some (List.filter (fun s -> not (s#equal initsym)) l)
                   | _ -> None
                 end
              | _ -> None) None callinvs

  method private sym_implies_safe (invindex: int) (sym: symbol_t) =
    let memreg = memregmgr#get_memory_region sym#getSeqNumber in
    self#memory_base_implies_safe invindex memreg#get_memory_base

  method private symlist_implies_safe (invindex: int) (syms: symbol_t list) =
    match syms with
    | [] -> None
    | h::tl ->
       match self#sym_implies_safe invindex h with
       | Some r ->
          List.fold_left (fun acc sym ->
              match acc with
              | None -> None
              | Some (deps,msg) ->
                 match self#sym_implies_safe invindex sym with
                 | Some (d,m) ->
                    let deps = join_dependencies deps d in
                    let msg = msg ^ "; " ^ m in
                    Some (deps, msg)
                 | _ -> None) (Some r) tl
       | _ -> None

  method private check_regions_safe inv =
    let syms = inv#get_regions in
    if List.exists self#is_uninterpreted syms then
      begin
        poq#set_diagnostic_arg
          1 ("encountered undetermined regions: " ^ (p2s (self#plist syms)));
        None
      end
    else
      let syms = poq#remove_null_syms syms in
      match syms with
      | [] ->
         begin
           poq#set_diagnostic_arg 1 ("encountered empty set of regions");
           None
         end
      | _ -> self#symlist_implies_safe inv#index syms

  method private memref_implies_safe invindex memref =
    let _ =
      poq#set_diagnostic_arg
        1 ("memory address: " ^ self#memref_to_string memref) in
    self#memory_base_implies_safe invindex memref#get_base

  method private memory_base_implies_safe
                   (invindex: int) (membase: memory_base_t) =
    let deps = DLocal [invindex]  in
    match membase with
    | CStackAddress stackvar when poq#env#is_local_variable stackvar ->
       let (vinfo, _) = poq#env#get_local_variable stackvar in
       let msg =
         "address of stack variable: " ^ vinfo.vname ^ " is valid memory" in
       Some (deps, msg)
    | CGlobalAddress gvar when poq#env#is_global_variable gvar ->
       let (vinfo,_) = poq#env#get_global_variable gvar in
       let msg  =
         "address of global variable: " ^ vinfo.vname ^ " is valid memory" in
       Some (deps,msg)
    | CStringLiteral _ ->
       let msg = "address of string literal" in
       Some (deps,msg)
    | CBaseVar  v -> self#var_implies_safe invindex v
    | _ -> None

  method private call_preserves_validity_excludes
                   (v: variable_t) (sym: symbol_t) xexps =
    let callee = poq#env#get_callsym_callee sym in
    let callcontext = poq#env#get_callsym_context sym  in
    let callloc = poq#env#get_callsym_location sym in
    if poq#env#is_fixed_value v then
      let _ =
        poq#set_diagnostic ("attempt at reducing call to " ^ callee.vname) in
      match xexps with
      | [] -> None
      | [_] ->
         begin
           poq#set_diagnostic
             ("no exclude expressions encountered for " ^ callee.vname);
           None
         end
      | _::tl ->
         let exps = List.map cd#get_exp (List.map int_of_string tl) in
         let preds = 
           List.map (fun e ->
               let pred = PDistinctRegion (e,v#getName#getSeqNumber) in
               begin
                 poq#add_local_spo callloc callcontext pred;
                 pred
               end) exps in
         let deps = DReduced ([],List.map (fun p -> LocalAssumption p) preds) in
         let msg =
           "reduced to local spos: "
           ^ (String.concat
                "; " (List.map (fun p -> p2s (po_predicate_to_pretty p)) preds)) in
         Some (deps, msg)
    else
      begin
        poq#set_diagnostic
          ("attempt at reducing " ^ callee.vname ^ " failed: "
           ^ (p2s v#toPretty) ^ " is not a fixed value");
        None
      end
    
  method private call_preserves_validity (v: variable_t) (sym: symbol_t) =
    let sideeffects = poq#get_sym_sideeffects sym in
    let callee = poq#env#get_callsym_callee sym in
    if List.exists (fun (se, _ ) ->
           match se with
           | XPreservesAllMemory -> true
           | XFunctional -> true
           | _ -> false) sideeffects then
      let deps = DEnvC ([], [PostAssumption (callee.vid, XPreservesAllMemory)]) in
      let msg = callee.vname ^ " preserves all memory" in
      Some (deps, msg)
    else if List.exists (fun (se, _) ->
                match se  with
                | XPreservesAllMemoryX _ -> true
                | _ -> false) sideeffects then
      let xexps = sym#getAttributes in
      self#call_preserves_validity_excludes v sym xexps
    else
      let pc = XPreservesAllMemory in
      begin
        poq#mk_postcondition_request pc callee;
        None
      end

  method private has_call_record callvar =
    let calls =  self#get_calls callvar in
    match calls with Some _ -> true | _ -> false

  method private validity_maintenance v callvar =
    let calls = self#get_calls callvar in
    match calls with
    | Some [] ->
       let deps = DLocal []  in
       let msg = "no calls between receiving pointer and this location" in
       Some (deps,msg)
    | Some l ->
       let pres = List.map (self#call_preserves_validity v) l in
       List.fold_left (fun acc call ->
           match acc with
           | None -> None
           | Some (deps,msg) ->
              match call with
              | Some (d,m) ->
                 let deps = join_dependencies deps d in
                 let msg = msg ^ "; " ^ m in
                 Some (deps,msg)
              | _ -> None) (List.hd pres) (List.tl pres)
    | None ->
       begin
         poq#set_diagnostic
           ("no call-record found for callvar: " ^ (p2s callvar#toPretty));
         None
       end

  method private global_implies_safe invindex g =
    let pred = PValidMem g in
    match poq#check_implied_by_assumptions pred with
    | Some pred ->
       let deps = DEnvC ([invindex],[GlobalApiAssumption pred]) in
       let msg =
         "valid memory implied by global assumption: "
         ^ (p2s (po_predicate_to_pretty pred)) in
       Some (deps,msg)
    | _ ->
       let xpred = po_predicate_to_xpredicate poq#fenv pred in
       begin
         poq#mk_global_request xpred;
         None
       end

  method private initial_value_implies_safe (invindex: int) (v: variable_t) =
    if poq#env#is_initial_parameter_value v then
      let vv = poq#env#get_initial_value_variable v in
      let deps = DLocal [invindex] in
      let msg = "initial value of argument: " ^ vv#getName#getBaseName in
      let _ =
        poq#set_diagnostic_arg 1 ("initial value of " ^ (p2s (vv#toPretty))) in
      match self#validity_maintenance v poq#env#get_fn_entry_call_var with
      | Some (d, m) ->
         let deps = join_dependencies deps d in
         let msg = msg ^ ";  " ^  m in
         Some (deps, msg)
      | _ -> None
    else if poq#is_global_expression (XVar v) then
      match self#global_implies_safe
              invindex (poq#get_global_expression (XVar v)) with
      | Some (deps,msg) ->
         begin
           match self#validity_maintenance v poq#env#get_fn_entry_call_var with
           | Some (d, m) ->
              let deps = join_dependencies deps d in
              let msg = msg ^ "; "  ^  m in
              Some (deps, msg)
           | _ -> None
         end
      | _ -> None
    else
      let vv = poq#env#get_initial_value_variable v in
      if poq#env#is_memory_variable vv then
        let (memref, offset) = poq#env#get_memory_variable vv in
        match memref#get_base with
        | CBaseVar v ->
           begin
             poq#set_diagnostic_arg
               1
               ("initial value of memory variable with base var: "
                ^ v#getName#getBaseName
                ^ " and offset: "
                ^ (p2s (offset_to_pretty offset)));
             None
           end
        | _ ->
           begin
             poq#set_diagnostic_arg
               1
               ("initial value of memory variable with base: "
                ^ (self#memref_to_string memref)
                ^ " and offset: "
                ^ (p2s (offset_to_pretty offset)));
             None
           end
      else
        None

  method private function_return_value_implies_safe
                   (_invindex: int) (v: variable_t) =
    let callee = poq#env#get_callvar_callee v in
    let _ =
      poq#set_diagnostic_arg 1 ("return value from " ^ callee.vname) in
    if self#has_call_record v then
      match self#validity_maintenance v v with
      | Some (deps,msg) ->
         let msg =
           "return value from " ^ callee.vname
           ^ " is valid by IH on receipt and validity is maintained: "
           ^ msg in
         Some (deps, msg)
      | _ -> None
    else
      match self#validity_maintenance v poq#env#get_fn_entry_call_var with
      | Some (deps,msg) ->
         let msg =
           "return value from " ^ callee.vname
           ^ " is valid by IH on receipt and validity is maintainted by all calls: "
           ^ msg  in
         Some (deps, msg)
      | _ -> None

  method private var_implies_safe (invindex: int) (v: variable_t)  =
    if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      self#memref_implies_safe invindex memref
    else if poq#env#is_function_return_value v then
      self#function_return_value_implies_safe invindex v
    else if poq#env#is_initial_value v then
      self#initial_value_implies_safe invindex v
    else
      None

  method private xpr_implies_safe (invindex: int) (x: xpr_t) =
    match x with
    | XVar v -> self#var_implies_safe invindex v
    | XConst (IntConst n) when n#equal numerical_zero ->
       let deps = DLocal [invindex] in
       let msg = "value is null pointer" in
       Some (deps,msg)
    | XOp (_, [x1; _]) ->  self#xpr_implies_safe invindex x1
    | _ -> None

  method private inv_implies_safe (inv: invariant_int) =
    let r = None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr with
         | Some x -> self#xpr_implies_safe inv#index x
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#get_fact with
         | NonRelationalFact (_, FRegionSet _) ->
            self#check_regions_safe inv
         | _ -> None in
    r
    
  method check_safe =
    self#global_free
    || (match invs with
        | [] -> false
        | _  ->
           (List.fold_left (fun acc inv ->
                acc ||
                  match self#inv_implies_safe inv with
                  | Some (deps,msg) ->
                     begin
                       poq#record_safe_result deps msg;
                       true
                     end
                  | _ -> false) false invs)
           || (match e with
               | CastE (_, StartOf (Mem e,_)) ->
                  let einvs = poq#get_exp_invariants e in
                  let _ =
                    List.iter (fun inv ->
                        poq#set_diagnostic
                          ("["
                           ^ (e2s e)
                           ^ "]: "
                           ^ (p2s (inv#value_to_pretty)))) einvs in
                  List.fold_left (fun acc einv ->
                      acc ||
                        match self#inv_implies_safe einv with
                        | Some (deps,msg) ->
                           begin
                             poq#record_safe_result deps msg;
                             true
                           end
                        | _ -> false) false einvs
               | _ -> false))
    
  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)

  method private initial_value_implies_delegation (invindex: int) (v: variable_t) =
    let vi = poq#env#get_initial_value_variable v in
    if poq#env#is_memory_variable vi then
      let (memref, offset) = poq#env#get_memory_variable vi in
      match memref#get_base with
      | CBaseVar bv when poq#is_api_expression (XVar bv) ->
         let a = poq#get_api_expression (XVar bv) in
         let pred = PValidMem (Lval (Mem a, offset)) in
         let deps = DEnvC ([invindex], [ApiAssumption pred]) in
         let msg =
           "condition "
           ^ (p2s (po_predicate_to_pretty pred))
           ^ " is delegated to the api" in
         Some (deps, msg)
      | _ -> None
    else
      None

  method private var_implies_delegation (invindex: int) (v: variable_t) =
    if poq#env#is_initial_value v then
      self#initial_value_implies_delegation invindex v
    else
      None

  method private xpr_implies_delegation (invindex: int) (x: xpr_t) =
    match x with
    | XVar v -> self#var_implies_delegation invindex v
    | _ -> None

  method private inv_implies_delegation (inv: invariant_int) =
    let r = None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr with
         | Some x -> self#xpr_implies_delegation inv#index x
         | _ -> None in
    r
    
  method check_delegation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_delegation inv with
             | Some (deps, msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs
                  
             
end


let check_valid_mem (poq:po_query_int) (e:exp) =
  let invs = poq#get_invariants 1 in
  let callinvs = poq#get_call_invariants in
  let _ = poq#set_diagnostic_invariants 1 in
  let _ = poq#set_diagnostic_call_invariants in
  let checker = new valid_mem_checker_t poq e invs callinvs in
  checker#check_safe || checker#check_violation || checker#check_delegation
