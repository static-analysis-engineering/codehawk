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

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open XprTypes
open XprToPretty

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty

(* cchpre *)
open CCHMemoryBase
open CCHPOPredicate
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class allocation_base_checker_t
        (poq: po_query_int) (e: exp) (invs: invariant_int list) =
object (self)

  method private memref_to_string (memref: memory_reference_int) =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  method private get_allocation_base (invindex: int) (x: xpr_t) =
    match x with
    | XVar v when poq#env#is_function_return_value v ->
       let callee = poq#env#get_callvar_callee v in
       let (pcs,_) = poq#get_postconditions v in
       let _ = poq#set_diagnostic ("return value from " ^ callee.vname) in
       begin
         match pcs with
         | [] ->
            let pc = XAllocationBase ReturnValue in
            begin
              poq#mk_postcondition_request pc callee;
              None
            end
         | _ ->
            List.fold_left (fun acc (pc,_) ->
                match acc with
                | Some _  -> acc
                | _ ->
                   match pc with
                   | XAllocationBase ReturnValue ->
                      let deps =
                        DEnvC ([invindex], [PostAssumption (callee.vid, pc)]) in
                      let msg =
                        "return value from: "
                        ^ callee.vname
                        ^ " is the base of allocated memory" in
                      Some (deps, msg)
                   | _ -> None) None pcs
       end
    | _ -> None

  method private is_heap_memory =
    match invs with
    | [] -> None
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv#expr with
              | Some (XVar v) when poq#env#is_function_return_value v ->
                 let callee = poq#env#get_callvar_callee v in
                 let (pcs, _) = poq#get_postconditions v in
                 let mk_request () =
                   let pc = XHeapAddress ReturnValue in
                   begin
                     poq#mk_postcondition_request pc callee;
                     None
                   end in
                 begin
                   match pcs with
                   | [] -> mk_request ()
                   | _ ->
                      match
                        (List.fold_left (fun facc (pc, _) ->
                             match facc with
                             | Some _ -> facc
                             | _ ->
                                match pc with
                                | XHeapAddress ReturnValue ->
                                   let deps =
                                     DEnvC
                                       ([inv#index],
                                        [PostAssumption (callee.vid,pc)]) in
                                   let msg =
                                     "return value from: "
                                     ^ callee.vname
                                     ^ " is heap-allocated" in
                                   Some  (deps, msg)
                                | _ -> None) acc pcs) with
                      | Some r -> Some r
                      | _ -> mk_request ()
                end
              | _ -> None) None invs

  method private memref_is_stack_memory
                   (invindex: int) (memref: memory_reference_int) =
    let _ =
      poq#set_diagnostic_arg
        1  ("memory address: " ^ (self#memref_to_string memref)) in
    match memref#get_base with
    | CStackAddress stackvar ->
       let (vinfo, _) = poq#env#get_local_variable stackvar in
       let deps = DLocal [invindex] in
       let msg = "address of stack variable: " ^ vinfo.vname in
       Some (deps,msg)
    | CBaseVar v -> self#var_is_stack_memory invindex v
    | _ -> None

  method private var_is_stack_memory (invindex: int) (v: variable_t) =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,_) = poq#get_postconditions v in
      List.fold_left (fun facc (pc,_) ->
          match facc with
          | Some _ -> facc
          | _ ->
             match pc with
             | XStackAddress ReturnValue ->
                let deps = DEnvC ([invindex], [PostAssumption (callee.vid,pc)]) in
                let msg =
                  "return value from: " ^ callee.vname ^ " is stack-allocated" in
                Some (deps, msg)
             | _ -> None) None pcs
    else if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      self#memref_is_stack_memory invindex memref
    else
      None

  method private xpr_is_stack_memory (invindex: int) (x: xpr_t) =
    match x with
    | XVar v  -> self#var_is_stack_memory invindex v
    | _ -> None

  method private is_stack_memory =
    match invs with
    | [] -> None
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv#expr with
              | Some x -> self#xpr_is_stack_memory inv#index x
              | _ -> None) None invs

  method private is_stack_address =
    match invs with
    | [] -> None
    |  _ ->
        List.fold_left (fun acc inv ->
            match acc with
            | Some _ -> acc
            | _ ->
               match inv#expr with
               | Some (XVar v) when poq#env#is_memory_address v ->
                  let memref = poq#env#get_memory_reference v in
                  begin
                    match memref#get_base with
                    | CStackAddress svar ->
                       let (vinfo, _offset) = poq#env#get_local_variable svar in
                       let deps = DLocal [inv#index] in
                       let msg = "address of stack variable: " ^ vinfo.vname in
                       Some (deps, msg)
                    | _ -> None
                  end
               | _ -> None) None invs

  method private is_global_address =
    match invs with
    | [] -> None
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ -> match inv#expr with
                  | Some (XVar v) when poq#env#is_memory_address v ->
                     let memref = poq#env#get_memory_reference v in
                     begin
                       match memref#get_base with
                       | CGlobalAddress gvar ->
                          let (vinfo, _offset) = poq#env#get_global_variable gvar in
                          let deps = DLocal [inv#index] in
                          let msg = "address of global variable: " ^ vinfo.vname in
                          Some (deps, msg)
                       |  _ -> None
                     end
                  | _ ->  None) None invs

  (* ----------------------------- safe ------------------------------------- *)

  method private var_implies_safe (invindex: int) (v: variable_t) =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs, _) = poq#get_postconditions v in
      let _ = poq#set_diagnostic ("return value from " ^ callee.vname) in
      let r =
        List.fold_left (fun acc (pc, _) ->
            match acc with
            | Some  _ -> acc
            | _ ->
               match pc with
               | XAllocationBase ReturnValue ->
                  let deps =
                    DEnvC ( [invindex],[PostAssumption (callee.vid,pc)]) in
                  let msg =
                    "return value from: " ^ callee.vname ^ " can be freed" in
                  Some (deps, msg)
               | _ -> None) None pcs in
      match r with
      | Some _ -> r
      | _ ->
         let pc = XAllocationBase ReturnValue  in
         begin
           poq#mk_postcondition_request pc callee;
           None
         end
    else if poq#env#is_memory_address v then
      let (memref,offset) = poq#env#get_memory_address v in
      match offset with
      | NoOffset ->
         if memref#has_base_variable then
           self#var_implies_safe invindex memref#get_base_variable
         else
           begin
             poq#set_diagnostic_arg
               1
               ("memory address without base variable: " ^ v#getName#getBaseName);
             None
           end
      | _ ->
         begin
           poq#set_diagnostic_arg
             1
             ("address + offset: "
              ^ (p2s (offset_to_pretty offset))
              ^ " cannot be an allocation base");
           None
         end
    else
      None

  method private global_implies_safe (invindex: int) (x: xpr_t) =
    let gx = poq#get_global_expression x in
    let pred = PAllocationBase gx in
    match poq#check_implied_by_assumptions  pred with
    | Some pred ->
       let deps = DEnvC ([invindex],[GlobalApiAssumption  pred]) in
       let msg =
         "alloation-base implied by global assumption: "
         ^ (p2s (po_predicate_to_pretty pred)) in
       Some (deps,msg)
    | _ ->
       let xpred = po_predicate_to_xpredicate poq#fenv pred in
       begin
         poq#mk_global_request xpred;
         None
       end

  method private xpr_implies_safe (invindex: int) (x: xpr_t) =
    match x with
    | x when poq#is_global_expression x ->
       self#global_implies_safe invindex x
    | XVar v -> self#var_implies_safe invindex v
    | XConst (IntConst n) when n#equal numerical_zero ->
       let deps = DLocal [invindex] in
       let msg = "null pointer can be freed" in
       Some (deps, msg)
    | _ -> None

  method private inv_implies_safe (inv: invariant_int) =
    match inv#expr with
    | Some x -> self#xpr_implies_safe inv#index x
    | _ -> None

  method check_safe =
    match invs with
    | [] ->
       begin
         poq#set_diagnostic ("no invariants for " ^ (e2s e));
         false
       end
    |  _ ->
        List.fold_left (fun acc inv ->
            acc ||
              match self#inv_implies_safe inv with
              | Some (deps,msg) ->
                 begin
                   poq#record_safe_result deps msg ;
                   true
                 end
              | _ -> false) false invs

  (* ----------------------- violation -------------------------------------- *)

  method private xpr_implies_violation (_invindex: int) (x:xpr_t) =
    let _ = poq#set_diagnostic_arg 1 ("UB: " ^ (x2s x)) in
    None

  method private base_offset_implies_open_ended_violation
                   (invindex: int) (v: variable_t) =
    match self#var_implies_safe invindex v with
    | Some (_deps, msg) ->
       let deps = DLocal [invindex] in
       let msg = "possibly some offset from valid base address: " ^ msg in
       Some (deps, msg)
    | _ -> None

  method private inv_implies_violation (inv: invariant_int) =
    let r = None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#upper_bound_xpr with
         | Some x -> self#xpr_implies_violation inv#index x
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#base_offset_value with
         | Some (_,XVar v, _, None,_) ->
            self#base_offset_implies_open_ended_violation inv#index v
         | _ -> None in
    r

  method check_violation =
    match invs with
    | [] -> false
    | _ ->
       match self#is_stack_memory with
       | Some (deps, msg) ->
          begin
            poq#record_violation_result deps msg;
            true
          end
       | _ ->
          match self#is_stack_address with
            Some (deps, msg) ->
            begin
              poq#record_violation_result deps msg;
              true
            end
          | _ ->
             match self#is_global_address with
               Some (deps, msg) ->
               begin
                 poq#record_violation_result deps msg;
                 true
               end
             | _ ->
                List.fold_left (fun acc inv ->
                    acc ||
                      match self#inv_implies_violation inv with
                      | Some (deps, msg) ->
                         begin
                           poq#record_violation_result deps msg;
                           true
                         end
                      | _ -> false) false invs

  (* ----------------------- delegation ------------------------------------- *)

  method private memref_implies_delegation
                   (invindex: int) (memref: memory_reference_int) =
    match memref#get_base with
    | CBaseVar v -> self#var_implies_delegation invindex v
    | _ -> None

  method private var_implies_delegation (invindex: int) (v: variable_t) =
    if poq#is_api_expression (XVar v) then
      let a = poq#get_api_expression (XVar v) in
      let pred = PAllocationBase a in
      let deps  = DEnvC ([invindex],[ApiAssumption  pred]) in
      let msg =
        "condition "
        ^ (p2s (po_predicate_to_pretty pred))
        ^ "  delegated to api" in
      Some (deps,msg)
    else if poq#env#is_memory_address v then
      let (memref,offset) = poq#env#get_memory_address v in
      match offset with
      | NoOffset -> self#memref_implies_delegation invindex memref
      | _ ->
         begin
           poq#set_diagnostic_arg
             1
             ("warning: memory address with offset: "
              ^ (p2s (offset_to_pretty offset)));
           None
         end
    else
      None

  method private xpr_implies_delegation (invindex: int) (x: xpr_t) =
    match x with
    | XVar v -> self#var_implies_delegation invindex v
    | _ -> None

  method private inv_implies_delegation (inv: invariant_int) =
    match inv#expr with
    | Some x when poq#is_api_expression x ->
       let pred = PAllocationBase (poq#get_api_expression x) in
       let deps = DEnvC ( [inv#index], [ApiAssumption pred]) in
       let msg =
         "condition "
         ^ (p2s (po_predicate_to_pretty pred))
         ^ " delegated to api" in
       Some (deps,msg)
    | Some x -> self#xpr_implies_delegation inv#index x
    | _ -> None

  method check_delegation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_delegation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs

end


let check_allocation_base (poq:po_query_int) (e:exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new allocation_base_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation
