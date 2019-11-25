(* =============================================================================
   CodeHawk C Analyzer 
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

(* chlib *)
open CHNumerical
open CHPretty
   
(* chutil *)
open CHPrettyUtil
   
(* xprlib *)
open XprTypes
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHMemoryBase
open CCHPreTypes
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)

let max_syms = 10

let rec get_stack_address e =
  match e with
  | AddrOf (Var (vname,vid),_) 
  | StartOf (Var (vname,vid),_) -> Some (vname,vid)
  | CastE (_, ee) -> get_stack_address ee
  | _ -> None

let is_stack_address e =
  match get_stack_address e with Some _ -> true | _ -> false

let rec get_string_literal e =
  match e with
  | Const (CStr s) -> Some s
  | CastE (_, ee) -> get_string_literal ee
  | _ -> None

let is_string_literal e =
  match get_string_literal e with Some _ -> true | _ -> false

let get_string_or_stack e =
  match get_stack_address e with
  | Some (vname,_) -> "address of stack variable " ^  vname
  | _ ->
     if is_string_literal e then
       "address of string literal"
     else
       raise (CCHFailure (STR "Internal error in check-no-overlap"))

let get_heap_address (poq:po_query_int) (arg:int) (inv:invariant_int) = None

let get_api_address (poq:po_query_int) (arg:int) (inv:invariant_int) =
  match inv#expr with
  | Some x when poq#is_api_expression x ->
     let e = poq#get_api_expression x in
     Some ("function argument: " ^ (e2s e))
  | _ ->
     match inv#get_fact with
     | NonRelationalFact (_,FRegionSet _) ->
        let syms = inv#get_regions in
        let memregmgr = poq#env#get_variable_manager#memregmgr in
        let get_api_sym s =
          let memreg = memregmgr#get_memory_region s#getSeqNumber in
          match memreg#get_memory_base with
          | CBaseVar v when poq#is_api_expression (XVar v) -> Some v
          | _ -> None in
        let is_api_sym s = match get_api_sym s with Some _ -> true | _ -> false in
        if List.for_all is_api_sym syms then
          Some ("function arguments: " 
                ^ String.concat ";" (List.map (fun s -> s#getBaseName) syms))
        else
          None
     | _ -> None

let is_heap_address poq arg inv =
    match get_heap_address poq arg inv with Some _ -> true | _ -> false

let is_api_address poq arg inv =
    match get_api_address poq arg inv with Some _ -> true | _ -> false

                                                                   
class no_overlap_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list) =
object (self)

  method private memref_to_string memref =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  method private is_new_memory arg v invindex = 
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,_) = poq#get_postconditions v in
      let _ = poq#set_diagnostic_arg
                arg ("function return value from " ^ callee.vname) in
      List.fold_left (fun acc (pc,_) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XNewMemory ReturnValue ->
                let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                let msg = "return value from " ^ callee.vname ^ " is new memory" in
                Some (deps,msg)
             | _ -> None) None pcs
    else
      None

  method private is_alloca_address arg v invindex =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,_) = poq#get_postconditions v in
      let _ = poq#set_diagnostic_arg
                arg ("function return value from " ^ callee.vname) in
      List.fold_left (fun acc (pc,_) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XStackAddress ReturnValue ->
                let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                let msg = "return value from " ^ callee.vname ^ " is new memory" in
                Some (deps,msg)
             | _ -> None) None pcs
    else if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      let _ = poq#set_diagnostic_arg arg (self#memref_to_string memref) in
      match memref#get_base with
      | CBaseVar basevar -> self#is_alloca_address arg basevar invindex
      | _ -> None
    else
      None

  method private is_stack_address arg  v invindex =
    if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      let _ = poq#set_diagnostic_arg arg (self#memref_to_string memref) in
      match memref#get_base with
      | CStackAddress stackvar ->
         let (vinfo,offset) = poq#env#get_local_variable stackvar in
         let deps = DLocal  [ invindex ] in
         let msg = "local stack variable: " ^ vinfo.vname in
         Some (deps,msg)
      | _ -> None
    else
      None

  method private is_api_value arg v invindex =
    if poq#is_api_expression (XVar v) then
      let xapi = poq#get_api_expression (XVar v) in
      let deps = DLocal [ invindex ] in
      let msg = "argument to the function: " ^ (e2s xapi) in
      Some (deps,msg)
    else if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      let _ = poq#set_diagnostic_arg arg (self#memref_to_string memref) in
      match memref#get_base with
      | CBaseVar basevar ->
         if poq#is_api_expression (XVar basevar) then
           let xapi = poq#get_api_expression (XVar basevar) in
           let deps = DLocal [ invindex ] in
           let msg = "base-var is argument to the function: " ^ (e2s xapi) in
           Some (deps,msg)
         else
           None
      | _ -> None
    else
      None

  method private is_global_value arg v invindex =
    if poq#is_global_expression (XVar v) then
      let xglobal = poq#get_global_expression (XVar v) in
      let deps = DLocal [ invindex ] in
      let msg = "initial value of global variable: " ^ (e2s xglobal) in
      Some (deps,msg)
    else
      None

  method private distinct_local_variables inv1index inv2index v1 v2 =
    if poq#env#is_memory_address v1 && poq#env#is_memory_address v2 then
      let memref1 = poq#env#get_memory_reference v1 in
      let memref2 = poq#env#get_memory_reference v2 in
      let _ = poq#set_diagnostic_arg 1 (self#memref_to_string memref1) in
      let _ = poq#set_diagnostic_arg 2 (self#memref_to_string memref2) in
      match (memref1#get_base, memref2#get_base) with
      | (CStackAddress svar1, CStackAddress svar2) ->
         let (vinfo1,_) = poq#env#get_local_variable svar1 in
         let (vinfo2,_) = poq#env#get_local_variable svar2 in
         if not (vinfo1.vid = vinfo2.vid) then
           let deps = DLocal [ inv1index ; inv2index ] in
           let msg = "distinct local variables: " ^ vinfo1.vname ^ " and "
                     ^ vinfo2.vname ^ " do not overlap" in
           Some (deps,msg)
         else
           None
      | _ -> None
    else
      None
                
    
  (* ----------------------------- safe ------------------------------------- *)

  method private var_implies_safe inv1index inv2index v1 v2 =
    match (self#is_alloca_address 1 v1 inv1index) with
    | Some (deps1,msg1) ->
       let _ = poq#set_diagnostic_arg 1 msg1 in
       begin
         match (self#is_stack_address 2 v2 inv2index) with
         | Some (deps2,msg2) ->
            let deps = join_dependencies deps1 deps2 in
            let msg = "address of dynamically allocated stack region ("
                      ^ msg1 ^ ") and regular stack address ("
                      ^ msg2 ^ ") do not overlap" in
            Some (deps,msg)
         | _ -> None
       end
    | _ ->
       match (self#is_stack_address 1 v1 inv1index) with
       | Some (deps1,msg1) ->
          let _ = poq#set_diagnostic_arg 1 msg1 in
          begin
            match (self#is_alloca_address 2 v2 inv2index) with
            | Some (deps2,msg2) ->
               let deps = join_dependencies deps1 deps2 in
               let msg  = "stack address (" ^ msg1
                          ^ ") and address of dynamically allocated stack region ("
                          ^ msg2 ^ ") do not overlap" in
               Some (deps,msg)
            | _ ->
               match (self#is_api_value 2 v2 inv2index) with
                 | Some (deps2,msg2) ->
                    let deps = join_dependencies deps1 deps2 in
                    let msg  = "stack address (" ^ msg1
                               ^ ") and address passed in as an argument ("
                               ^ msg2 ^ ") do not overlap"  in
                    Some (deps,msg)
                 | _ -> 
                    match (self#is_global_value 2 v2 inv2index) with
                    | Some (deps2,msg2) ->
                       let deps = join_dependencies deps1 deps2 in
                       let msg  = "stack address (" ^ msg1
                                  ^ ") and address passed in by global variable ("
                                  ^ msg2 ^ ") do not overlap" in
                       Some (deps,msg)
                    | _ -> None
          end
       | _ ->
          match (self#is_api_value 1 v1 inv1index) with
          | Some (deps1,msg1) ->
             let _ = poq#set_diagnostic_arg 1 msg1 in
             begin
               match (self#is_stack_address 2 v2 inv2index) with
               | Some (deps2,msg2) ->
                  let deps = join_dependencies deps1 deps2 in
                  let msg = "address passed in as an argument ("
                            ^ msg1 ^ ") and regular stack address ("
                            ^ msg2 ^ ") do not overlap" in
                  Some (deps,msg)
               | _ -> None
             end
          | _ ->
             match (self#is_global_value 1 v1 inv1index) with
             | Some (deps1,msg1) ->
                let _ = poq#set_diagnostic_arg 1 msg1 in
                begin
                  match (self#is_stack_address 2 v2 inv2index) with
                  | Some (deps2,msg2) ->
                     let deps = join_dependencies deps1 deps2 in
                     let msg = "address passed in by global variable ("
                               ^ msg1 ^ ") and regular stack address  ("
                               ^ msg2 ^ ") do not overlap" in
                     Some (deps,msg)
                  | _ -> None
                end
             | _ ->
                self#distinct_local_variables inv1index inv2index v1 v2
               
  method private xpr_implies_safe inv1index inv2index x1 x2 =
    match (x1,x2) with
    | (XVar v1, XVar v2) 
      | (XOp (_, [ XVar v1 ;  _ ]), XVar v2)
      | (XVar v1,  XOp (_, [ XVar v2 ; _ ]))
      | (XOp (_, [ XVar v1 ; _ ]), XOp (_, [ XVar v2 ; _ ])) ->
       self#var_implies_safe inv1index inv2index v1 v2
    | _ -> None

  method private inv_implies_safe inv1 inv2 =
    match (inv1#lower_bound_xpr, inv2#lower_bound_xpr) with
    | (Some x1, Some x2) -> self#xpr_implies_safe inv1#index inv2#index x1 x2
    | _ ->
       match (inv1#lower_bound_xpr_alternatives, inv2#expr) with
       | (None, _) | (_, None) | (Some [], _) -> None
       | (Some (h::tl), Some x2) ->
          begin
            match self#xpr_implies_safe inv1#index inv2#index h x2 with
            | Some r ->
               List.fold_left (fun acc x1 ->
                   match acc with
                   | None -> None
                   | Some (deps,msg) ->
                      match self#xpr_implies_safe inv1#index inv2#index x1 x2 with
                      | Some (d,m) ->
                         let deps = join_dependencies deps d in
                         let msg = msg ^ "; " ^ m in
                         Some (deps,msg)
                      | _ -> None)  (Some r) tl
            | _ -> None
          end
         
  method check_safe =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_safe inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
       
  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_no_overlap (poq:po_query_int) (e1:exp) (e2:exp) =
  let invs1 = poq#get_invariants 1 in
  let invs2 = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 1 in
  let _ = poq#set_diagnostic_invariants 2 in
  let checker = new no_overlap_checker_t poq e1 e2 invs1 invs2 in
  checker#check_safe || checker#check_violation || checker#check_delegation
