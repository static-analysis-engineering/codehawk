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
open CHLanguage
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
open CCHFileContract
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHMemoryBase
open CCHMemoryReference
open CCHPOPredicate   
open CCHPreTypes
open CCHProofObligation

   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)

(* An address is guaranteed to be non-null if
   * - it is explicitly checked non-null within the function
   * - it is the result of pointer arithmetic (by inductive hypothesis)
   * - it is a nonzero offset from a base address 
   *  
   * The requirement for a non-null memory address is lifted to the api if it is equal
   * to the initial value of a struct value pointed to by a parameter
   * The requirement for a non-null memory address is delegated to the postcondition of
   * a function if it is the return value of that function
   *)

class not_null_checker_t (poq:po_query_int) (e:exp) (invs:invariant_int list) =
object (self)

  method private memref_to_string memref =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  method private offset_to_string offset =
    match offset with
    | NoOffset -> ""
    | Field ((fname,_),foff) ->
       "offset: ." ^ fname ^ self#offset_to_string foff
    | Index (e,ioff) ->
       "offset: [" ^ (e2s e) ^ "]" ^ self#offset_to_string ioff

  method private memaddr_to_string memref offset =
    (self#memref_to_string memref) ^ (self#offset_to_string offset)

  (* ----------------------------- safe ------------------------------------- *)

  method private command_line_argument =
    if poq#is_command_line_argument e then
      let index = poq#get_command_line_argument_index e in
      match poq#get_command_line_argument_count with
      | Some (inv,i) ->
         if index < i then
           begin
             poq#record_safe_result
               (DLocal [inv])
               ("command-line argument " ^ (string_of_int index)
                ^ " is guaranteed not null for argument count " ^ (string_of_int i)) ;
             true
           end
         else
           begin
             poq#record_violation_result
               (DLocal [inv])
               ("command-line argument " ^ (string_of_int index)
                ^ " is not included in argument count of " ^ (string_of_int i)) ;
             true
           end
      | _ ->
         begin
           poq#set_diagnostic
             ("no invariant found for argument count; unable to validate access of "
              ^ "command-line argument " ^ (string_of_int index)) ;
           false
         end
    else
      false

  method private global_expression_safe invindex x =
    let pred = PNotNull (poq#get_global_expression x) in
    match poq#check_implied_by_assumptions pred with
    | Some apipred ->
       let deps = DEnvC ([ invindex ],[ GlobalApiAssumption apipred ]) in
       let msg = (p2s (po_predicate_to_pretty pred)) ^ " implied by global assumption: "
                 ^ (p2s (po_predicate_to_pretty apipred)) in
       Some (deps,msg)
    | _ ->
       let xpred = po_predicate_to_xpredicate poq#fenv pred in
       begin
         poq#mk_global_request xpred;
         None
       end

  method private function_return_value_safe invindex v =
    let callee = poq#env#get_callvar_callee v in
    let _ = poq#set_diagnostic_arg 1 ("function return value from: " ^ callee.vname) in
    let (pcs,epcs) = poq#get_postconditions v in
    match (pcs,epcs) with
    | ([],_) ->
       let pc = XNotNull ReturnValue in
       begin
         poq#mk_postcondition_request pc callee ;
         None
       end
    | (_,[]) ->
       List.fold_left (fun acc (pc,_) ->
           match acc with
           | Some _ -> acc
           | _ ->
              match pc with
              | XNotNull ReturnValue ->
                 let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                 let msg = "return value from " ^ callee.vname ^ " is guaranteed not null" in
                 Some (deps,msg)
              | _ ->
                 let pc = XNotNull ReturnValue in
                 begin
                   poq#mk_postcondition_request pc callee ;
                   poq#set_diagnostic
                     ("unable to exclude null return value from " ^ callee.vname) ;
                   None
                 end) None pcs
    | _ ->
       begin
         List.iter (fun (pc,_) ->
             match pc with
             | XNull ReturnValue ->
                poq#set_diagnostic
                   ("warning: " ^ callee.vname ^  " returns null when an error occurs")
             | _ ->  ()) epcs ;
         None
       end

  method private memory_address_safe invindex v =
    let (memref,offset) = poq#env#get_memory_address v in
    let _ = poq#set_diagnostic_arg
              1 ("memory address: " ^ (self#memaddr_to_string memref offset)) in
    let deps = DLocal [ invindex ] in
    match memref#get_base with
    | CStackAddress stackvar when poq#env#is_local_variable stackvar ->
       let (vinfo,_) = poq#env#get_local_variable stackvar in
       let msg = "address of stack variable: "  ^ vinfo.vname in
       Some (deps,msg)
    | CGlobalAddress gvar ->
       let (vinfo,_) = poq#env#get_global_variable gvar in
       let msg = "address of global variable: " ^ vinfo.vname in
       Some (deps,msg)
    | CStringLiteral _ ->
       let msg = "address of string literal" in
       Some (deps,msg)
    | CBaseVar v -> self#xpr_implies_safe invindex (XVar v)
    | _ -> None

  method private memory_variable_safe invindex v =
    let (memref,offset) = poq#env#get_memory_variable v in
    let _ = poq#set_diagnostic_arg
              1 ("memory variable: " ^ (self#memaddr_to_string memref offset)) in
    None                 

  method private xpr_implies_safe invindex x =
    match x with
    | XOp (XPlus, _) | XOp (XMinus, _) ->
       let deps = DLocal [ invindex ] in
       let msg = "value is compound expression: " ^ (x2s x) in
       Some (deps,msg)
    | x when poq#is_global_expression x ->
       self#global_expression_safe invindex x
    | XVar v when poq#env#is_function_return_value v ->
       self#function_return_value_safe invindex v
    | XVar v when poq#env#is_memory_address v ->
       self#memory_address_safe invindex v
    | XVar v when poq#env#is_memory_variable v ->
       self#memory_variable_safe invindex v
    | _ -> None

  method private xprlist_implies_safe invindex l =
    match l with
    | [] -> None
    | h::tl ->
       match self#xpr_implies_safe invindex h with
       | None -> None
       | Some r ->
          List.fold_left (fun acc x ->
              match self#xpr_implies_safe invindex x with
              | None -> None
              | Some (deps,msg) ->
                 begin
                   match self#xpr_implies_safe invindex x with
                   | Some (d,m) ->
                      let deps = join_dependencies deps d in
                      let msg = msg ^ "; " ^ m in
                      Some (deps,msg)
                   | _ -> None
                 end) (Some r) tl

  method private regions_implies_safe invindex symlist =
    match symlist with
    | [] -> None
    | _ ->
       let memregmgr = poq#env#get_variable_manager#memregmgr in
       let uninterpreted =
         List.filter (fun s ->
             (memregmgr#get_memory_region s#getSeqNumber)#is_uninterpreted) symlist in
       match uninterpreted with
       | [] ->
          if List.for_all (fun s ->
                 (memregmgr#get_memory_region s#getSeqNumber)#is_not_null) symlist then
            let deps = DLocal [ invindex ] in
            let msg =
              "all pointed to regions are not null: "
              ^ (String.concat
                   ","
                   (List.map (fun s ->
                        p2s (memregmgr#get_memory_region s#getSeqNumber)#toPretty) symlist)) in
            Some (deps,msg)
          else
            let _ = poq#set_diagnostic "some regions pointed to may be NULL" in
            None
       | _ ->
          let _ =
            poq#set_diagnostic
              ("encountered uninterpreted regions: "
               ^ (String.concat
                    ","
                    (List.map (fun s ->
                         p2s (memregmgr#get_memory_region s#getSeqNumber)#toPretty) uninterpreted)))  in
          None
                                         
              

  method private inv_implies_safe inv =
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
         | NonRelationalFact (_,FBaseOffsetValue(_,_,_,_,false)) ->
            let deps = DLocal [ inv#index ] in
            let msg = "null has been explicitly excluded (either by assignment or by checking)" in
            Some (deps,msg)
         | NonRelationalFact (_,FRegionSet symlist) ->
            self#regions_implies_safe inv#index symlist
         | _ -> None  in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr_alternatives with
         | None | Some [] -> None
         | Some l -> self#xprlist_implies_safe inv#index l in
    r
               
  method check_safe =
    self#command_line_argument
    || (List.fold_left (fun acc inv ->
            acc ||
              match self#inv_implies_safe inv with
              | Some (deps,msg) ->
                 begin
                   poq#record_safe_result deps msg ;
                   true
                 end
              | _ -> false) false invs)
            

  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false

  (* ----------------------- delegation ------------------------------------- *)

  method private memref_implies_delegation invindex memref =
    match memref#get_base with
    | CBaseVar v when poq#is_api_expression (XVar v) ->
       let a = poq#get_api_expression (XVar v) in
       let pred = PNotNull a in
       let deps = DEnvC ([ invindex ],[ ApiAssumption  pred ]) in
       let msg = "condition " ^  (p2s (po_predicate_to_pretty pred))
                 ^ " delegated to the api" in
       Some (deps,msg)
    | _ -> None

  method private var_implies_delegation invindex v =
    if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      self#memref_implies_delegation  invindex memref
    else
      None

  method private xpr_implies_delegation invindex x =
    if poq#is_api_expression x then
      let pred = PNotNull (poq#get_api_expression x) in
      let deps = DEnvC ([ invindex ],[ ApiAssumption pred ]) in
      let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                ^ " delegated to the api" in
      Some (deps,msg)
    else
      match x with
      | XVar v ->
         begin
           match self#var_implies_delegation invindex v with
           | Some r -> Some r
           | _ -> self#xpr_implies_safe invindex x
         end
      | _ -> self#xpr_implies_safe invindex x
      

  method private xprlist_implies_delegation invindex xlist =
    match xlist with
    | [] -> None
    | h::tl ->
       let r = self#xpr_implies_delegation invindex h in
       List.fold_left (fun acc x ->
           match acc with
           | None -> None
           | Some (deps,msg) ->
              match self#xpr_implies_delegation invindex x with
              | Some (d,m) ->
                 let deps = join_dependencies deps d in
                 let msg = msg ^ "; " ^ m in
                 Some (deps,msg)
              | _ -> None) r tl
       
  method private inv_implies_delegation inv =
    let r = None in
    let r = match r with
      | Some _ -> r
      |  _ ->
          match inv#base_offset_value with
          | Some (_,XVar v,_,_,false) ->
             let deps = DLocal [ inv#index ] in
             let msg = "offset from variable " ^ v#getName#getBaseName
                       ^ "; null has been excluded" in
             Some (deps,msg)
          | Some (_,XVar v,_,_,_) when poq#is_api_expression (XVar v) ->
             let pred = PNotNull (poq#get_api_expression (XVar v)) in
             let deps = DEnvC ([ inv#index ],[ ApiAssumption pred ]) in
             let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                       ^ " delegated to the api" in
             Some (deps,msg)
          | _ -> None in
    let r = match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr with
         | Some x when poq#is_api_expression x ->
            self#xpr_implies_delegation inv#index x
         | Some (XVar v) -> self#var_implies_delegation inv#index v
         | _ -> None in
    let r = match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr_alternatives with
         | Some xprlist -> self#xprlist_implies_delegation inv#index xprlist
         | _ -> None in
    r
         
  method check_delegation =
    List.fold_left  (fun acc inv ->
        acc  ||
          match self#inv_implies_delegation inv with
          | Some (deps,msg) ->
             begin
               poq#record_safe_result deps msg ;
               true
             end
          | _ -> false) false invs

end

let check_not_null (poq:po_query_int) (e:exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new not_null_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation
