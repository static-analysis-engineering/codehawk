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
open Xprt
open XprTypes
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHExternalPredicate
open CCHLibTypes
open CCHProofObligation
open CCHTypesToPretty
open CCHTypesUtil

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


class width_overflow_checker_t
        (poq:po_query_int)
        (e:exp)
        (k:ikind)
        (invs:invariant_int list) =
object (self)

  val safe_width = mkNumerical (get_safe_bit_width k)

  method private mk_safe_constraint x =
    XOp (XLt, [ x ; num_constant_expr safe_width ])

  method private mk_violation_constraint x =
    XOp (XGe, [ x ; num_constant_expr safe_width ])

  method private memref_to_string memref =
    "memory base: " ^  (p2s (memory_base_to_pretty memref#get_base))

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

  method private var_implies_safe (invindex:int) (v:variable_t) =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,epcs) = poq#get_postconditions v in
      let _ = poq#set_diagnostic_arg 1 ("return value from: " ^ callee.vname) in
      let request () =
        let xpred = XRelationalExpr (Lt, ReturnValue, NumConstant safe_width) in
        poq#mk_postcondition_request xpred callee  in
      match (pcs,epcs)  with
      | ([],_) -> begin (request ()) ; None end 
      | (_,[]) ->
         let r = 
           List.fold_left (fun facc (pc,_) ->
               match facc with
               | Some _ -> facc
               | _ ->
                  match pc with
                  | XRelationalExpr (Lt, ReturnValue, NumConstant n)
                       when n#leq safe_width ->
                     let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                     let msg = "return value from " ^ callee.vname
                               ^ " is guaranteed to be less than: " ^ n#toString in
                     Some (deps,msg)
                  | XRelationalExpr (Le, ReturnValue, NumConstant n)
                       when n#lt safe_width ->
                     let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                     let msg = "return value from " ^ callee.vname
                               ^ " is guaranteed to be less than or equal to: " ^ n#toString in
                     Some (deps,msg)
                  | XRelationalExpr (Eq, ReturnValue, NumConstant n)
                       when n#lt safe_width ->
                     let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                     let msg = "return value from " ^ callee.vname
                               ^ " is equal to: " ^ n#toString in
                     Some (deps,msg)
                  | _ -> None) None pcs in
         begin
           match r with
           | Some _ -> r
           | _ -> begin (request ()) ; r end
         end
      | _ ->
         begin
           poq#set_diagnostic_arg
             1 ("error-post: "
                ^ (String.concat
                     "; " (List.map (fun x -> (p2s (xpredicate_to_pretty (fst x)))) epcs))) ;
           None
         end
    else if poq#env#is_memory_address v then
      let (memref,offset) = poq#env#get_memory_address v in
      begin
        poq#set_diagnostic_arg
          1 ("memory address: " ^ (self#memaddr_to_string memref offset)) ;
        None
      end
    else if poq#env#is_memory_variable v then
      let (memref,offset) = poq#env#get_memory_variable v in
      begin
        poq#set_diagnostic_arg
          1 ("memory variable: " ^ (self#memaddr_to_string memref offset)) ;
        None
      end
    else
      None

  method private xpr_implies_safe (invindex:int) (x:xpr_t) =
    match x with
    | XConst (IntConst n) when n#lt safe_width ->
       let deps = DLocal [ invindex ] in
       let msg = "value: " ^ n#toString ^ "  is less than safe width: "
                 ^ safe_width#toString in
       Some (deps,msg)
    | XVar v -> self#var_implies_safe invindex v
    | _ -> None

  method private xpr_list_implies_safe (invindex:int) (l:xpr_t list) =
    match l with
    | [] -> None
    | h::tl  ->
       match self#xpr_implies_safe invindex h with
       | Some r ->
          List.fold_left (fun acc x ->
              match acc with
              | None -> None
              | Some (deps,msg) ->
                 match self#xpr_implies_safe invindex x with
                 | Some (d,m) ->
                    let deps = join_dependencies deps d in
                    let msg = msg ^ "; " ^ m in
                    Some (deps,msg)
                 | _ -> None) (Some r) tl
       | _ -> None
                   
  method private inv_implies_safe inv =
    let r = None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#upper_bound_xpr with
         | Some x -> self#xpr_implies_safe inv#index x
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#upper_bound_xpr_alternatives with
         | Some l -> self#xpr_list_implies_safe inv#index l
         | _ -> None in
    r
    
  method check_safe =
    match invs with
    | [] -> false
    | _ ->
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

  method private xpr_implies_violation invindex x =
    match x with
    | XConst  (IntConst n) when n#geq safe_width ->
       let deps = DLocal [ invindex ] in
       let msg = "lower bound on width value: " ^ n#toString ^ " violates "
                 ^ " bit width bound: " ^ safe_width#toString in
       Some (deps,msg)
    | _ -> None

  method private inv_implies_universal_violation inv =
    match inv#lower_bound_xpr with
    | Some x -> self#xpr_implies_violation inv#index x
    | _ -> None

  method private var_implies_existential_violation invindex v =
    if poq#env#is_tainted_value v then
      let safeconstraint = self#mk_safe_constraint (XVar v) in
      let vconstraint = self#mk_violation_constraint (XVar v) in
      match poq#get_witness vconstraint v with
      | Some violationvalue ->
         let (s,callee,pc) = poq#get_tainted_value_origin v  in
         let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
         let msg =
           s ^  " choose value: " ^ (x2s violationvalue)
           ^ " to violate safety constraint: " ^ (x2s safeconstraint) in
         Some (deps,msg)
      | _ -> None
    else
      None

  method private xpr_implies_existential_violation invindex x =
    match x with
    | XVar v -> self#var_implies_existential_violation invindex v
    | _ -> None

  method private xprlist_implies_existential_violation invindex xl =
    List.fold_left (fun acc x ->
        match  acc with
        | Some _ ->  acc
        | _ ->
           match self#xpr_implies_violation invindex x with
           | Some r -> Some  r
           | _ -> self#xpr_implies_existential_violation invindex x) None xl

  method private inv_implies_violation inv =
    match  self#inv_implies_universal_violation inv with
    | Some r -> Some r
    | _ ->
       match inv#expr with
       | Some x -> self#xpr_implies_existential_violation inv#index  x
       | _ ->
          match inv#upper_bound_xpr_alternatives with
          | Some [] -> None
          | Some xl ->
             self#xprlist_implies_existential_violation  inv#index xl
          | _ -> None
      
  method check_violation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_violation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_violation_result deps msg ;
                  true
                end
             |  _ -> false) false invs
                         
  (* ----------------------- delegation ------------------------------------- *)
                         
  method private inv_implies_delegation inv =
    match inv#upper_bound_xpr with
    | Some x when poq#is_api_expression x ->
       let pred = PWidthOverflow (poq#get_api_expression x,k) in
       let deps = DEnvC ([ inv#index ],[ ApiAssumption pred ]) in
       let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                 ^ " delegated to the api" in
       Some (deps,msg)
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
                  poq#record_safe_result deps msg ;
                  true
                end
             | _ -> false) false invs
end


let check_width_overflow (poq:po_query_int) (e:exp) (k:ikind) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new width_overflow_checker_t poq e k invs in
  checker#check_safe || checker#check_violation || checker#check_delegation
