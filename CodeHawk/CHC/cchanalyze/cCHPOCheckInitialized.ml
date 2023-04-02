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
open CHLogger
open CHPrettyUtil
   
(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHExternalPredicate
open CCHFileContract
open CCHFileEnvironment
open CCHLibTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHCheckValid
open CCHInvariantFact
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

let fenv = CCHFileEnvironment.file_environment

  (* An lval is guaranteed to be initialized if
   * - it is passed as a parameter (that is, it is the responsibility of the caller when
   *   passing a value, that that value is properly initialized, as the receiving function
   *   has no way of checking this) (checked by validity checker), or
   *  - if it has been assigned within the function
   *  - if the expression is the dereferencing of the address of a variable, and the
   *       variable is initialized
   *  - if the lval contains an embedded null dereference; null dereference is checked
   *    for separately
   * 
   * The requirement for an initialized value is lifted to the api if the lval is an element
   * of a struct pointed to by a parameter value
   *)
         
class initialized_checker_t (poq:po_query_int) (lval:lval) (invs:invariant_int list)  =
object (self)

  method private check_command_line_argument =
    if poq#is_command_line_argument (Lval lval) then
      let index = poq#get_command_line_argument_index (Lval lval) in
      match poq#get_command_line_argument_count with
      | Some (inv,i) ->
         if index < i then
           begin
             poq#record_safe_result
               (DLocal [ inv ])
               ("command-line argument " ^ (string_of_int index)
                ^ " is guaranteed initialized for argument count " ^ (string_of_int i)) ;
             true
           end
         else
           begin
             poq#record_violation_result
               (DLocal [ inv ])
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

  method private get_symbol_name s =
    s#getBaseName
    ^ (match s#getAttributes with
       | [] -> ""
       | l  -> "(" ^ (String.concat "" l) ^ ")")

  method private is_function_pointer memlval =
    match fenv#get_type_unrolled (type_of_lval poq#env#get_fdecls memlval)  with
    | TPtr (TFun _,_) -> true
    | _ -> false

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

  method private inv_implies_safe inv =
    match inv#get_fact with
    | NonRelationalFact (_,FInitializedSet l) ->
       let localAssigns =
         List.filter (fun s -> not (s#getBaseName = "parameter")) l in
       begin
         match localAssigns with
         | [] -> None
         | _ ->
            let deps = DLocal [ inv#index ] in
            let msg = (String.concat
                         "_xx_" (List.map self#get_symbol_name localAssigns)) in
            Some (deps,msg)
       end
    | _ -> None

  method private check_safe_functionpointer vinfo =
    let vinfovalues = poq#get_vinfo_offset_values vinfo in
    let _ = poq#set_diagnostic ("function pointer: " ^ vinfo.vname)  in
    List.fold_left (fun acc (inv,offset) ->
        match offset with
        | NoOffset ->
           begin
             match inv#expr with
             | Some (XVar v) when poq#env#is_memory_address v ->
                let (memref,offset) = poq#env#get_memory_address v in
                let _ = poq#set_diagnostic_arg
                          1 ("memory address: " ^ (self#memaddr_to_string memref offset)) in
                begin
                  match memref#get_base with
                  | CGlobalAddress v ->
                     let (gvinfo,gvoffset) = poq#env#get_global_variable v in
                     let deps = DLocal [ inv#index ] in
                     let msg = "variable " ^ vinfo.vname ^ " is initialized with function pointer "
                               ^ gvinfo.vname in
                     begin
                       poq#record_safe_result deps msg ;
                       true
                     end
                  | _ -> false
                end
             | Some x ->
                begin
                  poq#set_diagnostic  ("deref expr: " ^ (x2s x)) ;
                  false
                end
             | _ -> false
           end
        | _ ->
           begin
             poq#set_diagnostic
               ("offset: " ^  (p2s (offset_to_pretty offset))
                ^ "; invariant: " ^  (p2s inv#value_to_pretty) ^ ")") ;
             false
           end) false vinfovalues

  method private basevar_implies_deref_offset_safe invindex v memoffset =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,_) = poq#get_postconditions v in
      let _ = poq#set_diagnostic_arg 1 ("return value from: " ^ callee.vname) in
      let request () =
        match memoffset with
        | NoOffset | Field _ ->
           let xpred = XInitialized (ArgAddressedValue (ReturnValue, offset_to_s_offset memoffset)) in
           if List.mem callee.vname [ "malloc"; "calloc"; "realloc" ] then
             poq#set_diagnostic "[action]:identify side effects of intervening calls"
           else
             poq#mk_postcondition_request xpred callee
        | _ -> poq#set_diagnostic_arg
                 1 ("rv:memoffset: " ^ (p2s (offset_to_pretty memoffset))) in
      let returntype =
        match file_environment#get_type_unrolled callee.vtype with
        | TFun (t,_,_,_) -> t
        | t ->
           raise (CCHFailure
                    (LBLOCK [ STR "Unexpected function type: " ;
                              typ_to_pretty t ; STR " for: " ; STR callee.vname ])) in
      let tgttype =
        match returntype with
        | TPtr (t,_) -> t
        | _ ->
           raise (CCHFailure
                    (LBLOCK [ STR "Unexpected return type for dereferencing: " ;
                              typ_to_pretty returntype ; STR " for " ; STR callee.vname ])) in
      match pcs with
      | [] -> begin request () ; None end
      | _ ->
         let r =
           List.fold_left (fun facc (pc,_) ->
               match facc with
               | Some _  -> facc
               | _ ->
                  match pc with
                  | XInitialized (ArgAddressedValue (ReturnValue, soff))
                       when (offset_compare (s_offset_to_offset tgttype soff) memoffset) = 0 ->
                     let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                     let rec offset_s o = match o with
                       | NoOffset -> ""
                       | Field ((fname,_),oo) -> "." ^ fname ^ (offset_s oo)
                       | Index (e,oo) -> "[.]" ^ (offset_s oo) in
                     let offsetstring o =
                       let s = offset_s o in
                       if (String.length s) > 0 then
                         " (offset: " ^ s ^ ") "
                       else
                         "" in
                     let msg = "value addressed by return value from "
                               ^ callee.vname ^ (offsetstring memoffset) ^ " is initialized" in
                     Some (deps,msg)
                  | _ -> None) None pcs in
         match r with
         | Some _ -> r
         | _ -> begin request () ; None end
    else
      None
                      

  method private memref_implies_deref_offset_safe invindex memref offset memoffset =
    match offset with
    | NoOffset ->
       begin
         match memref#get_base with
         | CGlobalAddress gvar ->
            let (gvinfo,goffset) = poq#env#get_global_variable gvar in
            begin
              match goffset with
              | NoOffset ->
                 let lval = (Mem (Lval (Var (gvinfo.vname,gvinfo.vid),NoOffset)),memoffset) in
                 let pred = PInitialized lval in
                 begin
                   match poq#check_implied_by_assumptions pred with
                   | Some pred ->
                      let deps = DEnvC ([ invindex ],[ GlobalApiAssumption pred ]) in
                      let msg = "initialized implied by global assumption: "
                                ^  (p2s  (po_predicate_to_pretty pred)) in
                      Some (deps,msg)
                   | _ ->
                      let xpred = po_predicate_to_xpredicate poq#fenv pred in
                      begin
                        poq#mk_global_request xpred ;
                        None
                      end
                 end
              | _ -> None
            end
         | CStackAddress svar ->
            let (vinfo,voffset) = poq#env#get_local_variable svar in
            let _ = poq#set_diagnostic_arg
                      1 ("stack variable: " ^ vinfo.vname ^ (p2s (offset_to_pretty voffset))) in
            None
         | CBaseVar v ->
            (try
               self#basevar_implies_deref_offset_safe invindex v memoffset
             with
             | CCHFailure p ->
                begin
                  poq#set_diagnostic ("E:basevar: " ^ v#getName#getBaseName);
                  ch_error_log#add "initialized-basevar" p ;
                  None
                end
             | _ -> None)
         | _ -> None
       end
    | _ ->
       None
      
  method private vinv_implies_deref_offset_safe inv memoffset =
    let rec is_field_offset offset = 
      match offset with
      | NoOffset -> true
      | Field (_,NoOffset) -> true
      | _  -> false in
    match inv#expr with
    | Some x when poq#is_global_expression x ->
       if is_field_offset memoffset then
         let g = poq#get_global_expression x in
         let derefg = (Mem g,memoffset) in
         let pred = PInitialized derefg in
         begin
           match poq#check_implied_by_assumptions pred with
           | Some pred ->
              let deps = DEnvC ([ inv#index ],[ GlobalApiAssumption pred ]) in
              let msg = "initialized property implied by global assumption: "
                        ^ (p2s (po_predicate_to_pretty pred)) in
              Some (deps,msg)
           | _ ->
              let xpred = po_predicate_to_xpredicate poq#fenv pred in
              begin
                poq#mk_global_request xpred ;
                None
              end
         end
       else
         begin
           poq#set_diagnostic ("mem-offset: " ^ (p2s (offset_to_pretty memoffset))) ;
           None
         end
    | Some (XVar v) when poq#env#is_memory_address v ->
       let (memref,offset) = poq#env#get_memory_address v in
       let _ = poq#set_diagnostic_arg
                 1 ("D:memory address: " ^ (self#memaddr_to_string memref offset)) in
       let _ = poq#set_diagnostic
                 ("mem-offset: " ^ (p2s (offset_to_pretty memoffset))) in
       self#memref_implies_deref_offset_safe inv#index memref offset memoffset
    | Some x ->
       begin
         poq#set_diagnostic_arg 1 ("[deref] " ^ (x2s x)) ;
         None
       end
    | _ -> None

  method private check_safe_deref memlval memoffset =
    match (memlval,memoffset) with
    | ((Var (vname,vid),NoOffset),NoOffset) when self#is_function_pointer memlval && vid > 0 ->
       self#check_safe_functionpointer (poq#env#get_varinfo vid)
    | ((Var (vname,vid),NoOffset),_) when vid > 0 ->
       let vinfo = poq#env#get_varinfo vid in
       let vinfovalues = poq#get_vinfo_offset_values vinfo in
       let _ = poq#set_vinfo_diagnostic_invariants vinfo in
       let _ = poq#set_diagnostic ("[offset]: " ^ (p2s (offset_to_pretty memoffset))) in
       List.fold_left (fun acc (inv,offset) ->
           acc ||
             match offset with
             | NoOffset ->
                begin
                  match self#vinv_implies_deref_offset_safe inv memoffset with
                  | Some (deps,msg) ->
                     begin
                       poq#record_safe_result deps msg ;
                       true
                     end
                  | _ -> false
                end
             | _ ->
                begin
                  poq#set_diagnostic ("[deref offset]: " ^  (p2s (offset_to_pretty offset))) ;
                  false
                end) false vinfovalues
    | _ -> false
         
  method private check_safe_lval =
    match lval with
    | (Mem (Lval memlval), memoffset) ->
       self#check_safe_deref memlval memoffset
    | _ -> false
         
  method check_safe =
    self#check_command_line_argument
    ||
      (List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg ;
                  true
                end
             | _ -> false) false invs)
    ||
      self#check_safe_lval

  (* ----------------------- violation -------------------------------------- *)

  method private var_implies_violation invindex v =
    if poq#env#is_byte_sequence v then
      let bsv = poq#env#get_byte_sequence_origin v in
      let callee = poq#env#get_callvar_callee bsv in
      let deps = DLocal [ invindex ] in
      let msg = "value may be tainted by " ^ callee.vname in
      Some (deps,msg)
    else
      None

  method private xpr_implies_violation invindex x =
    let r = None in
    let r = match r with
      | Some _ -> r
      | _ ->
         match x with
         | XVar v -> self#var_implies_violation invindex v
         | _ -> None in
    r

  method  private xprlist_implies_violation invindex l =
    List.fold_left (fun acc x ->
        match acc with
        | Some _ -> acc
        | _ -> self#xpr_implies_violation invindex x) None l

  method private inv_implies_violation inv =
    let r = None in
    let r = match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr with
         | Some x ->  self#xpr_implies_violation inv#index x
         | _ -> None in
    let r = match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr_alternatives with
         | Some l -> self#xprlist_implies_violation inv#index l
         | _ -> None in
    r
    
  method check_violation =
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

  method private xpr_implies_delegation invindex x =
    if poq#is_api_expression x then
      let _ = poq#set_diagnostic_arg
                1 ("api expression: " ^ (e2s (poq#get_api_expression x))) in
      match poq#get_api_expression x with
      | Lval apilval ->
         let pred = PInitialized apilval in
         let deps = DEnvC ([ invindex ],[ ApiAssumption pred ]) in
         let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                   ^ " delegated to the api" in
         Some (deps,msg)
      | _ -> None
    else
      None

  method private inv_implies_delegation inv =
    match inv#expr with
    | Some x -> self#xpr_implies_delegation inv#index x
    | _ -> None

  method private check_invs_delegation =
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

  method private var_memoffset_deref_delegation invindex lval memoffset =
    match memoffset with
    | Field ((fname,fid),Index (Lval (Var (vname,vid),NoOffset),
                                (( NoOffset | Field (_,NoOffset)) as suboff))) when vid > 0 ->
       let vinfo = poq#env#get_varinfo vid in
       let vinfovalues = poq#get_vinfo_offset_values vinfo in
       let _ = poq#set_vinfo_diagnostic_invariants vinfo in
       let mkdeps n =
         let noffset = Field ((fname,fid),Index (make_constant_exp n,suboff))  in
         let memlval = (Mem (Lval lval),noffset) in
         let pred = PInitialized memlval  in
         let deps = DEnvC ([ invindex ],[ ApiAssumption pred ]) in
         let msg = "delegate condition " ^  (p2s (po_predicate_to_pretty pred))
                   ^ " to the api" in
         (deps,msg) in
       List.fold_left (fun acc (inv,offset) ->
           match acc with
           | Some _ -> acc
           | _ ->
              match (inv#lower_bound_xpr, inv#upper_bound_xpr) with
              | (Some (XConst (IntConst lb)), Some (XConst (IntConst ub)))
                   when (ub#sub lb)#lt (mkNumerical 10) ->
                 let numrange = mk_num_range lb (ub#add numerical_one) in
                 begin
                   match numrange with
                   | [] -> None
                   | h::tl ->
                      let (deps,msg) =
                        List.fold_left (fun (d,m) n ->
                            let (dd,mm) = mkdeps n in
                            let d = join_dependencies d dd in
                            let m = m ^ "; " ^ mm in
                            (d,m)) (mkdeps h) tl in
                      Some (deps,msg)
                 end
              | _ -> None) None vinfovalues
    | _ ->
       begin
         poq#set_diagnostic ("[U:memoffset] " ^ (p2s (offset_to_pretty memoffset))) ;
         None
       end

  method private vinv_implies_deref_offset_delegation inv memoffset =
    match inv#expr with
    | Some x when poq#is_api_expression x ->
       begin
         match poq#get_api_expression x with
         | Lval lval ->
            if is_constant_offset memoffset then
              let memlval =  (Mem (Lval lval),memoffset) in
              let pred = PInitialized memlval in
              let deps = DEnvC ([ inv#index ],[ ApiAssumption  pred ]) in
              let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                        ^ " delegated to the api" in
              Some (deps,msg)
            else
              self#var_memoffset_deref_delegation inv#index lval memoffset
         | _ ->
            begin
              poq#set_diagnostic_arg 1 ("[api] " ^ (x2s x)) ;
              None
            end
       end         
    | _ -> None
            
  method private check_lval_deref_delegation memlval memoffset =
    match memlval with
    | (Var (vname,vid),NoOffset) when vid > 0 ->
       let vinfo  = poq#env#get_varinfo vid in
       let vinfovalues = poq#get_vinfo_offset_values vinfo in
       List.fold_left (fun  acc (inv,offset) ->
           acc ||
             match offset with
             | NoOffset ->
                begin
                  match self#vinv_implies_deref_offset_delegation inv memoffset  with
                  | Some (deps,msg) ->
                     begin
                       poq#record_safe_result deps msg ;
                       true
                     end
                  | _ -> false
                end
             | _ -> false) false vinfovalues
    | _ -> false
      
  method  private check_lval_delegation =
    match lval with
    | (Mem  (Lval memlval), memoffset) ->
       self#check_lval_deref_delegation memlval memoffset
    | (Mem (BinOp (_,Lval (Var (vname,vid),NoOffset),Const (CInt (i64,_,_)),_) as e),NoOffset) when vid > 0  ->
       let vinfo = poq#env#get_varinfo vid in
       begin
         poq#set_vinfo_diagnostic_invariants vinfo ;
         poq#set_diagnostic_arg 1 ("offset: " ^ (Int64.to_string i64)) ;
         (let xpr = poq#get_external_value e in
          if is_random xpr then () else
            poq#set_diagnostic_arg 1 ("deref-value: " ^ (x2s xpr))) ;
         false
       end
    | _ -> false
   
  method check_delegation =
    self#check_invs_delegation || self#check_lval_delegation

end

let check_initialized (poq:po_query_int) (lval:lval) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new initialized_checker_t poq lval invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

