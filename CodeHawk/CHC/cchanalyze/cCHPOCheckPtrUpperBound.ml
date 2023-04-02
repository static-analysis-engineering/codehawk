(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
   
(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHSumTypeSerializer
open CCHTypesUtil
open CCHTypesToPretty

(* cchpre *)
open CCHCheckValid
open CCHInvariantFact
open CCHMemoryBase
open CCHPreTypes
open CCHPOPredicate
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let e2s x = p2s (exp_to_pretty x)
let x2s x = p2s (x2p x)

let cd = CCHDictionary.cdictionary

class ptr_upper_bound_checker_t
        ?(strict=false)
        (poq:po_query_int)
        (typ:typ)
        (op:binop)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list) =
object (self)

  method private get_predicate a1 a2 =
    if strict then
      PPtrUpperBoundDeref (typ, op, a1, a2)
    else
      PPtrUpperBound  (typ, op, a1, a2)

  method private memref_to_string memref =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  method var_implies_unsigned_length_conflict invindex v =
    let default () =
      if poq#env#is_function_return_value v then
        let (pcs,epcs) = poq#get_postconditions v in
        let callee = poq#env#get_callvar_callee v in
        let _ = poq#set_diagnostic_arg 4 ("function return value from " ^ callee.vname) in
        List.fold_left (fun acc (pc,_) ->
            match pc with
            | XRelationalExpr (Eq, ReturnValue, NumConstant n) when n#lt numerical_zero ->
               let deps = DEnvC ( [ invindex ],[ PostAssumption (callee.vid,pc) ]) in
               let msg =  "function return value from: " ^ callee.vname
                          ^ " may be negative: " ^ n#toString
                          ^ " (maybe an error condition), which may be cast to a large "
                          ^ "positive value" in
               Some (deps,msg)
            | _ -> None) None (pcs @ epcs)
      else
        None in                        
      
    if poq#env#is_tainted_value v then
      match poq#env#get_tainted_value_bounds v with
      | (Some (XConst (IntConst n)), _)  when n#lt numerical_zero ->
         let (msg,callee,pc) = poq#get_tainted_value_origin v in
         let deps = DEnvC (  [ invindex ],[ PostAssumption (callee.vid,pc) ]) in
         let msg = msg  ^ " choose -1"
                   ^ " to create a large positive value when cast to unsigned" in
         Some (deps,msg)
      | _ -> default ()
    else
      default ()
         
  method private unsigned_length_conflict =
    match e2 with
    | CastE (t, _) when is_unsigned_integral_type t ->
       let _ = poq#set_diagnostic_arg
                 4 ("value is cast to unsigned: " ^  (p2s (typ_to_pretty t))) in
       List.fold_left (fun acc inv2 ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv2#lower_bound_xpr with
              | Some (XConst (IntConst n)) when n#lt numerical_zero ->
                 let deps = DLocal ([ inv2#index ]) in
                 let msg = "negative value: " ^ n#toString
                           ^ ", may be cast to a large positive value when cast to: "
                           ^ (p2s  (typ_to_pretty t)) in
                 Some (deps,msg)
              | Some (XVar v) ->
                 self#var_implies_unsigned_length_conflict inv2#index v
              | _ -> None) None invs2
    | _ -> None

  method private unsigned_length_safe =
    match e2 with
    | CastE (t, _) when is_unsigned_integral_type t ->
       let _ = poq#set_diagnostic_arg
                 4 ("value is cast to unsigned: " ^ (p2s (typ_to_pretty t))) in
       List.fold_left (fun acc inv2 ->
           acc
           || match inv2#lower_bound_xpr with
              | Some (XConst (IntConst n)) -> n#geq numerical_zero
              | _ -> false) false invs2
    | _ -> true


  (* ----------------------------- safe ------------------------------------- *)

  method private null_terminated_string_implies_pluspi_safe =
    match (e1,e2) with
    | (StartOf (Var (vname1,vid1), NoOffset),
       CnApp ("ntp", [ Some (StartOf (Var (vname2,vid2), NoOffset)) ],_))
      | (CastE (_, StartOf (Var (vname1,vid1), NoOffset)),
         CnApp ("ntp", [ Some (CastE (_, StartOf (Var (vname2,vid2), NoOffset))) ],_))
      | (AddrOf (Var (vname1,vid1), NoOffset),
         CnApp ("ntp", [ Some (AddrOf (Var (vname2,vid2), NoOffset)) ],_))
      | (CastE (_, AddrOf (Var (vname1,vid1), NoOffset)),
         CnApp ("ntp", [ Some (CastE (_, AddrOf (Var (vname2,vid2), NoOffset))) ],_)) ->
       let vinfo1 = poq#env#get_varinfo vid1 in
       let vinfo2 = poq#env#get_varinfo vid2 in
       begin
         match (vinfo1.vtype,poq#get_ntp_value (StartOf (Var (vname2,vid2),NoOffset))) with
         | (TArray (_,Some (Const (CInt (len64,_,_))),_),  Some  (inv,ntplen)) ->
            let arraylen = num_constant_expr (mkNumericalFromInt64 len64) in
            let xconstraint = XOp (XLt, [ num_constant_expr ntplen ; arraylen ]) in
            let sconstraint = simplify_xpr xconstraint in
            if is_true sconstraint then
              let deps = DLocal [ inv#index ]  in
              let msg = "null terminator was set in array " ^ vinfo2.vname
                        ^ " at offset "  ^ ntplen#toString
                        ^ " in array: "  ^ vinfo1.vname ^ " with length: "  ^ (x2s arraylen) in
              Some (deps,msg)
            else
              begin
                poq#set_diagnostic
                  ("null terminator found in a rray " ^ vinfo2.vname
                   ^ " at offset " ^ ntplen#toString
                   ^ " which may violate bound: " ^ (x2s arraylen)
                   ^ " of array: " ^ vinfo1.vname) ;
                None
              end
         | _ ->
            begin
              poq#set_key_diagnostic
                "DomainRef:string:null-termination" "ability to track null-terminator" ;
              None
            end
       end
    | _ ->
       match e2 with
       | CnApp ("ntp", [ Some (StartOf (Var (vname2,vid2), NoOffset)) ],_)
         | CnApp ("ntp", [ Some (CastE (_, StartOf (Var (vname2,vid2), NoOffset))) ],_)
         | CnApp ("ntp", [ Some (CastE (_, CastE (_,StartOf (Var (vname2,vid2), NoOffset)))) ],_)
         | CnApp ("ntp", [ Some (AddrOf (Var (vname2,vid2), NoOffset)) ],_)
         | CnApp ("ntp", [ Some (CastE (_, AddrOf (Var (vname2,vid2), NoOffset))) ],_)
         | CnApp ("ntp", [ Some (CastE (_, CastE (_,AddrOf (Var (vname2,vid2), NoOffset)))) ],_) ->
          begin
            poq#set_key_diagnostic
              "DomainRef:string:null-termination" "ability to track null-terminator" ;
            None
          end
       | _ -> None
     
  method private buffer_implies_pluspi_safe
                   (bname:string)
                   (invindex:int)
                   (xsize:xpr_t)         (* byte size *)
                   (xoffset:xpr_t)       (* byte size *)
                   (xindexincr:xpr_t)    (* index size *) =
    let typesize = size_of_type poq#fenv typ in
    let (op,xop) = if strict then (Lt,XLt) else (Le,XLe) in
    let scompare = if strict then "less than" else "less than or equal to" in
    let xbyteincr = simplify_xpr (XOp (XMult, [ xindexincr ; typesize ]))  in
    let totaloffset = simplify_xpr (XOp (XPlus, [ xoffset ; xbyteincr ])) in
    let xconstraint = XOp (xop, [ totaloffset ; xsize ]) in
    let (b,sconstraint) = simplify_expr xconstraint in
    if is_true sconstraint then
      let msg = ("offset: " ^  (x2s xoffset) ^ " plus increment " ^ (x2s xindexincr)
                 ^ " times typesize: " ^ (x2s typesize)
                 ^ " is " ^ scompare ^ " size: " ^ (x2s xsize)
                 ^ " of buffer: " ^ bname) in
      Some (DLocal [],msg)
    else if poq#is_global_expression xindexincr then
      match (poq#x2global xsize, poq#x2global xoffset, poq#x2global typesize) with
      | (Some gsize, Some goffset, Some gtsize) ->
         let gindexincr = poq#get_global_expression xindexincr in
         let gbyteincr = BinOp (Mult, gindexincr, gtsize, TInt (IInt, [])) in
         let gtotaloffset =
           if is_zero xoffset then
             gbyteincr
           else
             BinOp (PlusA,  goffset, gbyteincr, TInt (IInt, [])) in
         let gpred = PValueConstraint (BinOp (op, gtotaloffset, gsize, TInt (IBool,[]))) in
         begin
           match poq#check_implied_by_assumptions gpred with
           | Some pred ->
              let gdeps = DEnvC ([ invindex ],[ GlobalApiAssumption pred ]) in
              let msg = "constraint " ^ (p2s (po_predicate_to_pretty gpred))
                        ^ " implied by global assumption "
                        ^ (p2s (po_predicate_to_pretty pred)) in
              Some (gdeps,msg)
           | _ ->
              let xpred = po_predicate_to_xpredicate poq#fenv gpred in
              begin
                poq#mk_global_request xpred ;
                None
              end
         end
      | _ ->
         begin
           poq#set_diagnostic
             ("global increment: "  ^ (e2s (poq#get_global_expression xindexincr))) ;
           None
         end
    else
      let simplifies =
        if b then
          " (remaining constraint: " ^  (x2s sconstraint) ^ ")"
        else
          "" in
      begin
        poq#set_diagnostic
          ("unable to prove constraint: " ^ (x2s xconstraint) ^ simplifies) ;
        None
      end

  method private check_pluspi_safe_xpr2 vname xsize xoffset deps1 inv2index x2  =
    match self#buffer_implies_pluspi_safe vname inv2index xsize xoffset x2 with
    | Some (deps,msg) ->
       let deps = join_dependencies deps1 deps in
       let msg = "buffer: " ^ vname ^ " ;" ^ msg in
       Some (deps,msg)
    | _ ->
       begin
         poq#set_diagnostic_arg 4 (x2s x2) ;
         None
       end

  method private invs2_implies_pluspi_safe vname xsize xoffset deps1 =
    List.fold_left (fun acc inv2 ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv2#upper_bound_xpr with
           | Some xincr ->
              self#check_pluspi_safe_xpr2 vname xsize xoffset deps1 inv2#index xincr
           | _ ->
              match inv2#upper_bound_xpr_alternatives with
              | Some [] -> None
              | Some (h::tl) ->
                 begin
                   match self#check_pluspi_safe_xpr2 vname xsize xoffset deps1 inv2#index h with
                   | Some r ->
                      List.fold_left (fun acc x ->
                          match acc with
                          | None -> None
                          | Some (deps,msg) ->
                             match self#check_pluspi_safe_xpr2 vname xsize xoffset deps1 inv2#index x with
                             | Some (d,m) ->
                                let deps = join_dependencies deps d in
                                let msg = msg ^ "; " ^  m in
                                Some (deps,msg)
                             | _ -> None) (Some r) tl
                   | _ -> None
                 end
              | _ -> None) None invs2

  method private memref_implies_pluspi_safe invindex memref =
    match memref#get_base with
    | CStringLiteral _ ->
       begin
         match e2 with
         | CnApp ("ntp", [ Some x ],_) when (cd#index_exp e1) = (cd#index_exp x) ->
            let deps = DLocal [ invindex ] in
            let msg = "null terminator of string is within bounds" in
            Some (deps,msg)
         | _ ->
            begin
              poq#set_diagnostic ("unusual bounds expression for string literal") ;
              None
            end
       end
    | _ -> None

  method private var1_implies_pluspi_safe invindex v =
    if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      let _ = poq#set_diagnostic_arg
                3 ("memory address: " ^  (self#memref_to_string memref)) in
      self#memref_implies_pluspi_safe invindex memref
    else
      None

  method private xpr1_implies_pluspi_safe invindex x =
    match x with
    | XVar v -> self#var1_implies_pluspi_safe invindex v
    | _ -> None

  method private check_pluspi_safe_invs1 =
    List.fold_left (fun acc inv1 ->
        acc ||
          match inv1#upper_bound_xpr with
          | Some x ->
             begin
               match self#xpr1_implies_pluspi_safe inv1#index x with
               | Some (deps,msg) ->
                  begin
                    poq#record_safe_result deps msg ;
                    true
                  end
               | _ -> false
             end
          | _ -> false) false invs1

  method private xpr_implies_pluspi_safe inv1index inv2index x1 x2 =
    match (x1,x2) with
    | _ -> None

  method private inv_implies_pluspi_safe inv1 inv2 =
    match (inv1#upper_bound_xpr, inv2#upper_bound_xpr) with
    | (Some x1, Some x2) -> self#xpr_implies_pluspi_safe inv1#index inv2#index x1 x2
    | _ -> None
         

  method private check_pluspi_safe_invs =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_pluspi_safe inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
    
         
  method check_safe =
    match self#null_terminated_string_implies_pluspi_safe with
    | Some (deps,msg) ->
       begin
         poq#record_safe_result deps msg ;
         true
       end
    | _ ->
       (self#unsigned_length_safe)
       && (match op with
           | PlusPI | IndexPI ->
              begin
                match poq#get_buffer_offset_size 3 typ e1 with
                | Some (vname,xsize,xoffset,deps1) ->
                   begin
                     match self#invs2_implies_pluspi_safe vname xsize xoffset deps1 with
                     | Some (deps,msg) ->
                        begin
                          poq#record_safe_result deps msg ;
                          true
                        end
                     | _ -> false
                   end
                | _ ->
                   self#check_pluspi_safe_invs1 || self#check_pluspi_safe_invs
              end
           | _ -> false)
            
                    
  (* ----------------------- violation -------------------------------------- *)

  method private buffer_implies_pluspi_violation
                   (invindex:int)
                   (xsize:xpr_t)          (* byte size *)
                   (xoffset:xpr_t)        (* byte size *)
                   (xindexincr:xpr_t) =   (* index size *)
    let typesize = size_of_type poq#fenv typ in
    let (op,xop) = if strict then (Lt,XLt) else (Le,XLe) in    
    let (vop,vxop) = if strict then (Ge,XGe) else (Gt,XGt) in
    let xbyteincr = simplify_xpr (XOp (XMult, [ xindexincr ; typesize ])) in
    let totaloffset = simplify_xpr (XOp (XPlus, [ xoffset ; xbyteincr ])) in
    let vxconstraint = XOp (vxop, [ totaloffset ; xsize ]) in
    let vsconstraint = simplify_xpr vxconstraint in
    if is_true vsconstraint then
      let xconstraint = XOp (xop, [ totaloffset ; xsize ]) in
      let msg = ("offset: " ^  (x2s xoffset) ^ " plus increment: " ^ (x2s xindexincr)
                 ^ " times typesize: " ^ (x2s typesize) ^ " violates safety constraint:  "
                 ^ (x2s xconstraint)) in
      Some (DLocal [], msg)
    else
      None

  method xpr2lst_implies_pluspi_universal_violation xsize xoffset inv2index  xlst =
    match xlst with
    | [] -> None
    | (h::tl) ->
       match self#buffer_implies_pluspi_violation inv2index xsize xoffset h with
       | Some r ->
          List.fold_left (fun acc x ->
              match acc with
              | None -> None
              | Some (deps,msg) -> 
                 match self#buffer_implies_pluspi_violation inv2index xsize xoffset x with
                 | Some (d,m) ->
                    let deps = join_dependencies deps d in
                    let msg = msg ^  "; " ^ m in
                    Some (deps,msg)
                 | _ -> None) (Some r) tl
       | _ -> None


  method private invs2_implies_pluspi_universal_violation xsize xoffset =
    List.fold_left (fun acc inv2 ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv2#upper_bound_xpr with
           | Some x ->
              begin
                match self#buffer_implies_pluspi_violation inv2#index xsize xoffset x with
                | Some  r -> Some r
                | _ ->
                   match inv2#upper_bound_xpr_alternatives with
                   | None -> None
                   | Some l ->
                      self#xpr2lst_implies_pluspi_universal_violation xsize xoffset inv2#index l
              end
           | _ ->
              match inv2#upper_bound_xpr_alternatives with
              | Some l ->
                 self#xpr2lst_implies_pluspi_universal_violation xsize xoffset inv2#index l
              | _ -> None) None invs2

  method private var2_implies_pluspi_existential_violation xsize xoffset inv2index v =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,epcs) = poq#get_postconditions v in
      List.fold_left (fun acc (pc,_) ->
          match pc with
          | XTainted (ReturnValue,_,Some (NumConstant ub)) ->
             let xincr = num_constant_expr ub in
             begin
               match self#buffer_implies_pluspi_violation inv2index xsize xoffset xincr with
               | Some (deps,msg) ->
                  let msg = "return value from " ^ callee.vname
                            ^ " may be tainted; choose value: " ^ ub#toString
                            ^ " to violate the upper bound constraint; " ^ msg in
                  Some (deps,msg)
               | _ -> None
             end
          | _ -> None) None (pcs@epcs)
    else if poq#env#is_tainted_value v then
      match poq#env#get_tainted_value_bounds v with
      | (_, Some ub) ->
         begin
           match self#buffer_implies_pluspi_violation inv2index xsize xoffset ub with
           | Some (deps,msg) ->
              let (s,callee,pc) = poq#get_tainted_value_origin v in
              let d = DEnvC ([ inv2index ],[ PostAssumption (callee.vid,pc) ]) in
              let deps = join_dependencies deps d in
              let msg = msg ^ "; " ^ s ^ " choose value: " ^ (x2s ub)
                        ^ " to violate the upper bound" in
              Some (deps,msg)
           | _ -> None
         end
      | _ -> None
    else
      None

  method private xpr2_implies_pluspi_existential_violation xsize xoffset inv2index x =
    match self#buffer_implies_pluspi_violation inv2index xsize xoffset x with
    | Some r -> Some r
    | _ ->
       match x with
       | XVar v ->
          self#var2_implies_pluspi_existential_violation xsize xoffset inv2index v
       | _ -> None

  method private xpr2lst_implies_pluspi_existential_violation xsize xoffset inv2index xlst =
    match xlst with
    | [] -> None
    | _ ->
       List.fold_left (fun acc x ->
           match acc with
           | Some _ -> acc
           | _ ->
              self#xpr2_implies_pluspi_existential_violation xsize xoffset inv2index x) None xlst

  method private invs2_implies_pluspi_existential_violation xsize xoffset =
    List.fold_left (fun acc inv2 ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv2#upper_bound_xpr with
           | Some x ->
              begin
                match self#xpr2_implies_pluspi_existential_violation xsize xoffset inv2#index x with
                | Some r -> Some r
                | _ ->
                   match inv2#upper_bound_xpr_alternatives with
                   | None -> None
                   | Some l ->
                      self#xpr2lst_implies_pluspi_existential_violation xsize xoffset inv2#index l
              end
           | _  ->
              match inv2#upper_bound_xpr_alternatives with
              | Some l ->
                 self#xpr2lst_implies_pluspi_existential_violation xsize xoffset inv2#index l
              |  _ -> None) None invs2
    
    
  method check_violation =
    match self#unsigned_length_conflict with
    | Some (deps,msg) ->
       begin
         poq#record_violation_result deps msg ;
         true
       end
    | _->
       match poq#get_buffer_offset_size 3 typ e1 with
       | Some (vname,xsize,xoffset,deps1) ->
          begin
            match op with
            | PlusPI | IndexPI ->
               begin
                 match self#invs2_implies_pluspi_universal_violation xsize xoffset with
                 | Some (deps,msg) ->
                    let deps = join_dependencies deps1 deps in
                    let msg = "buffer: " ^ vname ^ "; " ^ msg in
                    begin
                      poq#record_violation_result deps msg ;
                      true
                    end
                 | _ ->
                    match self#invs2_implies_pluspi_existential_violation xsize xoffset with
                    | Some (deps,msg) ->
                       let deps  = join_dependencies deps1 deps in
                       let msg = "buffer: " ^ vname ^ "; " ^ msg in
                       begin
                         poq#record_violation_result deps msg ;
                         true
                       end
                    | _ -> false
               end
            | _ -> false
          end
       | _ -> false
                         
  (* ----------------------- delegation ------------------------------------- *)

  method private xpr_implies_delegation invindices x1 x2 =
    match (poq#x2api x1, poq#x2api x2) with
    | (Some a1, Some a2) when poq#is_api_expression x1 || poq#is_api_expression x2 ->
       let pred = self#get_predicate a1 a2 in
       let deps = DEnvC (invindices,[ ApiAssumption pred ]) in
       let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                 ^ " delegated to the api" in
       Some (deps,msg)
    | (Some a1, _) ->
       begin
         poq#set_diagnostic_arg 3 ("api:" ^ (x2s x1)) ;
         None
       end
    | (_, Some a2) ->
       begin
         poq#set_diagnostic_arg 4 ("api:" ^ (x2s x2)) ;
         None
       end
    | _ -> None

  method private var_const_implies_delegation invindices v1 n =
    if poq#is_api_expression (XVar v1) then
      let pred = self#get_predicate (poq#get_api_expression (XVar v1)) (make_constant_exp n) in
      let deps = DEnvC ( invindices,[ ApiAssumption pred ]) in
      let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                ^ " delegated to the api" in
      Some (deps,msg)
    else if poq#env#is_memory_address v1 then
      let (memref,offset) = poq#env#get_memory_address v1 in
      match memref#get_base with
      | CBaseVar basevar ->
         self#var_const_implies_delegation invindices basevar n
      | _ -> None
    else
      None

  method private var_api_implies_delegation invindices v1 a2 =
    if poq#is_api_expression (XVar v1) then
      let pred = self#get_predicate (poq#get_api_expression (XVar v1)) a2 in
      let deps = DEnvC ( invindices, [ ApiAssumption pred ]) in
      let msg = "condition  " ^  (p2s (po_predicate_to_pretty pred))
                ^ " delegated to the api" in
      Some (deps,msg)
    else  if poq#env#is_memory_address v1 then
      let (memref,offset) = poq#env#get_memory_address v1 in
      match memref#get_base with
      | CBaseVar basevar ->
         self#var_api_implies_delegation invindices basevar a2
      | _ -> None
    else
      None
    

  method private inv_implies_delegation inv1 inv2 =
    let r = None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match (inv1#expr, inv2#upper_bound_xpr) with
         | (Some x1, Some x2) ->
            self#xpr_implies_delegation [inv1#index ; inv2#index] x1 x2
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match (inv1#expr, inv2#upper_bound_xpr) with
         | (Some (XVar v1), Some (XConst (IntConst n))) ->
            self#var_const_implies_delegation [ inv1#index ; inv2#index ] v1 n
         | _ -> None in
    let r =
      match  r with
      | Some _ -> r
      | _ ->
         match (inv1#expr, inv2#upper_bound_xpr) with
         | (Some (XVar v1), Some a2) when poq#is_api_expression  a2 ->
            self#var_api_implies_delegation [ inv1#index ; inv2#index ] v1 (poq#get_api_expression a2)
         | _ -> None in
    r

  method private buffer_implies_pluspi_delegation
                   (bname:string)
                   (invindex:int)
                   (xsize:xpr_t)      (* byte size *)
                   (xoffset:xpr_t)    (* byte size *)
                   (xincr:xpr_t)      (* index size *)   =
    let typesize = size_of_type poq#fenv typ in
    let (op,xop) = if strict then (Lt,XLt) else (Le,XLe)  in
    let xbyteincr = simplify_xpr (XOp (XMult, [ xincr ; typesize ])) in
    let totaloffset = simplify_xpr (XOp (XPlus, [ xoffset ; xbyteincr ])) in
    let xconstraint = XOp (xop, [ totaloffset ; xsize ]) in
    let sconstraint = simplify_xpr xconstraint in
    if poq#is_api_expression sconstraint then
      let aconstraint = poq#get_api_expression sconstraint in
      let pred = PValueConstraint aconstraint in
      let deps = DEnvC ( [ invindex ],[ ApiAssumption pred ]) in
      let msg = "constraint (derived from buffer: " ^ bname ^ " with size: "
                ^  (x2s xsize)  ^ " and offset: " ^ (x2s xoffset) ^ "): "
                ^ (p2s (po_predicate_to_pretty pred))
                ^ " delegated to the api" in
      Some (deps,msg)
    else
      None
         
  method private check_pluspi_delegation_xpr2 vname xsize xoffset deps1 inv2index x2  =
    match self#buffer_implies_pluspi_delegation vname inv2index xsize xoffset x2 with
    | Some (deps,msg) ->
       let deps = join_dependencies deps1 deps in
       let msg = "buffer: " ^ vname ^ "; " ^ msg in
       Some (deps,msg)
    | _ ->
       None

  method private invs2_implies_pluspi_delegation vname xsize xoffset deps1 =
    List.fold_left (fun acc inv2 ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv2#upper_bound_xpr with
           | Some xincr ->
              self#check_pluspi_delegation_xpr2 vname xsize xoffset deps1 inv2#index xincr
           | _ -> None) None invs2
         
  method check_delegation =
    match  (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_delegation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg ;
                        true
                      end
                   | _ ->
                      match op with
                      | PlusPI | IndexPI ->
                         begin
                           match poq#get_buffer_offset_size 3 typ e1 with
                           | Some (vname,xsize,xoffset,deps1) ->
                              begin
                                match self#invs2_implies_pluspi_delegation vname xsize xoffset deps1 with
                                | Some (deps,msg) ->
                                   begin
                                     poq#record_safe_result deps msg ;
                                     true
                                   end
                                | _ -> false
                              end
                           | _  -> false
                         end
                      | _ -> false) acc1 invs2) false invs1

end
     
let check_ptr_upper_bound
      ?(strict=false)
      (poq:po_query_int)
      (typ:typ)
      (op:binop)
      (e1:exp)
      (e2:exp) =
  let invs1 = poq#get_invariants 3 in
  let invs2 = poq#get_invariants 4 in
  let _ = poq#set_diagnostic_invariants 3 in
  let _ = poq#set_diagnostic_invariants 4 in
  let checker = new ptr_upper_bound_checker_t ~strict poq typ op e1 e2 invs1 invs2 in
  checker#check_safe || checker#check_violation || checker#check_delegation
