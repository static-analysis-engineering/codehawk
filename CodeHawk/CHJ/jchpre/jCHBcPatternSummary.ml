(* =============================================================================
   CodeHawk Java Analyzer
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
open CHPretty

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHBcPattern
open JCHFunctionSummary
open JCHPreAPI

module H = Hashtbl

let patterns = H.create 3
let add_pattern (cmsix:int) (p:bc_pattern_t) = H.replace patterns cmsix p

let get_pattern (cmsix:int) =
  if H.mem patterns cmsix then
    Some (H.find patterns cmsix)
  else
    None

let opcode_to_arithmetic_op (opc:opcode_t):arithmetic_op_t option =
  match opc with
  | OpAdd _ -> Some JPlus
  | OpSub _ -> Some JMinus
  | OpMult _ -> Some JTimes
  | OpDiv _ -> Some JDivide
  | _ -> None

let resolve_call mInfo c =
  match c.bcp_base_type with
  | TClass cn ->
     begin
       match c.bcp_type with
       | "static" | "special" -> [ (make_cms cn c.bcp_ms)#index ]
       | _ -> []
     end
  | _ -> []

let rec mk_basic_value_jterm (mInfo:method_info_int) (v:bc_basicvalue_t):jterm_t option =
  let cms = mInfo#get_class_method_signature in
  match v with
  | BcvArg i -> Some (JLocalVar i)
  | BcvIntConst n | BcvLongConst n | BcvByteConst n| BcvShortConst n ->
     Some (JConstant n)
  | BcvDoubleConst f | BcvFloatConst f -> Some (JFloatConstant f)
  | BcvThisField (cn,fs) ->
     Some (JObjectFieldValue (cms#index, 0, cn#index, fs#name))
  | BcvThatField (cn,fs,obj) ->
     begin
       match mk_object_value_jterm mInfo obj with
       | Some (JLocalVar i) ->
          Some (JObjectFieldValue (cms#index,i,cn#index,fs#name))
       | _ ->
          begin
            chlog#add "basic-value jterm: that field"
                      (LBLOCK [ cms#toPretty ; STR ": " ; bc_object_value_to_pretty obj ]) ;
            None
          end
     end
  | BcvStaticField (cn,fs) -> Some (JStaticFieldValue (cn#index, fs#name))
  | BcvArrayLength obj ->
     begin
       match mk_object_value_jterm mInfo obj with
       | Some t -> Some (JSize t)
       | _ ->
          begin
            chlog#add "basic-value jterm: arraylength"
                      (LBLOCK [ cms#toPretty ; STR ": " ; bc_object_value_to_pretty obj ]) ;
            None
          end
     end
  | BcvBinOpResult (op, v1, v2) ->
     begin
       match (opcode_to_arithmetic_op op,
              mk_basic_value_jterm mInfo v1,mk_basic_value_jterm mInfo v2) with
       | (Some op, Some t1, Some t2) -> Some (JArithmeticExpr (op, t1, t2))
       | _ -> None
     end
  | _ ->
     begin
       chlog#add "basic-value jterm"
                 (LBLOCK [ cms#toPretty; STR ": " ; bc_basic_value_to_pretty v ]) ;
       None
     end
  
and mk_object_value_jterm (mInfo:method_info_int) (v:bc_objectvalue_t):jterm_t option =
  let cms = mInfo#get_class_method_signature in
  match v with
  | BcoArg i -> Some (JLocalVar i)
  | _ ->
     begin
       chlog#add "object-value jterm"
                 (LBLOCK [ cms#toPretty; STR ": " ; bc_object_value_to_pretty v ]) ;
       None
     end

and mk_value_jterm (mInfo:method_info_int) (v:bc_value_t):jterm_t option =
  match v with
  | BcBasic bv -> mk_basic_value_jterm mInfo bv
  | BcObject ov -> mk_object_value_jterm mInfo ov
                         
let mk_basic_value_postconditions (mInfo:method_info_int) (v:bc_basicvalue_t) =
  let rvalue = match mk_basic_value_jterm mInfo v with
    | Some t -> PostRelationalExpr (JEquals, JLocalVar (-1), t)
    | _ -> PostTrue in
  let post = [ make_postcondition false rvalue ] in
  List.filter (fun p -> not (p#get_predicate = PostTrue)) post

let mk_object_value_postconditions (mInfo:method_info_int) (v:bc_objectvalue_t) =
  let rvalue = match mk_object_value_jterm mInfo v with
    | Some t -> PostRelationalExpr (JEquals, JLocalVar (-1), t)
    | _ -> PostTrue in
  let post = [ make_postcondition false rvalue ] in
  List.filter (fun p -> not (p#get_predicate = PostTrue)) post
  
     

let mk_value_postconditions (mInfo:method_info_int) (v:bc_value_t) =
  match v with
  | BcBasic bv -> mk_basic_value_postconditions mInfo bv
  | BcObject ov -> mk_object_value_postconditions mInfo ov

let mk_error_value_postconditions (mInfo:method_info_int) (v:bc_value_t) = []

let mk_pattern_postconditions
      (mInfo:method_info_int) (p:bc_pattern_t):postcondition_int list =
  match p with
  | BcpNop | BcpNopX | BcpAction _ | BcpThrow _
    | BcpActionExcept _ | BcpActionExceptThrow _ | BcpIllegalSeq _ -> []
  | BcpInfiniteLoop _ -> [ make_postcondition false PostFalse ]
  | BcpResult (_, v) -> mk_value_postconditions mInfo v
  | BcpResultExcept (_,_,v1,v2) ->
     (mk_value_postconditions mInfo v1) @ (mk_error_value_postconditions mInfo v2)
  | BcpResultExceptThrow (_,_,v,_) -> mk_value_postconditions mInfo v

(* --------------------------------------------------------------------------------- taint *)

let rec mk_bc_basic_value_taint_source mInfo v =
  let cms = mInfo#get_class_method_signature in
  let logmsg p = LBLOCK [ cms#toPretty ; NL ; INDENT (8,p) ] in
  match v with
  | BcvIntConst _ | BcvLongConst _ | BcvByteConst _ | BcvShortConst _ -> Some ([],[])
  | BcvDoubleConst _ | BcvFloatConst _ -> Some ([],[])
  | BcvThisField (cn,fs) -> Some  ([],[ JObjectFieldValue (cms#index,0,cn#index,fs#name) ])
  | BcvArg n -> Some ([],[ JLocalVar n ])
  | BcvConvert (_,v) -> mk_bc_basic_value_taint_source mInfo v
  | BcvUnOpResult (_,v) -> mk_bc_basic_value_taint_source mInfo v
  | BcvBinOpResult (_,v1,v2) ->
     let t1 = mk_bc_basic_value_taint_source mInfo v1 in
     let t2 = mk_bc_basic_value_taint_source mInfo v2 in
     begin
       match (t1,t2) with
       | (Some (a1,b1),Some (a2,b2)) -> Some (a1@a2, b1@b2)
       | _ -> None
     end
  | BcvQResult (_,testvals,rv1,rv2) ->
     let (valid,tv) = List.fold_left (fun (v,acc) bv ->
                          if v then
                            match mk_bc_value_taint_source mInfo bv with
                            | Some (tv,_) -> (true,tv@acc)
                            | _ -> (false,acc)
                          else
                            (false,acc)) (true,[]) testvals in
     if valid then
       let t1 = mk_bc_basic_value_taint_source mInfo rv1 in
       let t2 = mk_bc_basic_value_taint_source mInfo rv2 in
       begin
         match (t1,t2) with
         | (Some (a1,b1),Some (a2,b2)) -> Some (tv@a1@a2, b1@b2)
         | _ -> None
       end
     else
       None 
  | _ ->
     begin
       chlog#add "basic value taint source" (logmsg (bc_basic_value_to_pretty v)) ;
       None
     end

and mk_bc_object_value_taint_source mInfo v =
  let cms = mInfo#get_class_method_signature in
  let logmsg p = LBLOCK [ cms#toPretty ; NL ; INDENT (8,p) ] in
  match v with
  | BcoNull | BcoClassConst _ | BcoStringConst _ -> Some ([],[])
  | BcoThisField (cn,fs) -> Some  ([],[ JObjectFieldValue (cms#index,0,cn#index,fs#name) ])
  | BcoArg n -> Some ([],[ JLocalVar n ])
  | BcoCheckCast (_,v) -> mk_bc_object_value_taint_source mInfo v
  | BcoCallRv c ->
     let callvalues =
       match c.bcp_base_object with
       | Some o -> (BcObject o) :: c.bcp_args
       | _ -> c.bcp_args in
     begin
       match mk_bc_value_list_taint_source mInfo callvalues with
       | Some ([],[]) -> Some ([],[])
       | _ ->
          match resolve_call mInfo c with
          | [] ->
             begin
               chlog#add
                 "object call taint source"
                 (logmsg (bc_object_value_to_pretty v)) ;
               None
             end
          | l ->
             begin
               chlog#add
                 "resolved object call"
                 (logmsg (pretty_print_list l (fun i -> (retrieve_cms i)#toPretty) "[" "," "]")) ;
               None
             end
     end
  | _ ->
     begin
       chlog#add "object value taint source" (logmsg (bc_object_value_to_pretty v)) ;
       None
     end

and mk_bc_value_taint_source mInfo v:(taint_element_t list * jterm_t list) option =
  match v with
  | BcBasic bv -> mk_bc_basic_value_taint_source mInfo bv
  | BcObject ov -> mk_bc_object_value_taint_source mInfo ov

and mk_bc_value_list_taint_source mInfo vl =
  let (v,acc) =
    List.fold_left (fun (v,(tl,srcs)) bcv ->
        if v then
          match mk_bc_value_taint_source mInfo bcv with
          | Some (taintelems,sources) -> (true, (taintelems@tl,srcs@sources))
          | _ -> (false, (tl,srcs))
        else
          (false, (tl,srcs))) (true,([],[])) vl in
  if v then Some acc else None

and mk_action_taintflow (mInfo:method_info_int) (a:bc_action_t):taint_element_t list option =
  let cms = mInfo#get_class_method_signature in
  let logmsg p = LBLOCK [ cms#toPretty ; NL ; INDENT (8,p) ] in
  match a with
  | BcNop | BcNopX | BcInitObject | BcInitSuper -> Some []
  | BcNewObject (cn,args) ->
     let tlists = List.map (mk_bc_value_taint_source mInfo) args in
     if List.for_all (fun t -> match t with Some ([],[]) -> true | _ -> false) tlists then
       Some []
     else
       None
  | BcPutThisField (cn,fs,v) ->
     let rvtaint = mk_bc_value_taint_source mInfo v in
     let dst = JObjectFieldValue (cms#index, 0, cn#index, fs#name) in
     begin
       match rvtaint with
       | Some (taintelems,l) ->
          Some ((List.map (fun src -> TTransfer (src,dst)) l) @ taintelems)
       | _ ->
          begin
            chlog#add "action putfield taintflow" (logmsg (bc_value_to_pretty v)) ;
            None
          end
     end
  | BcDropValues vl ->
     let (valid,actiontaint) =
       List.fold_left (fun (v,acc) dvalue ->
           if v then
             match mk_bc_value_taint_source mInfo dvalue with
             | Some (taintelems,_) -> (v, acc @ taintelems)
             | _ -> (false,acc)
           else
             (false,acc)) (true,[]) vl in
     if valid then Some actiontaint else None
  | _ ->
     begin
       chlog#add "action taintflow" (logmsg (bc_action_to_pretty a)) ;
       None
     end

                                    
let mk_pattern_taintflow (mInfo:method_info_int) (p:bc_pattern_t):taint_int option =
  let cms = mInfo#get_class_method_signature in
  let logmsg p = LBLOCK [ cms#toPretty ; NL ; INDENT (8,p) ] in
  match p with
  | BcpNop | BcpNopX -> Some (make_taint [])
  | BcpResult (l,v) ->
     begin
       match mk_bc_value_taint_source mInfo v with
       | Some (taintelems,rv) ->
          let (valid,transfers) =
            List.fold_left (fun (v,acc) action ->
                if v then
                  match mk_action_taintflow mInfo action with
                  | Some l -> (v,acc@l)
                  | _ -> (false,acc)
                else
                  (false,acc)) (true,[]) l in
          if valid then
            let rvtransfers = List.map (fun t -> TTransfer (t, JLocalVar (-1))) rv in
            Some (make_taint (transfers @ rvtransfers @ taintelems))
          else
            None
       | _ ->
          begin
            chlog#add "return value" (logmsg (bc_value_to_pretty v)) ;
            None
          end
     end
  | BcpAction l ->
     let (valid,transfers) =
       List.fold_left (fun (v,acc) action ->
           if v then
             match mk_action_taintflow mInfo action with
             | Some l -> (v,acc@l)
             | _ -> (false,acc)
           else
             (false,acc)) (true,[]) l in
     if valid then
       Some (make_taint transfers)
     else
       None
  | _ ->
     begin
       chlog#add "pattern taint flow"
                 (LBLOCK [ cms#toPretty ; STR ": " ; NL ;
                           INDENT (8,bc_pattern_to_pretty p) ]) ;
       None
     end
