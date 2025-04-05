(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHNumerical
open CHLanguage

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHTraceResult

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHDoubleword
open BCHLibTypes

module H = Hashtbl
module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)


let memory_base_to_string (b: memory_base_t): string =
  match b with
  | BLocalStackFrame -> "stack"
  | BRealignedStackFrame -> "realigned"
  | BAllocatedStackFrame -> "allocated-stack"
  | BGlobal -> "global"
  | BaseVar v -> "var-" ^ v#getName#getBaseName
  | BaseArray (x, _) -> "array-" ^ (x2s x)
  | BaseStruct (x, _) -> "struct-" ^ (x2s x)
  | BaseUnknown s -> "unknown-" ^ s


let memory_base_to_pretty b = STR (memory_base_to_string b)


let rec memory_offset_to_string offset =
  match offset with
  | NoOffset -> ""
  | ConstantOffset (n,subOffset) ->
     "[" ^ n#toString ^ "]" ^ (memory_offset_to_string subOffset)
  | FieldOffset ((fname, _), subOffset) ->
     "." ^ fname ^ (memory_offset_to_string subOffset)
  | IndexOffset (v,size,subOffset) ->
    "[" ^ v#getName#getBaseName ^ ":" ^ (string_of_int size) ^ "]" ^
      (memory_offset_to_string subOffset)
  | ArrayIndexOffset (x, subOffset) ->
     "[" ^ (x2s x) ^  "]" ^ (memory_offset_to_string subOffset)
  | BasePtrArrayIndexOffset (x, subOffset) ->
     "[<[" ^ (x2s x) ^ "]>]" ^ (memory_offset_to_string subOffset)
  | UnknownOffset -> "?offset?"


let rec memory_offset_compare (o1: memory_offset_t) (o2: memory_offset_t) =
  match (o1, o2) with
  | (NoOffset, NoOffset) -> 0
  | (NoOffset, _) -> -1
  | (_, NoOffset) -> 1
  | (ConstantOffset (n1, so1), ConstantOffset (n2, so2)) ->
     let l1 = n1#compare n2 in
     if l1 = 0 then
       memory_offset_compare so1 so2
     else
       l1
  | (ConstantOffset _, _) -> -1
  | (_, ConstantOffset _) -> 1
  | (FieldOffset ((name1, key1), so1), FieldOffset ((name2, key2), so2)) ->
     let l1 = Stdlib.compare name1 name2 in
     if l1 = 0 then
       let l2 = Stdlib.compare key1 key2 in
       if l2 = 0 then
         memory_offset_compare so1 so2
       else
         l2
     else
       l1
  | (FieldOffset _, _) -> -1
  | (_, FieldOffset _) -> 1
  | (IndexOffset (v1, size1, so1), IndexOffset (v2, size2, so2)) ->
     let l1 = v1#compare v2 in
     if l1 = 0 then
       let l2 = Stdlib.compare size1 size2 in
       if l2 = 0 then
         memory_offset_compare so1 so2
       else
         l2
     else
       l1
  | (IndexOffset _, _) -> -1
  | (_, IndexOffset _) -> 1
  | (ArrayIndexOffset (x1, so1), ArrayIndexOffset (x2, so2)) ->
     let l1 = syntactic_comparison x1 x2 in
     if l1 = 0 then
       memory_offset_compare so1 so2
     else
       l1
  | (ArrayIndexOffset _, _) -> -1
  | (_, ArrayIndexOffset _) -> 1
  | (BasePtrArrayIndexOffset (x1, so1), BasePtrArrayIndexOffset (x2, so2)) ->
     let l1 = syntactic_comparison x1 x2 in
     if l1 = 0 then
       memory_offset_compare so1 so2
     else
       l1
  | (BasePtrArrayIndexOffset _, _) -> -1
  | (_, BasePtrArrayIndexOffset _) -> 1
  | (UnknownOffset, UnknownOffset) -> 0



let rec mk_maximal_memory_offset (n: numerical_t) (ty: btype_t): memory_offset_t =
  if is_struct_type ty then
    let compinfo = get_struct_type_compinfo ty in
    let optfinfo = get_struct_field_at_offset compinfo n#toInt in
    match optfinfo with
    | Some (finfo, rem) ->
       let fielduse = (finfo.bfname, compinfo.bckey) in
       if rem = 0 && is_scalar finfo.bftype then
         FieldOffset (fielduse, NoOffset)
       else
         let remoffset =
           mk_maximal_memory_offset (mkNumerical rem) finfo.bftype in
         FieldOffset (fielduse, remoffset)
    | _ ->
       UnknownOffset
  else if is_array_type ty then
    ConstantOffset (n, NoOffset)
  (* else if n#equal numerical_zero then
    NoOffset *)
  else
    begin
      ch_error_log#add
        "mk maximal memory offset"
        (LBLOCK [
             STR "Unexpected offset found for ";
             btype_to_pretty ty;
             STR " with offset ";
             n#toPretty]);
      UnknownOffset
    end


let rec address_memory_offset
          ?(tgtsize=None)
          ?(tgtbtype=t_unknown)
          (basetype: btype_t)
          (xoffset: xpr_t): memory_offset_t traceresult =
  let iszero x =
    match x with
    | XConst (IntConst n) -> n#equal CHNumerical.numerical_zero
    | _ -> false in
  let rbasetype = TR.tvalue (resolve_type basetype) ~default:t_unknown in
  match xoffset with
  | XConst (IntConst n) when is_unknown_type rbasetype ->
     let _ =
       log_diagnostics_result
         ~msg:"address-memory-offset:unknown basetype"
         __FILE__ __LINE__
         ["xoffset: " ^ n#toString] in
     Ok (ConstantOffset (n, NoOffset))
  | XConst (IntConst n) ->
     let tgtbtype =
       if is_unknown_type tgtbtype then None else Some tgtbtype in
     if is_struct_type rbasetype then
       structvar_memory_offset ~tgtsize ~tgtbtype rbasetype xoffset
     else if is_array_type rbasetype then
       arrayvar_memory_offset ~tgtsize ~tgtbtype rbasetype xoffset
     else
       let _ =
         log_diagnostics_result
           ~msg:"address-memory-offset:scalar basetype"
           __FILE__ __LINE__
           ["base type: " ^ (btype_to_string rbasetype)
            ^ "; xoffset: " ^ n#toString] in
       TR.tmap
         ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
         (fun size ->
           let scaledoffset = n#div (mkNumerical size) in
           BasePtrArrayIndexOffset (num_constant_expr scaledoffset, NoOffset))
         (size_of_btype rbasetype)
  | _ ->
     let tgtbtype =
       if is_unknown_type tgtbtype then None else Some tgtbtype in
     if is_struct_type rbasetype then
       structvar_memory_offset ~tgtsize ~tgtbtype rbasetype xoffset
     else if is_array_type rbasetype then
       arrayvar_memory_offset ~tgtsize ~tgtbtype rbasetype xoffset
     else
       let tsize_r = size_of_btype rbasetype in
       TR.tbind
         (fun tsize ->
           let optindex = BCHXprUtil.get_array_index_offset xoffset tsize in
           match optindex with
           | None ->
              Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                     ^ "Unable to extract index from " ^ (x2s xoffset)]
           | Some (indexxpr, xrem) when iszero xrem ->
              let _ =
                log_diagnostics_result
                  ~msg:"address-memory-offset:scalar basetype"
                  __FILE__ __LINE__
                  ["base type: " ^ (btype_to_string rbasetype)
                   ^ "; xoffset: " ^ (x2s xoffset)] in
              let scaledoffset = XOp (XDiv, [indexxpr; int_constant_expr tsize]) in
              let scaledoffset = Xsimplify.simplify_xpr scaledoffset in
              Ok (BasePtrArrayIndexOffset (scaledoffset, NoOffset))
           | _ ->
              Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                     ^ "Nonzero suboffset encountered when extracting index "
                     ^ "from " ^ (x2s xoffset) ^ " with base type "
                     ^ (btype_to_string rbasetype)])
         tsize_r

and structvar_memory_offset
~(tgtsize: int option)
~(tgtbtype: btype_t option)
(btype: btype_t)
(xoffset: xpr_t): memory_offset_t traceresult =
  match xoffset with
  | XConst (IntConst _) ->
     if is_struct_type btype then
       let compinfo = get_struct_type_compinfo btype in
       (get_field_memory_offset_at ~tgtsize ~tgtbtype compinfo xoffset)
     else
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
              ^ " xoffset: " ^ (x2s xoffset)
              ^ "; btype: " ^ (btype_to_string btype)]
  | _ ->
     if is_struct_type btype then
       let compinfo = get_struct_type_compinfo btype in
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "xoffset: " ^ (x2s xoffset)
              ^ "; type: struct " ^ compinfo.bcname]
     else
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "xoffset: " ^ (x2s xoffset)
              ^ "; btype: " ^ (btype_to_string btype)]

and arrayvar_memory_offset
~(tgtsize: int option)
~(tgtbtype: btype_t option)
(btype: btype_t)
(xoffset: xpr_t): memory_offset_t traceresult =
  let iszero x =
    match x with
    | XConst (IntConst n) -> n#equal CHNumerical.numerical_zero
    | _ -> false in

  if is_array_type btype then
    let eltty = get_element_type btype in
    TR.tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (fun elsize ->
        let optindex = BCHXprUtil.get_array_index_offset xoffset elsize in
        match optindex with
        | None ->
           Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                  ^ "Unable to extract index from " ^ (x2s xoffset)]
        | Some (indexxpr, xrem) when
               iszero xrem
               && Option.is_none tgtsize
               && Option.is_none tgtbtype ->
           Ok (ArrayIndexOffset (indexxpr, NoOffset))
        | Some (indexxpr, rem) ->
           if (TR.tfold_default is_struct_type false (resolve_type eltty)) then
             let eltty = TR.tvalue (resolve_type eltty) ~default:t_unknown in
             TR.tbind
               ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
               (fun suboff -> Ok (ArrayIndexOffset (indexxpr, suboff)))
               (structvar_memory_offset ~tgtsize ~tgtbtype eltty rem)
           else if is_array_type eltty then
             TR.tbind
               ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
               (fun suboff -> Ok (ArrayIndexOffset (indexxpr, suboff)))
               (arrayvar_memory_offset ~tgtsize ~tgtbtype eltty rem)
           else if is_scalar eltty then
             let x2index = XOp (XDiv, [rem; int_constant_expr elsize]) in
             let x2index = Xsimplify.simplify_xpr x2index in
             Ok (ArrayIndexOffset (x2index, NoOffset))
           else
             Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                    ^ "xoffset: " ^ (x2s xoffset)
                    ^ "; btype: " ^ (btype_to_string btype)
                    ^ "; elementtype: " ^ (btype_to_string eltty)])
      (size_of_btype eltty)
  else
    Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
           ^ " xoffset: " ^ (x2s xoffset)
           ^ "; btype: " ^ (btype_to_string btype)]


and get_field_memory_offset_at
~(tgtsize: int option)
~(tgtbtype: btype_t option)
(c: bcompinfo_t)
(xoffset: xpr_t): memory_offset_t traceresult =
  let check_tgttype_compliance (t: btype_t) (s: int) =
    match tgtsize, tgtbtype with
    | None, None -> true
    | Some size, None -> size = s
    | None, Some ty -> btype_equal ty t
    | Some size, Some ty -> size = s && btype_equal ty t in

  let compliance_failure (t: btype_t) (s: int) =
    let size_discrepancy size s =
      "size discrepancy between tgtsize: "
      ^ (string_of_int size)
      ^ " and field size: "
      ^ (string_of_int s) in
    let type_discrepancy ty t =
      "type discrepancy between tgttype: "
      ^ (btype_to_string ty)
      ^ " and field type: "
      ^ (btype_to_string t) in
    match tgtsize, tgtbtype with
    | Some size, Some ty when (size != s) && (not (btype_equal ty t)) ->
       (size_discrepancy size s) ^ " and " ^ (type_discrepancy ty t)
    | Some size, _ when size != s -> size_discrepancy size s
    | _, Some ty when not (btype_equal ty t) -> type_discrepancy ty t
    | _ -> "" in

  match xoffset with
  | XConst (IntConst n) ->
     let offset = n#toInt in
     let finfos = c.bcfields in
     let optfield_r =
       List.fold_left (fun acc_r finfo ->
           match acc_r with
           | Error e -> Error e
           | Ok (Some _) -> acc_r
           | Ok _ ->
              match finfo.bfieldlayout with
              | None ->
                 Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                        ^ "No field layout for field " ^ finfo.bfname]
              | Some (foff, sz) ->
                 if offset < foff then
                   Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                          ^ "Skipped over field: "
                          ^ (string_of_int offset)]
                 else if offset >= (foff + sz) then
                   Ok None
                 else
                   let offset = offset - foff in
                   TR.tbind
                  ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
                     (fun fldtype ->
                       if offset = 0
                          && (is_scalar fldtype)
                          && (check_tgttype_compliance fldtype sz) then
                         Ok (Some (FieldOffset
                                     ((finfo.bfname, finfo.bfckey), NoOffset)))
                       else
                         if offset = 0 && is_scalar fldtype then
                           Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                                  ^ "Scalar type or size is not consistent: "
                                  ^ (compliance_failure fldtype sz)]
                         else if is_struct_type fldtype then
                           TR.tmap
                             ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
                             (fun suboff ->
                               Some (FieldOffset
                                       ((finfo.bfname, finfo.bfckey), suboff)))
                             (structvar_memory_offset
                                ~tgtsize
                                ~tgtbtype
                                fldtype
                                (int_constant_expr offset))
                         else if is_array_type fldtype then
                           TR.tmap
                             ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
                             (fun suboff ->
                               Some (FieldOffset
                                       ((finfo.bfname, finfo.bfckey), suboff)))
                             (arrayvar_memory_offset
                                ~tgtsize
                                ~tgtbtype
                                fldtype
                                (int_constant_expr offset))
                         else
                           Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                                  ^ "Nonzero offset: " ^ (string_of_int offset)
                                  ^ " with unstructured field type: "
                                  ^ (btype_to_string fldtype)
                                  ^ " for field "
                                  ^ finfo.bfname])
                     (resolve_type finfo.bftype)) (Ok None) finfos in
     (match optfield_r with
      | Error e -> Error e
      | Ok (Some offset) -> Ok offset
      | Ok None ->
         Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                ^ "Unable to find field at offset " ^ (string_of_int offset)])
  | _ ->
  Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
         ^ "Unable to determine field for xoffset: " ^ (x2s xoffset)]


let rec is_unknown_offset offset =
  match offset with
  | UnknownOffset -> true
  | ConstantOffset (_, suboffset) -> is_unknown_offset suboffset
  | IndexOffset (_, _, suboffset) -> is_unknown_offset suboffset
  | _ -> false


let rec is_constant_offset offset =
  match offset with
  | NoOffset -> true
  | ConstantOffset (_, suboffset) -> is_constant_offset suboffset
  | _ -> false


let rec is_field_offset (offset: memory_offset_t): bool =
  match offset with
  | FieldOffset (_, NoOffset) -> true
  | FieldOffset (_, suboffset) -> is_field_offset suboffset
  | ConstantOffset (_, suboffset) -> is_field_offset suboffset
  | IndexOffset (_, _, suboffset) -> is_field_offset suboffset
  | _ -> false


let is_base_ptr_array_index_offset (offset: memory_offset_t): bool =
  match offset with
  | BasePtrArrayIndexOffset (_, suboffset) -> is_constant_offset suboffset
  | _ -> false


let rec is_index_offset (offset: memory_offset_t): bool =
  match offset with
  | IndexOffset (_, _, NoOffset) -> true
  | IndexOffset (_, _, suboffset) -> is_index_offset suboffset
  | ConstantOffset (_, suboffset) -> is_index_offset suboffset
  | FieldOffset (_, suboffset) -> is_index_offset suboffset
  | _ -> false


let get_index_offset_variables (offset: memory_offset_t): variable_t list =
  let rec aux (o: memory_offset_t) (vlst: variable_t list) =
    match o with
    | IndexOffset (v, _, suboffset) -> aux suboffset (v :: vlst)
    | ArrayIndexOffset (x, suboffset) ->
       aux suboffset ((Xprt.variables_in_expr x) @ vlst)
    | ConstantOffset (_, suboffset)
      | FieldOffset (_, suboffset) -> aux suboffset vlst
    | _ -> vlst in
  aux offset []


let rec get_constant_offsets
          (offset: memory_offset_t): numerical_t list traceresult =
  match offset with
  | NoOffset -> Ok [numerical_zero]
  | ConstantOffset (n, suboffset) ->
     TR.tmap (fun subo -> n :: subo) (get_constant_offsets suboffset)
  | _ ->
     Error [
         __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
         ^ "Offset is not constant: "
         ^ (memory_offset_to_string offset)]


let rec add_offset
      (offset1: memory_offset_t) (offset2: memory_offset_t): memory_offset_t =
  match offset1 with
  | NoOffset -> offset2
  | ConstantOffset (n, o) -> ConstantOffset(n, add_offset o offset2)
  | FieldOffset (f, o) -> FieldOffset (f, add_offset o offset2)
  | IndexOffset (v, i, o) -> IndexOffset (v, i, add_offset o offset2)
  | ArrayIndexOffset (x, o) -> ArrayIndexOffset (x, add_offset o offset2)
  | BasePtrArrayIndexOffset (x, o) ->
     BasePtrArrayIndexOffset (x, add_offset o offset2)
  | UnknownOffset -> UnknownOffset


let get_total_constant_offset (offset: memory_offset_t): numerical_t traceresult =
  TR.tmap
    ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
    (fun nl -> List.fold_left (fun acc n -> acc#add n) numerical_zero nl)
    (get_constant_offsets offset)

let memory_offset_to_pretty offset = STR (memory_offset_to_string offset)

let constant_offset_to_suffix_string n =
  fixed_length_int_string n#toString 4

let constant_offset_to_neg_suffix_string n =
  fixed_length_int_string n#neg#toString 4

let stack_offset_to_name offset =
  match offset with
  | ConstantOffset (n,NoOffset) when n#gt numerical_zero ->
     "arg_" ^ (constant_offset_to_suffix_string n)
  | ConstantOffset (n,NoOffset) when n#lt numerical_zero ->
     "var_" ^ (constant_offset_to_neg_suffix_string n)
  | ConstantOffset (n,NoOffset) when n#equal numerical_zero ->
     "var_0000"
  | NoOffset -> "var_0000"
  | _ -> "var.[" ^ (memory_offset_to_string offset) ^ "]"


let global_offset_to_name (size: int) (offset: memory_offset_t) =
  let prefix =
    match size with
    | 1 -> "gvb_"
    | 2 -> "gvh_"
    | _ -> "gv_" in
  try
    match offset with
    | ConstantOffset (n, s) when n#gt numerical_zero ->
       log_tfold_default
         (mk_tracelog_spec "global_offset_to_name")
         (fun dw ->
           prefix ^ dw#to_hex_string ^ (memory_offset_to_string s))
         ("gv_illegal_address")
         (numerical_to_doubleword n)
    | _ -> prefix ^ (memory_offset_to_string offset)
  with
  | BCH_failure p ->
     raise
       (BCH_failure
          (LBLOCK [STR "global_offset_to_name: "; p]))


let realigned_stack_offset_to_name offset =
  match offset with
  | ConstantOffset (n, NoOffset) when n#gt numerical_zero ->
     begin
       ch_error_log#add "realigned-stack location above zero" n#toPretty ;
       "vrrp." ^ (constant_offset_to_suffix_string n)
     end
  | ConstantOffset (n,NoOffset) when n#leq numerical_zero ->
     "vrr." ^ (constant_offset_to_neg_suffix_string n)
  | _ -> "vrr.[" ^ (memory_offset_to_string offset) ^ "]"


let rec boffset_to_memory_offset
          (boffset: boffset_t): memory_offset_t traceresult =
  match boffset with
  | BCHBCTypes.NoOffset -> Ok BCHLibTypes.NoOffset
  | Field (fuse, suboffset) ->
     tmap
       (fun o -> FieldOffset (fuse, o))
       (boffset_to_memory_offset suboffset)
  | Index (Const (CInt (i64, _, _)), suboffset) ->
     tmap
       (fun o ->
         let x = num_constant_expr (mkNumericalFromInt64 i64) in
         ArrayIndexOffset (x, o))
       (boffset_to_memory_offset suboffset)
  | Index (bexp, _) ->
     Error ["Unable to convert array index expression " ^ (exp_to_string bexp)]


class memory_reference_t
    ~(index: int)
    ~(base: memory_base_t):memory_reference_int =
object (self:'a)

  method index = index

  method compare (other:'a) = Stdlib.compare self#index other#index

  method get_base = base

  method get_name: string =
    match base with
    | BaseVar v -> v#getName#getBaseName
    | BaseArray (x, _) -> (x2s x)
    | BaseStruct (x, _) -> (x2s x)
    | BLocalStackFrame -> "var"
    | BRealignedStackFrame -> "varr"
    | BAllocatedStackFrame -> "vara"
    | BGlobal -> "gv"
    | BaseUnknown s -> "??" ^ s ^ "??"

  method get_type: btype_t option =
    match base with
    | BaseArray (_, ty) -> Some ty
    | BaseStruct (_, ty) -> Some ty
    | _ -> None

  method get_external_base: variable_t traceresult =
    match base with
    | BaseVar v -> Ok v
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Not an external base: "
              ^ (memory_base_to_string base)]

  method get_array_base: (xpr_t * btype_t) traceresult =
    match base with
    | BaseArray (x, t) -> Ok (x, t)
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Not an array base: "
              ^ (memory_base_to_string base)]

  method get_struct_base: (xpr_t * btype_t) traceresult =
    match base with
    | BaseStruct (x, t) -> Ok (x, t)
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Not a struct base: "
              ^ (memory_base_to_string base)]

  method has_external_base =
    match base with BaseVar _ -> true | _ -> false

  method has_array_base =
    match base with BaseArray _ -> true | _ -> false

  method has_struct_base =
    match base with BaseStruct _ -> true | _ -> false

  method is_stack_reference = match base with
    | BLocalStackFrame | BRealignedStackFrame | BAllocatedStackFrame -> true
    | _ -> false

  method is_realigned_stack_reference =
    match base with BRealignedStackFrame -> true | _ -> false

  method is_global_reference = match base with BGlobal -> true | _ -> false

  method is_unknown_reference =
    match base with BaseUnknown _ -> true | _ -> false

  method toPretty = LBLOCK [memory_base_to_pretty base]

end


class memory_reference_manager_t
        (vard:vardictionary_int):memory_reference_manager_int =
object (self)

  val table = H.create 3
  val vard = vard

  method reset = H.clear table

  method private mk_reference (base:memory_base_t) =
    let index = vard#index_memory_base base in
    if H.mem table index then
      H.find table index
    else
      let memref = new memory_reference_t ~index ~base in
      begin
        H.add table index memref;
        memref
      end

  method mk_local_stack_reference = self#mk_reference BLocalStackFrame

  method mk_realigned_stack_reference = self#mk_reference BRealignedStackFrame

  method mk_allocated_stack_reference = self#mk_reference BAllocatedStackFrame

  method mk_global_reference = self#mk_reference BGlobal

  method mk_basevar_reference v = self#mk_reference (BaseVar v)

  method mk_base_array_reference (x: xpr_t) (t: btype_t) =
    self#mk_reference (BaseArray (x, t))

  method mk_base_struct_reference (x: xpr_t) (t: btype_t) =
    self#mk_reference (BaseStruct (x, t))

  method mk_unknown_reference s = self#mk_reference (BaseUnknown s)

  method get_memory_reference (index: int): memory_reference_int traceresult =
    if H.mem table index then
      Ok (H.find table index)
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Memory reference index not found: " ^ (string_of_int index)]

  method get_memory_reference_type (index: int): btype_t option =
    tfold_default
      (fun memref -> memref#get_type)
      None
      (self#get_memory_reference index)

  method is_unknown_reference (index: int): bool traceresult =
    let memref_r = self#get_memory_reference index in
    tmap
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (fun memref -> memref#is_unknown_reference) memref_r

  method is_global_reference (index: int): bool traceresult =
    let memref_r = self#get_memory_reference index in
    tmap
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (fun memref -> memref#is_global_reference) memref_r

  method initialize =
    List.iter (fun (index, base) ->
        H.add table index (new memory_reference_t ~index ~base))
      vard#get_indexed_bases

end

let make_memory_reference_manager = new memory_reference_manager_t
