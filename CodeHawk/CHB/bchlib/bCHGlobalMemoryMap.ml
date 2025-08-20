(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2025  Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHDoubleword
open BCHLibTypes

module H = Hashtbl
module TR = CHTraceResult

let x2p = XprToPretty.xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)

let opti2s (i: int option) =
  if Option.is_some i then string_of_int (Option.get i) else "?"

let ty2s (ty: btype_t) =
  if is_unknown_type ty then "?" else btype_to_string ty
let optty2s (ty: btype_t option) =
  if Option.is_some ty then btype_to_string (Option.get ty) else "?"

let bcd = BCHBCDictionary.bcdictionary


let globalvalue_to_pretty (gv: globalvalue_t): pretty_t =
  match gv with
  | GConstantString s -> STR s
  | GScalarValue dw -> dw#toPretty


let _global_location_ref_to_pretty (gref: global_location_ref_t): pretty_t =
  match gref with
  | GLoad (gaddr, iaddr, gxpr, size, signed) ->
     LBLOCK [
         STR "load: ";
         gaddr#toPretty; STR ", ";
         STR iaddr; STR "  ";
         x2p gxpr;
         STR "  ";
         INT size;
         (if signed then STR " (signed)" else STR "")
       ]
  | GStore (gaddr, iaddr, gxpr, size, _optvalue) ->
     LBLOCK [
         STR "store: ";
         gaddr#toPretty; STR ", ";
         STR iaddr;
         STR "  ";
         x2p gxpr;
         STR "  ";
         INT size]
  | GAddressArgument (gaddr, iaddr, argindex, gxpr, btype, memoff) ->
     LBLOCK [
         STR "addr-arg: ";
         gaddr#toPretty; STR ", ";
         STR iaddr;
         STR " (";
         INT argindex;
         STR ") ";
         x2p gxpr;
         (if is_unknown_type btype then
            STR ""
          else
            LBLOCK [STR "  "; STR (btype_to_string btype)]);
         (match memoff with
          | Some NoOffset -> STR ""
          | Some memoff ->
             LBLOCK [
                 STR " ("; BCHMemoryReference.memory_offset_to_pretty memoff; STR ")"]
          | _ -> STR "")
       ]


let global_location_rec_to_pretty (grec: global_location_rec_t): pretty_t =
  LBLOCK [
      STR "addr: "; grec.gloc_address#toPretty; NL;
      STR "name: "; STR grec.gloc_name; NL;
      STR "type: "; STR (btype_to_string grec.gloc_btype); NL;
      (match grec.gloc_size with
       | Some s -> LBLOCK [STR "size: "; INT s; NL]
       | _ -> STR "");
      (match grec.gloc_initialvalue with
       | Some init -> LBLOCK [STR "init: "; globalvalue_to_pretty init; NL]
       | _ -> STR "");
      (match grec.gloc_desc with
       | Some desc -> LBLOCK [STR "desc: "; STR desc; NL]
       | _ -> STR "");
      (if grec.gloc_is_readonly then LBLOCK [STR "readonly"; NL] else STR "");
      (if grec.gloc_is_initialized then LBLOCK [STR "initialized"; NL] else STR "")
    ]


class global_location_t (grec: global_location_rec_t): global_location_int =
object (self)

  method grec: global_location_rec_t = grec

  method name: string = grec.gloc_name

  method address: doubleword_int = grec.gloc_address

  method btype: btype_t = grec.gloc_btype

  method is_struct: bool =
    match resolve_type self#btype with
    | Ok (TComp _) -> true
    | _ -> false

  method is_array: bool =
    match resolve_type self#btype with
    | Ok (TArray _) -> true
    | _ -> false

  method is_scalar: bool =
    match resolve_type self#btype with
    | Ok ty -> is_scalar ty
    | _ -> false

  method is_typed: bool = not (btype_equal self#btype t_unknown)

  method size: int option = grec.gloc_size

  method is_readonly: bool = grec.gloc_is_readonly

  method is_initialized: bool = grec.gloc_is_initialized

  method is_function_address: bool =
    BCHFunctionData.functions_data#is_function_entry_point self#address

  method contains_address (addr: doubleword_int): bool =
    (self#address#equal addr)
    || (match self#size with
        | Some s ->
           addr#index >= self#address#index
           && addr#index < (self#address#index + s)
        | _ -> false)

  method address_offset (xpr: xpr_t): xpr_t traceresult =
    (* xpr = cterm + remainder
       addroffset = cterm - gaddr
       xpr = addroffset + gaddr + remainder
       xproffset = xpr - gaddr = addroffset + remainder *)
    let cterm = BCHXprUtil.largest_constant_term xpr in
    let remainder = XOp (XMinus, [xpr; num_constant_expr cterm]) in
    let remainder = Xsimplify.simplify_xpr remainder in
    let addr = numerical_mod_to_doubleword cterm in
    let addroffset_r =
      if self#contains_address addr then
        if self#address#equal addr then
          Ok 0
        else
          Ok (addr#index - self#address#index)
      else
        Error [
            __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
            ^ "largest constant term: "
            ^ addr#to_hex_string
            ^ " not known to be part of this location ("
            ^ self#address#to_hex_string
            ^ ":"
            ^ self#name
            ^ ")"] in
    tmap
      (fun offset ->
        Xsimplify.simplify_xpr (XOp (XPlus, [remainder; int_constant_expr offset])))
      (addroffset_r)

  method private get_field_memory_offset_at
                   ~(tgtsize: int option)
                   ~(tgtbtype: btype_t option)
                   (loc: location_int)
                   (c: bcompinfo_t)
                   (xoffset: xpr_t): memory_offset_t traceresult =
    let _ =
      log_diagnostics_result
        ~msg:(p2s loc#toPretty)
        ~tag:"global:get-field-memory-offset-at"
        __FILE__ __LINE__
        ["tgtsize: " ^ (opti2s tgtsize);
         "tgtbtype: " ^ (optty2s tgtbtype);
         "compinfo: " ^ c.bcname;
         "xoffset: " ^ (x2s xoffset)] in
    let is_void_tgtbtype =
      match tgtbtype with
      | Some (TVoid _) -> true
      | _ -> false in
    let check_tgttype_compliance (t: btype_t) (s: int) =
      match tgtsize, tgtbtype with
      | None, None -> true
      | Some size, None -> size = s
      | Some size, Some (TVoid _) -> size = s
      | None, Some (TVoid _) -> true
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
             (* Error has been detected earlier *)
             | Error e -> Error e
             (* Result has already been determined *)
             | Ok (Some _) -> acc_r
             (* Still looking for a result *)
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
                     tbind
                       (fun fldtype ->
                         if offset = 0 && is_void_tgtbtype then
                           Ok (Some (FieldOffset
                                       ((finfo.bfname, finfo.bfckey), NoOffset)))
                         else if offset = 0
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
                             tmap
                               (fun suboff ->
                                 Some (FieldOffset
                                         ((finfo.bfname, finfo.bfckey), suboff)))
                               (self#structvar_memory_offset
                                  ~tgtsize
                                  ~tgtbtype
                                  loc
                                  fldtype
                                  (int_constant_expr offset))
                           else if is_array_type fldtype then
                             tmap
                               (fun suboff ->
                                 Some (FieldOffset
                                         ((finfo.bfname, finfo.bfckey), suboff)))
                               (self#arrayvar_memory_offset
                                  ~tgtsize
                                  ~tgtbtype
                                  loc
                                  fldtype
                                  (int_constant_expr offset))
                           else
                             Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                                    ^ "Nonzero offset: " ^ (string_of_int offset)
                                    ^ " with unstructured field type: "
                                    ^ (btype_to_string fldtype)])
                       (resolve_type finfo.bftype)) (Ok None) finfos in
       (match optfield_r with
        | Error e -> Error e
        | Ok (Some offset) -> Ok offset
        | Ok None ->
           Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                  ^ "Unable to find field at offset " ^ (string_of_int offset)])
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
              ^ "Unable to determine field for xoffset: " ^ (x2s xoffset)]

  method private structvar_memory_offset
                   ~(tgtsize: int option)
                   ~(tgtbtype: btype_t option)
                   (loc: location_int)
                   (btype: btype_t)
                   (xoffset: xpr_t): memory_offset_t traceresult =
    let _ =
      log_diagnostics_result
        ~msg:(p2s loc#toPretty)
        ~tag:"mmap:structvar-memory-offset"
        __FILE__ __LINE__
        ["tgtsize: " ^ (opti2s tgtsize);
         "tgtbtype: " ^ (optty2s tgtbtype);
         "btype: " ^ (btype_to_string btype);
         "xoffset: " ^ (x2s xoffset)] in
    match xoffset with
    | XConst (IntConst n) when
           n#equal CHNumerical.numerical_zero
           && Option.is_none tgtsize
           && Option.is_none tgtbtype ->
       Ok NoOffset
    | XConst (IntConst _) ->
       if is_struct_type btype then
         let compinfo = get_struct_type_compinfo btype in
         (self#get_field_memory_offset_at ~tgtsize ~tgtbtype loc compinfo xoffset)
       else
         Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
                ^ " xoffset: " ^ (x2s xoffset)
                ^ "; btype: " ^ (btype_to_string btype)]
    | XOp (XPlus, [XOp (XMult, [XConst (IntConst n); XVar v]);
                   XConst (IntConst m)]) when is_struct_type btype ->
       let compinfo = get_struct_type_compinfo btype in
       let fldoffset = XConst (IntConst m) in
       let memoffset_r =
         self#get_field_memory_offset_at
           ~tgtsize:None ~tgtbtype:None loc compinfo fldoffset in
       TR.tbind
         (fun memoffset ->
           match memoffset with
           | FieldOffset ((fname, fckey), NoOffset) ->
              let fcinfo = get_compinfo_by_key fckey in
              let field = get_compinfo_field fcinfo fname in
              let fieldtype = field.bftype in
              if is_array_type fieldtype then
                let eltype = get_element_type fieldtype in
                let elsize_r = size_of_btype eltype in
                TR.tbind
                  (fun elsize ->
                    if elsize = n#toInt then
                      let aoffset = ArrayIndexOffset (XVar v, NoOffset) in
                      let moffset =
                        BCHMemoryReference.add_offset memoffset aoffset in
                      Ok moffset
                    else
                      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
                             ^ "field: " ^ fname
                             ^ "; fieldtype: " ^ (btype_to_string fieldtype)
                             ^ "; elementsize: " ^ (string_of_int elsize)
                             ^ "; expected: " ^ n#toString])
                  elsize_r
              else
                Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                       ^ "not an array type"]
           | _ ->
              Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
                     ^ "fldoffset: " ^ (x2s fldoffset)
                     ^ "; memoffset: "
                     ^ (BCHMemoryReference.memory_offset_to_string memoffset)])
         memoffset_r

    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
                ^ " xoffset: " ^ (x2s xoffset)
                ^ "; btype: " ^ (btype_to_string btype)]

  method private arrayvar_memory_offset
                   ~(tgtsize: int option)
                   ~(tgtbtype: btype_t option)
                   (loc: location_int)
                   (btype: btype_t)
                   (xoffset: xpr_t): memory_offset_t traceresult =
    let _ =
      log_diagnostics_result
        ~msg:(p2s loc#toPretty)
        ~tag:"mmap:arrayvar-memory-offset"
        __FILE__ __LINE__
        ["tgtsize: " ^ (opti2s tgtsize);
         "tgtbtype: " ^ (optty2s tgtbtype);
         "btype: " ^ (btype_to_string btype);
         "xoffset: " ^ (x2s xoffset)] in
    let iszero x =
      match x with
      | XConst (IntConst n) -> n#equal CHNumerical.numerical_zero
      | _ -> false in
    match xoffset with
    | XConst (IntConst n) when
           n#equal CHNumerical.numerical_zero
           && Option.is_none tgtsize
           && Option.is_none tgtbtype ->
       Ok NoOffset
    | _ ->
       if is_array_type btype then
         let eltty = get_element_type btype in
         tbind
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
                  tbind
                    (fun suboff -> Ok (ArrayIndexOffset (indexxpr, suboff)))
                    (self#structvar_memory_offset ~tgtsize ~tgtbtype loc eltty rem)
                else if is_array_type eltty then
                 tbind
                   (fun suboff -> Ok (ArrayIndexOffset (indexxpr, suboff)))
                   (self#arrayvar_memory_offset ~tgtsize ~tgtbtype loc eltty rem)
                else if is_scalar eltty then
                  if iszero rem then
                    Ok (ArrayIndexOffset (indexxpr, NoOffset))
                  else
                    let suboff =
                      let x2index = XOp (XDiv, [rem; int_constant_expr elsize]) in
                      let x2index = Xsimplify.simplify_xpr x2index in
                      ArrayIndexOffset (x2index, NoOffset) in
                    Ok (ArrayIndexOffset (indexxpr, suboff))
                else
                  Error[__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
                        ^ "xoffset: " ^ (x2s xoffset)
                        ^ "; btype: " ^ (btype_to_string btype)
                        ^ "; elementtype: " ^ (btype_to_string eltty)])
           (size_of_btype eltty)
       else
         Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
                ^ "xoffset: " ^ (x2s xoffset)
                ^ "; btype: " ^ (btype_to_string btype)]

  method address_offset_memory_offset
           ?(tgtsize=None)
           ?(tgtbtype=t_unknown)
           (loc: location_int)
           (xoffset: xpr_t): memory_offset_t traceresult =
    let _ =
      log_diagnostics_result
        ~msg:(p2s loc#toPretty)
        ~tag:"mmap:address-offset-memory-offset"
        __FILE__ __LINE__
        ["xoffset: " ^ (x2s xoffset)
         ^ "; tgtsize: " ^ (opti2s tgtsize)
         ^ "; tgtbtype: " ^ (ty2s tgtbtype)] in
    match xoffset with
    | XConst (IntConst n)
         when n#equal CHNumerical.numerical_zero
              && Option.is_none tgtsize
              && is_unknown_type tgtbtype ->
       Ok NoOffset
    | XConst (IntConst n)
         when n#equal CHNumerical.numerical_zero && (not self#is_typed) ->
       Ok NoOffset
    | XConst (IntConst n)
         when n#equal CHNumerical.numerical_zero
              && self#is_scalar
              && Option.is_some tgtsize
              && Option.is_some self#size
              && (Option.get tgtsize) = (Option.get self#size) ->
       Ok NoOffset
    | XConst (IntConst n) when not self#is_typed ->
       Ok (ConstantOffset (n, NoOffset))
    | _ ->
       let tgtbtype =
         if is_unknown_type tgtbtype then None else Some tgtbtype in
       if self#is_struct then
         let btype = TR.tvalue (resolve_type self#btype) ~default:t_unknown in
         self#structvar_memory_offset ~tgtsize ~tgtbtype loc btype xoffset
       else if self#is_array then
         let btype = TR.tvalue (resolve_type self#btype) ~default:t_unknown in
         self#arrayvar_memory_offset ~tgtsize ~tgtbtype loc btype xoffset
       else
         Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ":"
                ^ (btype_to_string self#btype)
                ^ " is not known to be a struct or array"]

  method address_memory_offset
           ?(tgtsize=None)
           ?(tgtbtype=t_unknown)
           (loc: location_int)
           (xpr: xpr_t): memory_offset_t traceresult =
    TR.tbind
      (self#address_offset_memory_offset ~tgtsize ~tgtbtype loc)
      (self#address_offset xpr)

  method initialvalue: globalvalue_t option = grec.gloc_initialvalue

  method desc: string option = grec.gloc_desc

  method has_elf_symbol: bool =
    match self#desc with
    | Some "symbol-table" -> true
    | _ -> false

  method write_xml (node: xml_element_int) =
    begin
      (if is_known_type self#btype then
         node#setIntAttribute "tix" (bcd#index_typ self#btype));
      (match self#size with
       | Some s -> node#setIntAttribute "size" s
       | _ -> ())
    end

end


class global_memory_map_t: global_memory_map_int =
object (self)

  val locations = H.create 51             (* gaddr#ix -> gloc *)
  val locreferences = H.create 51         (* faddr#ix -> gref list *)
  val namedlocations = H.create 51        (* name -> ix *)
  val unconnectedreferences = H.create 51 (* faddr#ix -> gref list *)
  val sections = H.create 5

  method set_section
           ~(readonly: bool)
           ~(initialized: bool)
           (name: string)
           (addr: doubleword_int)
           (size: doubleword_int) =
    let _ =
      chlog#add
        "globalmemorymap:set_section"
        (LBLOCK [
             STR name;
             STR ": @";
             addr#toPretty;
             STR " (";
             size#toPretty;
             STR " bytes)"]) in
    H.add sections addr#value (name, size#value, readonly, initialized)

  method private is_initialized (addr: doubleword_int): bool =
    H.fold (fun k (_, size, _, initialized) acc ->
        if k <= addr#value && addr#value < (k + size) then
          initialized
        else
          acc) sections false

  method private is_readonly (addr: doubleword_int): bool =
    H.fold (fun k (_, size, readonly, _) acc ->
        if k <= addr#value && addr#value < (k + size) then
          readonly
        else
          acc) sections false

  method private get_section_name (addr: doubleword_int): string option =
    H.fold (fun k (name, size, _, _) acc ->
        if k <= addr#value && addr#value < (k + size) then
          Some name
        else
          acc) sections None

  method add_location
           ?(name = None)
           ?(desc = None)
           ?(btype = t_unknown)
           ?(initialvalue = None)
           ?(size = None)
           (address: doubleword_int): global_location_int traceresult =
    if address#lt (TR.tget_ok (BCHDoubleword.int_to_doubleword 20)) then
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Illegal global address: " ^ address#to_hex_string]
    else if H.mem locations address#index then
      begin
        log_error_result
          ~tag:"duplicate global location"
          ~msg:("Global location at address "
                ^ address#to_hex_string
                ^ "already exists")
          __FILE__ __LINE__ [];
        Ok (H.find locations address#index)
      end
    else
      match self#containing_location address with
      | Some gloc ->
         let msg =
           "Global location at address "
           ^ address#to_hex_string
           ^ " overlaps with "
           ^ gloc#name
           ^ " ("
           ^ gloc#address#to_hex_string
           ^ (match gloc#size with
              | Some s -> ", size: " ^ (string_of_int s)
              | _ -> "")
           ^ ")" in
         begin
           ch_error_log#add "overlapping global location" (STR msg);
           Error [msg]
         end
      | _ ->
         let gname =
           match name with
           | Some name -> name
           | _ -> "gv_" ^ address#to_hex_string in
         let is_readonly = self#is_readonly address in
         let is_initialized = self#is_initialized address in
         let section = self#get_section_name address in
         let grec = {
             gloc_name = gname;
             gloc_address = address;
             gloc_is_readonly = is_readonly;
             gloc_is_initialized = is_initialized;
             gloc_section = section;
             gloc_btype = btype;
             gloc_initialvalue = initialvalue;
             gloc_size = size;
             gloc_desc = desc
           } in
         let gloc = new global_location_t grec in
         begin
           H.add locations address#index gloc;
           H.add namedlocations gname address#index;
           chlog#add
             "global-memory-map:add-location"
             (LBLOCK [
                  address#toPretty;
                  STR ": ";
                  STR gname;
                  STR ":";
                  STR (btype_to_string btype);
                  STR "; ";
                  (match size with
                   | Some s -> LBLOCK [STR " (size: "; INT s; STR ")"]
                   | _ -> STR "");
                  (match section with
                   | Some name -> LBLOCK [STR " ("; STR name; STR ")"]
                   | _ -> STR "");
                  (if is_readonly then STR " (RO) " else STR "");
                  (if is_initialized then STR " (IV) " else STR "");
                  (match desc with
                   | Some desc -> LBLOCK [STR " ("; STR desc; STR ")"]
                   | _ -> STR "")
             ]);
           Ok gloc
         end

  method private add_global_ref
                   (faddr: doubleword_int) (gref: global_location_ref_t) =
    let entry =
      if H.mem locreferences faddr#index then
        H.find locreferences faddr#index
      else
        [] in
    H.replace locreferences faddr#index (gref :: entry)

  method private add_unconnected_ref
                   (faddr: doubleword_int) (gref: global_location_ref_t) =
    let entry =
      if H.mem unconnectedreferences faddr#index then
        H.find unconnectedreferences faddr#index
      else
        [] in
    H.replace unconnectedreferences faddr#index (gref :: entry)

  method add_gload
           (faddr: doubleword_int)
           (iaddr: ctxt_iaddress_t)
           (gxpr: xpr_t)
           (size: int)
           (signed: bool) =
    match self#xpr_containing_location gxpr with
    | Some gloc ->
       let gload = GLoad (gloc#address, iaddr, gxpr, size, signed) in
       self#add_global_ref faddr gload
    | _ ->
       (match gxpr with
        | XConst (IntConst n) ->
           let gaddr = numerical_mod_to_doubleword n in
           let gload = GLoad (gaddr, iaddr, gxpr, size, signed) in
           self#add_unconnected_ref faddr gload
        | _ ->
           ())

  method add_gstore
           (faddr: doubleword_int)
           (iaddr: ctxt_iaddress_t)
           (gxpr: xpr_t)
           (size: int)
           (optvalue: CHNumerical.numerical_t option) =
    match self#xpr_containing_location gxpr with
    | Some gloc ->
       let gstore = GStore (gloc#address, iaddr, gxpr, size, optvalue) in
       self#add_global_ref faddr gstore
    | _ ->
       (match gxpr with
        | XConst (IntConst n) ->
           let gaddr = numerical_mod_to_doubleword n in
           let gstore = GStore (gaddr, iaddr, gxpr, size, optvalue) in
           self#add_unconnected_ref faddr gstore
        | _ -> ())

  method add_gaddr_argument
           (faddr: doubleword_int)
           (iaddr: ctxt_iaddress_t)
           (gxpr: xpr_t)
           (argindex: int)
           (btype: btype_t) =
    match self#xpr_containing_location gxpr with
    | Some gloc ->
       let loc = BCHLocation.ctxt_string_to_location faddr iaddr in
       let memoff = TR.to_option (gloc#address_memory_offset loc gxpr) in
       let garg =
         GAddressArgument (gloc#address, iaddr, argindex, gxpr, btype, memoff) in
       begin
         self#add_global_ref faddr garg;
         Some gloc
       end
    | _ ->
       (match gxpr with
        | XConst (IntConst n) ->
           let gaddr = numerical_mod_to_doubleword n in
           let garg =
             GAddressArgument (gaddr, iaddr, argindex, gxpr, btype, Some NoOffset) in
           begin
             self#add_unconnected_ref faddr garg;
             None
           end
        | _ -> None)

  method update_named_location
           (name: string) (vinfo: bvarinfo_t): global_location_int traceresult =
    if self#has_location_with_name name then
      let ix = H.find namedlocations name in
      let grec = (H.find locations ix)#grec in
      let size = TR.to_option (size_of_btype vinfo.bvtype) in
      let newgrec = {
          grec with
          gloc_btype = vinfo.bvtype;
          gloc_size = size
        } in
      let newgloc = new global_location_t newgrec in
      begin
        H.replace locations ix newgloc;
        chlog#add
          "global-memory-map:update-location"
          (LBLOCK [
               newgrec.gloc_address#toPretty;
               STR ": ";
               STR newgrec.gloc_name;
               STR ":";
               STR (btype_to_string newgrec.gloc_btype);
               (match size with
                | Some s -> LBLOCK [STR " (size: "; INT s; STR ")"]
                | _ -> STR "")
          ]);
        Ok newgloc
      end
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "No location found with name " ^ name ^ " in global memory map"]

  method has_location_with_name (name: string) = H.mem namedlocations name

  method has_location (addr: doubleword_int) = H.mem locations addr#index

  method containing_location (addr: doubleword_int): global_location_int option =
    H.fold (fun _ gloc acc ->
        match acc with
        | Some _ -> acc
        | _ -> if gloc#contains_address addr then Some gloc else None)
      locations None

  method xpr_containing_location (xpr: xpr_t): global_location_int option =
    let cterm = BCHXprUtil.largest_constant_term xpr in
    let addr = numerical_mod_to_doubleword cterm in
    self#containing_location addr

  method get_location (addr: doubleword_int): global_location_int =
    if self#has_location addr then
      H.find locations addr#index
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No location found at address "; addr#toPretty]))

  method get_location_name (addr: doubleword_int): string =
    (self#get_location addr)#name

  method get_location_type (addr: doubleword_int): btype_t =
    (self#get_location addr)#btype

  method is_global_data_address (addr: doubleword_int): bool =
    H.fold (fun k (_, size, _, _) acc ->
        if k <= addr#value && addr#value < (k + size) then
          true
        else
          acc) sections false

  method has_elf_symbol (v: doubleword_int): bool =
    (H.mem locations v#index)
    && (H.find locations v#index)#has_elf_symbol

  method get_elf_symbol (v: doubleword_int): string =
    if self#has_elf_symbol v then
      (H.find locations v#index)#name
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Memory location at ";
                v#toPretty;
                STR " does not have an elf symbol"]))

  method private write_xml_gref
                   (vard: vardictionary_int)
                   (node: xml_element_int)
                   (gref: global_location_ref_t) =
    let xd = vard#xd in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let set_size (s: int) = seti "s" s in
    let set_gxpr (xpr: xpr_t) = seti "xix" (xd#index_xpr xpr) in
    let set_gaddr (a: doubleword_int) = set "g" a#to_hex_string in
    let set_iaddr (a: ctxt_iaddress_t) = set "i" a in
    let set_btype (t: btype_t) =
      if is_known_type t then seti "tix" (bcd#index_typ t) else () in
    let set_memoff (o: memory_offset_t option) =
      match o with
      | Some off -> seti "mix" (vard#index_memory_offset off)
      | _ -> () in
    match gref with
    | GLoad (gaddr, iaddr, gxpr, size, signed) ->
       begin
         set "t" "L";
         set_gaddr gaddr;
         set_gxpr gxpr;
         set_iaddr iaddr;
         set_size size;
         (if signed then set "sg" "yes")
       end
    | GStore (gaddr, iaddr, gxpr, size, optvalue) ->
       begin
         set "t" "S";
         set_gaddr gaddr;
         set_gxpr gxpr;
         set_iaddr iaddr;
         set_size size;
         (match optvalue with
          | Some n -> set "v" n#toString
          | _ -> ())
       end
    | GAddressArgument (gaddr, iaddr, argindex, gxpr, btype, memoff) ->
       begin
         set "t" "CA";
         set_gaddr gaddr;
         seti "aix" argindex;
         set_gxpr gxpr;
         set_iaddr iaddr;
         set_btype btype;
         set_memoff memoff
       end

  method write_xml_references
           (faddr: doubleword_int) (vard: vardictionary_int) (node: xml_element_int) =
    let xlocrefs = xmlElement "location-references" in
    let xunconnected = xmlElement "unconnected-references" in
    let locrefs =
      if H.mem locreferences faddr#index then
        H.find locreferences faddr#index
      else
        [] in
    let unconnectedrefs =
      if H.mem unconnectedreferences faddr#index then
        H.find unconnectedreferences faddr#index
      else
        [] in
    begin
      List.iter (fun gref ->
          let vnode = xmlElement "gref" in
          begin
            self#write_xml_gref vard vnode gref;
            xlocrefs#appendChildren [vnode]
          end) locrefs;
      List.iter (fun gref ->
          let vnode = xmlElement "gref" in
          begin
            self#write_xml_gref vard vnode gref;
            xunconnected#appendChildren [vnode]
          end) unconnectedrefs;
      node#appendChildren [xlocrefs; xunconnected]
    end

  method write_xml (node: xml_element_int) =
    let secnode = xmlElement "sections" in
    let locnode = xmlElement "locations" in
    begin
      (* record sections *)
      H.iter (fun ix (name, size, ro, init) ->
          let vnode = xmlElement "sec" in
          begin
            vnode#setAttribute
              "a" (TR.tget_ok (index_to_doubleword ix))#to_hex_string;
            vnode#setAttribute "name" name;
            vnode#setIntAttribute "size" size;
            (if ro then vnode#setAttribute "ro" "yes");
            (if init then vnode#setAttribute "init" "yes");
            secnode#appendChildren [vnode]
          end) sections;

      (* record locations *)
      H.iter (fun _ gloc ->
          let vnode = xmlElement "gloc" in
          begin
            vnode#setAttribute "a" gloc#address#to_hex_string;
            vnode#setAttribute "name" gloc#name;
            gloc#write_xml vnode;
            locnode#appendChildren [vnode]
          end) locations;
      node#appendChildren [secnode; locnode]
    end

end


let global_memory_map = new global_memory_map_t


let read_xml_symbolic_addresses (node: xml_element_int) =
  let get = node#getAttribute in
  let getx t =
    let tx = get t in
    fail_tvalue
      (trerror_record
         (STR ("BCHGlobalMemory.read_xml_symbolic_addresses:" ^ tx)))
      (string_to_doubleword tx) in
  let name = Some (get "name") in
  let address = getx "a" in
  ignore (global_memory_map#add_location ~name ~desc:(Some "userdata") address)


let read_xml_symbolic_addresses (node: xml_element_int) =
  List.iter read_xml_symbolic_addresses (node#getTaggedChildren "syma")


let update_global_location_type
      (vinfo: bvarinfo_t): global_location_int traceresult =
  let name = vinfo.bvname in
  let mkerror file line =
    let msg =
      file ^ ":" ^ (string_of_int line) ^ ": "
      ^"global location not updated for " ^ name in
    Error [msg] in
  if global_memory_map#has_location_with_name name then
    global_memory_map#update_named_location name vinfo
  else if String.length name > 3 && (String.sub name 0 3) = "gv_" then
    let index = String.index name '_' in
    if String.contains_from name (index + 1) '_' then
      let eindex = String.index_from name (index + 1) '_' in
      let hex = String.sub name (index + 1) ((eindex - index) - 1) in
      let hex = "0x" ^ hex in
      let msg =
        __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
        ^ "Address " ^ hex ^ " in global variable " ^ name ^ " not recognized" in
      TR.tbind
        ~msg
        (fun dw ->
          global_memory_map#add_location
            ~name:(Some name)
            ~desc:(Some "header file")
            ~btype: vinfo.bvtype
            ~size:(TR.to_option (size_of_btype vinfo.bvtype))
            dw)
        (string_to_doubleword hex)
    else
      mkerror __FILE__ __LINE__
  else
    mkerror __FILE__ __LINE__
