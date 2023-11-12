(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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

(* Named constants *)

(* chlib *)
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open XprToPretty
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHBCTypeXml
open BCHDoubleword
open BCHLibTypes
open BCHTypeDefinitions

module H = Hashtbl
module TR = CHTraceResult


let value_table = H.create 3  (* dw#index -> constant definition list *)
let flag_table = H.create 3
let address_table = H.create 3  (* to be deleted *)
let name_table = H.create 3  (* string -> constant definition list *)

let x2p = xpr_formatter#pr_expr

let bcd = BCHBCDictionary.bcdictionary


(* Note: constants and flags must still be added to the data structure
   for full integration. *)


class symbolic_addresses_t =
object (self)

  val address_table = H.create 3    (* dw#index -> constant_definition_t *)
  val addrname_table = H.create 3     (* name -> constant_definition_t *)
  val globalstructvars = H.create 3   (* dw#index -> length *)
  val globalarrayvars = H.create 3    (* dw#index -> length *)

  method add_address (a: constant_definition_t) =
    let index = a.xconst_value#index in
    let name = a.xconst_name in
    begin
      H.replace address_table index a;
      H.replace addrname_table name a;
      self#update_structured_var a
    end

  method is_in_structvar (dw: doubleword_int): bool =
    let dwindex = dw#index in
    H.fold (fun k v acc ->
        if acc then
          acc
        else
          if (dwindex >= k) && (dwindex < k + v) then
            true
          else
            acc) globalstructvars false

  method is_in_arrayvar (dw: doubleword_int): bool =
    let dwindex = dw#index in
    H.fold (fun k v acc ->
        if acc then
          acc
        else
          if (dwindex >= k) && (dwindex < k + v) then
            true
          else
            acc) globalarrayvars false

  method private get_fieldoffset_at
                   (c: bcompinfo_t) (offset: int):(boffset_t * int) =
    let finfos = c.bcfields in
    let fld0 = List.hd finfos in
    if offset = 0 then
      (Field ((fld0.bfname, fld0.bfckey), NoOffset), 0)
    else if offset < (size_of_btype fld0.bftype) then
      (* offset is within the first field *)
      match bcfiles#resolve_type fld0.bftype with
      | TComp (ffkey, _) ->
         let fcompinfo = bcfiles#get_compinfo ffkey in
         let (bboffset, rem) =
           self#get_fieldoffset_at fcompinfo offset in
         (Field ((fld0.bfname, fld0.bfckey), bboffset), rem)
      | ty when is_scalar ty && (size_of_btype ty) = offset ->
         (Field ((fld0.bfname, fld0.bfckey), NoOffset), 0)
      | _ ->
         let _ =
           chlog#add
             "get_fieldoffset_at"
             (LBLOCK
                [STR "compinfo: "; STR c.bcname; STR "; offset: "; INT offset]) in
         (Field ((fld0.bfname, fld0.bfckey), NoOffset), offset)
    else
      let optfield =
        List.fold_left (fun acc finfo ->
            match acc with
            | Some _ -> acc
            | _ ->
               match finfo.bfieldlayout with
               | Some (foffset, size) ->
                  if offset = foffset then
                    Some (Field ((finfo.bfname, finfo.bfckey), NoOffset), 0)
                  else if offset > foffset && offset < offset + size then
                    match bcfiles#resolve_type finfo.bftype with
                    | TComp (ffkey, _) ->
                       let fcompinfo = bcfiles#get_compinfo ffkey in
                       let (bboffset, rem) =
                         self#get_fieldoffset_at fcompinfo (offset - foffset) in
                       Some (Field ((finfo.bfname, finfo.bfckey), bboffset), rem)
                    | ty when is_scalar ty && (size_of_btype ty) = offset ->
                       Some (Field ((finfo.bfname, finfo.bfckey), NoOffset), 0)
                    | _ ->
                       Some (Field ((finfo.bfname, finfo.bfckey), NoOffset),
                             offset - foffset)
                  else
                    acc
               | _ ->
                  acc) None (List.tl finfos) in
      match optfield with
      | Some (offset, rem) -> (offset, rem)
      | _ -> (NoOffset, offset)


  method get_structvar_base_offset
           (dw: doubleword_int):(doubleword_int * boffset_t) option =
    if self#is_in_structvar dw then
      let dwindex = dw#index in
      let optdwoffset =
        H.fold (fun k v acc ->
            match acc with
            | Some _ -> acc
            | _ ->
               if (dwindex >= k) && (dwindex < k + v) then
                 Some (k, dwindex - k)
               else
                 acc) globalstructvars None in
      match optdwoffset with
      | Some (base, dwoffset) ->
         if H.mem address_table base then
           let constdef = H.find address_table base in
           (match bcfiles#resolve_type constdef.xconst_type with
            | TComp (key, _) ->
               let compinfo = bcfiles#get_compinfo key in
               let (offset, rem) = self#get_fieldoffset_at compinfo dwoffset in
               if rem = 0 then
                 Some (TR.tget_ok (int_to_doubleword base), offset)
               else
                 None
            | _ ->
               None)
         else
           None
      | _ ->
         None
    else
      None

  method get_arrayvar_base_offset
           (dw: doubleword_int):(doubleword_int * boffset_t) option =
    if self#is_in_arrayvar dw then
      let dwindex = dw#index in
      let optdwoffset =
        H.fold (fun k v acc ->
            match acc with
            | Some _ -> acc
            | _ ->
               if (dwindex >= k) && (dwindex < k + v) then
                 Some (k, dwindex - k)
               else
                 acc) globalarrayvars None in
      match optdwoffset with
      | Some (base, dwoffset) ->
         if H.mem address_table base then
           let constdef = H.find address_table base in
           (match bcfiles#resolve_type constdef.xconst_type with
            | TArray (ty, optlen, _) ->
               let elsize = size_of_btype ty in
               if elsize > 0 then
                 let elindex = dwoffset / elsize in
                 let boffset =
                   Index (Const (CInt (Int64.of_int elindex, IInt, None)), NoOffset) in
                 Some (TR.tget_ok (int_to_doubleword base), boffset)
               else
                 None
            | _ ->
               None)
         else
           None
      | _ -> None
    else
      None

  method private update_structured_var (a: constant_definition_t) =
    match bcfiles#resolve_type a.xconst_type with
    | TComp (key, _) as ty ->
       let compinfo = bcfiles#get_compinfo key in
       let size = size_of_btype ty in
       begin
         H.replace globalstructvars a.xconst_value#index size;
         chlog#add
           "set global structvar size"
           (LBLOCK [
                STR a.xconst_name;
                STR "; ";
                STR a.xconst_value#to_hex_string;
                STR ". ";
                STR compinfo.bcname;
                STR ": ";
                INT size])
       end
    | TArray (ty, optlen, _) ->
       (match optlen with
        | Some (Const (CInt (i64, _, _))) ->
           let arraylen = Int64.to_int i64 in
           let elsize = size_of_btype ty in
           let arraysize = arraylen * elsize in
           begin
             H.replace globalarrayvars a.xconst_value#index arraysize;
             chlog#add
               "set global arrayvar size"
               (LBLOCK [
                    STR a.xconst_name;
                    STR "; ";
                    STR a.xconst_value#to_hex_string;
                    STR ". ";
                    STR "length: ";
                    INT arraylen;
                    STR "; size: ";
                    INT arraysize])
           end
        | _ ->
           chlog#add
             "global array without length"
             (LBLOCK [
                  STR a.xconst_name;
                  STR "; ";
                  STR a.xconst_value#to_hex_string;
                  STR "."]))
    | _ ->
       ()

  method has_symbolic_address_name (v: doubleword_int) =
    H.mem address_table v#index

  method has_symbolic_address (name: string): bool =
    H.mem addrname_table name

  method get_symbolic_address (name: string): doubleword_int =
    if H.mem addrname_table name then
      (H.find addrname_table name).xconst_value
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No symbolic address found for name: "; STR name]))

  method get_untyped_symbolic_address_names: string list =
    H.fold (fun k v a ->
        if is_unknown_type v.xconst_type then k::a else a) addrname_table []

  method update_symbolic_address_btype (name: string) (t: btype_t) =
    if self#has_symbolic_address name then
      let c = H.find addrname_table name in
      if is_unknown_type c.xconst_type then
        let new_c = {c with xconst_type = t} in
        begin
          H.replace addrname_table name new_c;
          H.replace address_table c.xconst_value#index new_c;
          self#update_structured_var new_c
        end
      else
        let c = H.find addrname_table name in
        chlog#add
          "update-symbolic-address-btype"
          (LBLOCK [
               STR "No update for ";
               STR name;
               STR " with type: ";
               STR (btype_to_string t);
               STR ". Keep existing type: ";
               STR (btype_to_string c.xconst_type)])
    else
      ch_error_log#add
        "update-symbolic-address-btype"
        (LBLOCK [STR "No update for ";
                 STR name;
                 STR " with type ";
                 STR (btype_to_string t);
                 STR ". Name not found"])

  method get_symbolic_address_name (v: doubleword_int) =
    if H.mem address_table v#index then
      (H.find address_table v#index).xconst_name
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No symbolic address name found for "; v#toPretty]))

  method get_symbolic_address_type (v: doubleword_int) =
    if H.mem address_table v#index then
      (H.find address_table v#index).xconst_type
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No symbolic address type found for "; v#toPretty]))

end

let symbolic_addresses = new symbolic_addresses_t

let is_in_global_structvar (v: doubleword_int) =
  symbolic_addresses#is_in_structvar v


let get_structvar_base_offset (v: doubleword_int) =
  symbolic_addresses#get_structvar_base_offset v


let is_in_global_arrayvar (v: doubleword_int) =
  symbolic_addresses#is_in_arrayvar v


let get_arrayvar_base_offset (v: doubleword_int) =
  symbolic_addresses#get_arrayvar_base_offset v


let has_symbolic_address_name (v: doubleword_int) =
  symbolic_addresses#has_symbolic_address_name v


let has_symbolic_address (name: string): bool =
  symbolic_addresses#has_symbolic_address name


let get_symbolic_address (name: string): doubleword_int =
  symbolic_addresses#get_symbolic_address name


let get_untyped_symbolic_address_names (): string list =
  symbolic_addresses#get_untyped_symbolic_address_names


let update_symbolic_address_btype (name: string) (t: btype_t) =
  symbolic_addresses#update_symbolic_address_btype name t


let btype_equal (t1: btype_t) (t2: btype_t) =
  let i1 = bcd#index_typ t1 in
  let i2 = bcd#index_typ t2 in
  i1 = i2


let get_symbolic_address_name (v: doubleword_int) =
  symbolic_addresses#get_symbolic_address_name v


let get_symbolic_address_type (v: doubleword_int) =
  symbolic_addresses#get_symbolic_address_type v


let has_symbolic_name ?(ty=None) (v: doubleword_int) =
  if H.mem value_table v#index then
    match ty with
    | Some t -> List.exists (fun c -> btype_equal c.xconst_type t)
      (H.find value_table v#index)
    | _ -> false
  else if H.mem address_table v#index then
    match ty with
    | Some t -> List.exists (fun c -> btype_equal c.xconst_type t)
      (H.find address_table v#index)
    | _ -> false
  else
    false


let get_symbolic_name ?(ty=None) (v: doubleword_int) =
  if H.mem value_table v#index then
    match ty with
    | Some t ->
      (try
	 (List.find (fun c -> btype_equal c.xconst_type t)
	    (H.find value_table v#index)).xconst_name
       with
	 Not_found ->
	 raise
           (BCH_failure
              (LBLOCK [
                   STR "No symbolic constant of type ";
                   btype_to_pretty t;
		   STR " found for ";
                   v#toPretty])))
    | _ -> (List.hd (H.find value_table v#index)).xconst_name
  else if H.mem address_table v#index then
    match ty with
    | Some t ->
      (try
	 (List.find (fun c -> btype_equal c.xconst_type t)
	    (H.find address_table v#index)).xconst_name
       with
	 Not_found ->
	 raise
           (BCH_failure
              (LBLOCK [
                   STR "No symbolic address of type ";
                   btype_to_pretty t;
		   STR " found for ";
                   v#toPretty])))
    | _ -> (List.hd (H.find address_table v#index)).xconst_name
  else
    raise
      (BCH_failure
         (LBLOCK [
              STR "No symbolic constant or address found for "; v#toPretty]))


let has_constant_value ?(ty=None) (name: string) =
  if H.mem name_table name then
    match ty with
    | Some t -> List.exists (fun c -> btype_equal c.xconst_type t)
      (H.find name_table name)
    | _ -> true
  else
    false


let get_constant_value ?(ty=None) (name:string) =
  if H.mem name_table name then
    match ty with
    | Some t ->
      (try
	 (List.find
            (fun c -> c.xconst_name = name)
            (H.find name_table name)).xconst_value
       with
	 Not_found ->
	 raise
           (BCH_failure
              (LBLOCK [
                   STR "No value found of type ";
                   btype_to_pretty t;
		   STR " for symbolic name ";
                   STR name])))
    | _ -> (List.hd (H.find name_table name)).xconst_value
  else
    raise
      (BCH_failure
         (LBLOCK [STR "No value found for symbolic name "; STR name]))


let has_symbolic_flags (ty: btype_t) =
  let typename = btype_to_string ty in H.mem flag_table typename


let get_symbolic_flags (ty:btype_t) (v:doubleword_int) =
  let typename = btype_to_string ty in
  try
    let flags = H.find flag_table typename in
    let vBitsSet = v#get_bits_set in
    List.map (fun pos ->
      try
	let flag =
          List.find (fun f -> f.xflag_pos = pos) flags in flag.xflag_name
      with
	Not_found -> "?pos:" ^ (string_of_int pos)) vBitsSet
  with
    Not_found ->
      raise (BCH_failure (LBLOCK [ STR "No flags found for " ; STR typename ]))


let get_xpr_symbolic_name ?(typespec=None) (xpr: xpr_t) =
  let (ty, flags) =
    match typespec with Some (n,f) -> (Some n,f) | _ -> (None,false) in
  match xpr with
  | XConst (IntConst num) ->
     TR.tfold_default
       (fun v ->
         if has_symbolic_name ~ty v then
           Some (get_symbolic_name ~ty v)
         else if flags then
           let name = Option.get ty in
           if has_symbolic_flags name then
	     let flagNames = get_symbolic_flags name v in
	     match flagNames with
	     | [] -> Some "none"
	     | _ -> Some (String.concat "," flagNames)
           else
	     None
         else
           None)
       None
       (numerical_to_doubleword num)
  | _ ->
     None


let read_xml_description (node: xml_element_int) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let getText tag = (getc tag)#getText in
  let hasText tag = (getc tag)#hasText in
  if has "desc" then
    get "desc"
  else if hasc "desc" && hasText "desc" then
    getText "desc"
  else
    ""


let add_constant (c:constant_definition_t) =
  let index = c.xconst_value#index in
  let name = c.xconst_name in
  let valueEntry =
    if H.mem value_table index then
      H.find value_table index
    else
      [] in
  let nameEntry =
    if H.mem name_table name then
      H.find name_table name
    else
      [] in
  begin
    H.replace value_table index (c :: valueEntry);
    H.replace name_table name (c :: nameEntry)
  end


let read_xml_symbolic_constant (node: xml_element_int) (t: btype_t) =
  let get = node#getAttribute in
  let getx t =
    let tx = get t in
    fail_tvalue
      (trerror_record
         (STR ("BCHConstantDefinitions.read_xml_symbolic_constant:" ^ tx)))
    (string_to_doubleword tx) in
  let c = {
    xconst_name = get "name";
    xconst_value = getx "value";
    xconst_type = t;
    xconst_desc = read_xml_description node;
    xconst_is_addr = false
  } in
  add_constant c


let read_xml_symbolic_constants (node:xml_element_int) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let t = t_named (get "type") in
  let _ = chlog#add "symbolic constants" (btype_to_pretty t) in
  List.iter
    (fun n -> read_xml_symbolic_constant n t)
    ((getc "values")#getTaggedChildren "symc")


let add_flag (ty:btype_t) (f:flag_definition_t) =
  let typename = btype_to_string ty in
  let entry = if H.mem flag_table typename then
      f :: (H.find flag_table typename)
    else
      [f] in
  H.replace flag_table typename entry


let read_xml_symbolic_flag (node: xml_element_int) (t: btype_t) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let getx tag =
    let tx = get tag in
    fail_tvalue
      (trerror_record
         (STR ("BCHConstantDefinitions.read_xml_symbolic_flag:" ^ tx)))
      (string_to_doubleword tx) in
  let has = node#hasNamedAttribute in
  let position =
    if has "value" then
      let dwValue = getx "value" in
      let bitsSet = dwValue#get_bits_set in
      match bitsSet with
      | [i] -> i
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
	           STR "Value ";
                   STR dwValue#to_hex_string;
                   STR " of type ";
                   btype_to_pretty t;
	           STR " and name ";
                   STR (get "name");
	           STR " is not a suitable flag value with ";
	           INT (List.length bitsSet);
                   STR " bits set"]))
    else if has "pos" then
      geti "pos"
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Flag constant ";
                STR (get "name");
		STR " of type ";
                btype_to_pretty t;
		STR " does not have a value or position "])) in
  let f = {
    xflag_name = get "name";
    xflag_pos = position;
    xflag_type = t;
    xflag_desc = read_xml_description node;
  } in
  add_flag t f


let read_xml_symbolic_flags (node:xml_element_int) =
  let get = node#getAttribute in
  let t = t_named (get "type") in
  let _ = chlog#add "symbolic flags" (btype_to_pretty t) in
  let getc = (node#getTaggedChild "values")#getTaggedChildren in
  begin
    List.iter (fun n -> read_xml_symbolic_flag n t) (getc "symf");
    List.iter (fun n -> read_xml_symbolic_constant n t) (getc "symc")
  end


let add_address (a: constant_definition_t) =
  symbolic_addresses#add_address a


let read_xml_symbolic_addresses (node: xml_element_int) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let getx t =
    let tx = get t in
    fail_tvalue
      (trerror_record
         (STR ("BCHConstantDefinitions.read_xml_symbolic_addresses:" ^ tx)))
      (string_to_doubleword tx) in
  let has = node#hasNamedAttribute in
  let hasc = node#hasOneTaggedChild in
  let symname = get "name" in
  let symtype =
    if hasc "type" || hasc "btype" then
      let tNode = if hasc "type" then getc "type" else getc "btype" in
      read_xml_type tNode
    else if has "type" then
      t_named (get "type")
    else
      raise
        (BCH_failure
	   (LBLOCK [
                STR "Symbolic address ";
                STR (get "name");
		STR " does not have a type"])) in
  let symtype =
    if is_unknown_type symtype then
      if bcfiles#has_varinfo symname then
        let vinfo = bcfiles#get_varinfo symname in
        vinfo.bvtype
      else
        symtype
    else
      symtype in
  let a = {
      xconst_name = symname;
      xconst_value = getx "a";
      xconst_type = symtype;
      xconst_desc = read_xml_description node;
      xconst_is_addr = true
    } in
  let _ =
    chlog#add
      "symbolic address"
      (LBLOCK [
           STR a.xconst_name;
           STR ": ";
           a.xconst_value#toPretty;
           STR ", type: ";
           STR (btype_to_string a.xconst_type)]) in
  add_address a


let read_xml_symbolic_addresses (node:xml_element_int) =
  List.iter read_xml_symbolic_addresses (node#getTaggedChildren "syma")


let win32_constants = [
  ("MAX_PATH", "0x00000104", "maximum path length");
  ("NI_MAXHOST", "0x401", "maximum host name length");
  ("NI_MAXSERV", "0x20", "maximum service name length");
  ("SOCKET_ERROR", "0xffffffff", "socket error")
]


let _ =
  List.iter (fun (name, v, desc) ->
      let cv =
        fail_tvalue
          (trerror_record (STR ("BCHConstantDefinitions:" ^ v)))
          (string_to_doubleword v) in
      let c = {
          xconst_name = name;
	  xconst_value = cv;
	  xconst_desc = desc;
	  xconst_type = t_named "win32";
	  xconst_is_addr = false} in
      add_constant c) win32_constants


let constant_statistics_to_pretty () =
  LBLOCK [
      STR "symbolic constants: ";
      INT (H.length value_table);
      NL;
      STR "symbolic flags    : ";
      INT (H.length flag_table);
      NL]
