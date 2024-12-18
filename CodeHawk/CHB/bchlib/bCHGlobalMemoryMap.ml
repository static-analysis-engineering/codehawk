(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024 Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHDoubleword
open BCHLibTypes

module H = Hashtbl
module TR = CHTraceResult


let bcd = BCHBCDictionary.bcdictionary


let globalvalue_to_pretty (gv: globalvalue_t): pretty_t =
  match gv with
  | GConstantString s -> STR s
  | GScalarValue dw -> dw#toPretty


let _global_location_ref_to_pretty (gref: global_location_ref_t): pretty_t =
  match gref with
  | GLoad (_, iaddr, gaddr, size, signed) ->
     LBLOCK [
         STR "load: ";
         STR iaddr; STR "  ";
         gaddr#toPretty;
         STR "  ";
         INT size;
         (if signed then STR " (signed)" else STR "")
       ]
  | GStore (_, iaddr, gaddr, size, _optvalue) ->
     LBLOCK [
         STR "store: "; STR iaddr; STR "  "; gaddr#toPretty; STR "  "; INT size]
  | GAddressArgument (_, iaddr, argindex, gaddr, btype) ->
     LBLOCK [
         STR "addr-arg: ";
         STR iaddr;
         STR " (";
         INT argindex;
         STR ") ";
         gaddr#toPretty;
         (if is_unknown_type btype then
            STR ""
          else
            LBLOCK [STR "  "; STR (btype_to_string btype)])
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

  method size: int option = grec.gloc_size

  method is_readonly: bool = grec.gloc_is_readonly

  method is_initialized: bool = grec.gloc_is_initialized

  method contains_address (addr: doubleword_int): bool =
    (self#address#equal addr)
    || (match self#size with
        | Some s ->
           addr#index >= self#address#index
           && addr#index < (self#address#index + s)
        | _ -> false)

  method address_offset (addr: doubleword_int): int traceresult =
    if self#contains_address addr then
      if self#address#equal addr then
        Ok 0
      else
        Ok (addr#index - self#address#index)
    else
      Error [
          "memmap#address_offset: address "
          ^ addr#to_hex_string
          ^ " not known to be part this location ("
          ^ self#address#to_hex_string
          ^ ":"
          ^ self#name
          ^ ")"]

  method private get_fieldoffset_at
                   (c: bcompinfo_t)
                   (offset: int): (boffset_t * int) traceresult =
    let finfos = c.bcfields in
    let fld0 = List.hd finfos in
    let fld0type_r = resolve_type fld0.bftype in
    let fld0size_r = tbind size_of_btype fld0type_r in
    match fld0type_r, fld0size_r with
    | Error e, _
      | _, Error e -> Error e
    | Ok fld0type, Ok fld0size ->
       if offset = 0 then
         Ok ((Field ((fld0.bfname, fld0.bfckey), NoOffset), 0))
       else if offset < fld0size then
         (* offset is within the first field *)
         if is_struct_type fld0type then
           let cinfo = get_struct_type_compinfo fld0type in
           tbind
             ~msg:("memmap:get_fieldoffset_at with offset " ^ (string_of_int offset))
             (fun (boffset, rem) ->
               Ok (Field ((fld0.bfname, fld0.bfckey), boffset), rem))
             (self#get_fieldoffset_at cinfo offset)
         else
           Error ["non-struct first field not yet implemented"]
       else
         let optfield_r =
           List.fold_left (fun acc_r finfo ->
               match acc_r with
               | Error e -> Error e
               | Ok (Some _) -> acc_r
               | Ok _ ->
                  let fldtype_r = resolve_type finfo.bftype in
                  let fldsize_r = tbind size_of_btype fldtype_r in
                  match fldtype_r, fldsize_r with
                  | Error e, _ | _, Error e -> Error e
                  | Ok fldtype, Ok _fldsize ->
                     match finfo.bfieldlayout with
                     | Some (foff, sz) ->
                        if offset = foff then
                          Ok (Some (Field ((finfo.bfname, finfo.bfckey), NoOffset), 0))
                        else if offset > foff && offset < foff + sz then
                          match fldtype with
                          | TComp (ffkey, _) ->
                             let fcinfo = BCHBCFiles.bcfiles#get_compinfo ffkey in
                             (match self#get_fieldoffset_at fcinfo (offset - foff) with
                              | Error e -> Error e
                              | Ok (bboff, rem) ->
                                 Ok (Some (Field
                                             ((finfo.bfname, finfo.bfckey),
                                              bboff), rem)))
                          | _ ->
                             Ok (Some (Field
                                         ((finfo.bfname, finfo.bfckey), NoOffset),
                                       offset - foff))
                        else
                          Ok None
                     | _ -> Ok None) (Ok None) (List.tl finfos) in
         match optfield_r with
         | Error e -> Error e
         | Ok (Some (offset, rem)) -> Ok (offset, rem)
         | _ -> Ok (NoOffset, offset)

  method private structvar_memory_offset (offset: int): memory_offset_t traceresult =
    if self#is_struct then
      let compinfo = get_struct_type_compinfo self#btype in
      tbind
        ~msg:"memmap:structvar_memory_offset"
        (fun (boffset, rem) ->
          if rem = 0 then
            BCHMemoryReference.boffset_to_memory_offset boffset
          else
            Error [
                "memmap:structvar_memory_offset: remainder: "
                ^ (string_of_int rem)])
        (self#get_fieldoffset_at compinfo offset)
    else
      Error [
          "memmap:structvar_memory_offset: type is not know to be a struct: "
          ^ (btype_to_string self#btype)]

  method private arrayvar_memory_offset (_offset: int): memory_offset_t traceresult =
    Error ["not yet implemented"]

  method address_memory_offset (addr: doubleword_int): memory_offset_t traceresult =
    tbind
      ~msg:"memmap:address_memory_offset"
      (fun offset ->
        if offset = 0 then
          Ok BCHLibTypes.NoOffset
        else if self#is_struct then
          self#structvar_memory_offset offset
        else if self#is_array then
          self#arrayvar_memory_offset offset
        else
          Error [
              "memmap:address_memory_offset: type "
              ^ (btype_to_string self#btype)
              ^ " is not known to be a struct or array"])
      (self#address_offset addr)

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

  val locations = H.create 51        (* ix -> gloc *)
  val locreferences = H.create 51    (* ix -> gref list *)
  val namedlocations = H.create 51   (* name -> ix *)
  val orphanreferences = H.create 51 (* ix -> gref list *)
  val sections = H.create 5

  method set_section
           ~(readonly: bool)
           ~(initialized: bool)
           (name: string)
           (addr: doubleword_int)
           (size: doubleword_int) =
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
           (address: doubleword_int) =
    if H.mem locations address#index then
      begin
        ch_error_log#add
          "duplicate global location"
          (LBLOCK [
               STR "Global location at address ";
               address#toPretty;
               STR " already exists"]);
        ()
      end
    else
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
          ])
      end

  method private add_global_ref
                   (addr: doubleword_int) (gref: global_location_ref_t) =
    let entry =
      if H.mem locreferences addr#index then
        H.find locreferences addr#index
      else
        [] in
    H.replace locreferences addr#index (gref :: entry)

  method private add_orphan_ref
                   (addr: doubleword_int) (gref: global_location_ref_t) =
    let entry =
      if H.mem orphanreferences addr#index then
        H.find orphanreferences addr#index
      else
        [] in
    H.replace orphanreferences addr#index (gref :: entry)

  method add_gload
           (faddr: doubleword_int)
           (iaddr: ctxt_iaddress_t)
           (gaddr: doubleword_int)
           (size: int)
           (signed: bool) =
    let gload = GLoad (faddr, iaddr, gaddr, size, signed) in
    match self#containing_location gaddr with
    | Some gloc -> self#add_global_ref gloc#address gload
    | _ -> self#add_orphan_ref gaddr gload

  method add_gstore
           (faddr: doubleword_int)
           (iaddr: ctxt_iaddress_t)
           (gaddr: doubleword_int)
           (size: int)
           (optvalue: CHNumerical.numerical_t option) =
    let gstore = GStore (faddr, iaddr, gaddr, size, optvalue) in
    match self#containing_location gaddr with
    | Some gloc -> self#add_global_ref gloc#address gstore
    | _ -> self#add_orphan_ref gaddr gstore

  method add_gaddr_argument
           (faddr: doubleword_int)
           (iaddr: ctxt_iaddress_t)
           (gaddr: doubleword_int)
           (argindex: int)
           (btype: btype_t) =
    let garg = GAddressArgument (faddr, iaddr, argindex, gaddr, btype) in
    match self#containing_location gaddr with
    | Some gloc -> self#add_global_ref gloc#address garg
    | _ -> self#add_orphan_ref gaddr garg

  method update_named_location (name: string) (vinfo: bvarinfo_t) =
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
          ])
      end
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No location found with name ";
                STR name;
                STR " in global memory map"]))

  method has_location_with_name (name: string) = H.mem namedlocations name

  method has_location (addr: doubleword_int) = H.mem locations addr#index

  method containing_location (addr: doubleword_int): global_location_int option =
    H.fold (fun _ gloc acc ->
        match acc with
        | Some _ -> acc
        | _ -> if gloc#contains_address addr then Some gloc else None)
    locations None

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
                   (node: xml_element_int) (ix: int) (gref: global_location_ref_t) =
    let gloca = TR.tget_ok (index_to_doubleword ix) in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let set_size (s: int) = seti "s" s in
    let set_gaddr (a: doubleword_int) =
      if a#equal gloca then () else set "a" a#to_hex_string in
    let set_faddr (a: doubleword_int) = set "f" a#to_hex_string in
    let set_iaddr (a: ctxt_iaddress_t) = set "i" a in
    let set_btype (t: btype_t) =
      if is_known_type t then seti "tix" (bcd#index_typ t) else () in
    match gref with
    | GLoad (faddr, iaddr, gaddr, size, signed) ->
       begin
         set "t" "L";
         set_faddr faddr;
         set_gaddr gaddr;
         set_iaddr iaddr;
         set_size size;
         (if signed then set "sg" "yes")
       end
    | GStore (faddr, iaddr, gaddr, size, optvalue) ->
       begin
         set "t" "S";
         set_faddr faddr;
         set_gaddr gaddr;
         set_iaddr iaddr;
         set_size size;
         (match optvalue with
          | Some n -> set "v" n#toString
          | _ -> ())
       end
    | GAddressArgument (faddr, iaddr, argindex, gaddr, btype) ->
       begin
         set "t" "CA";
         set_faddr faddr;
         seti "aix" argindex;
         set_gaddr gaddr;
         set_iaddr iaddr;
         set_btype btype;
       end

  method write_xml (node: xml_element_int) =
    let secnode = xmlElement "sections" in
    let locnode = xmlElement "locations" in
    let orphannode = xmlElement "no-locations" in
    begin
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
      H.iter (fun ix gloc ->
          let vnode = xmlElement "gloc" in
          begin
            vnode#setAttribute "a" gloc#address#to_hex_string;
            vnode#setAttribute "name" gloc#name;
            gloc#write_xml vnode;
            (if H.mem locreferences ix then
               let locrefs = H.find locreferences ix in
               (List.iter (fun gref ->
                    let grefnode = xmlElement "gref" in
                    begin
                      self#write_xml_gref grefnode ix gref;
                      vnode#appendChildren [grefnode]
                    end) locrefs));
            locnode#appendChildren [vnode]
          end) locations;
      H.iter (fun ix greflist ->
          let vnode = xmlElement "orphan-loc" in
          begin
            vnode#setAttribute
              "a" (TR.tget_ok (index_to_doubleword ix))#to_hex_string;
            List.iter (fun gref ->
                let grefnode = xmlElement "gref" in
                begin
                  self#write_xml_gref grefnode ix gref;
                  vnode#appendChildren [grefnode]
                end) greflist;
            orphannode#appendChildren [vnode]
          end) orphanreferences;
      node#appendChildren [secnode; locnode; orphannode]
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
  global_memory_map#add_location ~name ~desc:(Some "userdata") address


let read_xml_symbolic_addresses (node: xml_element_int) =
  List.iter read_xml_symbolic_addresses (node#getTaggedChildren "syma")


let update_global_location_type (vinfo: bvarinfo_t) =
  let name = vinfo.bvname in
  if global_memory_map#has_location_with_name name then
    global_memory_map#update_named_location name vinfo
  else if String.length name > 3 && (String.sub name 0 3) = "gv_" then
    let index = String.index name '_' in
    if String.contains_from name (index + 1) '_' then
      let eindex = String.index_from name (index + 1) '_' in
      let hex = String.sub name (index + 1) ((eindex - index) - 1) in
      let hex = "0x" ^ hex in
      match (string_to_doubleword hex) with
      | Error e ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Address: ";
                   STR hex;
                   STR " in global variable name ";
                   STR name;
                   STR " not recognized: ";
                   STR (String.concat "; " e)
           ]))
      | Ok dw ->
         global_memory_map#add_location
           ~name:(Some name)
           ~desc:(Some "header file")
           ~btype: vinfo.bvtype
           ~size:(TR.to_option (size_of_btype vinfo.bvtype))
           dw
    else
      chlog#add
        "global location not updated"
        (LBLOCK [STR vinfo.bvname; STR ": "; STR (btype_to_string vinfo.bvtype)])
  else
      chlog#add
        "global location not updated"
        (LBLOCK [STR vinfo.bvname; STR ": "; STR (btype_to_string vinfo.bvtype)])
