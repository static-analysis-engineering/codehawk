(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

module H = Hashtbl

(* chlib *)
open CHCommon
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHStringIndexTable
open CHXmlDocument

(* cchcil *)
open CCHBasicTypes
open CCHLibTypes
open CCHSumTypeSerializer
open CCHUtilities

let cd = CCHDictionary.cdictionary


let ibool b = if b then 1 else 0

class cdeclarations_t:cdeclarations_int =
object (self)

  val initinfo_table = mk_index_table "initinfo-table"
  val offset_init_table = mk_index_table "offset-init-table"
  val varinfo_table = mk_index_table "varinfo-table"
  val fieldinfo_table = mk_index_table "fieldinfo-table"
  val compinfo_table = mk_index_table "compinfo-table"
  val enumitem_table = mk_index_table "enumitem-table"
  val enuminfo_table = mk_index_table "enuminfo-table"
  val typeinfo_table = mk_index_table "typeinfo-table"
  val location_table = mk_index_table "location-table"
  val filename_table = mk_string_index_table "filename-table"
  val varinfos = H.create 5
  val mutable tables = []

  initializer
    tables <- [
      location_table;
      initinfo_table;
      offset_init_table;
      typeinfo_table;
      varinfo_table;
      fieldinfo_table;
      compinfo_table;
      enumitem_table;
      enuminfo_table]


  method reset =
    begin
      filename_table#reset;
      List.iter (fun t -> t#reset) tables
    end

  method private populate_varinfo_table =
    let items = varinfo_table#items in
    List.iter (fun ((tags,_),index) ->
        let vname = List.hd tags in
        H.add varinfos vname index) items

  method get_varinfo_by_name (name:string) =
    if H.mem varinfos name then
      self#get_varinfo (H.find varinfos name)
    else
      raise
        (CCHFailure
           (LBLOCK [
                STR "No global variable found in cdeclarations with name ";
                STR  name]))

  method get_opaque_varinfos =
    let indices = List.map snd varinfo_table#items in
    try
      List.filter
        (fun vinfo -> vinfo.vid = (-1))
        (List.map self#get_varinfo indices)
    with
    | CHFailure p  | CCHFailure p ->
       begin
         ch_error_log#add
           "opaque varinfos"
           (LBLOCK [
                p;
                STR "; indices: ";
                pretty_print_list indices (fun i -> INT i) "[" "," "]"]);
         []
       end

  method has_varinfo_by_name (name:string) = H.mem varinfos name

  method index_init (init:init) =
    let (tags,args) = match init with
      | SingleInit exp -> (["single"], [cd#index_exp exp])
      | CompoundInit (typ,olist) ->
         (["compound"],
          (cd#index_typ typ) :: (List.map self#index_offset_init olist)) in
    initinfo_table#add (tags,args)

  method get_init (index:int):init =
    let (tags,args) = initinfo_table#retrieve index in
    let t = t "initinfo" tags in
    let a = a "initinfo" args in
    match (t 0) with
    | "single" -> SingleInit (cd#get_exp (a 0))
    | "compound" ->
       CompoundInit (
           cd#get_typ (a 0),
           List.map self#get_offset_init (List.tl args))
    | s ->
       raise
         (CCHFailure (LBLOCK [STR "Init tag "; STR s; STR " not recognized"]))

  method index_offset_init (oinit:(offset * init)) =
    let (offset,init) = oinit in
    let args = [cd#index_offset offset; self#index_init init] in
    offset_init_table#add ([],args)

  method get_offset_init (index:int):(offset * init) =
    let (_,args) = offset_init_table#retrieve index in
    let a = a "offset-init" args in
    (cd#get_offset (a 0), self#get_init (a 1))

  method index_varinfo (vinfo:varinfo) =
    let vinitix = match vinfo.vinit with
      | Some i -> [self#index_init i] | _ -> [] in
    let tags = [vinfo.vname; storage_mfts#ts vinfo.vstorage] in
    let args =
      [vinfo.vid;
       cd#index_typ vinfo.vtype;
       cd#index_attributes vinfo.vattr;
       ibool vinfo.vglob;
       ibool vinfo.vinline;
       self#index_location vinfo.vdecl;
       ibool vinfo.vaddrof;
       vinfo.vparam] @ vinitix in
    varinfo_table#add (tags,args)

  method get_varinfo (index:int):varinfo =
    try
      let (tags,args) = varinfo_table#retrieve index in
      let t = t "varinfo" tags in
      let a = a "varinfo" args in
      { vname = t 0;
        vstorage = storage_mfts#fs (t 1);
        vid = a 0;
        vtype = cd#get_typ (a 1);
        vattr = cd#get_attributes (a 2);
        vglob = (a 3) = 1;
        vinline = (a 4) = 1;
        vdecl = self#get_location (a 5);
        vaddrof = (a 6) = 1;
        vparam = (a 7);
        vinit =
          if (List.length args) > 8 then
            Some (self#get_init (a 8))
          else
            None
      }
    with
    | Failure s ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Failure in cdecls:get varinfo ";
                 INT index;
                 STR ": ";
                 STR s]))

  method index_fieldinfo (finfo:fieldinfo) =
    let tags = [finfo.fname] in
    let args =
      [finfo.fckey;
       cd#index_typ finfo.ftype;
       (match finfo.fbitfield with Some b -> b | _ -> -1);
       cd#index_attributes finfo.fattr;
       self#index_location finfo.floc] in
    fieldinfo_table#add (tags,args)

  method get_fieldinfo (index:int):fieldinfo =
    let (tags,args) = fieldinfo_table#retrieve index in
    let t = t "fieldinfo" tags in
    let a = a "fieldinfo" args in
    { fname = t 0;
      fckey = a 0;
      ftype = cd#get_typ (a 1);
      fbitfield = if (a 2) = (-1) then None else Some (a 2);
      fattr = cd#get_attributes (a 3);
      floc = self#get_location (a 4) }

  method index_compinfo (cinfo:compinfo) =
    let tags = [cinfo.cname] in
    let args =
      [cinfo.ckey; ibool cinfo.cstruct; cd#index_attributes cinfo.cattr]
      @ (List.map self#index_fieldinfo cinfo.cfields) in
    compinfo_table#add (tags,args)

  method get_compinfo (index:int):compinfo =
    let (tags,args) = compinfo_table#retrieve index in
    let t = t "compinfo" tags in
    let a = a "compinfo" args in
    { cname = t 0;
      ckey = a 0;
      cstruct = (a 1) = 1;
      cattr = cd#get_attributes (a 2);
      cfields = List.map self#get_fieldinfo (get_list_suffix args 3) }

  method index_enumitem (eitem: enumitem) =
    let (name, attrs, exp, loc) = eitem in
    let tags = [name] in
    let args = [
        cd#index_exp exp;
        self#index_location loc;
        cd#index_attributes attrs] in
    enumitem_table#add (tags, args)

  method get_enumitem (index:int):enumitem =
    let (tags,args) = enumitem_table#retrieve index in
    let t = t "enumitem" tags in
    let a = a "enumitem" args in
    (t 0, cd#get_attributes (a 2), cd#get_exp (a 0), self#get_location (a 1))

  method index_enuminfo (einfo:enuminfo) =
    let tags = [einfo.ename; ikind_mfts#ts einfo.ekind] in
    let args =
      [cd#index_attributes einfo.eattr]
      @ (List.map self#index_enumitem einfo.eitems) in
    enuminfo_table#add (tags,args)

  method get_enuminfo (index:int):enuminfo =
    let (tags,args) = enuminfo_table#retrieve index in
    let t = t "enuminfo" tags in
    let a = a "enuminfo" args in
    { ename = t 0;
      ekind = ikind_mfts#fs (t 1);
      eattr = cd#get_attributes (a 0);
      eitems = List.map self#get_enumitem (List.tl args) }

  method index_typeinfo (tinfo:typeinfo) =
    let tags = [tinfo.tname] in
    let args = [cd#index_typ tinfo.ttype] in
    typeinfo_table#add (tags,args)

  method get_typeinfo (index:int):typeinfo =
    let (tags,args) = typeinfo_table#retrieve index in
    let t = t "typeinfo" tags in
    let a = a "typeinfo" args in
    { tname = t 0; ttype = cd#get_typ (a 0) }

  method index_location (loc:location) =
    if loc.byte = -1 && loc.line = -1 then
      (-1)
    else
      let args = [self#index_filename loc.file; loc.byte; loc.line] in
      location_table#add ([],args)

  method get_location (index:int) =
    if index = (-1) then
      { file = ""; byte = (-1); line = (-1) }
    else
      let (_,args) = location_table#retrieve index in
      let a = a ("location " ^ (string_of_int index)) args in
      { file = self#get_filename (a 0);
        byte = (a 1);
        line = (a 2) }

  method index_filename (f:string) = filename_table#add f

  method get_filename (index:int) = filename_table#retrieve index

  method write_xml_varinfo
           ?(tag="ivinfo") (node:xml_element_int) (vinfo:varinfo) =
    node#setIntAttribute tag (self#index_varinfo vinfo)

  method read_xml_varinfo ?(tag="ivinfo") (node:xml_element_int):varinfo =
    self#get_varinfo (node#getIntAttribute tag)

  method write_xml_init ?(tag="iinit") (node:xml_element_int) (init:init) =
    node#setIntAttribute tag (self#index_init init)

  method read_xml_init ?(tag="iinit") (node:xml_element_int):init =
    self#get_init (node#getIntAttribute tag)

  method write_xml_fieldinfo
           ?(tag="ifinfo") (node:xml_element_int) (finfo:fieldinfo) =
    node#setIntAttribute tag (self#index_fieldinfo finfo)

  method read_xml_fieldinfo ?(tag="ifinfo") (node:xml_element_int):fieldinfo =
    self#get_fieldinfo (node#getIntAttribute tag)

  method write_xml_compinfo
           ?(tag="icinfo") (node:xml_element_int) (cinfo:compinfo) =
    node#setIntAttribute tag (self#index_compinfo cinfo)

  method read_xml_compinfo ?(tag="icinfo") (node:xml_element_int):compinfo =
    self#get_compinfo (node#getIntAttribute tag)

  method write_xml_enumitem
           ?(tag="ieitem") (node:xml_element_int) (eitem:enumitem) =
    node#setIntAttribute tag (self#index_enumitem eitem)

  method read_xml_enumitem ?(tag="ieitem") (node:xml_element_int):enumitem =
    self#get_enumitem (node#getIntAttribute tag)

  method write_xml_enuminfo
           ?(tag="ieinfo") (node:xml_element_int) (einfo:enuminfo) =
    node#setIntAttribute tag (self#index_enuminfo einfo)

  method read_xml_enuminfo ?(tag="ieinfo") (node:xml_element_int):enuminfo =
    self#get_enuminfo (node#getIntAttribute tag)

  method write_xml_typeinfo
           ?(tag="itinfo") (node:xml_element_int) (tinfo:typeinfo) =
    node#setIntAttribute tag (self#index_typeinfo tinfo)

  method read_xml_typeinfo ?(tag="itinfo") (node:xml_element_int):typeinfo =
    self#get_typeinfo (node#getIntAttribute tag)

  method write_xml_location
           ?(tag="iloc") (node:xml_element_int) (loc:location) =
    node#setIntAttribute tag (self#index_location loc)

  method read_xml_location ?(tag="iloc") (node:xml_element_int):location =
    self#get_location (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    let snode = xmlElement "filename-table" in
    begin
      filename_table#write_xml snode;
      node#appendChildren
        (List.map (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables);
      node#appendChildren [snode]
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables;
      filename_table#read_xml (getc filename_table#get_name);
      self#populate_varinfo_table
    end

  method toPretty =
    LBLOCK [
        STR filename_table#get_name;
        INT filename_table#size;
        NL;
        (LBLOCK
           (List.map (fun t ->
                LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables))]

end

let cdeclarations = new cdeclarations_t
