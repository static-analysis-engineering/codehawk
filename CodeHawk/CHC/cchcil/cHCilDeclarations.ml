(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* cil *)
open GoblintCil

(* chlib *)
open CHCommon

(* chutil *)
open CHIndexTable
open CHStringIndexTable
open CHTimingLog
open CHTraceResult
open CHXmlDocument

(* chcil *)
open CHCilTypes
open CHCilFileUtil
open CHCilSumTypeSerializer

let cd = CHCilDictionary.cildictionary


let ibool b = if b then 1 else 0


class cildeclarations_t: cildeclarations_int =
object (self)

  val varinfo_table = mk_index_table "varinfo-table"
  val initinfo_table = mk_index_table "initinfo-table"
  val offset_init_table = mk_index_table "offset-init-table"
  val fieldinfo_table = mk_index_table "fieldinfo-table"
  val compinfo_table = mk_index_table "compinfo-table"
  val enumitem_table = mk_index_table "enumitem-table"
  val enuminfo_table = mk_index_table "enuminfo-table"
  val typeinfo_table = mk_index_table "typeinfo-table"
  val location_table = mk_index_table "location-table"
  val string_table = mk_string_index_table "filename-table"
  val mutable tables = []
  val mutable cfilename = ""

  initializer
    tables <- [
      location_table ;
      initinfo_table ;
      offset_init_table ;
      typeinfo_table ;
      varinfo_table ;
      fieldinfo_table ;
      compinfo_table ;
      enumitem_table ;
      enuminfo_table
    ]

  method set_filename s = cfilename <- s

  method index_init_opt (iinfo: init option) =
    match  iinfo with
    | None -> (-1)
    | Some init -> self#index_init init

  method index_init (init:init) =
    let (tags,args) = match init with
      | SingleInit exp -> (["single"], [cd#index_exp exp])
      | CompoundInit (typ, olist) when (List.length olist) > 5000 ->
         (["compound"],
          [(cd#index_typ typ); self#index_offset_init (List.hd olist)])
      | CompoundInit (typ, olist) ->
         (["compound"],
          (cd#index_typ typ) :: (List.map self#index_offset_init olist)) in
    initinfo_table#add (tags,args)

  method index_offset_init (oi: (offset * init)) =
    let (offset, init) = oi in
    let args = [cd#index_offset offset; self#index_init init] in
    offset_init_table#add ([], args)

  method index_varinfo (vinfo: varinfo) =
    let vinit_ix = match vinfo.vinit.init with
      | Some i -> [self#index_init i]
      | _ -> [] in
    let tags = [vinfo.vname; storage_mfts#ts vinfo.vstorage] in
    let locix_r = self#index_location vinfo.vdecl in
    match locix_r with
    | Ok locix ->
       let args =
         [vinfo.vid;
          cd#index_typ vinfo.vtype;
          cd#index_attributes vinfo.vattr;
          ibool vinfo.vglob;
          ibool vinfo.vinline;
          locix;
          ibool vinfo.vaddrof;
          0] @ vinit_ix in
       varinfo_table#add (tags,args)
    | Error e ->
       begin
         log_error
             "index_varinfo: %s; %s [%s:%d]"
             vinfo.vname
             (String.concat ", " e)
             __FILE__ __LINE__;
         raise
           (CHFailure
              (LBLOCK [
                   STR "index_varinfo: ";
                   STR vinfo.vname;
                   STR "; ";
                   STR (String.concat ", " e)]))
       end

  method index_fieldinfo (finfo: fieldinfo) =
    let tags = [finfo.fname] in
    let locix_r = self#index_location finfo.floc in
    match locix_r with
    | Ok locix ->
       let args =
         [finfo.fcomp.ckey;
          cd#index_typ finfo.ftype;
          (match finfo.fbitfield with Some b -> b | _ -> -1);
          cd#index_attributes finfo.fattr;
          locix
         ] in
       fieldinfo_table#add (tags, args)
    | Error e ->
       begin
         log_error
           "index fieldinfo: %s %s [%s:%d]"
           finfo.fname
           (String.concat ", " e)
           __FILE__ __LINE__;
         raise
           (CHFailure
              (LBLOCK [
                   STR "index fieldinfo: ";
                   STR finfo.fname;
                   STR (String.concat ", " e)]))
       end

  method index_compinfo (cinfo: compinfo) =
    let tags = [cinfo.cname] in
    let args =
      [cinfo.ckey;
       ibool cinfo.cstruct;
       cd#index_attributes cinfo.cattr]
      @ (List.map self#index_fieldinfo cinfo.cfields) in
    compinfo_table#add (tags, args)

  method index_enumitem (eitem: enumitem) =
    let (name, attrs, exp, loc) = eitem in
    let tags = [name] in
    let locix_r = self#index_location loc in
    match locix_r with
    | Ok locix ->
       let args = [cd#index_exp exp; locix; cd#index_attributes attrs] in
       enumitem_table#add (tags, args)
    | Error e ->
       begin
         log_error
           "index enumitem: %s %s [%s:%d]"
           name
           (String.concat ", " e)
           __FILE__ __LINE__;
         raise
           (CHFailure
              (LBLOCK [
                   STR "index enumitem: ";
                   STR name;
                   STR (String.concat ", " e)]))
       end

  method index_enuminfo (einfo: enuminfo) =
    let tags = [einfo.ename; ikind_mfts#ts einfo.ekind] in
    let args =
      [cd#index_attributes einfo.eattr]
      @ (List.map self#index_enumitem einfo.eitems) in
    enuminfo_table#add (tags,args)

  method index_typeinfo (tinfo: typeinfo) =
    let tags = [tinfo.tname] in
    let args = [cd#index_typ tinfo.ttype] in
    typeinfo_table#add (tags,args)

  method index_location (loc: location): int traceresult =
    if loc.byte = -1 && loc.line = -1 then
      Ok (-1)
    else
      let filename_r =
        get_location_filename
          !CHCilFileUtil.project_path_prefix cfilename loc.file in
      tmap
        (fun filename ->
          let args = [self#index_filename filename; loc.byte; loc.line] in
          location_table#add ([], args))
        filename_r

  method index_filename (f: string) = string_table#add f

  method write_xml_varinfo
           ?(tag="ivinfo") (node: xml_element_int) (vinfo: varinfo) =
    node#setIntAttribute tag (self#index_varinfo vinfo)

  method write_xml_init ?(tag="iinit") (node: xml_element_int) (init: init) =
    node#setIntAttribute tag (self#index_init init)

  method write_xml_fieldinfo
           ?(tag="ifinfo") (node: xml_element_int) (finfo: fieldinfo) =
    node#setIntAttribute tag (self#index_fieldinfo finfo)

  method write_xml_compinfo
           ?(tag="icinfo") (node: xml_element_int) (cinfo: compinfo) =
    node#setIntAttribute tag (self#index_compinfo cinfo)

  method write_xml_enumitem
           ?(tag="ieitem") (node: xml_element_int) (eitem: enumitem) =
    node#setIntAttribute tag (self#index_enumitem eitem)

  method write_xml_enuminfo
           ?(tag="ieinfo") (node: xml_element_int) (einfo: enuminfo) =
    node#setIntAttribute tag (self#index_enuminfo einfo)

  method write_xml_typeinfo
           ?(tag="itinfo") (node: xml_element_int) (tinfo: typeinfo) =
    node#setIntAttribute tag (self#index_typeinfo tinfo)

  method write_xml_location
           ?(tag="iloc") (node: xml_element_int) (loc: location) =
    let locix_r = self#index_location loc in
    match locix_r with
    | Ok locix -> node#setIntAttribute tag locix
    | Error e ->
       raise
         (CHFailure
            (LBLOCK [STR "write_xml_location: "; STR (String.concat ", " e)]))

  method write_xml (node: xml_element_int) =
    let snode = xmlElement string_table#get_name in
    begin
      string_table#write_xml snode ;
      node#appendChildren
        (List.map (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables);
      node#appendChildren [snode]
    end

end


let cildeclarations = new cildeclarations_t
