(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHCommon
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchcil *)
open BCHBCDictionary
open BCHBCWriteXml
open BCHCBasicTypes
open BCHCilTypes


module H = Hashtbl


let bcd = BCHBCDictionary.bcdictionary


class bcfiles_t: bcfiles_int =
object (self)

  val files = H.create 3

  val gtypes = H.create 3   (* btname -> (typeinfo.ix, loc.ix) *)
  val gcomptags = H.create 3   (* bcname -> (compinfo.ix, loc.ix) *)
  val gcomptagdecls = H.create 3  (* idem *)
  val genumtags = H.create 3   (* bename -> (enuminfo.ix, loc.ix) *)
  val genumtagdecls = H.create 3  (* idem *)
  val gvardecls = H.create 3   (* bvname -> (varinfo.ix, loc.ix) *)
  val gvars = H.create 3   (* idem *)
  val gfuns = H.create 3   (* bsvar.bvname -> fundec *)
  val mutable ifuns = []

  method add_bcfile (f: bcfile_t) =
    let i = bcd#index_location in
    List.iter (fun g ->
        match g with
        | GType (tinfo, loc) ->
           H.add gtypes tinfo.btname (bcd#index_typeinfo tinfo, i loc)
        | GCompTag (cinfo, loc) ->
           H.add gcomptags cinfo.bcname (bcd#index_compinfo cinfo, i loc)
        | GCompTagDecl (cinfo, loc) ->
           H. add gcomptagdecls cinfo.bcname (bcd#index_compinfo cinfo, i loc)
        | GEnumTag (einfo, loc) ->
           H.add genumtags einfo.bename (bcd#index_enuminfo einfo, i loc)
        | GEnumTagDecl (einfo, loc) ->
           H.add genumtagdecls einfo.bename (bcd#index_enuminfo einfo, i loc)
        | GVarDecl (vinfo, loc) ->
           H.add gvardecls vinfo.bvname (bcd#index_varinfo vinfo, i loc)
        | GVar (vinfo, iinfo, loc) ->
           H.add gvars
             vinfo.bvname
             (bcd#index_varinfo vinfo,
              (match iinfo with
               | Some iinfo -> bcd#index_init iinfo
               | _ -> (-1)),
              i loc)
        | GFun (fundec, loc) ->
           begin
             H.add gfuns fundec.bsvar.bvname (fundec, loc);
             ifuns <- (bcd#index_varinfo fundec.bsvar) :: ifuns
           end
        | _ -> ()) f.bglobals
    
  method has_gfun (name: string) = H.mem gfuns name

  method get_gfun (name: string) =
    if self#has_gfun name then
      let (gfun, _) = H.find gfuns name in
      gfun
    else
      raise
        (CHFailure
           (LBLOCK [STR "No function found with name "; STR name]))

  method private get_gfun_loc (name: string) =
    if self#has_gfun name then
      H.find gfuns name
    else
      raise
        (CHFailure
           (LBLOCK [STR "No function found with name "; STR name]))

  method get_gfun_names: string list =
    List.map (fun i -> (bcd#get_varinfo i).bvname) ifuns

  method private write_xml_gtypes (node: xml_element_int) =
    let gtypedata = H.fold (fun k v a -> (k, v)::a) gtypes [] in
    node#appendChildren
      (List.map (fun (name, (tyix, locix)) ->
           let gnode = xmlElement "gt" in
           begin
             gnode#setAttribute "name" name;
             gnode#setIntListAttribute "ixs" [tyix; locix];
             gnode
           end) gtypedata)

  method private read_xml_gtypes (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun tn ->
        let name = tn#getAttribute "name" in
        match tn#getIntListAttribute "ixs" with
        | [tyix; locix] -> H.add gtypes name (tyix, locix)
        | _ -> ()) (getcc "gt")

  method private write_xml_gcomps (node: xml_element_int) =
    let gcomps = H.fold (fun k v a -> (k, v)::a) gcomptags [] in
    node#appendChildren
      (List.map (fun (name, (cix, locix)) ->
           let cnode = xmlElement "ci" in
           begin
             cnode#setAttribute "name" name;
             cnode#setIntListAttribute "ixs" [cix; locix];
             cnode
           end) gcomps)

  method private read_xml_gcomps (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun cn ->
        let name = cn#getAttribute "name" in
        match cn#getIntListAttribute "ixs" with
        | [cix; locix] -> H.add gcomptags name (cix, locix)
        | _ -> ()) (getcc "ci")

  method private write_xml_gcompdecls (node: xml_element_int) =
    let gcomps = H.fold (fun k v a -> (k, v)::a) gcomptagdecls [] in
    node#appendChildren
      (List.map (fun (name, (cix, locix)) ->
           let cnode = xmlElement "cid" in
           begin
             cnode#setAttribute "name" name;
             cnode#setIntListAttribute "ixs" [cix; locix];
             cnode
           end) gcomps)

  method private read_xml_gcompdecls (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun cn ->
        let name = cn#getAttribute "name" in
        match cn#getIntListAttribute "ixs" with
        | [cix; locix] -> H.add gcomptags name (cix, locix)
        | _ -> ()) (getcc "cid")
    
  method private write_xml_genums (node: xml_element_int) =
    let genums = H.fold (fun k v a -> (k, v)::a) genumtags [] in
    node#appendChildren
      (List.map (fun (name, (eix, locix)) ->
           let enode = xmlElement "ei" in
           begin
             enode#setAttribute "name" name;
             enode#setIntListAttribute "ixs" [eix; locix];
             enode
           end) genums)

  method private read_xml_genums (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun en ->
        let name = en#getAttribute "name" in
        match en#getIntListAttribute "ixs" with
        | [eix; locix] -> H.add genumtags name (eix, locix)
        | _ -> ()) (getcc "ei")

  method private write_xml_genumdecls (node: xml_element_int) =
    let genums = H.fold (fun k v a -> (k, v)::a) genumtagdecls [] in
    node#appendChildren
      (List.map (fun (name, (eix, locix)) ->
           let enode = xmlElement "eid" in
           begin
             enode#setAttribute "name" name;
             enode#setIntListAttribute "ixs" [eix; locix];
             enode
           end) genums)

  method private read_xml_genumdecls (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun en ->
        let name = en#getAttribute "name" in
        match en#getIntListAttribute "ixs" with
        | [eix; locix] -> H.add genumtagdecls name (eix, locix)
        | _ -> ()) (getcc "eid")
    
  method private write_xml_gvars (node: xml_element_int) =
    let gvarinfos = H.fold (fun k v a -> (k, v)::a) gvars [] in
    node#appendChildren
      (List.map (fun (name, (vix, iix, locix)) ->
           let vnode = xmlElement "vi" in
           begin
             vnode#setAttribute "name" name;
             vnode#setIntListAttribute "ixs" [vix; iix; locix];
             vnode
           end) gvarinfos)

  method private read_xml_gvars (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun vn ->
        let name = vn#getAttribute "name" in
        match vn#getIntListAttribute "ixs" with
        | [vix; iix; locix] -> H.add gvars name (vix, iix, locix)
        | _ -> ()) (getcc "vi")

  method private write_xml_gvardecls (node: xml_element_int) =
    let gvarinfos = H.fold (fun k v a -> (k, v)::a) gvardecls [] in
    node#appendChildren
      (List.map (fun (name, (vix, locix)) ->
           let vnode = xmlElement "vid" in
           begin
             vnode#setAttribute "name" name;
             vnode#setIntListAttribute "ixs" [vix; locix];
             vnode
           end) gvarinfos)

  method private read_xml_gvardecls (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun vn ->
        let name = vn#getAttribute "name" in
        match vn#getIntListAttribute "ixs" with
        | [vix; locix] -> H.add gvardecls name (vix, locix)
        | _ -> ()) (getcc "vid")

  method private write_xml_ifuns (node: xml_element_int) =
    node#setIntListAttribute "ifuns" ifuns

  method private read_xml_ifuns (node: xml_element_int) =
    node#getIntListAttribute "ifuns"

  method write_xml_function (node: xml_element_int) (name: string) =
    if self#has_gfun name then
      let (fundec, loc) = self#get_gfun_loc name in
      begin
        write_xml_function_definition node fundec;
        bcd#write_xml_location node loc
      end
    else
      ()

  method read_xml_function (node: xml_element_int) (name: string) =
    let fundec = read_xml_function_definition node in
    let loc = bcd#read_xml_location node in
    H.add gfuns name (fundec, loc)
    
  method write_xml (node: xml_element_int) =
    let tnode = xmlElement "typeinfos" in
    let cnode = xmlElement "compinfos" in
    let cdnode = xmlElement "compinfodecls" in
    let enode = xmlElement "enuminfos" in
    let ednode = xmlElement "enuminfodecls" in
    let vnode = xmlElement "varinfos" in
    let vdnode = xmlElement "varinfodecls" in
    let ifunnode = xmlElement "ifuns" in
    begin
      self#write_xml_gtypes tnode;
      self#write_xml_gcomps cnode;
      self#write_xml_gcompdecls cdnode;
      self#write_xml_genums enode;
      self#write_xml_genumdecls ednode;
      self#write_xml_gvars vnode;
      self#write_xml_gvardecls vdnode;
      self#write_xml_ifuns ifunnode;
      node#appendChildren[
          tnode; cnode; cdnode; enode; ednode; vnode; vdnode; ifunnode]
    end

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      self#read_xml_gtypes (getc "typeinfos");
      self#read_xml_gcomps (getc "compinfos");
      self#read_xml_gcompdecls (getc "compinfodecls");
      self#read_xml_genums (getc "enuminfos");
      self#read_xml_genumdecls (getc "enuminfodecls");
      self#read_xml_gvars (getc "varinfos");
      self#read_xml_gvardecls (getc "varinfodecls");
      ifuns <- self#read_xml_ifuns (getc "ifuns")
    end
 
end


let bcfiles = new bcfiles_t
