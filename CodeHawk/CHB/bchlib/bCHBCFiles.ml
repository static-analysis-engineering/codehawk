(* =============================================================================
   CodeHawk Binary Analyzer C Parser
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2024  Aarno Labs LLC

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
open BCHBCTypeTransformer
open BCHBCWriteXml


module H = Hashtbl


let bcd = BCHBCDictionary.bcdictionary


class bcfiles_t: bcfiles_int =
object (self)

  val files = H.create 3

  val gtypes = H.create 3   (* btname -> (typeinfo.ix, loc.ix) *)
  val gcomptags = H.create 3   (* (bcname, bckey) -> (compinfo.ix, loc.ix) *)
  val gcomptagdecls = H.create 3  (* idem *)
  val genumtags = H.create 3   (* bename -> (enuminfo.ix, loc.ix) *)
  val genumtagdecls = H.create 3  (* idem *)
  val gvardecls = H.create 3   (* bvname -> (varinfo.ix, loc.ix) *)
  val gvars = H.create 3   (* idem *)
  val gfuns = H.create 3   (* bsvar.bvname -> (fundec, loc.ix) *)
  val mutable varinfo_vid_counter = 10000

  method private get_varinfo_id =
    begin
      varinfo_vid_counter <- varinfo_vid_counter + 1;
      varinfo_vid_counter
    end

  method add_bcfile (f: bcfile_t) =
    let i = bcd#index_location in
    List.iter (fun g ->
        match g with
        | GType (tinfo, loc) ->
           begin
             ignore (bcd#index_typeinfo tinfo);
             H.replace gtypes tinfo.btname (bcd#index_typ tinfo.bttype, i loc)
           end
        | GCompTag (cinfo, loc) ->
           H.replace
             gcomptags
             (cinfo.bcname, cinfo.bckey)
             (bcd#index_compinfo cinfo, i loc)
        | GCompTagDecl (cinfo, loc) ->
           H.replace
             gcomptagdecls
             (cinfo.bcname, cinfo.bckey)
             (bcd#index_compinfo cinfo, i loc)
        | GEnumTag (einfo, loc) ->
           H.replace genumtags einfo.bename (bcd#index_enuminfo einfo, i loc)
        | GEnumTagDecl (einfo, loc) ->
           H.replace genumtagdecls einfo.bename (bcd#index_enuminfo einfo, i loc)
        | GVarDecl (vinfo, loc) ->
           H.replace gvardecls vinfo.bvname (bcd#index_varinfo vinfo, i loc)
        | GVar (vinfo, iinfo, loc) ->
           H.replace gvars
             vinfo.bvname
             (bcd#index_varinfo vinfo,
              (match iinfo with
               | Some iinfo -> bcd#index_init iinfo
               | _ -> (-1)),
              i loc)
        | GFun (fundec, loc) ->
             H.replace gfuns fundec.bsvar.bvname (fundec, bcd#index_location loc);
        | _ -> ()) f.bglobals

  method update_global (g: bglobal_t) =
    let i = bcd#index_location in
    match g with
    | GCompTag (cinfo, loc) ->
       H.replace
         gcomptags
         (cinfo.bcname, cinfo.bckey)
         (bcd#index_compinfo cinfo, i loc)
    | GCompTagDecl (cinfo, loc) ->
       H.replace
         gcomptagdecls
         (cinfo.bcname, cinfo.bckey)
         (bcd#index_compinfo cinfo, i loc)
    | _ -> ()

  method add_fundef (name: string) (ty: btype_t) =
    if H.mem gfuns name then
      (* function already exists *)
      ()
    else
      (* check if the variable name already exists *)
      let bvarloc =
        if H.mem gvars name then
          let (vix, _, lix) = H.find gvars name in
          Some (bcd#get_varinfo vix, bcd#get_location lix)
        else if H.mem gvardecls name then
          let (vix, lix) = H.find gvardecls name in
          Some (bcd#get_varinfo vix, bcd#get_location lix)
        else
          None in
      (* else create a new variable *)
      let (bvar, loc) =
        match bvarloc with
        | Some (vinfo, loc) -> (vinfo, loc)
        | _ ->
           let loc = {line = (-1); file = ""; byte = (-1)} in
           let vinfo = {
               bvname = name;
               bvtype = ty;
               bvstorage = NoStorage;
               bvglob = true;
               bvinit = None;
               bvdecl = loc;
               bvinline = false;
               bvid = self#get_varinfo_id;
               bvattr = [];
               bvaddrof = false;
               bvparam = 0
             } in
           begin
             H.replace
               gvars
               vinfo.bvname
               (bcd#index_varinfo vinfo, (-1), bcd#index_location loc);
             (vinfo, loc)
           end in
      let fundec = {
          bsvar = bvar;
          bsformals = self#mk_formals ty loc;
          bslocals = [];
          bsbody = {battrs = []; bstmts = []}
        } in
      begin
        H.replace gfuns name (fundec, bcd#index_location fundec.bsvar.bvdecl);
        chlog#add
          "add function definition"
          (LBLOCK [STR name; STR ": "; btype_to_pretty ty])
      end

  method private mk_formals (ty: btype_t) (loc: b_location_t) =
    match ty with
    | TFun (_, Some funargs, _, _)
      | TPtr (TFun (_, Some funargs, _, _), _) ->
       List.mapi (fun i (name, argty, attrs) ->
           { bvname = name;
             bvtype = argty;
             bvstorage = NoStorage;
             bvglob = false;
             bvinit = None;
             bvdecl = loc;
             bvinline = false;
             bvid = self#get_varinfo_id;
             bvattr = attrs;
             bvaddrof = false;
             bvparam = i + 1
         }) funargs
    | _ -> []


  method has_typedef (name: string) = H.mem gtypes name

  method get_typedef (name: string): btype_t =
    if self#has_typedef name then
      let (tix, _) = H.find gtypes name in
      bcd#get_typ tix
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No typedef found with name "; STR name]))

  method resolve_type (ty: btype_t): btype_t traceresult =
    let rec aux (t: btype_t): btype_t traceresult =
      match t with
      | TVoid _
        | TInt _
        | TFloat _
        | THandle _
        | TComp _
        | TEnum _
        | TCppComp _
        | TCppEnum _
        | TClass _
        | TBuiltin_va_list _
        | TVarArg _
        | TUnknown _ -> Ok t
      | TPtr (tt, a) -> tmap (fun v -> TPtr (v, a)) (aux tt)
      | TRef (tt, a) -> tmap (fun v -> TRef (v, a)) (aux tt)
      | TArray (tt, e, a) -> tmap (fun v -> TArray (v, e, a)) (aux tt)
      | TFun (tt, fs, b, a) ->
         let auxtt_r = aux tt in
         let auxfs_r = auxfs fs in
         (match auxtt_r, auxfs_r with
          | Ok v1, Ok v2 -> Ok (TFun (v1, v2, b, a))
          | Error e1, Ok _ -> Error e1
          | Ok _, Error e2 -> Error e2
          | Error e1, Error e2 -> Error (e1 @ e2))
      | TNamed (name, a) when self#has_typedef name ->
         aux (add_attributes (self#get_typedef name) a)
      | TNamed (name, _) ->
         Error ["resolve_type: type name not found: " ^ name]

    and auxfs (fs: bfunarg_t list option): bfunarg_t list option traceresult =
      match fs with
      | None -> Ok None
      | Some l ->
         let fs_r = List.map (fun (s, t, a) -> (s, aux t, a)) l in
         let fs_r =
           List.fold_left (fun acc (s, t_r, a) ->
               match acc with
               | Error _ -> acc
               | Ok accv ->
                  (match t_r with
                   | Error e -> Error e
                   | Ok v -> Ok ((s, v, a) :: accv))) (Ok []) fs_r in
         match fs_r with
         | Ok v -> Ok (Some v)
         | Error e -> Error e
                        (* Some (List.map (fun (s, t, a) -> (s, aux t, a)) l) *)

    in
    aux ty


  method typedefs: (string * btype_t) list =
    H.fold (fun k (ix, _loc) a -> (k, bcd#get_typ ix) :: a) gtypes []

  method has_compinfo (key: int) =
    let e1 = H.fold (fun (_, ckey) _ a -> a || key = ckey) gcomptags false in
    e1 || (H.fold (fun (_, ckey) _ a -> a || key = ckey) gcomptagdecls false)

  method has_compinfo_by_name (name: string) =
    let e1 = H.fold (fun (cname, _) _ a -> a || cname = name) gcomptags false in
    e1 || (H.fold (fun (cname, _) _ a -> a || cname = name) gcomptagdecls false)

  method get_compinfo (key: int): bcompinfo_t =
    if self#has_compinfo key then
      let values =
        (H.fold (fun (_, ckey) (ix, _) a -> (ckey, ix) :: a) gcomptags [])
        @ (H.fold (fun (_, ckey) (ix, _) a -> (ckey, ix) :: a) gcomptagdecls []) in
      let (_, ix) = List.find (fun (ckey, _) -> key = ckey) values in
      bcd#get_compinfo ix
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No comptag found with key "; INT key]))

  method get_compinfo_by_name (name: string): bcompinfo_t =
    let found =
      H.fold (fun (cname, _) (ix, _) acc ->
          match acc with
          | Some _ -> acc
          | _ -> if cname = name then Some ix else acc) gcomptags None in
    let found =
      H.fold (fun (cname, _) (ix, _) acc ->
          match acc with
          | Some _ -> acc
          | _ -> if cname = name then Some ix else acc) gcomptagdecls found in
    match found with
    | Some ix -> bcd#get_compinfo ix
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "No comptag found with name "; STR name]))

  method has_enuminfo (name: string) =
    (H.mem genumtags name) || (H.mem genumtagdecls name)

  method get_enuminfo (name: string) =
    if self#has_enuminfo name then
      let ix =
        if H.mem genumtags name then
          let (ix, _) = H.find genumtags name in ix
        else
          let (ix, _) = H.find genumtagdecls name in ix
      in
      bcd#get_enuminfo ix
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No enuminfo found with name "; STR name]))

  method has_varinfo (name: string) =
    (H.mem gvars name) || (H.mem gvardecls name)

  method get_varinfo (name: string) =
    if self#has_varinfo name then
      let ix =
        if H.mem gvars name then
          let (ix, _, _) = H.find gvars name in ix
        else
          let (ix, _) = H.find gvardecls name in ix
      in
      bcd#get_varinfo ix
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No varinfo found with name "; STR name]))

  method list_varinfos =
    let result = ref [] in
    let v2s v = v.bvname ^ ": " ^ (btype_to_string v.bvtype) in
    begin
      H.iter (fun _name (ix, _, _) ->
          result := (v2s (bcd#get_varinfo ix)) :: !result) gvars;
      H.iter (fun _name (ix, _) ->
          result := (v2s (bcd#get_varinfo ix)) :: !result) gvardecls;
      !result
    end
    
  method has_gfun (name: string) = H.mem gfuns name

  method get_gfun (name: string) =
    if self#has_gfun name then
      let (gfun, _) = H.find gfuns name in
      gfun
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No function found with name "; STR name]))

  method private get_gfun_loc (name: string) =
    if self#has_gfun name then
      H.find gfuns name
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No function found with name "; STR name]))

  method get_gfun_names: string list =
    H.fold (fun k _ a -> k::a) gfuns []
  (* List.map (fun i -> (bcd#get_varinfo i).bvname) ifuns *)

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
      (List.map (fun ((name, ckey), (cix, locix)) ->
           let cnode = xmlElement "ci" in
           begin
             cnode#setAttribute "name" name;
             cnode#setIntAttribute "key" ckey;
             cnode#setIntListAttribute "ixs" [cix; locix];
             cnode
           end) gcomps)

  method private read_xml_gcomps (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun cn ->
        let name = cn#getAttribute "name" in
        let ckey = cn#getIntAttribute "key" in
        match cn#getIntListAttribute "ixs" with
        | [cix; locix] -> H.add gcomptags (name, ckey) (cix, locix)
        | _ -> ()) (getcc "ci")

  method private write_xml_gcompdecls (node: xml_element_int) =
    let gcomps = H.fold (fun k v a -> (k, v)::a) gcomptagdecls [] in
    node#appendChildren
      (List.map (fun ((name, ckey), (cix, locix)) ->
           let cnode = xmlElement "cid" in
           begin
             cnode#setAttribute "name" name;
             cnode#setIntAttribute "key" ckey;
             cnode#setIntListAttribute "ixs" [cix; locix];
             cnode
           end) gcomps)

  method private read_xml_gcompdecls (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun cn ->
        let name = cn#getAttribute "name" in
        let ckey = cn#getIntAttribute "key" in
        match cn#getIntListAttribute "ixs" with
        | [cix; locix] -> H.add gcomptags (name, ckey) (cix, locix)
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

  method private write_xml_gfuns (node: xml_element_int) =
    let gfundefs = H.fold (fun k v a -> (k, v)::a) gfuns [] in
    node#appendChildren
      (List.map (fun (name, (fundec, locix)) ->
           let fnode = xmlElement "gfun" in
           begin
             fnode#setAttribute "name" name;
             fnode#setIntAttribute "locix" locix;
             write_xml_function_definition fnode fundec;
             fnode
           end) gfundefs)

  method private read_xml_gfuns (node: xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun gn ->
        let name = gn#getAttribute "name" in
        let locix = gn#getIntAttribute "locix" in
        let fundec = read_xml_function_definition gn in
        H.add gfuns name (fundec, locix)) (getcc "gfun")
    
  method write_xml (node: xml_element_int) =
    let tnode = xmlElement "typeinfos" in
    let cnode = xmlElement "compinfos" in
    let cdnode = xmlElement "compinfodecls" in
    let enode = xmlElement "enuminfos" in
    let ednode = xmlElement "enuminfodecls" in
    let vnode = xmlElement "varinfos" in
    let vdnode = xmlElement "varinfodecls" in
    let gfunnode = xmlElement "gfuns" in
    begin
      self#write_xml_gtypes tnode;
      self#write_xml_gcomps cnode;
      self#write_xml_gcompdecls cdnode;
      self#write_xml_genums enode;
      self#write_xml_genumdecls ednode;
      self#write_xml_gvars vnode;
      self#write_xml_gvardecls vdnode;
      self#write_xml_gfuns gfunnode;
      node#appendChildren[
          tnode; cnode; cdnode; enode; ednode; vnode; vdnode; gfunnode]
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
      self#read_xml_gfuns (getc "gfuns")
    end
 
end


let bcfiles = new bcfiles_t
