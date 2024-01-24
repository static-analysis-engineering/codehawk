(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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

(* chutil *)
open CHLogger
open CHXmlDocument

(* cchlib *)
open CCHExternalPredicate
open CCHFunctionSummary
open CCHLibTypes
open CCHUtilities

module H = Hashtbl


let id = CCHInterfaceDictionary.interface_dictionary


let read_xml_instr_list (node:xml_element_int) params lvars =
  List.map
    (fun n -> read_xml_instr n ~lvars params) (node#getTaggedChildren "instr")


class function_contract_t
        ?(parameters=[])
        (ignorefn:bool)
        (name:string):function_contract_int =
object (self)

  val ignorefn = ignorefn
  val postconditions = new CHUtils.IntCollections.set_t
  val preconditions = new CHUtils.IntCollections.set_t
  val sideeffects = new CHUtils.IntCollections.set_t
  val notes = H.create 3
  val instrs = H.create 3           (* line nr -> contract_instr_t list *)
  val params = H.create 3           (* name -> param seq nr (starting at 1) *)
  val mutable localvars = []        (* string list *)

  initializer
    List.iteri (fun i name -> H.add params name i) parameters

  method add_postcondition (pc:xpredicate_t) =
    postconditions#add (id#index_xpredicate pc)

  method add_precondition (pre:xpredicate_t) =
    preconditions#add (id#index_xpredicate pre)

  method get_name = name

  method ignore_function = ignorefn

  method private has_local_var (name:string) = List.mem name localvars

  method private get_local_vars = localvars

  method get_postcondition_ixs = postconditions#toList

  method get_precondition_ixs = preconditions#toList

  method get_sideeffect_ixs = sideeffects#toList

  method get_postconditions = List.map id#get_xpredicate postconditions#toList

  method get_preconditions = List.map id#get_xpredicate preconditions#toList

  method get_sideeffects = List.map id#get_xpredicate sideeffects#toList

  method get_notes = H.fold (fun _ v a -> v@a) notes []

  method get_tagged_notes tag = if H.mem notes tag then H.find notes tag else []

  method get_instrs (line:int) =
    if H.mem instrs line then H.find instrs line else []

  method has_instrs (line:int) = H.mem instrs line

  method private read_xml_parameters (node:xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun n ->
        let get = n#getAttribute in
        let geti = n#getIntAttribute in
        H.add params (get "name") (geti "nr")) (getcc "par")

  method private write_xml_parameters (node:xml_element_int) =
    node#appendChildren
      (List.map  (fun (name,nr) ->
           let pnode = xmlElement "par" in
           begin
             pnode#setAttribute "name" name;
             pnode#setIntAttribute "nr" nr;
             pnode
           end)  self#get_params)

  method private get_params = H.fold (fun k v a -> (k,v)::a) params []

  method private read_xml_notes (node:xml_element_int) =
    List.iter (fun n ->
        let has = n#hasNamedAttribute in
        let get = n#getAttribute in
        let note = {
            cn_tag = if has "tag" then get "tag" else "all";
            cn_prq = if has "prq" then get "prq" else "none";
            cn_txt = if has "txt" then get "txt" else "none"} in
        let entry =
          if H.mem notes note.cn_tag then
            H.find notes note.cn_tag
          else
            [] in
        H.replace notes note.cn_tag (note::entry)) (node#getTaggedChildren "note")

  method private write_xml_notes (node:xml_element_int) =
    node#appendChildren
      (List.map (fun n ->
           let nnode = xmlElement "note" in
           begin
             (if n.cn_tag = "all" then
                ()
              else
                nnode#setAttribute "tag" n.cn_tag);
             (if n.cn_prq = "none" then
                ()
              else
                nnode#setAttribute "prq" n.cn_prq);
             (if n.cn_txt = "none" then
                ()
              else
                nnode#setAttribute "txt" n.cn_txt);
             nnode
           end) self#get_notes)

  method private read_xml_postconditions
                   (node:xml_element_int) (gvars:string list) =
    let (post, errorpost) =
      read_xml_postcondition_list node ~gvars self#get_params in
    let _ = match errorpost with
      | [] -> ()
      | _ ->
         raise
           (CCHFailure
              (STR "Error postconditions not supported in function contract")) in
    List.iter (fun (p, _) -> postconditions#add (id#index_xpredicate p)) post

  method private write_xml_postconditions (node:xml_element_int) =
    node#appendChildren
      (List.map (fun ipost ->
           let pnode = xmlElement "post" in
           begin
             write_xmlx_xpredicate pnode self#get_params (id#get_xpredicate ipost);
             pnode
           end) postconditions#toList)

  method private read_xml_preconditions
                   (node:xml_element_int) (gvars:string list) =
    let pre = read_xml_precondition_list node ~gvars self#get_params in
    List.iter (fun (p,_) -> preconditions#add (id#index_xpredicate p)) pre

  method private write_xml_preconditions (node:xml_element_int) =
    node#appendChildren
      (List.map (fun ipre ->
           let pnode = xmlElement "pre" in
           begin
             write_xmlx_xpredicate
               pnode self#get_params (id#get_xpredicate ipre);
             pnode
           end) preconditions#toList)

  method private read_xml_sideeffects
                   (node:xml_element_int) (gvars:string list) =
    let se = read_xml_sideeffect_list node ~gvars self#get_params in
    List.iter (fun (p,_) -> sideeffects#add (id#index_xpredicate p)) se

  method private read_xml_instrs (node:xml_element_int) =
    let setinstrs =
      read_xml_instr_list node self#get_params self#get_local_vars in
    List.iter (fun i ->
        match i with
        | SetVar (line,_,_) ->
           let entry = if H.mem instrs line then H.find instrs line else  [] in
           H.replace instrs line (i::entry)) setinstrs

  method private read_xml_localvars (node:xml_element_int) =
    List.iter
      (fun n -> localvars <- (n#getAttribute "name") :: localvars)
      (node#getTaggedChildren "lvar")

  method private write_xml_localvars (node:xml_element_int) =
    node#appendChildren
      (List.map (fun v ->
           let vnode = xmlElement "lvar" in
           begin
             vnode#setAttribute "name" v;
             vnode
           end) localvars)

  method read_xml (node:xml_element_int) (gvars:string list) =
    let hasc = node#hasOneTaggedChild in
    let getc = node#getTaggedChild in
    try
      begin
        self#read_xml_parameters (getc "parameters");
        (if hasc "notes" then
           self#read_xml_notes (getc "notes"));
        (if hasc "localvars" then
           self#read_xml_localvars (getc "localvars"));
        (if hasc "preconditions" then
           self#read_xml_preconditions (getc "preconditions") gvars);
        (if hasc "postconditions" then
           self#read_xml_postconditions (getc "postconditions") gvars);
        (if hasc "instrs" then
           self#read_xml_instrs (getc "instrs"))
      end
    with
    | CCHFailure p ->
       begin
         ch_error_log#add
           "function contract"
           (LBLOCK [STR "function: "; STR name]);
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Error in reading function contract for ";
                   STR name;
                   STR ": ";
                   p]))
       end
    | XmlReaderError (line,col,p) ->
       let msg =
         LBLOCK [
             STR "Xml error in function contract "; STR name; STR ": "; p] in
       begin
         ch_error_log#add "function contract" msg;
         raise (XmlReaderError (line, col, msg))
       end
    | _ ->
       begin
         ch_error_log#add
           "function contract"
           (LBLOCK [
                STR "Unknown error in reading function contract for ";
                STR name]);
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Unknown error in reading function contract for ";
                   STR name]))
       end

  method write_xmlx (node:xml_element_int) =
    begin
      (if H.length notes > 0  then
         let nnode = xmlElement "notes" in
         begin
           self#write_xml_notes nnode;
           node#appendChildren [nnode]
         end);
      (let parnode = xmlElement "parameters" in
       begin
         self#write_xml_parameters parnode;
         node#appendChildren [parnode]
       end);
      (if List.length localvars > 0 then
         let lnode = xmlElement "localvars" in
         begin
           self#write_xml_localvars lnode;
           node#appendChildren [lnode]
         end);
      (if preconditions#size > 0 then
         let pnode = xmlElement "preconditions" in
         begin
           self#write_xml_preconditions pnode;
           node#appendChildren [pnode]
         end);
      (if postconditions#size > 0  then
         let pnode = xmlElement "postconditions" in
         begin
           self#write_xml_postconditions pnode;
           node#appendChildren [pnode]
         end);
    end

  method postconditions_to_pretty =
    LBLOCK
      (List.map (fun pc ->
           LBLOCK [xpredicate_to_pretty pc; NL]) self#get_postconditions)

  method preconditions_to_pretty =
    LBLOCK
      (List.map (fun pre ->
           LBLOCK [xpredicate_to_pretty pre; NL]) self#get_preconditions)

  method toPretty =
    LBLOCK [
        STR "Postconditions:";
        NL;
        INDENT
          (3,
           LBLOCK
             (List.map
                (fun p ->
                  LBLOCK [xpredicate_to_pretty p; NL])
                self#get_postconditions)); NL]


end


class file_contract_t:file_contract_int =
object (self)

  val mutable globalvars = []
  val functioncontracts = H.create 3   (* name -> function_contract_int *)

  method reset =
    begin
      globalvars <- [];
      H.clear functioncontracts
    end

  method add_function_contract (name:string) (parameters:string list) =
    if H.mem functioncontracts name then
      ch_error_log#add
        "function contract"
        (LBLOCK [STR "Function contract for "; STR name; STR "; not added"])
    else
      let fn = new function_contract_t ~parameters false name in
      H.add functioncontracts name fn

  method add_precondition (fname:string) (pre:xpredicate_t) =
    if H.mem functioncontracts fname then
      let fncontract = H.find functioncontracts fname in
      let gvars = get_xpredicate_global_variables pre in
      let _ =
        List.iter (fun gvname ->
            if self#has_global_variable gvname then
              ()
            else
              self#add_global_variable gvname) gvars in
      fncontract#add_precondition pre

  method get_function_contract (name:string) =
    if H.mem functioncontracts name then
      H.find functioncontracts name
    else
      raise
        (CCHFailure
           (LBLOCK [STR "Function contract for "; STR name; STR " not found"]))

  method private get_function_contracts =
    H.fold (fun _ v a -> v::a) functioncontracts []

  method get_global_variables = globalvars

  method private has_global_variable (vname:string) =
    List.exists (fun gv -> gv.cgv_name = vname) globalvars

  method private get_global_variable (vname:string) =
    try
      List.find (fun gv -> gv.cgv_name = vname) globalvars
    with
    | Not_found ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "contract global variable ";
                 STR vname;
                 STR " not  found"]))

  method gv_is_not_null (vname:string) =
    (self#has_global_variable vname)
    && (self#get_global_variable vname).cgv_notnull

  method gv_field_is_initialized (vname:string) (fname:string) =
    (self#has_global_variable vname)
    && (let gvar = List.find (fun gv -> gv.cgv_name = vname) globalvars in
        (List.mem fname gvar.cgv_initialized_fields)
        || (List.mem "all-fields" gvar.cgv_initialized_fields))

  method get_gv_lower_bound (vname:string) =
    if self#has_global_variable vname then
      (self#get_global_variable vname).cgv_lb
    else
      None

  method get_gv_upper_bound (vname:string) =
    if self#has_global_variable vname then
      (self#get_global_variable vname).cgv_ub
    else
      None

  method has_function_contract (name:string) = H.mem functioncontracts name

  method ignore_function (name:string) =
    H.mem functioncontracts name && (H.find functioncontracts name)#ignore_function

  method private add_global_variable (name:string) =
    let gv = {
        cgv_name = name;
        cgv_value = None;
        cgv_lb = None;
        cgv_ub = None;
        cgv_static = false;
        cgv_const = false;
        cgv_notnull = false;
        cgv_initialized_fields = [] } in
    globalvars <- gv :: globalvars

  method private read_xml_global_variables (node:xml_element_int) =
    if node#hasOneTaggedChild "global-variables" then
      List.iter (fun n ->
          let get = n#getAttribute in
          let geti = n#getIntAttribute in
          let has = n#hasNamedAttribute in
          let gv = {
              cgv_name = get "name";
              cgv_value = if has "value" then Some (geti "value") else None;
              cgv_lb = if has "lb" then Some (geti "lb") else None;
              cgv_ub = if has "ub" then Some (geti "ub") else None;
              cgv_static = has "static" && (get "static" = "yes");
              cgv_const = has "const" && (get "const" = "yes");
              cgv_notnull = has "notnull" && (get "notnull" = "yes");
              cgv_initialized_fields = if has "finit" then [(get "finit")] else []
            } in
          globalvars <- gv :: globalvars)
                ((node#getTaggedChild "global-variables")#getTaggedChildren "gvar")

  method read_xml (node:xml_element_int) =
    try
      begin
        self#read_xml_global_variables node;
        List.iter (fun n ->
            let name = n#getAttribute "name" in
            let _ = ch_info_log#add "function contract" (STR name) in
            let ignorefn =
              n#hasNamedAttribute "ignore" && (n#getAttribute "ignore") = "yes" in
            let c = new function_contract_t ignorefn name in
            begin
              c#read_xml n (List.map (fun gv -> gv.cgv_name) globalvars);
              H.add functioncontracts name c
            end) ((node#getTaggedChild "functions")#getTaggedChildren "function")
      end
    with
    | CCHFailure p ->
       begin
         ch_error_log#add "file contract" p;
         raise (CCHFailure p)
       end
    | XmlReaderError (line,col,p) ->
       raise (XmlReaderError (line,col,p))
    | _ ->
       begin
         ch_error_log#add "file contract" (STR "unknown error");
         raise (CCHFailure (STR "File contract: unknown error"))
       end

  method private write_xml_global_variables (node:xml_element_int) =
    let gvars =
      List.sort (fun g1 g2 ->
          Stdlib.compare g1.cgv_name g2.cgv_name) globalvars in
    node#appendChildren
      (List.map (fun gv ->
           let gnode = xmlElement "gvar" in
           let set = gnode#setAttribute in
           let seti = gnode#setIntAttribute in
           begin
             set "name" gv.cgv_name;
             (match gv.cgv_value with Some n -> seti "value" n | _ -> ());
             (match gv.cgv_lb with Some n -> seti "lb" n | _ -> ());
             (match gv.cgv_ub with Some n -> seti "ub" n | _ -> ());
             (if gv.cgv_static then set "static" "yes");
             (if gv.cgv_const then set "const" "yes");
             (if gv.cgv_notnull then set "notnull" "yes");
             gnode
           end) gvars)

  method private write_xml_function_contracts (node:xml_element_int) =
    let fncontracts =
      List.sort (fun f1 f2 ->
          Stdlib.compare f1#get_name f2#get_name) self#get_function_contracts in
    node#appendChildren
      (List.map  (fun fn ->
           let fnode = xmlElement "function" in
           begin
             fn#write_xmlx fnode;
             fnode#setAttribute "name" fn#get_name;
             fnode
           end) fncontracts)

  method write_xmlx (node:xml_element_int) =
    let gnode = xmlElement "global-variables" in
    let fnode = xmlElement "functions" in
    begin
      self#write_xml_global_variables gnode;
      self#write_xml_function_contracts fnode;
      node#appendChildren [gnode; fnode]
    end

  method toPretty =
    LBLOCK (List.map (fun f -> f#toPretty) self#get_function_contracts)

end


let file_contract = new file_contract_t


class global_contract_t:global_contract_int =
object

  val mutable nofree = false

  method is_nofree = nofree

  method read_xml (node:xml_element_int) =   (* global-assumptions node *)
    List.iter (fun n ->
        match n#getAttribute "name" with
        | "no-free" ->
           begin
             nofree <- true;
             chlog#add "global assumption" (STR "no free")
           end
        | s ->
           begin
             ch_error_log#add
               "global contract"
               (LBLOCK [
                    STR "Global assumption "; STR s; STR " not recognized"]);
             raise
               (CCHFailure
                  (LBLOCK [
                       STR "Global assumption "; STR s; STR " not recognized"]))
           end) (node#getTaggedChildren "ga")

end


let global_contract = new global_contract_t
