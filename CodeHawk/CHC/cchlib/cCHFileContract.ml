(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2026 Aarno Labs LLC

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
open CHPrettyUtil
open CHTimingLog
open CHXmlDocument

(* cchlib *)
open CCHCAttributes
open CCHBasicTypes
open CCHExternalPredicate
open CCHFileEnvironment
open CCHFunctionSummary
open CCHLibTypes
open CCHUtilities

module H = Hashtbl


let id = CCHInterfaceDictionary.interface_dictionary

let p2s = pretty_to_string


let read_xml_instr_list (node:xml_element_int) params lvars =
  List.map
    (fun n -> read_xml_instr n ~lvars params) (node#getTaggedChildren "instr")


class globalvar_contract_t (name: string): globalvar_contract_int =
object (self)

  val name = name
  val mutable lb: int option = None
  val mutable ub: int option = None
  val mutable value: int option = None
  val mutable static: bool = false
  val mutable constant: bool = false
  val mutable not_null: bool = false
  val mutable initialized_fields: string list = []

  method set_lower_bound (lbv: int) = lb <- Some lbv

  method set_upper_bound (ubv: int) = ub <- Some ubv

  method set_value (v: int) = value <- Some v

  method set_static = static <- true

  method set_const = constant <-true

  method set_not_null = not_null <- true

  method add_initialized_field (s: string) =
    initialized_fields <- s :: initialized_fields

  method get_name = name

  method get_lower_bound = lb

  method get_upper_bound = ub

  method get_value = value

  method is_static = static

  method is_const = constant

  method is_not_null = not_null

  method has_lower_bound = match lb with Some _ -> true | _ -> false

  method has_upper_bound = match ub with Some _ -> true | _ -> false

  method read_xml (node: xml_element_int) =
    let get = node#getAttribute in
    let geti = node#getIntAttribute in
    let has = node#hasNamedAttribute in
    begin
      (if has "value" then self#set_value (geti "value"));
      (if has "lb" then self#set_lower_bound (geti "lb"));
      (if has "ub" then self#set_upper_bound (geti "ub"));
      (if has "static" && (get "static") = "yes" then self#set_static);
      (if has "const" && (get "const") = "yes" then self#set_const);
      (if has "notnull" && (get "notnull") = "yes" then self#set_not_null);
      (if has "finit" then self#add_initialized_field (get "finit"))
    end

  method write_xml (node: xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    begin
      set "name" self#get_name;
      (if self#is_static then set "static" "yes");
      (if self#is_const then set "const" "yes");
      (if self#is_not_null then set "notnull" "yes");
      (match self#get_lower_bound with Some lb -> seti "lb" lb | _ -> ());
      (match self#get_upper_bound with Some ub -> seti "ub" ub | _ -> ());
      (match self#get_value with Some v -> seti "value" v | _ -> ());
    end

  method toPretty =
    LBLOCK [
        STR name;
        (match self#get_lower_bound with
         | Some lb -> LBLOCK [STR "; lb: "; INT lb] | _ -> STR "");
        (match self#get_upper_bound with
         | Some ub -> LBLOCK [STR "; ub: "; INT ub] | _ -> STR "");
        (if self#is_static then STR "; static" else STR "");
        (if self#is_const then STR "; const" else STR "");
        (if self#is_not_null then STR "; not-null" else STR "")
      ]

end


class function_contract_t
        ?(parameters=[])
        (ignorefn:bool)
        (name:string):function_contract_int =
object (self)

  val ignorefn = ignorefn
  val postconditions = new CHUtils.IntCollections.set_t
  val errorpostconditions = new CHUtils.IntCollections.set_t
  val preconditions = new CHUtils.IntCollections.set_t
  val sideeffects = new CHUtils.IntCollections.set_t
  val notes = H.create 3
  val instrs = H.create 3           (* line nr -> contract_instr_t list *)
  val params = H.create 3           (* name -> param seq nr (starting at 1) *)
  val mutable localvars = []        (* string list *)

  initializer
    List.iteri (fun i name -> H.add params name i) parameters

  method add_postcondition (pc:xpredicate_t) =
    let ix = id#index_xpredicate pc in
    if postconditions#has ix then
      ()
    else
      begin
        log_info
          "add postcondition %s to %s function contract [%s:%d]"
          (p2s (xpredicate_to_pretty pc))
          name
          __FILE__ __LINE__;
        postconditions#add ix
      end

  method add_error_postcondition (pc: xpredicate_t) =
    let ix = id#index_xpredicate pc in
    if errorpostconditions#has ix then
      ()
    else
      begin
        log_info
          "add error postcondition %s to %s function contract [%s:%d]"
          (p2s (xpredicate_to_pretty pc))
          name
          __FILE__ __LINE__;
        errorpostconditions#add ix
      end

  method add_precondition (pre:xpredicate_t) =
    let ix = id#index_xpredicate pre in
    if preconditions#has ix then
      ()
    else
      begin
        log_info
          "add precondition %s to %s function contract [%s:%d]"
          (p2s (xpredicate_to_pretty pre))
          name
          __FILE__ __LINE__;
        preconditions#add ix
      end

  method add_sideeffect (s: xpredicate_t) =
    let ix = id#index_xpredicate s in
    if sideeffects#has ix then
      ()
    else
      begin
        log_info
          "add side effect %s to %s function contract [%s:%d]"
          (p2s (xpredicate_to_pretty s))
          name
          __FILE__ __LINE__;
        sideeffects#add ix
      end

  method get_name = name

  method ignore_function = ignorefn

  method private has_local_var (name:string) = List.mem name localvars

  method private get_local_vars = localvars

  method get_postcondition_ixs = postconditions#toList

  method get_precondition_ixs = preconditions#toList

  method get_sideeffect_ixs = sideeffects#toList

  method get_postconditions = List.map id#get_xpredicate postconditions#toList

  method get_error_postconditions =
    List.map id#get_xpredicate errorpostconditions#toList

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
    let _ =
      log_info
        "function contract: read %d postconditions, %d error postconditions [%s:%d]"
        (List.length post)
        (List.length errorpost)
        __FILE__ __LINE__ in
    begin
      List.iter (fun (p, _) -> postconditions#add (id#index_xpredicate p)) post;
      List.iter (fun (p, _) ->
          errorpostconditions#add (id#index_xpredicate p)) errorpost
    end

  method private write_xml_postconditions (node:xml_element_int) =
    let _ =
      log_info
        "Write xml postconditions: %d [%s:%d]"
        (List.length postconditions#toList)
        __FILE__ __LINE__ in
    node#appendChildren
      ((List.map (fun ipost ->
            let pnode = xmlElement "post" in
            begin
              write_xmlx_xpredicate
                pnode self#get_params (id#get_xpredicate ipost);
              pnode
            end) postconditions#toList)
       @ (List.map (fun ipost ->
              let pnode = xmlElement "error-post" in
              begin
                write_xmlx_xpredicate
                  pnode self#get_params (id#get_xpredicate ipost);
                pnode
              end) errorpostconditions#toList))

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
    let _ = log_info "function_contract#read_xml [%s:%d]" __FILE__ __LINE__ in
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
      (if postconditions#size > 0 || errorpostconditions#size > 0 then
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

  val globalvars = H.create 3   (* name -> globalvar_contraint_int *)
  val functioncontracts = H.create 3   (* name -> function_contract_int *)

  (* name -> attributes that contributed to the function contract, in
     reverse order: (attribute, recognized, pre, post, side effects); an
     attribute is recognized if it generates conditions or is a contract
     marker *)
  val attributeorigins = H.create 3

  (* names of the functions whose contract was read from the contract file *)
  val contractfilefunctions = H.create 3

  (* names of the application functions declared chkc_exported: their
     postconditions are guarantees of the module (primary proof obligations
     at return sites) *)
  val exportedfunctions = H.create 3

  (* name -> side effects declared on an application function: not used and
     not checked (reported for exported functions) *)
  val declaredsideeffects = H.create 3

  method reset =
    begin
      H.clear globalvars;
      H.clear functioncontracts;
      H.clear attributeorigins;
      H.clear contractfilefunctions;
      H.clear exportedfunctions;
      H.clear declaredsideeffects
    end

  method add_function_contract (name:string) (parameters:string list) =
    if H.mem functioncontracts name then
      ch_error_log#add
        "function contract"
        (LBLOCK [STR "Function contract for "; STR name; STR "; not added"])
    else
      let fn = new function_contract_t ~parameters false name in
      H.add functioncontracts name fn

  method add_globalvar_contract (name: string): globalvar_contract_int =
    if H.mem globalvars name then
      H.find globalvars name
    else
      let gv = new globalvar_contract_t name in
      begin
        H.add globalvars name gv;
        gv
      end

  method add_precondition (fname:string) (pre:xpredicate_t) =
    if H.mem functioncontracts fname then
      let fncontract = H.find functioncontracts fname in
      (* let gvars = get_xpredicate_global_variables pre in
      let _ =
        List.iter (fun gvname ->
            if self#has_global_variable gvname then
              ()
            else
              self#add_global_variable gvname) gvars in *)
      fncontract#add_precondition pre
    else
      log_warning
        "No function contract for %s; unable to add precondition %s [%s:%d]"
        fname
        (p2s (xpredicate_to_pretty pre))
        __FILE__ __LINE__

  method add_postcondition (fname: string) (post: xpredicate_t) =
    if H.mem functioncontracts fname then
      let fncontract = H.find functioncontracts fname in
      fncontract#add_postcondition post
    else
      log_warning
        "No function contract for %s; unable to add postcondition %s [%s:%d]"
        fname
        (p2s (xpredicate_to_pretty post))
        __FILE__ __LINE__

  method add_error_postcondition (fname: string) (post: xpredicate_t) =
    if H.mem functioncontracts fname then
      let fncontract = H.find functioncontracts fname in
      fncontract#add_error_postcondition post
    else
      log_warning
        "No function contract for %s; unable to add error postcondition %s [%s:%d]"
        fname
        (p2s (xpredicate_to_pretty post))
        __FILE__ __LINE__

  method add_sideeffect (fname: string) (s: xpredicate_t) =
    if H.mem functioncontracts fname then
      let fncontract = H.find functioncontracts fname in
      fncontract#add_sideeffect s
    else
      log_warning
        "No function contract for %s; unable to add side effect %s [%s:%d]"
        fname
        (p2s (xpredicate_to_pretty s))
        __FILE__ __LINE__

  method get_function_contract (name:string) =
    if H.mem functioncontracts name then
      H.find functioncontracts name
    else
      raise
        (CCHFailure
           (LBLOCK [STR "Function contract for "; STR name; STR " not found"]))

  method get_globalvar_contract (name: string) =
    if H.mem globalvars name then
      H.find globalvars name
    else
      raise
        (CCHFailure
           (LBLOCK [STR "Global var contract for "; STR name; STR " not found"]))

  method private get_function_contracts =
    H.fold (fun _ v a -> v::a) functioncontracts []

  method get_globalvar_contracts =
    H.fold (fun _ v a -> v::a) globalvars []

  method has_function_contract (name:string) = H.mem functioncontracts name

  method has_globalvar_contract (name: string) = H.mem globalvars name

  method ignore_function (name:string) =
    H.mem functioncontracts name && (H.find functioncontracts name)#ignore_function

  method private read_xml_global_variables (node: xml_element_int) =
    if node#hasOneTaggedChild "global-variables" then
      let xgvars =
        (node#getTaggedChild "global-variables")#getTaggedChildren "gvar" in
      List.iter (fun n ->
          let name = n#getAttribute "name" in
          if H.mem globalvars name then
            ch_error_log#add
              "read_xml_global_variables"
              (LBLOCK [STR "Duplicate encountered for "; STR name])
          else
            let gvarcontract = self#add_globalvar_contract name in
            gvarcontract#read_xml n) xgvars
    else
      ()

  method read_xml (node:xml_element_int) =
    let _ = log_info "file_contract#read_xml [%s:%d]" __FILE__ __LINE__ in
    try
      begin
        self#read_xml_global_variables node;
        List.iter (fun n ->
            let name = n#getAttribute "name" in
            let _ =
              log_info
                "file_contract: read function contract %s [%s:%d]"
                name __FILE__ __LINE__ in
            let _ = ch_info_log#add "function contract" (STR name) in
            let ignorefn =
              n#hasNamedAttribute "ignore" && (n#getAttribute "ignore") = "yes" in
            let c = new function_contract_t ignorefn name in
            begin
              c#read_xml
                n
                (List.map (fun gvc -> gvc#get_name) self#get_globalvar_contracts);
              H.add functioncontracts name c;
              H.replace contractfilefunctions name ()
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

  method private get_globalvar_attributes (gvar: varinfo) =
    match gvar.vattr with
    | [] -> ()
    | attrs ->
       let gvarcontract = self#add_globalvar_contract gvar.vname in
       List.iter (attribute_update_globalvar_contract gvarcontract) attrs

  method private add_function_attribute_conditions
                   (vinfo: varinfo) (attr: attribute) =
    let (xpre, xpost, xside) =
      convert_attribute_to_function_conditions vinfo.vname attr in
    let xerr = convert_attribute_to_error_postconditions vinfo.vname attr in
    let logx kind x =
      log_diagnostics_result
        ~tag:("add_function_attribute_conditions:" ^ kind)
        ~msg:vinfo.vname
        __FILE__ __LINE__
        [p2s (xpredicate_to_pretty x)] in
    let recognized =
      (match (xpre, xpost, xside, xerr) with
       | ([], [], [], []) -> is_contract_marker_attribute attr
       | _ -> true) in
    let origins =
      if H.mem attributeorigins vinfo.vname then
        H.find attributeorigins vinfo.vname
      else
        [] in
    begin
      H.replace
        attributeorigins
        vinfo.vname
        ((attr, recognized, xpre, xpost @ xerr, xside) :: origins);
      List.iter (logx "pre") xpre;
      List.iter (logx "post") xpost;
      List.iter (logx "error-post") xerr;
      List.iter (logx "side") xside;
      List.iter (self#add_precondition vinfo.vname) xpre;
      List.iter (self#add_postcondition vinfo.vname) xpost;
      List.iter (self#add_error_postcondition vinfo.vname) xerr;
      List.iter (self#add_sideeffect vinfo.vname) xside
    end

  method private get_function_attributes (xfun: varinfo) =
    let _ =
      log_info "get_function_attributes for %s [%s:%d]"
        xfun.vname __FILE__ __LINE__ in
    match xfun.vtype with
    | TFun (_returntype, fargs, _varargs, attrs)
      | TPtr (TFun (_returntype, fargs, _varargs, attrs), _) ->
       let pars =
         match fargs with
         | Some plist -> List.map (fun (name, _, _) -> name) plist
         | _ -> [] in
       begin
         (match attrs with
          | [] -> ()
          | _ ->
             begin
               self#add_function_contract xfun.vname pars;
               List.iter (self#add_function_attribute_conditions xfun) attrs
             end);
         (match xfun.vattr with
          | [] -> ()
          | attrs ->
             begin
               self#add_function_contract xfun.vname pars;
               List.iter (self#add_function_attribute_conditions xfun) attrs
             end)
       end
    | _ ->
       ()

  (* Attributes on functions defined in this file (application functions).
     Their pre- and postconditions are conjectures that are checked:
     a precondition becomes an api (contract) assumption of the function,
     checked by the callers' call-site proof obligations; a postcondition
     becomes a return-site proof obligation in the function. Side effects
     of a function with code are used by callers but never checked, so they
     are not taken from attributes (e.g., GCC pure -> preserves-all-memory);
     they are logged instead. A contract is created only if there is at least
     one pre- or postcondition, because the presence of a function contract
     makes callers use its postconditions and side effects instead of the
     call-site postcondition assumptions. *)
  method private get_application_function_attributes (fn: varinfo) =
    let typeattrs =
      match fn.vtype with
      | TFun (_, _, _, attrs) -> attrs
      | _ -> [] in
    let attrs = typeattrs @ fn.vattr in
    let _ =
      if List.exists is_exported_attribute attrs then
        H.replace exportedfunctions fn.vname () in
    let conditions =
      List.map (convert_attribute_to_function_conditions fn.vname) attrs in
    let xpre = List.concat (List.map (fun (p, _, _) -> p) conditions) in
    let xpost = List.concat (List.map (fun (_, p, _) -> p) conditions) in
    (* Out-parameter postconditions (chkc_initializes) of a function with
       code are not checked at its return sites yet (with an error
       discriminator they hold only in the success outcome); they are not
       used, so that callers in this file do not rely on unchecked
       conditions. Callers in other files use them from the declaration
       (external function). *)
    let is_outparam_post (p: xpredicate_t) =
      match p with
      | XInitialized (ArgAddressedValue (ArgValue (ParFormal _, _), _)) -> true
      | _ -> false in
    let (outposts, xpost) = List.partition is_outparam_post xpost in
    let xside = List.concat (List.map (fun (_, _, s) -> s) conditions) in
    let logx kind x =
      log_diagnostics_result
        ~tag:("get_application_function_attributes:" ^ kind)
        ~msg:fn.vname
        __FILE__ __LINE__
        [p2s (xpredicate_to_pretty x)] in
    begin
      List.iter (logx "side effect not used (not checked)") xside;
      List.iter (logx "out-parameter postcondition not used (not checked)")
        outposts;
      (match xside with
       | [] -> ()
       | _ -> H.replace declaredsideeffects fn.vname xside);
      match (xpre, xpost) with
      | ([], []) -> ()
      | _ ->
         let pars =
           match fn.vtype with
           | TFun (_, Some plist, _, _) ->
              List.map (fun (name, _, _) -> name) plist
           | _ -> [] in
         begin
           (if not (self#has_function_contract fn.vname) then
              self#add_function_contract fn.vname pars);
           List.iter (logx "pre") xpre;
           List.iter (logx "post") xpost;
           List.iter (self#add_precondition fn.vname) xpre;
           List.iter (self#add_postcondition fn.vname) xpost
         end
    end

  method collect_file_attributes =
    let appfns = file_environment#get_application_functions in
    let is_defined (v: varinfo) =
      List.exists (fun (f: varinfo) -> f.vname = v.vname) appfns in
    let xfuns =
      List.filter (fun v -> not (is_defined v))
        file_environment#get_external_functions in
    let gvars = file_environment#get_globalvars in
    begin
      List.iter self#get_function_attributes xfuns;
      List.iter self#get_application_function_attributes appfns;
      List.iter self#get_globalvar_attributes gvars
    end

  method private write_xml_global_variables (node:xml_element_int) =
    node#appendChildren
      (List.map (fun gvarc ->
           let gnode = xmlElement "gvar" in
           begin
             gvarc#write_xml gnode;
             gnode
           end) (self#get_globalvar_contracts))

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

  (* The contracts of the external functions (declared, not defined in this
     file) as used by the analysis, with their origin: the attributes on the
     declaration (each with the conditions it generates) and/or the contract
     file. Read by the python front end to classify the specification of
     external functions as complete or partial. A library summary, if present,
     takes precedence over the contract at call sites (create_po_call); this
     is recorded in the summary attribute. *)
  method write_xml_external_contracts (node: xml_element_int) =
    let appfns = file_environment#get_application_functions in
    let is_defined (v: varinfo) =
      List.exists (fun (f: varinfo) -> f.vname = v.vname) appfns in
    let xfuns =
      List.filter (fun v ->
          (not (is_defined v)) && H.mem functioncontracts v.vname)
        file_environment#get_external_functions in
    let xfuns =
      List.sort_uniq (fun v1 v2 -> Stdlib.compare v1.vname v2.vname) xfuns in
    let pnodes tag (preds: xpredicate_t list) =
      List.map (fun p ->
          let pnode = xmlElement tag in
          begin
            pnode#setAttribute "p" (p2s (xpredicate_to_pretty p));
            pnode
          end) preds in
    node#appendChildren
      (List.map (fun (v: varinfo) ->
           let fnode = xmlElement "function" in
           let fncontract = H.find functioncontracts v.vname in
           let origins =
             if H.mem attributeorigins v.vname then
               List.rev (H.find attributeorigins v.vname)
             else
               [] in
           let anodes =
             List.map (fun (attr, recognized, xpre, xpost, xside) ->
                 let anode = xmlElement "attribute" in
                 begin
                   anode#setAttribute "a" (CCHTypesToPretty.attribute_to_string attr);
                   (match attr with
                    | Attr (name, _) -> anode#setAttribute "name" name);
                   (if not recognized then
                      anode#setAttribute "recognized" "no");
                   (if is_contract_marker_attribute attr then
                      anode#setAttribute "marker" "yes");
                   anode#appendChildren
                     ((pnodes "pre" xpre)
                      @ (pnodes "post" xpost)
                      @ (pnodes "side" xside));
                   anode
                 end) origins in
           let cnode = xmlElement "contract" in
           begin
             fnode#setAttribute "name" v.vname;
             (if H.mem contractfilefunctions v.vname then
                fnode#setAttribute "contract-file" "yes");
             (if file_environment#has_external_header v.vname
                 && function_summary_library#has_summary
                      (file_environment#get_external_header v.vname) v.vname then
                fnode#setAttribute "summary" "yes");
             cnode#appendChildren
               ((pnodes "pre" fncontract#get_preconditions)
                @ (pnodes "post" fncontract#get_postconditions)
                @ (pnodes "side" fncontract#get_sideeffects));
             fnode#appendChildren (anodes @ [cnode]);
             fnode
           end) xfuns)

  method is_exported_function (name: string) = H.mem exportedfunctions name

  (* The exported application functions of this file with their declared
     contract: postconditions are guarantees (primary proof obligations),
     preconditions are assumed in this module and checked at the call sites
     in the client modules, side effects are declared but not checked. *)
  method write_xml_exported_functions (node: xml_element_int) =
    let names =
      List.sort Stdlib.compare
        (H.fold (fun k _ a -> k :: a) exportedfunctions []) in
    let pnodes tag (preds: xpredicate_t list) =
      List.map (fun p ->
          let pnode = xmlElement tag in
          begin
            pnode#setAttribute "p" (p2s (xpredicate_to_pretty p));
            pnode
          end) preds in
    node#appendChildren
      (List.map (fun name ->
           let fnode = xmlElement "function" in
           begin
             fnode#setAttribute "name" name;
             (if H.mem functioncontracts name then
                let c = H.find functioncontracts name in
                fnode#appendChildren
                  ((pnodes "pre" c#get_preconditions)
                   @ (pnodes "post" c#get_postconditions)));
             (if H.mem declaredsideeffects name then
                fnode#appendChildren
                  (pnodes "side" (H.find declaredsideeffects name)));
             fnode
           end) names)

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
