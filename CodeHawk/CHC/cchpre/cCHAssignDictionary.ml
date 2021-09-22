(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHIndexTable
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHDictionary
open CCHLibTypes
open CCHSumTypeSerializer
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHPreSumTypeSerializer
open CCHPreTypes

module H = Hashtbl


let cd = CCHDictionary.cdictionary
let cdecls = CCHDeclarations.cdeclarations

let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [ STR "Type " ; STR name ; STR " tag: " ; STR tag ;
             STR " not recognized. Accepted tags: " ;
             pretty_print_list accepted (fun s -> STR s) "" ", " "" ] in
  begin
    ch_error_log#add "serialization tag" msg ;
    raise (CCHFailure msg)
  end

let mk_assignment
      (fname:string)
      (env:cfundeclarations_int)
      (loc:location)
      (ctxt:program_context_int)
      (lhs:lval)
      (rhs:exp) =
  let isfield = is_field_offset (snd lhs) in
  let data = {
      asg_rhs = rhs ;
      asg_loc = loc ;
      asg_context = ctxt } in
  match lhs with
  | (Var (vname,vid),NoOffset) ->
     let vinfo = env#get_varinfo_by_vid vid in
     if vinfo.vglob then
       match vinfo.vstorage with
       | Static -> Some (StaticAssignment (fname,vname,vid,data))
       | _ -> Some (GlobalAssignment (fname,vname,vid,data))
     else
       None
  | (Var (vname,vid),Index (Const (CInt64 (i64,_,_)),NoOffset)) ->
     let vinfo = env#get_varinfo_by_vid vid in
     if vinfo.vglob then
       let index = Int64.to_int i64 in
       match vinfo.vstorage with
       | Static -> Some (StaticIndexAssignment (fname,vname,vid,index,data))
       | _ -> Some (GlobalIndexAssignment (fname,vname,vid,index,data))
     else
       None           
  | (_,o) when isfield ->
     let (fieldname,ckey) = get_field_offset o in
     Some (FieldAssignment (fname,fieldname,ckey,lhs,data))
  | _ ->
     Some (UnknownAssignment (fname,lhs,data))

class assignment_dictionary_t:assignment_dictionary_int =
object (self)

  val function_name_table = mk_index_table "function-name-table"
  val assignment_table = mk_index_table "assignment-table"
  val global_value_table = mk_index_table "global-value-table"

  val mutable tables = []

  initializer
    tables <- [function_name_table; assignment_table; global_value_table]

  method reset = List.iter (fun t -> t#reset) tables

  method get_assignments =
    List.map (fun (_,index) ->
        self#get_assignment index) assignment_table#items

  method get_global_values =
    List.map (fun (_,index) ->
        self#get_global_value index) global_value_table#items

  method private index_function_name (name:string) =
    function_name_table#add ([name],[])

  method private get_function_name (index:int) =
    let (tags,_) = function_name_table#retrieve index in
    List.hd tags

  method index_assignment (a:assignment_t) =
    let tags = [ assignment_mcts#ts a ] in
    let argsdata d =
      [cd#index_exp d.asg_rhs;
       cdecls#index_location d.asg_loc;
       ccontexts#index_context d.asg_context] in
    let ifun = self#index_function_name in
    let key = match a with
      | InitAssignment (vname,vid,init) ->
         (tags @ [ vname ], [ vid ; cdecls#index_init init ])
      | GlobalAssignment (fname,vname,vid,data) ->
         (tags @ [ vname ], [ vid ; ifun fname ] @ (argsdata data))
      | GlobalIndexAssignment (fname,vname,vid,index,data) ->
         (tags @ [ vname ], [ vid ; ifun fname ; index ] @ (argsdata data))
      | StaticAssignment (fname,vname,vid,data) ->
         (tags @ [ vname ], [ vid ; ifun fname ] @ (argsdata data))
      | StaticIndexAssignment (fname,vname,vid,index,data) ->
         (tags @ [ vname ], [ vid ; ifun fname ; index ] @ (argsdata data))
      | FieldAssignment (fname,fieldname,ckey,lval,data) ->
         (tags @ [ fieldname ] ,
          [ ckey ; ifun fname ; cd#index_lval lval ] @ (argsdata data))
      | UnknownAssignment (fname,lval,data) ->
         (tags, [ ifun fname; cd#index_lval lval ] @ (argsdata data)) in
    assignment_table#add key

  method get_assignment (index:int):assignment_t =
    let name = "assignment" in
    let (tags,args) = assignment_table#retrieve index in
    let f = self#get_function_name in
    let a = a name args in
    let t = t name tags in
    let d n = {
        asg_rhs = cd#get_exp (a n) ;
        asg_loc = cdecls#get_location (a (n+1)) ;
        asg_context = ccontexts#get_context (a (n+2)) } in
    match (t 0) with
    | "init" -> InitAssignment (t 1, a 0, cdecls#get_init (a 1))
    | "g" -> GlobalAssignment (f (a 1), t 1, a 0, d 2)
    | "gi" -> GlobalIndexAssignment (f (a 1), t 1, a 0, a 1, d 3)
    | "s" -> StaticAssignment (f (a 1), t 1, a 0, d 2)
    | "si" -> StaticIndexAssignment (f (a 1), t 1, a 0, a 1, d 3)
    | "f" -> FieldAssignment (f (a 1), t 1, a 0, cd#get_lval (a 2), d 3)
    | "u" -> UnknownAssignment (f (a 0), cd#get_lval (a 1), d 2)
    | s -> raise_tag_error name s assignment_mcts#tags

  method index_global_value (v:global_value_t) =
    let tags = [ global_value_mcts#ts v ] in
    let key = match v with
      | GlobalValue (vname,vid,initexp, exps) ->
         let initix = match initexp with
           | Some e -> cd#index_exp e
           | _ -> (-1) in
         (tags @ [vname ], [vid; initix] @ (List.map cd#index_exp exps)) in
    global_value_table#add key

  method get_global_value (index:int) =
    let name = "global_value" in
    let (tags,args) = global_value_table#retrieve index in
    let a = a name args in
    let t = t name tags in
    match (t 0) with
    | "gv" ->
       let init =
         if (a 1) = -1 then
           None
         else
           Some (cd#get_exp (a 1)) in
       let exps = List.map cd#get_exp (get_list_suffix args 2) in
       GlobalValue(t 1, a 0, init, exps)
    | s -> raise_tag_error name s  global_value_mcts#tags

  method read_xml_assignment
           ?(tag="iasg") (node:xml_element_int):assignment_t =
    self#get_assignment (node#getIntAttribute tag)

  method write_xml_assignment
           ?(tag="iasg") (node:xml_element_int) (a:assignment_t) =
    node#setIntAttribute tag (self#index_assignment a)

  method read_xml_global_value
           ?(tag="igv") (node:xml_element_int):global_value_t =
    self#get_global_value (node#getIntAttribute tag)

  method write_xml_global_value
           ?(tag="igv") (node:xml_element_int) (gv:global_value_t) =
    node#setIntAttribute tag (self#index_global_value gv)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin t#write_xml tnode; tnode end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK (
        List.map (fun t ->
            LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end

let assigndictionary = new assignment_dictionary_t
