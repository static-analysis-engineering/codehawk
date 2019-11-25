(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHXmlDocument

(* xprlib *)
open XprDictionary
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHDeclarations
open CCHDictionary
open CCHLibTypes
open CCHUtilities

(* cchpre *)
open CCHPreSumTypeSerializer
open CCHPreTypes

let cd = CCHDictionary.cdictionary
let id = CCHInterfaceDictionary.interface_dictionary
let ccd = CCHContext.ccontexts
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

let ibool b = if b then 1 else 0

class vardictionary_t (xd:xprdictionary_int) (fdecls:cfundeclarations_int):vardictionary_int =
object (self)

  val xd = xd
  val fdecls = fdecls
  val memory_base_table = mk_index_table "memory-base-table"
  val memory_reference_data_table = mk_index_table "memory-reference-data-table"
  val constant_value_variable_table = mk_index_table "constant-value-variable-table"
  val c_variable_denotation_table = mk_index_table "c-variable-denotation-table"
  val mutable tables = []

  initializer
    tables <- [
      memory_base_table ;
      memory_reference_data_table ;
      constant_value_variable_table;
      c_variable_denotation_table 
    ]

  method xd = xd

  method fdecls = fdecls

  method get_indexed_variables =
    List.map (fun (_,index) -> (index,self#get_c_variable_denotation index))
             c_variable_denotation_table#items

  method index_memory_base (b:memory_base_t) =
    let tags = [ memory_base_mcts#ts b ] in
    let key = 
      match b with
      | CNull i -> (tags,[ i ])
      | CStringLiteral s -> (tags,[ cd#index_string s ])
      | CStackAddress v
        | CGlobalAddress v 
        | CBaseVar v -> (tags, [ xd#index_variable v ])
      | CUninterpreted s -> (tags @ [ s ],[]) in
    memory_base_table#add key

  method get_memory_base (index:int):memory_base_t =
    let name = "memory_base" in
    let (tags,args) = memory_base_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "null" -> CNull (a 0)
    | "str" ->  CStringLiteral (cd#get_string (a 0))
    | "sa" -> CStackAddress (xd#get_variable (a 0))
    | "ga" -> CGlobalAddress (xd#get_variable (a 0))
    | "bv" -> CBaseVar (xd#get_variable (a 0))
    | "ui" -> CUninterpreted (t 1)
    | s -> raise_tag_error name s memory_base_mcts#tags  

  method index_memory_reference_data (m:memory_reference_data_t) =
    let args = [ self#index_memory_base m.memrefbase ;
                 cd#index_typ m.memreftype ] in
    memory_reference_data_table#add ([],args)

  method get_memory_reference_data (index:int) =
    let (_,args) = memory_reference_data_table#retrieve index in
    let a = a "memory_reference_data" args in
    { memrefbase = self#get_memory_base (a 0) ; memreftype = cd#get_typ (a 1) }    

  method index_constant_value_variable (c:constant_value_variable_t) =
    let tags = [ constant_value_variable_mcts#ts c ] in
    let xargs lst = List.map (fun a ->
                        match a with
                        | Some x -> xd#index_xpr x
                        | _ -> (-1)) lst in
    let index_opt_xpr optx =
      match optx with Some x -> xd#index_xpr x | _ -> (-1) in
    let key =
      match c with
      | InitialValue (v,t) ->
         let args = [ xd#index_variable v; cd#index_typ t ] in
         (tags,args)
      | FunctionReturnValue (loc,pctxt,vinfo,xprlist) ->
         let args = [ cdecls#index_location loc ; ccd#index_context pctxt ;
                      vinfo.vid ] in
         let args = args @ (xargs xprlist) in
         (tags,args)
      | ExpReturnValue (loc,pctxt,xpr,xprlist,typ) ->
         let args = [ cdecls#index_location loc ; ccd#index_context pctxt ;
                      xd#index_xpr xpr ; cd#index_typ typ ] in
         let args = args @ (xargs xprlist) in
         (tags,args)
      | FunctionSideEffectValue (loc,pctxt, vinfo,xprlist,argnr,typ) ->
         let args = [ cdecls#index_location loc ; ccd#index_context pctxt ;
                      vinfo.vid ; argnr ; cd#index_typ typ ] in
         let args = args @ (xargs xprlist) in
         (tags,args)
      | ExpSideEffectValue (loc,pctxt,xpr,xprlist,argnr,typ) ->
         let args = [ cdecls#index_location loc ; ccd#index_context pctxt ;
                      xd#index_xpr xpr ; argnr ; cd#index_typ typ ] in
         let args = args @ (xargs xprlist) in
         (tags,args)
      | TaintedValue (v,xoptlb,xoptub,typ) ->
         let args = [ xd#index_variable v ; index_opt_xpr xoptlb ;
                      index_opt_xpr xoptub ; cd#index_typ typ ] in
         (tags,args)
      | ByteSequence (v,xoptlen) ->
         let args = [ xd#index_variable v ; index_opt_xpr xoptlen ] in
         (tags,args)
      | SymbolicValue (x,t) ->
         let args = [ xd#index_xpr x ; cd#index_typ t ] in
         (tags,args)
      | MemoryAddress (i,o) -> (tags, [ i ; cd#index_offset o]) in
    constant_value_variable_table#add key

  method get_constant_value_variable (index:int) =
    let name = "constant_value_variable" in
    let (tags,args) = constant_value_variable_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let xargs lst = List.map (fun x -> if x = (-1) then None else Some (xd#get_xpr x)) lst in
    let get_opt_xpr i = if i = (-1) then None else Some (xd#get_xpr i) in
    match (t 0) with
    | "iv" -> InitialValue (xd#get_variable (a 0), cd#get_typ (a 1))
    | "frv" ->
       let arglist = xargs (get_list_suffix args 3) in
       FunctionReturnValue (cdecls#get_location (a 0), ccd#get_context (a 1),
                            fdecls#get_varinfo_by_vid (a 2), arglist)
    | "erv" ->
       let arglist = xargs (get_list_suffix args 4) in
       ExpReturnValue ( cdecls#get_location (a 0), ccd#get_context (a 1),
                        xd#get_xpr (a 2), arglist, cd#get_typ (a 3))
    | "fsev" ->
       let arglist = xargs (get_list_suffix args 5) in
       FunctionSideEffectValue (cdecls#get_location (a 0),ccd#get_context (a 1),
                                fdecls#get_varinfo_by_vid (a 2), arglist, a 3,cd#get_typ (a 4))
    | "esev" ->
       let arglist = xargs (get_list_suffix args 5) in
       ExpSideEffectValue (cdecls#get_location (a 0), ccd#get_context (a 1),
                           xd#get_xpr (a 2),arglist, a 3, cd#get_typ (a 4))
    | "sv" -> SymbolicValue (xd#get_xpr (a 0), cd#get_typ (a 1))
    | "tv" -> TaintedValue  (xd#get_variable (a 0), get_opt_xpr (a 1),
                             get_opt_xpr (a 2), cd#get_typ (a 3))
    | "bs" -> ByteSequence (xd#get_variable (a 0), get_opt_xpr (a 1))
    | "ma" -> MemoryAddress (a 0, cd#get_offset (a 1))
    | s -> raise_tag_error name s constant_value_variable_mcts#tags


  method index_c_variable_denotation (v:c_variable_denotation_t) =
    let tags = [ c_variable_denotation_mcts#ts v ] in
    let key = 
      match v with
      | LocalVariable (vinfo,o) ->
         let args = [ vinfo.vid ; cd#index_offset o ] in
         (tags,args)
      | GlobalVariable (vinfo,o) ->
         let args = [ vinfo.vid ; cd#index_offset o ] in
         (tags,args)
      | MemoryVariable (i,o) -> (tags, [ i ; cd#index_offset o ])
      | MemoryRegionVariable i -> (tags, [ i ])
      | ReturnVariable t -> (tags,[ cd#index_typ t ])
      | FieldVariable ((fname,ckey)) -> (tags @ [fname],[ckey])
      | CheckVariable (l,t) ->
         let args = [ cd#index_typ t ] @
                      (List.concat (List.map (fun (isppo,id,iexp) -> [ ibool isppo; id; iexp  ]) l)) in
         (tags,args)
      | AuxiliaryVariable c -> (tags,[ self#index_constant_value_variable c ])
      | AugmentationVariable (name,purpose,index) -> (tags @ [ name; purpose ],[ index ]) in
    c_variable_denotation_table#add key

  method get_c_variable_denotation (index:int):c_variable_denotation_t =
    let (tags,args) = c_variable_denotation_table#retrieve index in
    let name = "c_variable_denotation" in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "lv" -> LocalVariable (fdecls#get_varinfo_by_vid (a 0),cd#get_offset (a 1))
    | "gv" -> GlobalVariable (fdecls#get_varinfo_by_vid (a 0), cd#get_offset (a 1))
    | "mv" -> MemoryVariable (a 0, cd#get_offset (a 1))
    | "mrv" -> MemoryRegionVariable (a 0)
    | "rv" -> ReturnVariable (cd#get_typ (a 0))
    | "fv" -> FieldVariable ((t 1,a 0))
    | "cv" ->
       let arglist = list_tripleup (List.tl args) in
       let arglist = List.map (fun (x,y,z) -> (x=1,y,z)) arglist in
       CheckVariable (arglist, cd#get_typ (a 0))
    | "av" -> AuxiliaryVariable (self#get_constant_value_variable (a 0))
    | "xv" -> AugmentationVariable (t 1, t 2, a 0)
    | s -> raise_tag_error name s c_variable_denotation_mcts#tags

     
  method write_xml_memory_base
           ?(tag="imb") (node:xml_element_int) (b:memory_base_t) =
    node#setIntAttribute tag (self#index_memory_base b)

  method read_xml_memory_base
           ?(tag="imb") (node:xml_element_int):memory_base_t =
    self#get_memory_base (node#getIntAttribute tag)

  method write_xml_memory_reference_data
           ?(tag="imrd") (node:xml_element_int) (m:memory_reference_data_t) =
    node#setIntAttribute tag (self#index_memory_reference_data m)

  method read_xml_memory_reference_data
           ?(tag="imrd") (node:xml_element_int):memory_reference_data_t =
    self#get_memory_reference_data (node#getIntAttribute tag)

  method write_xml_constant_value_variable
           ?(tag="icvv") (node:xml_element_int) (c:constant_value_variable_t) =
    node#setIntAttribute tag (self#index_constant_value_variable c)

  method read_xml_constant_value_variable
           ?(tag="icvv") (node:xml_element_int):constant_value_variable_t =
    self#get_constant_value_variable (node#getIntAttribute tag)

  method write_xml_c_variable_denotation
           ?(tag="cvd") (node:xml_element_int) (v:c_variable_denotation_t) =
    node#setIntAttribute tag (self#index_c_variable_denotation v)

  method read_xml_c_variable_denotation
           ?(tag="cvd") (node:xml_element_int):c_variable_denotation_t =
    self#get_c_variable_denotation (node#getIntAttribute tag)                              
  
  method write_xml (node:xml_element_int) =
    let xnode = xmlElement "xpr-dictionary" in
    begin
      node#appendChildren
        (List.map (fun t ->
             let tnode = xmlElement t#get_name in
             begin t#write_xml tnode ; tnode end) tables) ;
      xd#write_xml xnode ;
      node#appendChildren [ xnode ]
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      xd#read_xml (getc "xpr-dictionary") ;
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

  method toPretty =
    LBLOCK (List.map (fun t ->
                LBLOCK [ STR t#get_name ; STR ": " ; INT t#size ; NL ]) tables)


end

let mk_vardictionary = new vardictionary_t
