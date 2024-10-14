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

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHXmlDocument

(* cchlib *)
open CCHLibTypes
open CCHSumTypeSerializer
open CCHUtilities


let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [
        STR "Type ";
        STR name; STR " tag: ";
        STR tag;
        STR " not recognized. Accepted tags: ";
        pretty_print_list accepted (fun s -> STR s) "" ", " ""] in
  begin
    ch_error_log#add "serialization tag" msg;
    raise (CCHFailure msg)
  end


class interface_dictionary_t:interface_dictionary_int =
object (self)

  val api_parameter_table = mk_index_table "api-parameter-table"
  val s_offset_table  = mk_index_table "s-offset-table"
  val s_term_table = mk_index_table "s-term-table"
  val xpredicate_table = mk_index_table "xpredicate-table"
  val postrequest_table = mk_index_table "postrequest-table"
  val postassume_table = mk_index_table "postassume-table"
  val ds_condition_table = mk_index_table "ds-condition-table"
  val mutable tables = []

  initializer
    tables <- [
      api_parameter_table;
      s_offset_table;
      s_term_table;
      xpredicate_table;
      postrequest_table;
      postassume_table;
      ds_condition_table
   ]

  method reset = List.iter (fun t -> t#reset) tables

  method index_api_parameter (a:api_parameter_t) =
    let tags = [api_parameter_mcts#ts a] in
    let key = match a with
      | ParFormal i -> (tags, [i])
      | ParGlobal g -> (tags @ [g], []) in
    api_parameter_table#add key

  method get_api_parameter (index:int) =
    let name = "api_parameter" in
    let (tags,args) = api_parameter_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "pf" -> ParFormal (a 0)
    | "pg" -> ParGlobal (t 1)
    | s -> raise_tag_error name s api_parameter_mcts#tags

  method index_s_offset (s:s_offset_t) =
    let tags = [s_offset_mcts#ts s] in
    let key = match s with
      | ArgNoOffset -> (tags,[])
      | ArgFieldOffset (name,t) ->
         (tags @ [name], [self#index_s_offset t])
      | ArgIndexOffset (index,t) ->
         (tags @ [index#toString],[self#index_s_offset t]) in
    s_offset_table#add key

  method get_s_offset (index:int) =
    let name = "s_offset" in
    let (tags,args) = s_offset_table#retrieve index in
    let t  = t name tags in
    let a  = a name args in
    match (t  0) with
    | "no" -> ArgNoOffset
    | "fo" -> ArgFieldOffset (t 1, self#get_s_offset (a 0))
    | "io" ->
       ArgIndexOffset (mkNumericalFromString (t 1), self#get_s_offset (a 0))
    | s -> raise_tag_error name s s_offset_mcts#tags

  method index_s_term (s:s_term_t) =
    let tags = [s_term_mcts#ts s] in
    let optterm t =
      match t with Some t -> self#index_s_term t | _ -> (-1) in
    let key = match s with
      | ArgValue (p,s) ->
         (tags, [self#index_api_parameter p; self#index_s_offset s])
      | LocalVariable name -> (tags @ [name], [])
      | ExternalState name -> (tags @ [name], [])
      | ReturnValue -> (tags,[])
      | NamedConstant name -> (tags @ [name],[])
      | NumConstant num -> (tags @ [num#toString] ,[])
      | IndexSize t -> (tags, [self#index_s_term t])
      | ByteSize t -> (tags, [self#index_s_term t])
      | ArgAddressedValue (t,s) ->
         (tags, [self#index_s_term t; self#index_s_offset s])
      | ArgNullTerminatorPos t -> (tags, [self#index_s_term t])
      | ArgSizeOfType t -> (tags, [self#index_s_term t])
      | ArithmeticExpr (op,t1,t2) ->
         (tags @ [binop_mfts#ts op],
          [self#index_s_term t1; self#index_s_term t2])
      | FormattedOutputSize t -> (tags, [self#index_s_term t])
      | Region t -> (tags, [self#index_s_term t])
      | RuntimeValue -> (tags,[])
      | ChoiceValue (opt1,opt2) -> (tags, [optterm opt1; optterm opt2]) in
    s_term_table#add key

  method get_s_term (index:int) =
    let name = "s_term" in
    let (tags,args) = s_term_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let optterm n =
      if (a n) = (-1) then None else Some (self#get_s_term (a n)) in
    match (t 0) with
    | "av" -> ArgValue (self#get_api_parameter (a 0), self#get_s_offset (a 1))
    | "lv" -> LocalVariable (t 1)
    | "es" -> ExternalState (t 1)
    | "rv" -> ReturnValue
    | "nc" -> NamedConstant (t 1)
    | "ic" -> NumConstant (mkNumericalFromString (t 1))
    | "is" -> IndexSize (self#get_s_term (a 0))
    | "bs" -> ByteSize (self#get_s_term (a 0))
    | "aa" -> ArgAddressedValue (self#get_s_term (a 0), self#get_s_offset (a 1))
    | "at" -> ArgNullTerminatorPos (self#get_s_term (a 0))
    | "st" -> ArgSizeOfType (self#get_s_term (a 0))
    | "ax" ->
       ArithmeticExpr
         (binop_mfts#fs (t 1), self#get_s_term (a 0), self#get_s_term (a 1))
    | "fs" -> FormattedOutputSize (self#get_s_term (a 0))
    | "rg" -> Region (self#get_s_term (a 0))
    | "rt" -> RuntimeValue
    | "cv" -> ChoiceValue (optterm 0, optterm 1)
    | s -> raise_tag_error name s s_term_mcts#tags

  method index_xpredicate (p:xpredicate_t) =
    let tags = [xpredicate_mcts#ts p] in
    let term = self#index_s_term in
    let optterm t =
      match t with Some t -> self#index_s_term t | _ -> (-1) in
    let key = match p with
      | XAllocationBase t -> (tags, [term t])
      | XBlockWrite (t1,t2) -> (tags, [ term t1; term t2])
      | XBuffer (t1,t2) -> (tags, [term t1; term t2])
      | XConstTerm t -> (tags, [term t])
      | XControlledResource (r,t) -> (tags @ [r], [term t])
      | XExternalStateValue (t1, t2) -> (tags, [term t1; term t2])
      | XFalse -> (tags,[])
      | XFormattedInput t -> (tags, [term t])
      | XFreed t -> (tags, [term t])
      | XFunctional -> (tags, [])
      | XGlobalAddress t -> (tags, [term t])
      | XHeapAddress t -> (tags, [term t])
      | XInitialized t -> (tags, [term t])
      | XInitializedRange (t1, t2) -> (tags, [term t1; term t2])
      | XInitializesExternalState (t1, t2) -> (tags, [term t1; term t2])
      | XInvalidated t -> (tags, [term t])
      | XInputFormatString t -> (tags, [term t])
      | XNewMemory t -> (tags, [term t])
      | XNoOverlap (t1,t2) -> (tags, [term t1; term t2])
      | XNotNull t -> (tags, [term t])
      | XNotZero t -> (tags, [term t])
      | XNonNegative t -> (tags, [term t])
      | XNull t -> (tags, [term t])
      | XNullTerminated t -> (tags, [term t])
      | XOutputFormatString t -> (tags, [term t])
      | XPreservesAllMemory -> (tags, [])
      | XPreservesAllMemoryX l -> (tags,List.map term l)
      | XPreservesMemory t -> (tags,[term t])
      | XPreservesNullTermination -> (tags, [])
      | XPreservesValue t -> (tags, [term t])
      | XPreservesValidity t -> (tags, [term t])
      | XRepositioned t -> (tags, [term t])
      | XRelationalExpr (op,t1,t2) ->
         (tags @ [binop_mfts#ts op], [term t1; term t2])
      | XRevBuffer (t1,t2) -> (tags, [term t1; term t2])
      | XStackAddress t -> (tags, [term t])
      | XConfined t -> (tags,[term t])
      | XTainted (t,opt1,opt2) -> (tags, [term t; optterm opt1; optterm opt2])
      | XUniquePointer t -> (tags, [term t])
      | XValidMem t -> (tags, [term t])
      | XPolicyPre (t,pname,pstates) -> (tags @ (pname :: pstates), [term t])
      | XPolicyValue (t,pname,None) -> (tags @ [pname], [term t])
      | XPolicyValue (t,pname,Some tname) -> (tags @ [pname; tname], [term t])
      | XPolicyTransition (t,pname,ptrans) ->
         (tags @ [pname; ptrans], [term t]) in
    xpredicate_table#add key

  method get_xpredicate (index:int) =
    let name = "xpredicate" in
    let (tags,args) = xpredicate_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let term n = self#get_s_term (a n) in
    let optterm n =
      if (a n) = (-1) then None else Some (self#get_s_term (a n)) in
    match (t 0) with
    | "ab" -> XAllocationBase (term 0)
    | "bw" -> XBlockWrite (term 0, term 1)
    | "b" -> XBuffer (term 0, term 1)
    | "c" -> XConstTerm (term 0)
    | "cf" -> XConfined (term 0)
    | "cr" -> XControlledResource (t 1, term 0)
    | "esv" -> XExternalStateValue (term 0, term 1)
    | "f" -> XFalse
    | "fi" -> XFormattedInput (term 0)
    | "fn" -> XFunctional
    | "fr" -> XFreed (term 0)
    | "ga" -> XGlobalAddress (term 0)
    | "ha" -> XHeapAddress (term 0)
    | "i" -> XInitialized (term 0)
    | "ies" -> XInitializesExternalState (term 0, term 1)
    | "ir" -> XInitializedRange (term 0, term 1)
    | "ifs" -> XInputFormatString (term 0)
    | "iv" -> XInvalidated (term 0)
    | "nm" -> XNewMemory (term 0)
    | "nn" -> XNotNull (term 0)
    | "no" -> XNoOverlap (term 0, term 1)
    | "nt" -> XNullTerminated (term 0)
    | "nz" -> XNotZero (term 0)
    | "nng" -> XNonNegative (term 0)
    | "null" -> XNull (term 0)
    | "ofs" -> XOutputFormatString (term 0)
    | "pr" -> XPreservesMemory (term 0)
    | "prm" -> XPreservesAllMemory
    | "prmx" -> XPreservesAllMemoryX (List.map self#get_s_term args)
    | "prn" -> XPreservesNullTermination
    | "pv" -> XPreservesValue (term 0)
    | "prv" -> XPreservesValidity (term 0)
    | "rep" -> XRepositioned (term 0)
    | "rb" -> XRevBuffer (term 0, term 1)
    | "sa" -> XStackAddress (term 0)
    | "tt" -> XTainted (term 0, optterm 1, optterm 2)
    | "up" -> XUniquePointer (term 0)
    | "vm" -> XValidMem (term 0)
    | "pop" -> XPolicyPre (term 0, t 1, (List.tl (List.tl tags)))
    | "pov" ->
       if (List.length tags) = 2 then
         XPolicyValue (term 0, t 1,None)
       else
         XPolicyValue (term 0, t 1, Some (t 2))
    | "pox" -> XPolicyTransition (term 0, t 1, t 2)
    | "x" -> XRelationalExpr (binop_mfts#fs (t 1), term 0, term 1)
    | s -> raise_tag_error name s xpredicate_mcts#tags

  method index_postrequest (pr:postrequest_t) =
    let (fvid,pc) = pr in
    postrequest_table#add ([],[fvid; self#index_xpredicate pc])

  method get_postrequest (index:int) =
    let (_,args) = postrequest_table#retrieve index in
    let a = a "postrequest" args in
    (a 0, self#get_xpredicate (a 1))

  method index_postassume (pa:postassume_t) =
    let (fvid,pc) = pa in
    postassume_table#add ([],[fvid; self#index_xpredicate pc])

  method get_postassume (index:int) =
    let (_,args) = postassume_table#retrieve index in
    let a = a "postassume" args in
    (a 0, self#get_xpredicate (a 1))
  method index_ds_condition (d:ds_condition_t) =
    let tags = [d.dsc_name] in
    let args = [d.dsc_ckey] @ (List.map self#index_xpredicate d.dsc_fields) in
    ds_condition_table#add (tags,args)

  method get_ds_condition (index:int) =
    let (tags,args) = ds_condition_table#retrieve index in
    let t = t "ds_condition" tags in
    { dsc_name = t 0; dsc_ckey = List.hd args;
      dsc_fields = List.map self#get_xpredicate (List.tl args) }

  method write_xml_api_parameter
           ?(tag="iiap") (node:xml_element_int) (p:api_parameter_t) =
    node#setIntAttribute tag (self#index_api_parameter p)

  method read_xml_api_parameter ?(tag="iiap") (node:xml_element_int) =
    self#get_api_parameter (node#getIntAttribute tag)

  method write_xml_s_term ?(tag="iit") (node:xml_element_int) (t:s_term_t) =
    node#setIntAttribute tag (self#index_s_term t)

  method read_xml_s_term ?(tag="iit") (node:xml_element_int) =
    self#get_s_term (node#getIntAttribute tag)

  method write_xml_xpredicate
           ?(tag="ixpre") (node:xml_element_int) (p:xpredicate_t) =
    node#setIntAttribute tag (self#index_xpredicate p)

  method read_xml_xpredicate
           ?(tag="ixpre") (node:xml_element_int):xpredicate_t =
    self#get_xpredicate (node#getIntAttribute tag)

  method write_xml_postrequest
           ?(tag="iipr") (node:xml_element_int) (p:postrequest_t) =
    node#setIntAttribute tag (self#index_postrequest p)

  method read_xml_postrequest ?(tag="iipr") (node:xml_element_int) =
    self#get_postrequest (node#getIntAttribute tag)

  method write_xml_ds_condition
           ?(tag="idsc") (node:xml_element_int) (d:ds_condition_t) =
    node#setIntAttribute tag (self#index_ds_condition d)

  method read_xml_ds_condition
           ?(tag="idsc") (node:xml_element_int):ds_condition_t =
    self#get_ds_condition (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end


let interface_dictionary = new interface_dictionary_t
