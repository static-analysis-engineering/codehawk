(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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
open CHBounds
open CHCommon
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHIndexTable
open CHStringIndexTable
open CHSumTypeSerializer
open CHXmlDocument

(* xprlib *)
open XprTypes
open XSumTypeSerializer


class xprdictionary_t:xprdictionary_int =
object (self)

  val numerical_table = mk_index_table "numerical-table"
  val bound_table = mk_index_table  "bound-table"
  val interval_table = mk_index_table "interval-table"
  val symbol_table = mk_index_table "symbol-table"
  val variable_table = mk_index_table "variable-table"
  val xcst_table = mk_index_table "xcst-table"
  val xpr_table = mk_index_table "xpr-table"
  val xpr_list_table = mk_index_table "xpr-list-table"
  val xpr_list_list_table = mk_index_table "xpr-list-list-table"
  val mutable tables = []

  initializer
    tables <- [
      numerical_table ;
      bound_table ;
      interval_table ;
      symbol_table ;
      variable_table ;
      xcst_table ;
      xpr_table ;
      xpr_list_table ;
      xpr_list_list_table
    ]

  method index_numerical (n:numerical_t) = numerical_table#add ([n#toString],[])

  method get_numerical (index:int) =
    let (tags,args) = numerical_table#retrieve index in
    let t = t "numerical" tags in
    mkNumericalFromString (t 0)

  method index_bound (b:bound_t) =
    let key =
      match b#getBound with
      | MINUS_INF -> (["m"],[])
      | PLUS_INF -> (["p"],[])
      | NUMBER n -> (["n"],[self#index_numerical n]) in
    bound_table#add key

  method get_bound (index:int) =
    let (tags,args) = bound_table#retrieve index in
    let t = t "bound" tags in
    let a = a "bound" args in
    match (t 0) with
    | "m" -> minus_inf_bound
    | "p" -> plus_inf_bound
    | "n" -> bound_of_num (self#get_numerical (a 0))
    | s ->
       raise (CHFailure (LBLOCK [ STR "Tag " ; STR s ;
                                  STR " not recognized for bounds " ]))

  method index_interval (i:interval_t) =
    let key = ([],[ self#index_bound i#getMin ; self#index_bound i#getMax]) in
    interval_table#add key

  method get_interval (index:int) =
    let (tags,args) = interval_table#retrieve index in
    let a = a "interval" args in
    new interval_t (self#get_bound (a 0)) (self#get_bound (a 1))     

  method index_symbol (s:symbol_t) =
    let tags = s#getBaseName :: s#getAttributes in
    let args = [ s#getSeqNumber ] in
    symbol_table#add (tags,args)

  method get_symbol (index:int) =
    let (tags,args) = symbol_table#retrieve index in
    let t = t "symbol" tags in
    let a = a "symbol" args in
    let name = t 0 in
    let atts = List.tl tags in
    let seqnr = a 0 in
    new symbol_t ~atts ~seqnr name 

  method index_variable (v:variable_t) =
    let tags = [ variable_type_mfts#ts v#getType ] in
    let args = [ self#index_symbol v#getName ] in
    variable_table#add (tags,args)

  method get_variable (index:int) =
    let (tags,args) = variable_table#retrieve index in
    let t = t "variable" tags in
    let a = a "variable" args in
    let vtype = variable_type_mfts#fs (t 0) in
    let name = self#get_symbol (a 0) in
    new variable_t name vtype

  method index_xcst (c:xcst_t) =
    let tags = [ xcst_mcts#ts c ] in
    match c with
    | SymSet l ->
       let args = List.map self#index_symbol l in
       xcst_table#add (tags,args)
    | IntConst n ->
       let args = [ self#index_numerical n ] in
       xcst_table#add (tags,args)
    | BoolConst b ->
       let args = [ if b then 1 else 0 ] in
       xcst_table#add (tags,args)
    | XRandom | XUnknownInt | XUnknownSet ->
       xcst_table#add (tags,[])

  method get_xcst (index:int) =
    let (tags,args) = xcst_table#retrieve index in
    let t = t "xcst" tags in
    let a = a "xcst" args in
    match (t 0) with
    | "ss" -> SymSet (List.map self#get_symbol args)
    | "ic" -> IntConst (self#get_numerical (a 0))
    | "bc" -> BoolConst ((a 0) = 1)
    | "r" -> XRandom
    | "ui" -> XUnknownInt
    | "us" -> XUnknownSet
    | s ->
       raise (CHFailure (LBLOCK [ STR "Tag " ; STR s ;
                                  STR " not recognized for xcst " ]))

  method index_xpr (x:xpr_t) =
    let tags = [ xpr_mcts#ts x ] in
    match x with
    | XVar v ->
       let args = [ self#index_variable v ] in
       xpr_table#add (tags,args)
    | XConst c ->
       let args = [ self#index_xcst c ] in
       xpr_table#add (tags,args)
    | XOp (op,l) ->
       let tags = tags @ [ xop_mfts#ts op ] in
       let args = List.map self#index_xpr l in
       xpr_table#add (tags,args)
    | XAttr (s,x) ->
       let tags = tags @ [ s ] in
       let args = [ self#index_xpr x ] in
       xpr_table#add (tags,args)

  method get_xpr (index:int) =
    let (tags,args) = xpr_table#retrieve index in
    let t = t "xpr" tags in
    let a = a "xpr" args in
    match (t 0) with
    | "v" -> XVar (self#get_variable (a 0))
    | "c" -> XConst (self#get_xcst (a 0))
    | "x" -> XOp (xop_mfts#fs (t 1),List.map self#get_xpr args)
    | "a" -> XAttr (t 1, self#get_xpr (a 0))
    | s ->
       raise (CHFailure (LBLOCK [ STR "Tag " ; STR s ;
                                  STR " not recognized for xpr" ]))

  method index_xpr_list (l:xpr_t list) =
    xpr_list_table#add ([],List.map self#index_xpr l)

  method get_xpr_list (index:int) =
    let (_,args) = xpr_list_table#retrieve index in
    List.map self#get_xpr args

  method index_xpr_list_list (l:xpr_t list list) =
    xpr_list_list_table#add ([], List.map self#index_xpr_list l)

  method get_xpr_list_list (index:int) =
    let (_,args) = xpr_list_list_table#retrieve index in
    List.map self#get_xpr_list args

  method write_xml_numerical ?(tag="in") (node:xml_element_int) (n:numerical_t) =
    node#setIntAttribute tag (self#index_numerical n)

  method read_xml_numerical ?(tag="in") (node:xml_element_int):numerical_t =
    self#get_numerical (node#getIntAttribute tag)

  method write_xml_symbol ?(tag="isym") (node:xml_element_int) (s:symbol_t) =
    node#setIntAttribute tag (self#index_symbol s)

  method read_xml_symbol ?(tag="isym") (node:xml_element_int):symbol_t =
    self#get_symbol (node#getIntAttribute tag)

  method write_xml_variable ?(tag="ivar") (node:xml_element_int) (v:variable_t) =
    node#setIntAttribute tag (self#index_variable v)

  method read_xml_variable ?(tag="ivar") (node:xml_element_int):variable_t =
    self#get_variable (node#getIntAttribute tag)

  method write_xml_xcst ?(tag="icst") (node:xml_element_int) (c:xcst_t) =
    node#setIntAttribute tag (self#index_xcst c)

  method read_xml_xcst ?(tag="icst") (node:xml_element_int):xcst_t =
    self#get_xcst (node#getIntAttribute tag)

  method write_xml_xpr ?(tag="ixpr") (node:xml_element_int) (x:xpr_t) =
    node#setIntAttribute tag (self#index_xpr x)

  method read_xml_xpr ?(tag="ixpr") (node:xml_element_int):xpr_t =
    self#get_xpr (node#getIntAttribute tag)

  method write_xml_xpr_list ?(tag="ixprl") (node:xml_element_int) (x:xpr_t list) =
    node#setIntAttribute tag (self#index_xpr_list x)

  method read_xml_xpr_list ?(tag="ixprl") (node:xml_element_int):xpr_t list =
    self#get_xpr_list (node#getIntAttribute tag)

  method write_xml_xpr_list_list ?(tag="ixprll") (node:xml_element_int) (x:xpr_t list list) =
    node#setIntAttribute tag (self#index_xpr_list_list x)

  method read_xml_xpr_list_list ?(tag="ixprll") (node:xml_element_int):xpr_t list list =
    self#get_xpr_list_list (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map (fun t ->
           let tnode = xmlElement t#get_name in
           begin t#write_xml tnode ; tnode end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK (List.map (fun t ->
                LBLOCK [ STR t#get_name ; STR ": " ; INT t#size ; NL ]) tables)

end

let mk_xprdictionary () = new xprdictionary_t
