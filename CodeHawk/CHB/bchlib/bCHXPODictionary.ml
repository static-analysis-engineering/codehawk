(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs LLC

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

(* xprlib *)
open XprDictionary
open XprTypes
   
(* bchlib *)
open BCHBasicTypes
open BCHDictionary
open BCHDoubleword
open BCHLibTypes
open BCHSumTypeSerializer
open BCHUtilities


let bcd = BCHBCDictionary.bcdictionary
let bd = BCHDictionary.bdictionary
let id = BCHInterfaceDictionary.interface_dictionary


class xpodictionary_t (xd: xprdictionary_int): xpodictionary_int =
object (self)

  val xd = xd
  val xpo_predicate_table = mk_index_table "xpo-predicate-table"

  val mutable tables = []

  initializer
    tables <- [
      xpo_predicate_table
    ]

  method reset =
    begin
      List.iter (fun t -> t#reset) tables
    end

  method xd = xd

  method index_xpo_predicate (xpo: xpo_predicate_t) =
    let tags = [xpo_predicate_mcts#ts xpo] in
    let ib b = if b then 1 else 0 in
    let ix = self#xd#index_xpr in
    let it = bcd#index_typ in
    let key = match xpo with
      | XPOAllocationBase x -> (tags, [ix x])
      | XPOBlockWrite (ty, x1, x2) -> (tags, [it ty; ix x1; ix x2])
      | XPOBuffer (ty, x1, x2) -> (tags, [it ty; ix x1; ix x2])
      | XPOEnum (x, s, b) -> (tags, [ix x; bd#index_string s; ib b])
      | XPOFalse -> (tags, [])
      | XPOFreed x -> (tags, [ix x])
      | XPOFunctional -> (tags, [])
      | XPOFunctionPointer (ty, x) -> (tags, [it ty; ix x])
      | XPOIncludes (x, c) -> (tags, [ix x; id#index_c_struct_constant c])
      | XPOInitialized x -> (tags, [ix x])
      | XPOInitializedRange (ty, x1, x2) -> (tags, [it ty; ix x1; ix x2])
      | XPOInputFormatString x -> (tags, [ix x])
      | XPOInvalidated x -> (tags, [ix x])
      | XPOModified x -> (tags, [ix x])
      | XPONewMemory (x1, x2) -> (tags, [ix x1; ix x2])
      | XPOStackAddress x -> (tags, [ix x])
      | XPOHeapAddress x -> (tags, [ix x])
      | XPOGlobalAddress x -> (tags, [ix x])
      | XPONoOverlap (x1, x2) -> (tags, [ix x1; ix x2])
      | XPONotNull x -> (tags, [ix x])
      | XPONull x -> (tags, [ix x])
      | XPONotZero x -> (tags, [ix x])
      | XPONonNegative x -> (tags, [ix x])
      | XPOPositive x -> (tags, [ix x])
      | XPONullTerminated x -> (tags, [ix x])
      | XPOOutputFormatString x -> (tags, [ix x])
      | XPORelationalExpr (op, x1, x2) ->
         (tags @ [relational_op_mfts#ts op], [ix x1; ix x2])
      | XPOSetsErrno -> (tags, [])
      | XPOStartsThread (x, xl) -> (tags, (ix x) :: (List.map ix xl))
      | XPOTainted x -> (tags, [ix x])
      | XPOValidMem x -> (tags, [ix x])
      | XPODisjunction pl -> (tags, List.map self#index_xpo_predicate pl)
      | XPOConditional (p1, p2) ->
         (tags, [self#index_xpo_predicate p1; self#index_xpo_predicate p2])
    in
    xpo_predicate_table#add key

  method write_xml_xpo_predicate
           ?(tag="ixpo") (node: xml_element_int) (xpo: xpo_predicate_t) =
    node#setIntAttribute tag (self#index_xpo_predicate xpo)

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

end
        

let mk_xpodictionary = new xpodictionary_t
