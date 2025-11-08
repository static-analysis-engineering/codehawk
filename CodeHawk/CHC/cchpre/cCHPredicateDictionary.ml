(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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

(* cchlib *)
open CCHSumTypeSerializer
open CCHUtilities

(* cchpre *)
open CCHPreSumTypeSerializer
open CCHPreTypes

module H = Hashtbl


let cdecls = CCHDeclarations.cdeclarations
let cd = CCHDictionary.cdictionary
let id = CCHInterfaceDictionary.interface_dictionary


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


class predicate_dictionary_t:predicate_dictionary_int =
object (self)

  val po_predicate_table = mk_index_table "po-predicate-table"

  val mutable tables = []

  initializer
    tables <- [po_predicate_table]

  method reset = List.iter (fun t -> t#reset)  tables

  method index_po_predicate (p:po_predicate_t) =
    let tags = [po_predicate_mcts#ts p] in
    let key = match p with
      | PNotNull e
        | PNull e
        | PValidMem e
        | PInScope e
        | PNewMemory e
        | PGlobalAddress e
        | PHeapAddress e
        | PAllocationBase e -> (tags, [cd#index_exp e])
      | PControlledResource (r,e) -> (tags @ [r], [cd#index_exp e])
      | PStackAddressEscape (v,e) ->
         (tags, [cd#index_opt_lval v; cd#index_exp e])
      | PTypeAtOffset (t,e)
        | PLowerBound (t,e)
        | PUpperBound (t,e) -> (tags,[cd#index_typ t; cd#index_exp e])
      | PIndexLowerBound e -> (tags,[cd#index_exp e])
      | PIndexUpperBound (e1,e2) -> (tags,[cd#index_exp e1; cd#index_exp e2])
      | PInitialized v -> (tags,[cd#index_lval v])
      | PLocallyInitialized (vinfo, v) ->
         (tags, [cdecls#index_varinfo vinfo; cd#index_lval v])
      | PInitializedRange (e1, e2) -> (tags,[cd#index_exp e1; cd#index_exp e2])
      | PCast (tfrom, tto, e)
        | PPointerCast(tfrom, tto, e)
        | PFormatCast (tfrom, tto, e) ->
         (tags, [cd#index_typ tfrom; cd#index_typ tto; cd#index_exp e])
      | PSignedToUnsignedCastLB (ikfrom, ikto, e)
        | PSignedToUnsignedCastUB (ikfrom, ikto, e)
        | PUnsignedToSignedCast (ikfrom, ikto, e)
        | PUnsignedToUnsignedCast (ikfrom, ikto, e)
        | PSignedToSignedCastLB (ikfrom, ikto, e)
        | PSignedToSignedCastUB (ikfrom, ikto, e) ->
         (tags @ [ikind_mfts#ts ikfrom; ikind_mfts#ts ikto],
          [cd#index_exp e])
      | PNotZero e
        | PNonNegative e
        | PNullTerminated e -> (tags, [cd#index_exp e])
      | PIntUnderflow (op, e1, e2, ik)
        | PIntOverflow (op, e1, e2, ik)
        | PUIntUnderflow (op, e1, e2, ik)
        | PUIntOverflow (op, e1, e2, ik) ->
         (tags @ [binop_mfts#ts op; ikind_mfts#ts ik],
          [cd#index_exp e1; cd#index_exp e2])
      | PWidthOverflow (e, ik) ->
         (tags @ [ikind_mfts#ts ik], [cd#index_exp e])
      | PPtrLowerBound (t, op, e1, e2)
        | PPtrUpperBound (t,op,e1,e2)
        | PPtrUpperBoundDeref (t, op, e1, e2) ->
         (tags @ [binop_mfts#ts op],
          [cd#index_typ t; cd#index_exp e1; cd#index_exp e2])
      | PCommonBase (e1,e2)
        | PCommonBaseType (e1, e2) -> (tags,[cd#index_exp e1; cd#index_exp e2])
      | PFormatString e -> (tags, [cd#index_exp e])
      | PVarArgs (e,n,el) ->
         (tags, n::(cd#index_exp e)::(List.map cd#index_exp el))
      | PNoOverlap (e1, e2) -> (tags, [cd#index_exp e1; cd#index_exp e2])
      | PValueConstraint e -> (tags, [cd#index_exp e])
      | PDSCondition (c, e) -> (tags, [id#index_ds_condition c; cd#index_exp e])
      | PContract (fid, name,e) -> (tags @ [name], [fid; cd#index_exp e])
      | PConfined e -> (tags, [cd#index_exp e])
      | PMemoryPreserved e -> (tags, [cd#index_exp e])
      | PValuePreserved e -> (tags, [cd#index_exp e])
      | PUniquePointer e -> (tags, [cd#index_exp e])
      | PPreservedAllMemory -> (tags, [])
      | PPreservedAllMemoryX l -> (tags, List.map cd#index_exp l)
      | PContractObligation s -> (tags @ [s], [])
      | PBuffer (e1, e2) -> (tags, [cd#index_exp e1; cd#index_exp e2])
      | PRevBuffer (e1, e2) -> (tags, [cd#index_exp e1; cd#index_exp e2])
      | PDistinctRegion (e, i) -> (tags, [cd#index_exp e; i])
      | POutputParameterInitialized (vinfo, offset) ->
         (tags, [cdecls#index_varinfo vinfo; cd#index_offset offset])
      | POutputParameterUnaltered (vinfo, offset) ->
         (tags, [cdecls#index_varinfo vinfo; cd#index_offset offset])
    in
    po_predicate_table#add key

  method get_po_predicate (index:int):po_predicate_t =
    let name = "po_predicate" in
    let (tags,args) = po_predicate_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "ga" -> PGlobalAddress (cd#get_exp (a 0))
    | "ha" -> PHeapAddress (cd#get_exp (a 0))
    | "cr" -> PControlledResource (t 1, cd#get_exp (a 0))
    | "nn" -> PNotNull (cd#get_exp (a 0))
    | "null" -> PNull (cd#get_exp (a 0))
    | "vm" -> PValidMem (cd#get_exp (a 0))
    | "is" -> PInScope (cd#get_exp (a 0))
    | "sae" -> PStackAddressEscape (cd#get_opt_lval (a 0), cd#get_exp (a 1))
    | "ab" -> PAllocationBase (cd#get_exp (a 0))
    | "tao" -> PTypeAtOffset (cd#get_typ (a 0), cd#get_exp (a 1))
    | "lb" -> PLowerBound (cd#get_typ (a 0), cd#get_exp (a 1))
    | "ub" -> PUpperBound (cd#get_typ (a  0), cd#get_exp (a 1))
    | "ilb" -> PIndexLowerBound (cd#get_exp (a 0))
    | "iub" -> PIndexUpperBound (cd#get_exp (a 0), cd#get_exp (a 1))
    | "i" -> PInitialized (cd#get_lval (a 0))
    | "li" -> PLocallyInitialized (cdecls#get_varinfo (a 0), cd#get_lval (a 1))
    | "ir" -> PInitializedRange (cd#get_exp (a 0), cd#get_exp (a 1))
    | "c" -> PCast (cd#get_typ (a 0), cd#get_typ (a 1), cd#get_exp (a 2))
    | "fc" ->
       PFormatCast (cd#get_typ (a 0), cd#get_typ (a 1), cd#get_exp (a 2))
    | "pc" ->
       PPointerCast (cd#get_typ (a 0), cd#get_typ (a 1), cd#get_exp (a 2))
    | "csul" ->
       PSignedToUnsignedCastLB
         (ikind_mfts#fs (t 1), ikind_mfts#fs (t 2), cd#get_exp (a 0))
    | "csuu" ->
       PSignedToUnsignedCastUB
         (ikind_mfts#fs (t 1), ikind_mfts#fs (t 2), cd#get_exp (a 0))
    | "cus" ->
       PUnsignedToSignedCast
         (ikind_mfts#fs (t 1), ikind_mfts#fs ( t 2), cd#get_exp (a 0))
    | "cuu" ->
       PUnsignedToUnsignedCast
         (ikind_mfts#fs (t 1), ikind_mfts#fs ( t 2), cd#get_exp (a 0))
    | "cssl" ->
       PSignedToSignedCastLB
         (ikind_mfts#fs (t 1), ikind_mfts#fs ( t 2), cd#get_exp (a 0))
    | "cssu" ->
       PSignedToSignedCastUB
         (ikind_mfts#fs (t 1), ikind_mfts#fs ( t 2), cd#get_exp (a 0))
    | "z" -> PNotZero (cd#get_exp (a 0))
    | "nneg" -> PNonNegative (cd#get_exp (a  0))
    | "nt" -> PNullTerminated (cd#get_exp (a 0))
    | "iu" ->
       PIntUnderflow
         (binop_mfts#fs (t 1),
          cd#get_exp (a 0),
          cd#get_exp (a 1),
          ikind_mfts#fs (t 2))
    | "io" ->
       PIntOverflow
         (binop_mfts#fs (t 1),
          cd#get_exp (a 0),
          cd#get_exp (a 1),
          ikind_mfts#fs (t 2))
    | "uiu" ->
       PUIntUnderflow
         (binop_mfts#fs (t 1),
          cd#get_exp (a 0),
          cd#get_exp (a 1),
          ikind_mfts#fs (t 2))
    | "uio" ->
       PUIntOverflow
         (binop_mfts#fs (t 1),
          cd#get_exp (a 0),
          cd#get_exp (a 1),
          ikind_mfts#fs (t 2))
    | "w" -> PWidthOverflow (cd#get_exp (a 0), ikind_mfts#fs (t 1))
    | "plb" ->
       PPtrLowerBound
         (cd#get_typ (a 0),
          binop_mfts#fs (t 1),
          cd#get_exp (a 1),
          cd#get_exp (a 2))
    | "pub" ->
       PPtrUpperBound
         (cd#get_typ (a 0),
          binop_mfts#fs (t 1),
          cd#get_exp (a 1),
          cd#get_exp (a 2))
    | "pubd" ->
       PPtrUpperBoundDeref
         (cd#get_typ (a 0),
          binop_mfts#fs (t 1),
          cd#get_exp (a 1),
          cd#get_exp (a 2))
    | "cb" -> PCommonBase (cd#get_exp (a 0), cd#get_exp (a 1))
    | "cbt" -> PCommonBaseType (cd#get_exp (a 0), cd#get_exp (a 1))
    | "ft" -> PFormatString (cd#get_exp (a 0))
    | "va" ->
       let (n,el) = (List.hd args,List.map cd#get_exp (List.tl args)) in
       PVarArgs (List.hd el, n, List.tl el)
    | "no" -> PNoOverlap (cd#get_exp (a 0), cd#get_exp (a 1))
    | "vc" -> PValueConstraint (cd#get_exp (a 0))
    | "ds" -> PDSCondition (id#get_ds_condition (a 0), cd#get_exp (a 1))
    | "ctt" -> PContract (a 0, t 1, cd#get_exp (a 1))
    | "cf" -> PConfined (cd#get_exp (a 0))
    | "pm" -> PMemoryPreserved (cd#get_exp (a 0))
    | "pv" -> PValuePreserved (cd#get_exp (a 0))
    | "up" -> PUniquePointer (cd#get_exp (a 0))
    | "prm" -> PPreservedAllMemory
    | "prmx" -> PPreservedAllMemoryX (List.map cd#get_exp args)
    | "cob" -> PContractObligation (t 1)
    | "b" -> PBuffer (cd#get_exp (a 0), cd#get_exp (a 1))
    | "rb" -> PRevBuffer (cd#get_exp (a  0), cd#get_exp (a 1))
    | "nm" -> PNewMemory (cd#get_exp (a 0))
    | "dr" -> PDistinctRegion (cd#get_exp (a 0), a 1)
    | "opi" ->
       POutputParameterInitialized
         (cdecls#get_varinfo (a 0), cd#get_offset (a 1))
    | "opu" ->
       POutputParameterUnaltered
         (cdecls#get_varinfo (a 0), cd#get_offset (a 1))
    | s -> raise_tag_error name s po_predicate_mcts#tags


  method read_xml_po_predicate
           ?(tag="ipr") (node:xml_element_int):po_predicate_t =
    self#get_po_predicate (node#getIntAttribute tag)

  method write_xml_po_predicate
           ?(tag="ipr") (node:xml_element_int) (p:po_predicate_t) =
    node#setIntAttribute tag (self#index_po_predicate p)

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

let predicate_dictionary = new predicate_dictionary_t
