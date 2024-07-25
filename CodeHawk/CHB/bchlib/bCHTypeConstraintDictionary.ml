(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHBCSumTypeSerializer
open BCHLibTypes
open BCHSumTypeSerializer


let bd = BCHDictionary.bdictionary


let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [
        STR "Type ";
        STR name;
        STR " tag: ";
        STR tag;
        STR " not recognized. Accepted tags: ";
        pretty_print_list accepted (fun s -> STR s) "" ", " ""] in
  begin
    ch_error_log#add "serialization tag" msg;
    raise (BCH_failure msg)
  end


class type_constraint_dictionary_t: type_constraint_dictionary_int =
object (self)

  val type_basevar_table = mk_index_table "type-base-variable"
  val type_caplabel_table = mk_index_table "type-cap-label-table"
  val type_variable_table = mk_index_table "type-variable-table"
  val type_constant_table = mk_index_table "type-constant-table"
  val type_term_table = mk_index_table "type-term-table"
  val type_constraint_table = mk_index_table "type-constraint-table"

  val mutable tables= []

  initializer
    tables <- [
      type_basevar_table;
      type_caplabel_table;
      type_variable_table;
      type_constant_table;
      type_term_table;
      type_constraint_table
    ]

  method index_type_basevar (v: type_base_variable_t) =
    let tags = [type_base_variable_mcts#ts v] in
    let key =
      match v with
      | FunctionType s -> (tags @ [s], [])
      | DataAddressType s -> (tags @ [s], [])
      | GlobalVariableType s -> (tags @ [s], [])
      | RegisterLhsType (r, faddr, iaddr) ->
         (tags @ [faddr; iaddr], [bd#index_register r])
      | LocalStackLhsType (off, faddr, iaddr) ->
         (tags @ [faddr; iaddr], [off]) in
    type_basevar_table#add key

  method get_type_basevar (index: int): type_base_variable_t =
    let name = "type_base_variable_t" in
    let (tags, args) = type_basevar_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "f" -> FunctionType (t 1)
    | "d" -> DataAddressType (t 1)
    | "g" -> GlobalVariableType (t 1)
    | "r" -> RegisterLhsType (bd#get_register (a 0), t 1, t 2)
    | "s" -> LocalStackLhsType (a 0, t 1, t 2)
    | s -> raise_tag_error name s type_base_variable_mcts#tags

  method index_type_caplabel (c: type_cap_label_t) =
    let tags = [type_cap_label_mcts#ts c] in
    let key =
      match c with
      | FRegParameter r -> (tags, [bd#index_register r])
      | FStackParameter (size, offset) -> (tags, [size; offset])
      | FLocStackAddress offset -> (tags, [offset])
      | FReturn -> (tags, [])
      | Load -> (tags, [])
      | Store -> (tags, [])
      | Deref -> (tags, [])
      | LeastSignificantByte -> (tags, [])
      | LeastSignificantHalfword -> (tags, [])
      | OffsetAccess (size, off) -> (tags, [size; off])
      | OffsetAccessA (size, off) -> (tags, [size; off]) in
    type_caplabel_table#add key

  method get_type_caplabel (index: int): type_cap_label_t =
    let name = "type_cap_label_t" in
    let (tags, args) = type_caplabel_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "fr" -> FRegParameter (bd#get_register (a 0))
    | "fs" -> FStackParameter (a 0, a 1)
    | "sa" -> FLocStackAddress (a 0)
    | "fx" -> FReturn
    | "l" -> Load
    | "s" -> Store
    | "d" -> Deref
    | "lsb" -> LeastSignificantByte
    | "lsh" -> LeastSignificantHalfword
    | "a" -> OffsetAccess (a 0, a 1)
    | "aa" -> OffsetAccessA (a 0, a 1)
    | s -> raise_tag_error name s type_cap_label_mcts#tags

  method index_type_variable (v: type_variable_t) =
    let key =
      ([],
       ((self#index_type_basevar v.tv_basevar)
        :: (List.map self#index_type_caplabel v.tv_capabilities))) in
    type_variable_table#add key

  method get_type_variable (index: int): type_variable_t =
    let name = "type_variable_t" in
    let (_, args) = type_variable_table#retrieve index in
    let a = a name args in
    {tv_basevar = self#get_type_basevar (a 0);
     tv_capabilities = List.map self#get_type_caplabel (List.tl args)}

  method index_type_constant (c: type_constant_t) =
    let tags = [type_constant_mcts#ts c] in
    let key =
      match c with
      | TyAsciiDigit -> (tags, [])
      | TyAsciiCapsLetter -> (tags, [])
      | TyAsciiSmallLetter -> (tags, [])
      | TyAsciiControl -> (tags, [])
      | TyAsciiPrintable -> (tags, [])
      | TyAscii -> (tags, [])
      | TyExtendedAscii -> (tags, [])
      | TyZero -> (tags, [])
      | TyTInt k -> (tags @ [ikind_mfts#ts k], [])
      | TyTStruct (key, name) -> (tags @ [name], [key])
      | TyTFloat k -> (tags @ [fkind_mfts#ts k], [])
      | TyBottom -> (tags, [])
      | TyTUnknown -> (tags, []) in
    type_constant_table#add key

  method get_type_constant (index: int): type_constant_t =
    let name = "type_constant_t" in
    let (tags, args) = type_constant_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "ad" -> TyAsciiDigit
    | "acl" -> TyAsciiCapsLetter
    | "asl" -> TyAsciiSmallLetter
    | "ac" -> TyAsciiControl
    | "ap" -> TyAsciiPrintable
    | "a" -> TyAscii
    | "ax" -> TyExtendedAscii
    | "z" -> TyZero
    | "ti" -> TyTInt (ikind_mfts#fs (t 1))
    | "tf" -> TyTFloat (fkind_mfts#fs (t 1))
    | "ts" -> TyTStruct (a 0, t 1)
    | "b" -> TyBottom
    | "u" -> TyTUnknown
    | s -> raise_tag_error name s type_constant_mcts#tags

  method index_type_term (t: type_term_t) =
    let tags = [type_term_mcts#ts t] in
    let key =
      match t with
      | TyVariable v -> (tags, [self#index_type_variable v])
      | TyConstant c -> (tags, [self#index_type_constant c]) in
    type_term_table#add key

  method get_type_term (index: int): type_term_t =
    let name = "type_term_t" in
    let (tags, args) = type_term_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "v" -> TyVariable (self#get_type_variable (a 0))
    | "c" -> TyConstant (self#get_type_constant (a 0))
    | s -> raise_tag_error name s type_term_mcts#tags

  method index_type_constraint (c: type_constraint_t) =
    let tags = [type_constraint_mcts#ts c] in
    let key =
      match c with
      | TyVar v -> (tags, [self#index_type_term v])
      | TySub (t1, t2) ->
         (tags, [self#index_type_term t1; self#index_type_term t2])
      | TyGround (t1, t2) ->
         (tags, [self#index_type_term t1; self#index_type_term t2])
      | TyZeroCheck t -> (tags, [self#index_type_term t]) in
    type_constraint_table#add key

  method get_type_constraint (index: int): type_constraint_t =
    let name = "type_constraint_t" in
    let (tags, args) = type_constraint_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "v" -> TyVar (self#get_type_term (a 0))
    | "s" -> TySub (self#get_type_term (a 0), self#get_type_term (a 1))
    | "g" -> TyGround (self#get_type_term (a 0), self#get_type_term (a 1))
    | "z" -> TyZeroCheck (self#get_type_term (a 0))
    | s -> raise_tag_error name s type_term_mcts#tags

  method write_xml (node: xml_element_int) =
    begin
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables)
    end

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method reset = List.iter (fun t -> t#reset) tables

end


let type_constraint_dictionary = new type_constraint_dictionary_t
