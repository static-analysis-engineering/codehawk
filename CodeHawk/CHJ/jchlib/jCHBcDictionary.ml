(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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
open CHXmlDocument
open CHIndexTable

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHJTerm
open JCHSumTypeSerializer

let cd = JCHDictionary.common_dictionary
let jtd = JCHJTDictionary.jtdictionary


class bcdictionary_t:bcdictionary_int =
object (self)

  val pc_list_table = mk_index_table "pc-list-table"
  val stack_slot_data_table = mk_index_table "slot-table"
  val stack_slot_data_list_table = mk_index_table "slot-list-table"
  val opcode_table = mk_index_table "opcode-table"

  val mutable tables = []

  initializer
    tables <- [
      pc_list_table;
      stack_slot_data_table;
      stack_slot_data_list_table;
      opcode_table
   ]

  method index_pc_list (l:int list) =  pc_list_table#add ([],l)

  method get_pc_list (index:int):int list =
    let (_,args) = pc_list_table#retrieve index in args

  method index_stack_slot_data (s:stack_slot_data_t) =
    let (pctags, pcargs) =
      match (s.ss_srcs, s.ss_dsts) with
      | ([], []) -> (["n"; "n"], [0; 0])
      | ([], [dst]) -> (["n"; "s"], [0; dst])
      | ([], dsts) -> (["n"; "m"], [0; self#index_pc_list dsts])
      | ([src], []) -> (["s"; "n"], [src; 0])
      | (srcs, []) -> (["m"; "n"], [self#index_pc_list srcs; 0])
      | ([src], [dst]) -> (["s"; "s"], [src; dst])
      | ([src], dsts) -> (["s"; "m"], [src; self#index_pc_list dsts])
      | (srcs, [dst]) -> (["m"; "s"], [self#index_pc_list srcs; dst])
      | (srcs, dsts) ->
         (["m"; "m"], [self#index_pc_list srcs; self#index_pc_list dsts]) in
    let args =
      pcargs @ [
          s.ss_level;
          jtd#index_jterm_range
            s.ss_value#get_lowerbounds s.ss_value#get_upperbounds]
      @ (List.map cd#index_value_type s.ss_types) in
    stack_slot_data_table#add (pctags,args)

  method get_stack_slot_data (index:int) =
    let (tags,args) = stack_slot_data_table#retrieve index in
    let t = t "stack-slot-data" tags in
    let a = a "stack-slot-data" args in
    let srcs =
      match (t 0) with
      | "n" -> []
      | "s" -> [a 0]
      | "m" -> self#get_pc_list (a 0)
      | s -> raise (JCH_failure (LBLOCK [STR "stack-slot-srcs tag"; STR s])) in
    let dsts =
      match (t 1) with
      | "n" -> []
      | "s" -> [a 1]
      | "m" -> self#get_pc_list (a 1)
      | s -> raise (JCH_failure (LBLOCK [STR "stack-slot-dsts tag"; STR s])) in
    let (lbs,ubs) = jtd#get_jterm_range (a 3) in
    { ss_srcs = srcs;
      ss_dsts = dsts;
      ss_level = a 2;
      ss_types = List.map cd#get_value_type (get_list_suffix args 4);
      ss_value = mk_jterm_range lbs ubs
    }

  method index_stack_slot_data_list (l:stack_slot_data_t list) =
    let args = List.map self#index_stack_slot_data l in
    stack_slot_data_list_table#add ([],args)

  method get_stack_slot_data_list (index:int) =
    let (_,args) = stack_slot_data_list_table#retrieve index in
    List.map self#get_stack_slot_data args

  method index_opcode (opc:opcode_t) =
    let tags = [opcode_serializer#to_string opc] in
    let key = match opc with
      | OpLoad (t,reg)
        | OpStore (t,reg) ->
         (tags @ [java_basic_type_serializer#to_string t], [reg])
      | OpIInc (inc, reg) ->
         (tags, [inc; reg])
      | OpIntConst i32 ->
         (tags, [Int32.to_int i32])
      | OpLongConst i64 ->
         (tags @ [Int64.to_string i64], [])
      | OpFloatConst f
        | OpDoubleConst f -> (tags @ [string_of_float f], [])
      | OpByteConst i
        | OpShortConst i -> (tags, [i])
      | OpStringConst s ->
         (tags, [cd#index_string s])
      | OpClassConst o ->
         (tags, [cd#index_object_type o])
      | OpAdd t
        | OpSub t
        | OpMult t
        | OpDiv t
        | OpRem t
        | OpNeg t -> (tags @ [java_basic_type_serializer#to_string t], [])
      | OpIfEq i
        | OpIfNe i
        | OpIfLt i
        | OpIfGe i
        | OpIfGt i
        | OpIfLe i
        | OpIfNull i
        | OpIfNonNull i
        | OpIfCmpEq i
        | OpIfCmpNe i
        | OpIfCmpLt i
        | OpIfCmpGe i
        | OpIfCmpGt i
        | OpIfCmpLe i
        | OpIfCmpAEq i
        | OpIfCmpANe i -> (tags, [i])
      | OpGoto i
        | OpJsr i
        | OpRet i -> (tags, [i])
      | OpTableSwitch (i,i32,j32,a) ->
         (tags,[i; Int32.to_int i32; Int32.to_int j32] @ (Array.to_list a))
      | OpLookupSwitch (i, l) ->
         (tags,
          [i] @ (List.concat (List.map (fun (i32,i) -> [Int32.to_int i32; i]) l)))
      | OpNew cn ->
         (tags, [cn#index])
      | OpNewArray vt ->
         (tags, [cd#index_value_type vt])
      | OpAMultiNewArray (t,i) ->
         (tags, [cd#index_object_type t; i])
      | OpCheckCast t
        | OpInstanceOf t ->
         (tags, [cd#index_object_type t])
      | OpGetStatic (cn,fs)
        | OpPutStatic (cn,fs)
        | OpGetField (cn,fs)
        | OpPutField (cn,fs) ->
         (tags, [cn#index; fs#index])
      | OpArrayLoad t
        | OpArrayStore t ->
         (tags @ [java_basic_type_serializer#to_string t], [])
      | OpInvokeVirtual (t,ms) ->
         (tags, [cd#index_object_type t; ms#index])
      | OpInvokeSpecial (cn,ms)
        | OpInvokeStatic (cn,ms)
        | OpInvokeInterface (cn,ms) ->
         (tags, [cn#index; ms#index])
      | OpInvokeDynamic (i,ms) -> (tags, [i; ms#index])
      | OpReturn t ->
         (tags @ [java_basic_type_serializer#to_string t], [])
      | _ -> (tags,[]) in
    opcode_table#add key

  method get_opcode (index:int):opcode_t =
    let (tags,args) = opcode_table#retrieve index in
    let t = t "opcode" tags in
    let a = a "opcode" args in
    match (t 0) with
    | "ld" ->
       OpLoad (java_basic_type_serializer#from_string (t 1), a 0)
    | "st" ->
       OpStore (java_basic_type_serializer#from_string (t 1), a 0)
    |"inc" ->
      OpIInc (a 0, a 1)
    | "icst" ->
       OpIntConst (Int32.of_int (a 0))
    | "lcst" ->
       OpLongConst (Int64.of_string (t 1))
    | "fcst" ->
       OpFloatConst (float_of_string (t 1))
    | "dcst" ->
       OpDoubleConst (float_of_string (t 1))
    | "bcst" ->
       OpByteConst (a 0)
    | "shcst" ->
       OpShortConst (a 0)
    | "scst" ->
       OpStringConst (cd#get_string (a 0))
    | "ccst" ->
       OpClassConst (cd#get_object_type (a 0))
    | "add" ->
       OpAdd (java_basic_type_serializer#from_string (t 1))
    | "sub" ->
       OpSub (java_basic_type_serializer#from_string (t 1))
    | "mult" ->
       OpMult (java_basic_type_serializer#from_string (t 1))
    | "div" ->
       OpDiv (java_basic_type_serializer#from_string (t 1))
    | "rem" ->
       OpRem (java_basic_type_serializer#from_string (t 1))
    | "neg" ->
       OpNeg (java_basic_type_serializer#from_string (t 1))
    | "ifeq" ->
       OpIfEq (a 0)
    | "ifne" ->
       OpIfNe (a 0)
    | "iflt" ->
       OpIfLt (a 0)
    | "ifge" ->
       OpIfGe (a 0)
    | "ifgt" ->
       OpIfGt (a 0)
    | "ifle" ->
       OpIfLe (a 0)
    | "ifnull" ->
       OpIfNull (a 0)
    | "ifnonnull" ->
       OpIfNonNull (a 0)
    | "ifcmpeq" ->
       OpIfCmpEq (a 0)
    | "ifcmpne" ->
       OpIfCmpNe (a 0)
    | "ifcmplt" ->
       OpIfCmpLt (a 0)
    | "ifcmpge" ->
       OpIfCmpGe (a 0)
    | "ifcmpgt" ->
       OpIfCmpGt (a 0)
    | "ifcmple" ->
       OpIfCmpLe (a 0)
    | "ifcmpaeq" ->
       OpIfCmpAEq (a 0)
    | "ifcmpane" ->
       OpIfCmpANe (a 0)
    | "goto" ->
       OpGoto (a 0)
    | "jsr" ->
       OpJsr (a 0)
    | "jret" ->
       OpRet (a 0)
    | "table" ->
       OpTableSwitch (
           a 0,
           Int32.of_int (a 1),
           Int32.of_int (a 2),
           Array.of_list (get_list_suffix args 3))
    | "lookup" ->
       OpLookupSwitch (
           a 0,
           List.map
             (fun (i,j) -> (Int32.of_int i, j))
             (list_pairup (get_list_suffix args 1)))
    | "new" ->
       OpNew (cd#retrieve_class_name (a 0))
    | "newa" ->
       OpNewArray (cd#get_value_type (a 0))
    | "mnewa" ->
       OpAMultiNewArray (cd#get_object_type (a 0), a 1)
    | "ccast" ->
       OpCheckCast (cd#get_object_type (a 0))
    | "iof" ->
       OpInstanceOf (cd#get_object_type (a 0))
    | "gets" ->
       OpGetStatic
         (cd#retrieve_class_name (a 0), cd#retrieve_field_signature (a 1))
    | "puts" ->
       OpPutStatic
         (cd#retrieve_class_name (a 0), cd#retrieve_field_signature (a 1))
    | "getf" ->
       OpGetField
         (cd#retrieve_class_name (a 0), cd#retrieve_field_signature (a 1))
    | "putf" ->
       OpPutField
         (cd#retrieve_class_name (a 0), cd#retrieve_field_signature (a 1))
    | "ald" ->
       OpArrayLoad (java_basic_type_serializer#from_string (t 1))
    | "ast" ->
       OpArrayStore (java_basic_type_serializer#from_string (t 1))
    | "invv" ->
       OpInvokeVirtual
         (cd#get_object_type (a 0), cd#retrieve_method_signature (a 1))
    | "invsp" ->
       OpInvokeSpecial
         (cd#retrieve_class_name (a 0), cd#retrieve_method_signature (a 1))
    | "invst" ->
       OpInvokeStatic
         (cd#retrieve_class_name (a 0), cd#retrieve_method_signature (a 1))
    | "invi" ->
       OpInvokeInterface
         (cd#retrieve_class_name (a 0), cd#retrieve_method_signature (a 1))
    | "invd" ->
       OpInvokeDynamic (a 0, cd#retrieve_method_signature (a 1))
    | "ret" ->
       OpReturn (java_basic_type_serializer#from_string (t 1))
    | s -> opcode_serializer#from_string s

  method write_xml_stack_slot_data_list
           ?(tag="issdl") (node:xml_element_int) (l:stack_slot_data_t list) =
    node#setIntAttribute tag (self#index_stack_slot_data_list l)

  method read_xml_stack_slot_data_list
           ?(tag="issdl") (node:xml_element_int):stack_slot_data_t list =
    self#get_stack_slot_data_list (node#getIntAttribute tag)

  method write_xml_opcode ?(tag="iopc") (node:xml_element_int) (opc:opcode_t) =
    node#setIntAttribute tag (self#index_opcode opc)

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
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables;

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end


let mk_bcdictionary () = new bcdictionary_t
