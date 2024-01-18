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
open CHNumerical
open CHPretty

(* chutil *)
open CHUtil
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm
open JCHXmlUtil

let _minint = mkNumericalFromString "-2147483648"
let _maxint = mkNumericalFromString "2147483647"
let _minlongint = mkNumericalFromString "-9223372036854775808"
let _maxlongint = mkNumericalFromString "9223372036854775807"

(* -----------------------------------------------------------------------------
   Conversion of java field descriptor to value_type_t
   source: Lindholm, Yellin, The Java Virtual Machine Specification, 2nd Ed, p. 100

   FieldDescriptor: FieldType
   ComponentType  : FieldType
   FieldType      : BaseType | ObjectType | ArrayType
   BaseType       : B | C | D | F | I | J | S | Z
   ObjectType     : L<classname>;
   ArrayType      : [ComponentType
   ----------------------------------------------------------------------------- *)

let _c_dollarsign  = 0x0024   (* $ *)
let c_semicolon    = 0x003B   (* ; *)
let c_leftbracket  = 0x005B   (* [ *)

let c_B            = 0x0042   (* B *)
let c_C            = 0x0043   (* C *)
let c_D            = 0x0044   (* D *)
let c_F            = 0x0046   (* F *)
let c_I            = 0x0049   (* I *)
let c_J            = 0x004A   (* J *)
let c_L            = 0x004C   (* L *)
let c_S            = 0x0053   (* S *)
let c_V            = 0x0056   (* V *)
let c_Z            = 0x005A   (* Z *)


let in_range c lower_bound upper_bound = c >= lower_bound && c <= upper_bound


let is_name_start_char c =
  (in_range c 0x0061 0x007A) ||    (* a-z *)
  (in_range c 0x0041 0x005A) ||    (* A-Z *)
  (c = 0x005F)                     (*  _  *)


let is_name_char c =
  (is_name_start_char c)     ||
  (c = 0x002D)               ||     (*  -  *)
  (c = 0x002E)               ||     (*  .  *)
  (c = 0x0024)               ||     (*  $  *)
  (c = 0x00B7)               ||
  (in_range c 0x0030 0x0039) ||     (* 0-9 *)
  (in_range c 0x0300 0x036F) ||
  (in_range c 0x203F 0x2040)


let is_digit c = in_range c 0x0030 0x0039


let is_start_type_encoding_char c =
  List.mem c [c_B; c_C; c_D; c_F; c_I; c_J; c_L; c_S; c_V; c_Z; c_leftbracket]

let basic_types =
  [(c_B, Byte);
    (c_C, Char);
    (c_D, Double);
    (c_F, Float);
    (c_I, Int);
    (c_J, Long);
    (c_S, Short);
    (c_Z, Bool);
    (c_V, Void)]


let is_basic_type_encoding_char c = List.mem c (List.map fst basic_types)


let get_basic_type c =
  try
    let (_,ty) =  List.find (fun (k, _) -> k = c) basic_types in ty
  with
  | Not_found ->
     raise (JCH_failure (LBLOCK [STR "No type found for character "; INT c]))


class value_type_decoder_t (s:string) =
object (self)

  val len = String.length s
  val mutable ch = IO.input_string s
  val mutable pos = 0
  val mutable char_la = 0
  val name_buffer = Buffer.create 17

  method private stop msg =
    let unparsed = String.sub s (pos-1) (((String.length s) - pos) + 1) in
    raise
      (JCH_failure
         (LBLOCK [
              STR "Stop at position ";
              INT pos;
              STR " while reading ";
              STR msg;
              NL;
              STR "Unprocessed: ";
              STR unparsed]))

  method private read =
    begin
      pos <- pos + 1;
      Char.code (IO.read ch)
    end

  method private next_char =
    if pos = len then
      char_la <- 0
    else
      char_la <- self#read

  method private read_char expected_char =
    if char_la = expected_char then
      self#next_char
    else
      raise
        (JCH_failure
           (LBLOCK [
                STR "Expected to see ";
                INT expected_char;
		STR ", but found ";
                INT char_la ;
                STR " in parsing ";
		STR s]))

  method private check_char_la predicate msg =
    if predicate char_la then
      ()
    else
      raise (JCH_failure msg)

  method private fill_name_buffer c =
    Buffer.add_char name_buffer (Char.chr c)

  method private read_name =
    begin
      Buffer.clear name_buffer;
      self#check_char_la is_name_start_char
	(LBLOCK [
             INT char_la; STR " is not a valid starting character of a name"]);
      self#fill_name_buffer char_la;
      self#next_char;
      while is_name_char char_la do
	begin
	  self#fill_name_buffer char_la;
	  self#next_char
	end
      done;
      Buffer.contents name_buffer
    end

  method private read_index =
    begin
      Buffer.clear name_buffer;
      self#check_char_la is_digit (LBLOCK [INT char_la; STR " is not a digit"]);
      self#fill_name_buffer char_la;
      self#next_char;
      while is_digit char_la do
	begin
	  self#fill_name_buffer char_la;
	  self#next_char
	end
      done;
      int_of_string (Buffer.contents name_buffer)
    end

  method private read_object_name =
    let name = self#read_name in
    begin
      self#read_char c_semicolon;
      make_cn name
    end

  method private read_cnix =
    let index = self#read_index in
    begin
      self#read_char c_semicolon;
      retrieve_cn index
    end

  method private read_value_cnix_type =
    if is_basic_type_encoding_char char_la then
      let c = char_la in
      begin self#next_char; TBasic (get_basic_type c) end
    else if char_la = c_L then
      begin self#next_char; TObject (TClass self#read_cnix) end
    else if char_la = c_leftbracket then
      begin self#next_char; TObject (TArray self#read_value_cnix_type) end
    else
      begin
	self#stop "Error in read_value_type";
	raise (JCH_failure (LBLOCK [STR "Error in read_value_cnix_type"]))
      end

  method private read_value_type =
    if is_basic_type_encoding_char char_la then
      let c = char_la in
      begin self#next_char; TBasic (get_basic_type c) end
    else if char_la = c_L then
      begin self#next_char; TObject (TClass self#read_object_name) end
    else if char_la = c_leftbracket then
      begin
        self#next_char;
        TObject (TArray self#read_value_type)
      end
    else
      begin
	self#stop "Error in read_value_type";
	raise (JCH_failure (LBLOCK [STR "Error in read_value_type"]))
      end

  method get_value_cnix_type =
    begin
      self#next_char;
      self#read_value_cnix_type
    end

  method get_value_type =
    begin
      self#next_char;
      self#read_value_type
    end
end


let _decode_value_type s =
  try
    match s with
    | "XIZX" -> TBasic Int2Bool
    | "XBZX" -> TBasic ByteBool
    | "XLX" -> TBasic Object
    | "V" -> TBasic Void
    | _ ->
       let s = string_replace '/' "." s in
       (new value_type_decoder_t s)#get_value_type
  with
  | Invalid_argument _ ->
     raise
       (JCH_failure
          (LBLOCK [STR "Error in decode_value_type: "; STR s]))


let decode_value_cnix_type s =
  try
    match s with
    | "XIZX" -> TBasic Int2Bool
    | "XBZX" -> TBasic ByteBool
    | "XLX" -> TBasic Object
    | "V" -> TBasic Void
    | _ -> (new value_type_decoder_t s)#get_value_cnix_type
  with
  | Invalid_argument _ ->
     raise
       (JCH_failure
          (LBLOCK [STR "Error in decode_value_cnix_type: "; STR s]))


let write_xml_slot_value (node:xml_element_int) (v:jterm_range_int) =
  v#write_xml node


let _read_xml_slot_value (node:xml_element_int) =
  let has = node#hasNamedAttribute in
  try
    if has "value" then
      Some (read_xml_jterm_range node)
    else
      None
  with
  | JCH_failure p ->
    begin
      pr_debug [STR "Error in reading stack slot value: "; p; NL];
      None
    end


let write_xml_instruction_list (node:xml_element_int) (l:int list) =
  node#appendChildren
    (List.map (fun i ->
      let iNode = xmlElement "instr" in
      begin
        iNode#setIntAttribute "pc" i;
        iNode
      end) l)


let _write_xml_block_list (node:xml_element_int) (l:(int*int) list) =
  node#appendChildren
    (List.map (fun (x,y) ->
      let bNode = xmlElement "block" in
      let seti = bNode#setIntAttribute in
      begin
        seti "start" x;
        seti "end" y;
        bNode
      end) l)


let _write_xml_stack_slot (node:xml_element_int) (s:logical_stack_slot_int) =
  let seti = node#setIntAttribute in
  let append = node#appendChildren in
  begin
    (match s#get_sources with
    | [] -> ()
    | [src] -> seti "src-pc" src
    | l ->
      let sNode = xmlElement "sources" in
      begin write_xml_instruction_list sNode l; append [sNode] end);
    (match s#get_destinations with
    | [] -> ()
    | [dst] -> seti "dst-pc" dst
    | l ->
      let dNode = xmlElement "destinations" in
      begin
        write_xml_instruction_list dNode l;
        append [dNode]
      end);
    seti "level" s#get_level;
    write_xml_asm_cnix_value_types node s#get_type;
    (if s#has_value then write_xml_slot_value node s#get_value)
  end


let write_xml_op_stack_layout
      (d:bcdictionary_int) (node:xml_element_int) (layout:op_stack_layout_int) =
  d#write_xml_stack_slot_data_list
    node (List.map (fun s -> s#to_stack_slot_data) layout#get_slots)
  (*
  let seti = node#setIntAttribute in
  begin
    node#appendChildren (List.map (fun s ->
      let sNode = xmlElement "slot" in
      begin write_xml_stack_slot sNode s; sNode end) layout#get_slots);
    seti "levels" layout#get_levels;
    seti "slots" (List.length layout#get_slots)
  end
   *)


let _read_xml_slot_types (node:xml_element_int):value_type_t list =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  if has "ty" then
    [decode_value_cnix_type (get "ty")]
  else
    let ttnode = node#getTaggedChild "types" in
    List.map
      (fun tnode -> decode_value_cnix_type (tnode#getAttribute "type"))
      (ttnode#getTaggedChildren "type")


let read_xml_and_set_method_stack_layout
      (d:bcdictionary_int)
      (node:xml_element_int)
      (stack_layout:method_stack_layout_int) =
  List.iter (fun inode ->
      let pc = inode#getIntAttribute "pc" in
      let stackslotdata = d#read_xml_stack_slot_data_list inode in
      let oplayout = stack_layout#get_stack_layout pc in
      List.iter (fun ss ->
          let slot = oplayout#get_slot ss.ss_level in
          begin
            slot#set_type ss.ss_types;
            slot#set_value ss.ss_value
          end) stackslotdata) (node#getTaggedChildren "instr")
