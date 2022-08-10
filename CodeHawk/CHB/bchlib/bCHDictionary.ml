(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHIndexTable
open CHPrettyUtil
open CHStringIndexTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHSumTypeSerializer
open BCHUtilities

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


let mk_constantstring (s:string):constantstring =
  if has_control_characters s then
    (hex_string s, true, String.length s)
  else
    (s,false, String.length s)


class bdictionary_t:bdictionary_int =
object (self)

  val string_table = mk_string_index_table "string-table"
  val address_table = mk_index_table "address-table"
  val arm_extension_register_table = mk_index_table "arm-extension-register-table"
  val arm_extension_register_element_table =
    mk_index_table "arm-extension-register-element-table"
  val arm_extension_register_replicated_element_table =
    mk_index_table "arm-extension-register-replicated-element-table"
  val register_table = mk_index_table "register-table"
  val flag_table = mk_index_table "flag-table"

  val mutable tables = []
  val mutable stringtables = []

  initializer
    begin
      tables <- [
        address_table;
        arm_extension_register_table;
        arm_extension_register_element_table;
        arm_extension_register_replicated_element_table;
        register_table;
        flag_table;
      ];
      stringtables <- [
          string_table
        ]
    end
  
  method reset =
    begin
      List.iter (fun t -> t#reset) stringtables;
      List.iter (fun t -> t#reset) tables
    end

  method index_string (s:string):int = string_table#add s

  method get_string (index:int) = string_table#retrieve index

  method index_address (dw:doubleword_int) =
    address_table#add ([dw#to_hex_string],[])

  method index_address_string (s:string) =
    address_table#add ([s],[])

  method get_address (index:int) =
    let (tags,_) = address_table#retrieve index in
    let t  = t "address" tags in
    string_to_doubleword (t 0)

  method get_address_string (index:int) =
    let (tags,_) = address_table#retrieve index in
    let t = t "address" tags in
    (t 0)

  method index_arm_extension_register (r: arm_extension_register_t) =
    arm_extension_register_table#add
      ([arm_extension_reg_type_mfts#ts r.armxr_type], [r.armxr_index])

  method get_arm_extension_register (index: int) =
    let name = "arm_extension_register" in
    let (tags, args) = arm_extension_register_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    {armxr_type = arm_extension_reg_type_mfts#fs (t 0); armxr_index = a 0}

  method index_arm_extension_register_element
           (e: arm_extension_register_element_t) =
    arm_extension_register_element_table#add
      ([],
       [self#index_arm_extension_register e.armxr;
        e.armxr_elem_index;
        e.armxr_elem_size])

  method get_arm_extension_register_element (index: int) =
    let name = "arm_extension_register_element" in
    let (_, args) = arm_extension_register_element_table#retrieve index in
    let a = a name args in
    {armxr = self#get_arm_extension_register (a 0);
     armxr_elem_index = (a 1);
     armxr_elem_size = (a 2)}

  method index_arm_extension_register_replicated_element
           (e: arm_extension_register_replicated_element_t) =
    arm_extension_register_replicated_element_table#add
      ([],
       [self#index_arm_extension_register e.armxrr;
        e.armxrr_elem_size;
        e.armxrr_elem_count])

  method get_arm_extension_register_replicated_element (index: int) =
    let name = "arm_extension_register_replicated_element" in
    let (_, args) =
      arm_extension_register_replicated_element_table#retrieve index in
    let a = a name args in
    {armxrr = self#get_arm_extension_register (a 0);
     armxrr_elem_size = (a 1);
     armxrr_elem_count = (a 2)}

  method index_flag (f: flag_t) =
    let tags = [flag_mcts#ts f] in
    let key = match f with
      | X86Flag e -> (tags @ [eflag_mfts#ts e], [])
      | ARMCCFlag c -> (tags @ [arm_cc_flag_mfts#ts c], []) in
    flag_table#add key

  method get_flag (index: int) =
    let name = flag_mcts#name in
    let (tags, args) = flag_table#retrieve index in
    let t = t name tags in
    match (t 0) with
    | "x" -> X86Flag (eflag_mfts#fs (t 1))
    | "a" -> ARMCCFlag (arm_cc_flag_mfts#fs (t 1))
    | s -> raise_tag_error name s flag_mcts#tags

  method index_register (r:register_t) =
    let tags = [register_mcts#ts r] in
    let key = match r with
      | SegmentRegister s -> (tags @ [ segment_mfts#ts s ],[])
      | CPURegister r -> (tags @ [ cpureg_mfts#ts r ],[])
      | DoubleRegister (r1,r2) ->
         (tags @ [ cpureg_mfts#ts r1 ; cpureg_mfts#ts r2 ],[])
      | FloatingPointRegister i 
        | ControlRegister i
        | DebugRegister i
        | MmxRegister i
        | XmmRegister i -> (tags,[i])
      | MIPSRegister r ->  (tags @ [ mips_reg_mfts#ts r ],[])
      | MIPSSpecialRegister r -> (tags @ [mips_special_reg_mfts#ts r], [])
      | MIPSFloatingPointRegister i -> (tags, [i])
      | ARMRegister r -> (tags @ [arm_reg_mfts#ts r], [])
      | ARMSpecialRegister r -> (tags @ [arm_special_reg_mfts#ts r], [])
      | ARMExtensionRegister xr ->
         (tags, [self#index_arm_extension_register xr])
      | ARMExtensionRegisterElement xre ->
         (tags, [self#index_arm_extension_register_element xre])
      | ARMExtensionRegisterReplicatedElement xrre ->
         (tags, [self#index_arm_extension_register_replicated_element xrre])
      | PowerGPRegister r -> (tags, [r]) in
    register_table#add key

  method get_register (index:int) =
    let name = register_mcts#name in
    let (tags,args) = register_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "s" -> SegmentRegister (segment_mfts#fs (t 1))
    | "c" -> CPURegister (cpureg_mfts#fs (t 1))
    | "d" -> DoubleRegister (cpureg_mfts#fs (t 1),cpureg_mfts#fs (t 2))
    | "f" -> FloatingPointRegister (a 0)
    | "ctr" -> ControlRegister (a 0)
    | "dbg" -> DebugRegister (a 0)
    | "m" -> MmxRegister (a 0)
    | "x" -> XmmRegister (a 0)
    | "p" -> MIPSRegister (mips_reg_mfts#fs (t 1))
    | "ps" -> MIPSSpecialRegister (mips_special_reg_mfts#fs (t 1))
    | "pfp" -> MIPSFloatingPointRegister (a 0)
    | "a" -> ARMRegister (arm_reg_mfts#fs (t 1))
    | "as" -> ARMSpecialRegister (arm_special_reg_mfts#fs (t 1))
    | "armx" -> ARMExtensionRegister (self#get_arm_extension_register (a 0))
    | "armxe" ->
       ARMExtensionRegisterElement (self#get_arm_extension_register_element (a 0))
    | "armxr" ->
       ARMExtensionRegisterReplicatedElement
         (self#get_arm_extension_register_replicated_element (a 0))
    | "pwrgpr" -> PowerGPRegister (a 0)
    | s -> raise_tag_error name s register_mcts#tags


  method write_xml_register ?(tag="ireg") (node:xml_element_int) (r:register_t) =
    node#setIntAttribute tag (self#index_register r)

  method read_xml_register ?(tag="ireg") (node:xml_element_int):register_t =
    self#get_register (node#getIntAttribute tag)

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_string s)

  method read_xml_string ?(tag="istr") (node:xml_element_int):string =
    self#get_string (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    begin
      node#appendChildren
        (List.map
           (fun t -> let tnode = xmlElement t#get_name in
                     begin t#write_xml tnode ; tnode end) stringtables) ;
      node#appendChildren
        (List.map
           (fun t -> let tnode = xmlElement t#get_name in
                     begin t#write_xml tnode ; tnode end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      List.iter (fun t -> t#read_xml (getc t#get_name)) stringtables ;
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end

                                
let bdictionary = new bdictionary_t
