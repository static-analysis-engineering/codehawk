(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI
open JCHBcDictionary
open JCHBytecode
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHCGDictionary
open JCHMethodInfo
open JCHPreAPI
open JCHStackLayout
open JCHXmlUtil

let write_xml_target_info (node:xml_element_int) (mInfo:method_info_int) (pc:int) (opc:opcode_t) =
  match opc with
  | OpInvokeVirtual _ | OpInvokeInterface _ ->
     let loc = get_bytecode_location mInfo#get_index pc in
     if app#has_instruction loc then
       let iInfo = app#get_instruction loc in
       if iInfo#has_method_target then
         let mtgt = iInfo#get_method_target () in
         if mtgt#is_top then
           let reason = mtgt#get_reason_for_top in
           node#setPrettyAttribute "reason" reason
         else
           let tgts = mtgt#get_all_targets in
           let tgts = List.map (fun minfo -> minfo#get_class_name#index) tgts in
           let tgts = ConstrainedVirtualTargets("iinfo",tgts) in
           cgdictionary#write_xml_target node tgts
  | _ -> ()

let write_xml_bc_instructions (d:bcdictionary_int) (node:xml_element_int) (mInfo:method_info_int) = 
  let stacklayout = mInfo#get_method_stack_layout in
  let append = node#appendChildren in
  mInfo#bytecode_iteri (fun pc opc ->
    let iNode = xmlElement "instr" in
    let opstacklayout = stacklayout#get_stack_layout pc in
    begin
      d#write_xml_opcode iNode opc ;
      write_xml_op_stack_layout d iNode opstacklayout ;
      write_xml_target_info iNode mInfo pc opc ;
      append [ iNode ] ;
      iNode#setIntAttribute "pc" pc 
    end)
