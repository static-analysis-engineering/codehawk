(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs LLC

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
open CHIntervals
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHByteUtilities
open BCHConstantDefinitions
open BCHFloc
open BCHFunctionInterface
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO

(* bchlibpower32 *)
open BCHFnPowerDictionary
open BCHPowerDictionary
open BCHPowerTypes


module H = Hashtbl


class fn_analysis_results_t (fn: pwr_assembly_function_int) =
object (self)

  val faddr = fn#faddr
  val finfo = get_function_info fn#faddr
  val env = (get_function_info fn#faddr)#env
  val vard = (get_function_info fn#faddr)#env#varmgr#vard
  val id =
    mk_pwr_opcode_dictionary
      fn#faddr (get_function_info fn#faddr)#env#varmgr#vard

  method private write_xml_instruction
                   (node: xml_element_int)
                   (ctxtiaddr: ctxt_iaddress_t)
                   (instr: pwr_assembly_instruction_int) =
    let loc = ctxt_string_to_location faddr ctxtiaddr in
    let floc = get_floc loc in
    let espoffset = floc#get_stackpointer_offset "arm" in
    begin
      pwr_dictionary#write_xml_pwr_opcode node instr#get_opcode;
      id#write_xml_instr node instr floc;
      id#write_xml_sp_offset node espoffset;
      pwr_dictionary#write_xml_pwr_bytestring
        node (byte_string_to_printed_string instr#get_instruction_bytes)
    end

  method private write_xml_instructions (node: xml_element_int) =
    fn#itera
      (fun baddr block ->
        let bNode = xmlElement "bl" in
        begin
          block#itera
            (fun ctxtiaddr instr ->
              let iNode = xmlElement "i" in
              begin
                self#write_xml_instruction iNode ctxtiaddr instr;
                bNode#appendChildren [iNode];
                iNode#setAttribute "ia" ctxtiaddr
              end);
          node#appendChildren [bNode];
          bNode#setAttribute "ba" baddr
        end)

  method private write_xml_cfg_block
                   (node: xml_element_int) (b: pwr_assembly_block_int) =
    let set = node#setAttribute in
    let blockloc = b#location in
    begin
      set "ba" b#context_string;
      set "eq" (make_i_location blockloc b#last_address)#ci
    end

  method private write_xml_cfg (node: xml_element_int) =
    let nodes = ref [] in
    let edges = ref [] in
    let bbNode = xmlElement "blocks" in
    let eeNode = xmlElement "edges" in
    begin
      fn#itera
        (fun baddr block ->
          let bNode = xmlElement "bl" in
          begin
            self#write_xml_cfg_block bNode block;
            List.iter (fun succ ->
                let eNode = xmlElement "e" in
                let seta tag a = eNode#setAttribute tag a in
                begin
                  seta "src" baddr;
                  seta "tgt" succ;
                  edges := eNode :: !edges
                end) block#successors;
            nodes := bNode :: !nodes
          end);
      bbNode#appendChildren (List.rev !nodes);
      eeNode#appendChildren (List.rev !edges);
      node#appendChildren [bbNode; eeNode]
    end

  method private write_xml (node: xml_element_int) =
    let append = node#appendChildren in
    let cNode = xmlElement "cfg" in
    let dNode = xmlElement "instr-dictionary" in
    let iiNode = xmlElement "instructions" in
    begin
      self#write_xml_cfg cNode;
      self#write_xml_instructions iiNode;
      id#write_xml dNode;
      append [cNode; dNode; iiNode]
    end

  method save =
    let node = xmlElement "application-results" in
    begin
      self#write_xml node;
      node#setAttribute "a" faddr#to_hex_string;
      save_app_function_results_file faddr#to_hex_string node;
      save_vars faddr#to_hex_string vard
    end

end


class pwr_analysis_result_t: pwr_analysis_results_int =
object (self)

  val table = H.create 3

  method record_results ?(save=true) (fn: pwr_assembly_function_int) =
    let fndata = new fn_analysis_results_t fn in
    begin
      (if save then fndata#save);
      H.add table fn#faddr#to_hex_string fn;
    end

  method write_xml (node: xml_element_int) =
    let ffnode = xmlElement "functions" in
    let _ =
      H.iter (fun faddr fn ->
          let fnode = xmlElement "fn" in
          begin
            fnode#setAttribute "fa" faddr;
            fnode#setAttribute "md5" fn#get_function_md5;
            ffnode#appendChildren [fnode]
          end) table in
    node#appendChildren [ffnode]

  method save =
    let node = xmlElement "application-results" in
    begin
      self#write_xml node;
      save_resultdata_file node
    end

end


let pwr_analysis_results = new pwr_analysis_result_t
