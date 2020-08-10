(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma

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
open BCHApiParameter
open BCHBasicTypes
open BCHByteUtilities
open BCHConstantDefinitions
open BCHFloc
open BCHFunctionApi
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSpecializations

(* bchlibmips32 *)
open BCHMIPSDisassemblyUtils
open BCHFnMIPSDictionary   
open BCHMIPSTypes
open BCHMIPSLoopStructure
open BCHMIPSOperand
open BCHMIPSDictionary
open BCHMIPSOpcodeRecords

module H = Hashtbl

class fn_analysis_results_t (fn:mips_assembly_function_int) =
object (self)

  val faddr = fn#get_address
  val finfo = get_function_info  fn#get_address
  val env = (get_function_info fn#get_address)#env
  val vard = (get_function_info fn#get_address)#env#varmgr#vard
  val id = mk_mips_opcode_dictionary
             fn#get_address (get_function_info fn#get_address)#env#varmgr#vard
  val specialization =
    let fa = fn#get_address#to_hex_string in
    if specializations#has_specialization fa then
      Some (specializations#get_specialization fa)
    else
      None

  method private write_xml_instruction
                   (node:xml_element_int) (ctxtiaddr:ctxt_iaddress_t)
                   (instr:mips_assembly_instruction_int)
                   (restriction:block_restriction_t option) =
    let loc = ctxt_string_to_location faddr ctxtiaddr in
    let floc = get_floc loc in
    let espoffset = floc#get_stackpointer_offset "mips" in
    begin
      mips_dictionary#write_xml_mips_opcode node instr#get_opcode ;
      id#write_xml_instr node instr floc restriction;
      id#write_xml_sp_offset node espoffset ;
      mips_dictionary#write_xml_mips_bytestring
        node (byte_string_to_printed_string instr#get_instruction_bytes)
    end

  method private write_xml_instructions (node:xml_element_int) =
    fn#itera (fun baddr block ->
        let bNode = xmlElement "bl" in
        let restriction =
          let fa = fn#get_address#to_hex_string in
          match specialization with
          | Some s ->
             if s#has_block_restriction fa baddr then
               Some (s#get_block_restriction fa baddr)
             else
               None
          | _ -> None in
        begin
          block#itera  (fun ctxtiaddr instr ->
              let iNode = xmlElement "i" in
              begin
                self#write_xml_instruction iNode ctxtiaddr instr restriction ;
                bNode#appendChildren [ iNode ] ;
                iNode#setAttribute "ia" ctxtiaddr
              end);
          node#appendChildren [ bNode ] ;
          bNode#setAttribute "ba" baddr
        end)

  method private write_xml_cfg_block (node:xml_element_int) (b:mips_assembly_block_int) =
    let set = node#setAttribute in
    let blockloc = b#get_location in
    let looplevels = get_loop_levels b#get_context_string in
    let llNode = xmlElement "loops" in
    begin
      llNode#appendChildren
        (List.map (fun a ->
	     let lNode = xmlElement "lv" in              (* level *)
	     begin
	       lNode#setAttribute "a" a ;
	       lNode
	     end) looplevels) ;
      node#appendChildren [ llNode ] ;
      set "ba" b#get_context_string ;
      set "ea" (make_i_location blockloc b#get_last_address)#ci ;
    end 

  method private write_xml_cfg (node:xml_element_int) =
    let _ = record_loop_levels faddr in
    let nodes = ref [] in
    let edges = ref [] in
    let bbNode = xmlElement "blocks" in
    let eeNode = xmlElement "edges" in
    begin
      fn#itera (fun baddr block ->
	let bNode = xmlElement "bl" in
	begin
	  self#write_xml_cfg_block bNode block ;
	  List.iter (fun succ ->
	    let eNode = xmlElement "e" in
	    let seta tag a = eNode#setAttribute tag a in
	    begin
	      seta "src" baddr ;
	      seta "tgt" succ ;
	      edges := eNode :: !edges
	    end) block#get_successors ;
	  nodes := bNode :: !nodes
	end) ;
      bbNode#appendChildren (List.rev !nodes) ;
      eeNode#appendChildren (List.rev !edges) ;
      node#appendChildren [ bbNode ; eeNode ]
    end

  method private write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let cNode = xmlElement "cfg" in
    let dNode = xmlElement "instr-dictionary" in
    let iiNode = xmlElement "instructions" in
    begin
      self#write_xml_cfg cNode ;
      self#write_xml_instructions iiNode ;
      id#write_xml dNode ;
      append [ cNode ; dNode ; iiNode ]
    end

  method save =
    let node = xmlElement "application-results" in
    begin
      self#write_xml node ;
      node#setAttribute "a" faddr#to_hex_string ;
      save_app_function_results_file faddr#to_hex_string node ;
      save_vars faddr#to_hex_string vard
    end

end

class mips_analysis_results_t:mips_analysis_results_int =
object (self)

  val table = H.create 3

  method record_results ?(save=true) (fn:mips_assembly_function_int) =
    let fndata = new fn_analysis_results_t fn in
    begin
      (if save then fndata#save) ;
      H.add table fn#get_address#to_hex_string fn
    end

  method write_xml (node:xml_element_int) =
    let ffnode = xmlElement "functions" in
    let _ = H.iter (fun faddr fn ->
                let fnode = xmlElement "fn" in
                begin
                  fnode#setAttribute "fa" faddr ;
                  fnode#setAttribute "md5" fn#get_function_md5 ;
                  ffnode#appendChildren [ fnode ]
                end) table in
    node#appendChildren [ ffnode ]

  method save =
    let node = xmlElement "application-results" in
    begin
      self#write_xml node ;
      save_resultdata_file node
    end

end

let mips_analysis_results = new mips_analysis_results_t
  
