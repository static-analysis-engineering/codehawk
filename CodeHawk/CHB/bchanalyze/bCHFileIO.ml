(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHLanguage
open CHPretty

(* chutil *)
open CHFileIO
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open Xprt
open XprToPretty
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHDisassemblySummary
open BCHFloc
open BCHFunctionApi
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummary
open BCHGlobalState
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo
open BCHVariableNames
open BCHXmlUtil
   
(* bchlibx86 *)
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHAssemblyInstructionAnnotations
open BCHDisassemblyMetrics
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHX86Dictionary

(* bchlibmips32 *)
open BCHMIPSAssemblyInstructions
open BCHMIPSDictionary

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMDictionary


let xml_error filename line column p = 
  LBLOCK [ STR "Xml error in " ; STR filename ; 
     STR " (" ; INT line ; STR ", " ; INT column ; STR "): " ; p ]

let get_bch_root (info:string):xml_element_int =
  let exename = system_info#get_filename in
  let root = xmlElement "codehawk-binary-analysis" in
  let hNode = xmlElement "header" in
  let aNode = xmlElement "application" in
  begin
    aNode#setAttribute "name" exename ;
    aNode#setAttribute "info" info ;
    aNode#setAttribute "time" (current_time_to_string ()) ;
    root#appendChildren [ hNode ] ;
    hNode#appendChildren [ aNode ] ;
    root
  end

let save_functions_list () =
  let filename = get_functions_filename () in
  let doc = xmlDocument () in
  let root  = get_bch_root "functions" in
  let ffNode = xmlElement "functions" in
  begin
    assembly_functions#bottom_up_itera (fun faddr f ->
      let fNode = xmlElement "function" in
      let set = fNode#setAttribute in
      let seti = fNode#setIntAttribute in
      let setx t x = set t x#to_hex_string in
      begin
	ffNode#appendChildren [ fNode ] ;
	(if functions_data#has_function_name faddr then 
	   let name = (functions_data#get_function faddr)#get_function_name in
           let name = if has_control_characters name then
                        "__xx__" ^ (hex_string name) else name in
	    set "name" name) ;
	 setx "va" faddr ;
	 seti "instructions" f#get_instruction_count ;
	 seti "blocks" f#get_block_count
      end) ;
    doc#setNode root ;
    root#appendChildren [ ffNode ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_global_state () =
  let filename = get_global_state_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "global-state" in
  let gNode = xmlElement "global-state" in
  begin
    global_system_state#write_xml gNode ;
    doc#setNode root ;
    root#appendChildren [ gNode ] ; 
    file_output#saveFile filename doc#toPretty
  end

let save_system_info () =
  let filename = get_system_info_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "system-info" in
  let sNode = xmlElement "system-info" in
  begin
    system_info#write_xml sNode ;
    doc#setNode root ;
    root#appendChildren [ sNode ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_resultmetrics (rnode:xml_element_int) =
  let filename = get_resultmetrics_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "metrics" in
  begin
    doc#setNode root ;
    root#appendChildren [ rnode ] ;
    file_output#saveFile filename doc#toPretty
  end


let load_system_info () =
  let filename = get_system_info_filename () in
  load_xml_file filename "system-info" 

let save_function_asm (f:assembly_function_int) =
  try
    let fname = f#get_address#to_hex_string in
    let filename = get_function_filename fname "asm.xml" in
    let doc = xmlDocument () in
    let root = get_bch_root "function-assembly-code" in
    let fNode = xmlElement "assembly-code" in
    begin
      f#write_xml fNode ;
      doc#setNode root ;
      root#appendChildren [ fNode ] ;
      file_output#saveFile filename doc#toPretty
    end
  with
    BCH_failure p ->
    raise (BCH_failure (LBLOCK [ STR "Unable to save function asm: " ; p ]))

let save_disassembly_status () =
  let filename = get_disassembly_status_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "disassembly-status" in
  let fnode = xmlElement "disassembly-status" in
  begin
    disassembly_summary#set_disassembly_metrics (get_disassembly_metrics ()) ;
    disassembly_summary#write_xml fnode ;
    doc#setNode root ;
    root#appendChildren [ fnode ] ;
    file_output#saveFile filename doc#toPretty
  end
  

let save_x86dictionary () =
  let filename = get_x86dictionary_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "x86dictionary" in
  let fnode = xmlElement "x86dictionary" in
  begin
    x86dictionary#write_xml fnode ;
    doc#setNode root ;
    root#appendChildren [ fnode ] ;
    file_output#saveFile filename doc#toPretty
  end

let load_x86dictionary () =
  let filename = get_x86dictionary_filename ()  in
  let optnode = load_xml_file filename "x86dictionary" in
  match optnode with
  | Some xnode -> x86dictionary#read_xml xnode
  | _ -> ()

let save_mips_dictionary () =
  let filename = get_mips_dictionary_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "mips-dictionary" in
  let fnode = xmlElement "mips-dictionary" in
  begin
    mips_dictionary#write_xml fnode ;
    doc#setNode root ;
    root#appendChildren [ fnode ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_mips_assembly_instructions () =
  let filename = get_mips_assembly_instructions_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "mips-assembly-instructions" in
  let fnode = xmlElement "mips-assembly-instructions" in
  begin
    (!mips_assembly_instructions)#write_xml fnode;
    doc#setNode root;
    root#appendChildren [ fnode ];
    file_output#saveFile filename doc#toPretty
  end

let save_arm_dictionary () =
  let filename = get_arm_dictionary_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "arm-dictionary" in
  let fnode = xmlElement "arm-dictionary" in
  begin
    arm_dictionary#write_xml fnode;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end

let save_arm_assembly_instructions () =
  let filename = get_arm_assembly_instructions_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "arm-assembly-instructions" in
  let fnode = xmlElement "arm-assembly-instructions" in
  begin
    (!arm_assembly_instructions)#write_xml fnode;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end

let load_mips_dictionary () =
  let filename = get_mips_dictionary_filename () in
  let optnode = load_xml_file filename  "mips-dictionary" in
  match optnode with
  | Some xnode -> mips_dictionary#read_xml xnode
  | _ -> ()

let load_arm_dictionary () =
  let filename = get_arm_dictionary_filename () in
  let optnode = load_xml_file filename "arm-dictionary" in
  match optnode with
  | Some xnode -> arm_dictionary#read_xml xnode
  | _ -> ()
               

let save_function_info (finfo:function_info_int) = 
  let fname = finfo#get_address#to_hex_string in
  let filename = get_function_filename fname "finfo.xml" in
  let doc = xmlDocument () in
  let root = get_bch_root "function-info" in
  let fNode = xmlElement "function-info" in
  begin
    finfo#write_xml fNode ;
    doc#setNode root ;
    root#appendChildren [ fNode ] ;
    file_output#saveFile filename doc#toPretty
  end 

let save_function_variables (finfo:function_info_int) =
  let fname = finfo#get_address#to_hex_string in
  save_vars fname finfo#env#varmgr#vard

let save_function_invariants (finfo:function_info_int) =
  let fname = finfo#get_address#to_hex_string in
  save_invs fname finfo#finv
  
let save_function_type_invariants (finfo:function_info_int) =
  let fname = finfo#get_address#to_hex_string in
  save_tinvs fname finfo#ftinv

let save_function_summary (finfo:function_info_int) = ()
                                                    
let save_function_chif (fname:string) (proc:procedure_int) =
  let filename = get_function_filename fname "chif.txt" in
  file_output#saveFile filename proc#toPretty


let write_xml_jni_calls (node:xml_element_int) jniCalls = ()

let save_results_jni_calls () =
  let jniCalls = get_jni_calls() in
  let num_calls = (List.fold_left (fun acc (_,l) -> acc + (List.length l)) 0 jniCalls) in
  let results_file_name = (get_resultmetrics_filename()) in
  try
    let results_doc = readXmlDocument results_file_name in
    let disassembly_metrics_node = (results_doc#getRoot#getTaggedChild "disassembly_metrics") in
    let jnicalls_node = xmlElement "jnicalls" in
    begin
      jnicalls_node#setIntAttribute "jnicalls" num_calls ;
      disassembly_metrics_node#appendChildren [ jnicalls_node ] ;
      file_output#saveFile results_file_name results_doc#toPretty
    end
  with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    raise (BCH_failure (xml_error results_file_name line col p))  

