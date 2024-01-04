(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHFileIO
open CHLogger
open CHXmlDocument
open CHXmlReader

(* bchcil *)
open BCHBCDictionary
open BCHBCFiles

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDictionary
open BCHInterfaceDictionary
open BCHLibTypes
open BCHLocationInvariant
open BCHLocationVarInvariant
open BCHSystemData
open BCHSystemSettings
open BCHTypeInvariants
open BCHXmlUtil
open BCHUtilities
open BCHVersion

(* Filename conventions -------------------------------------------------------
 *
 * Given an executable file with name name.ext (ext may be omitted):
 * - executable content:
 *       name.ext.ch/x/name_ext_<sections> (xml files)
 *                   x/name_ext_pe_header.xml
 *                   x/name_ext_elf_header.xml
 *                   x/name_ext_elf_dictionary.xml
 *
 * - analysis artifacts:
 *      name.ext.ch/a/name_ext_functions.xml
 *                  a/name_ext_global_state.xml
 *                  a/name_ext_system_info.xml
 *                  a/name_ext_functions.jar
 *                  a/name_ext_asm.log
 *                  a/name_ext_orphan.log
 *                  a/name_ext_bdict.xml
 *                  a/name_ext_ixdict.xml
 *                  a/functions/name_ext_<address>/name_ext_address_finfo.xml
 *                                                 name_ext_address_vars.xml
 *                                                 name_ext_address_invs.xml
 *                                                 name_ext_address_tinvs.xml
 *
 * - results artifacts:
 *      name.ext.ch/r/name_ext_data.xml
 *                  r/name_ext_metrics.xml
 *                  r/name_ext_x86dict.xml   (x86)
 *                  r/name_ext_mipsdict.xml  (mips)
 *                  r/name_ext_mips_asm.xml  (mips)
 *                  r/name_ext_armdict.xml   (arm)
 *                  r/name_ext_arm_asm.xml   (arm)
 *                  r/functions/name_ext_<address>.xml
 *
 * - artifacts parsed from c files:
 *      name.ext.ch/c/name_ext_bcfile.xml
 *                  c/functions/name_ext_<address>.xml
 *
 * - exports:
 *      name.ext.ch/exports/functions/name_ext_address>.xml  (currently not used)
 *
 * - userdata:
 *      name.ext.ch/u/name_ext_system_u.xml
 *                    classes/name_ext_<classname>_cppclass_u.xml
 *                    functions/name_ext_<address>_u.xml
 *                    structconstants/name_ext_<structname>_structconstant_u.xml
 *                    structs/name_ext_<structname>_struct_u.xml
 *
 * - statusinfo:
 *      name.ext.ch/s/name_ext_disassembly.xml
 * ----------------------------------------------------------------------------
 *)

let get_filename () =
  let name = replace_dot system_data#get_filename in
  if system_data#is_elf then name ^ "_ELF" else name

let get_chdir () = system_data#get_filename ^ ".ch"

let get_analysis_dir () = Filename.concat (get_chdir ()) "a"

let get_results_dir () = Filename.concat (get_chdir ()) "r"

let get_bc_dir () = Filename.concat (get_chdir ()) "c"
let get_executable_dir () = Filename.concat (get_chdir ()) "x"
let get_export_dir () = Filename.concat (get_chdir ())  "exports"
let get_userdata_dir () = Filename.concat (get_chdir ()) "u"
let get_status_dir () = Filename.concat (get_chdir ()) "s"


let functions_file_path = ref []


(* Returns a list of strings that form the components separated by the separator;
	 without the separator itself included *)
let string_nsplit (separator:char) (s:string):string list =
  let result = ref [] in
  let len = String.length s in
  let start = ref 0 in
  begin
    while !start < len do
      let s_index =
        try String.index_from s !start separator with Not_found -> len in
      let substring = String.sub s !start (s_index - !start) in
      begin
	result := substring :: !result ;
	start := s_index + 1
      end
    done;
    List.rev !result
  end


let get_bch_root (info:string):xml_element_int =
  let exename = system_data#get_filename in
  let root = xmlElement "codehawk-binary-analyzer" in
  let chversion = version#get_version in
  let chdate = version#get_date in
  let hNode = xmlElement "header" in
  begin
    hNode#setAttribute "name" exename;
    hNode#setAttribute "info" info;
    hNode#setAttribute "time" (current_time_to_string ());
    hNode#setAttribute "chb-version" chversion;
    hNode#setAttribute "chb-date" chdate;
    root#appendChildren [hNode];
    root
  end


let create_directory dir =
  let sys_command s =
    let _ = pverbose [ STR "Trying " ; STR s ; NL ] in
    let e = Sys.command s in
    pverbose [ STR "Executing " ; STR s ; STR " (exit value: " ; INT e ; NL ] in
  let subs = string_nsplit '/' dir in
  let directories = List.fold_left (fun a s ->
    match (s,a) with
    | ("",[]) -> [ "/" ]
    | ("",_) -> a
    | (d,[]) -> [ d ]
    | (d,["/"]) -> [ "/" ^ d ]
    | (d,h::_) -> (h ^ "/" ^ d) :: a) [] subs in
  List.iter (fun d -> if Sys.file_exists d then () else sys_command ("mkdir " ^ d))
    (List.rev directories)


(* ------------------------------------ add name_ext_functions.jar to classpath *)
let set_functions_file_path () =
  let name = get_filename () in
  let analysisdir = get_analysis_dir () in
  let _ = create_directory analysisdir in
  let jarfile = Filename.concat analysisdir (name ^ "_functions.jar") in
  match open_path jarfile with
  | Some p -> functions_file_path := p :: !functions_file_path
  | _ -> ()


let get_functions_file_path () = !functions_file_path

(* ----------------------------------------------------------- c-parsed files *)
let get_bc_filename (name: string) =
  let exename = get_filename () in
  let fdir = get_bc_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ name)


let get_bcfiles_filename () = get_bc_filename "bcfiles.xml"


let save_bc_files () =
  let filename = get_bcfiles_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "bcfiles" in
  let bcnode = xmlElement "bcfiles" in
  begin
    bcfiles#write_xml bcnode;
    doc#setNode root;
    root#appendChildren [bcnode];
    file_output#saveFile filename doc#toPretty
  end

(* ----------------------------------------------------------- userdata files *)
let get_userdata_filename (name:string) =
  let exename = get_filename () in
  let fdir = get_userdata_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ name)

let get_userdata_system_filename () = get_userdata_filename "system_u.xml"

let get_annotation_system_filename () = get_userdata_filename "system_a.xml"

let get_ida_dbfe_filename () = get_userdata_filename "dbfe_ida.xml"

let get_memory_string_filename (address:string) =
  get_userdata_filename (address ^ "_mem.xml")

let get_userdata_function_filename (name:string) =
  let exename = get_filename () in
  let fdir = get_userdata_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "functions" in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ name ^ "_u.xml")

let get_userdata_structconstant_filename (name:string) =
  let exename = get_filename () in
  let fdir = get_userdata_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "structconstants" in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ name ^ "_structconstant_u.xml")

let get_userdata_cpp_class_filename (name:string) =
  let exename = get_filename () in
  let fdir = get_userdata_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "classes" in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ name ^ "_cppclass_u.xml")

let get_userdata_struct_filename (name:string) =
  let exename = get_filename () in
  let fdir = get_userdata_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "structs" in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ name  ^ "_struct_u.xml")

let get_userdata_jumptable_filename (jaddr:string) =
  let exename = get_filename () in
  let fdir = get_userdata_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "jumptables" in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ jaddr ^ "_jt_u.xml")

(* ------------------------------------------------------- exported files *)
let get_export_function_filename (name:string) =
  let fdir = get_export_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "functions" in
  let _ = create_directory fdir in
  Filename.concat fdir (name ^ ".xml")

let get_export_data_filename (name:string) =
  let fdir = get_export_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "data" in
  let _ = create_directory fdir in
  Filename.concat fdir (name ^ ".xml")

let get_export_ordinal_table_filename () =
  let fdir = get_export_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir "ordinal_table.xml"

(* --------------------------------------------------- executable content *)
let get_disassembly_filename (ext:string) =
  let exename = get_filename () in
  let fdir = get_executable_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename  ^ "_" ^ ext)

let get_section_filename (sname:string) =
  let sname = replace_slash sname in
  let sname = if has_control_characters sname then hex_string sname else sname in
  get_disassembly_filename ("section_" ^ sname ^ ".xml")

let get_segment_filename (index:int) =
  let sname = "segment_" ^ (string_of_int index) ^ ".xml" in
  get_disassembly_filename sname

let get_pe_header_filename () =
  get_disassembly_filename "pe_header.xml"

let get_executable_dump_filename () =
  get_disassembly_filename "xdump.xml"

let get_elf_header_filename () =
  get_disassembly_filename "elf_header.xml"

let get_elf_dictionary_filename () =
  get_disassembly_filename "elf_dictionary.xml"

(* ------------------------------------------------------- analysis files *)

let get_functions_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_functions.xml")

let get_function_filename (fname:string) (ext:string) =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "functions" in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir (exename ^ "_" ^ fname) in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ fname ^ "_" ^ ext)


let get_vars_filename (fname:string) =
  get_function_filename fname "vars.xml"


let get_invs_filename (fname:string) =
  get_function_filename fname "invs.xml"


let get_tinvs_filename (fname:string) =
  get_function_filename fname "tinvs.xml"


let get_varinvs_filename (fname: string) =
  get_function_filename fname "varinvs.xml"


let get_functions_directory () =
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "functions" in
  let _ = create_directory fdir in
  fdir

let get_global_state_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_global_state.xml")

let get_system_info_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_system_info.xml")

let get_bdictionary_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir  () in
  let  _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_bdict.xml")

let get_bcdictionary_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir  () in
  let  _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_bcdict.xml")

let get_interface_dictionary_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_ixdict.xml")

let get_asm_listing_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename  ^ "_asm.log")

let get_orphan_code_listing_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename  ^ "_orphan.log")

let get_duplicate_coverage_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_duplicates.log")

let get_jni_calls_filename () =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_jni_calls.xml")

(* ------------------------------------------------------ results files *)
let get_resultmetrics_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_metrics.xml")


let get_resultdata_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_data.xml")


let get_x86dictionary_filename  () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_x86dict.xml")


let get_mips_dictionary_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_mipsdict.xml")


let get_mips_assembly_instructions_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_mips_asm.xml")


let get_arm_dictionary_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_armdict.xml")


let get_arm_assembly_instructions_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_arm_asm.xml")


let get_pwr_dictionary_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_pwrdict.xml")


let get_pwr_assembly_instructions_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_pwr_asm.xml")


let get_cfgs_filename () =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_cfgs.xml")


let get_app_function_results_filename (name:string) =
  let exename = get_filename () in
  let fdir = get_results_dir () in
  let _ = create_directory fdir in
  let fdir = Filename.concat fdir "functions" in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_" ^ name ^ ".xml")

(* ------------------------------------------------------ status files *)

let get_disassembly_status_filename () =
  let exename = get_filename () in
  let fdir = get_status_dir () in
  let _ = create_directory fdir in
  Filename.concat fdir (exename ^ "_disassembly.xml")


let load_xml_file (filename:string) (tag:string) =
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in Some (doc#getRoot#getTaggedChild tag)
    with
  | XmlDocumentError (line,col,p)
  | XmlReaderError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (BCH_failure msg)
    end
  else
    None

let load_ida_dbfe_file () =
  let filename = get_ida_dbfe_filename () in
  load_xml_file filename "function-entry-points"

let load_resultmetrics_file () =
  let filename = get_resultmetrics_filename () in
  load_xml_file filename "results"

let load_system_file () =
  let filename = get_system_info_filename () in
  load_xml_file filename "system-info"

let load_global_state_file () =
  let filename = get_global_state_filename () in
  load_xml_file filename "global-state"

let load_userdata_system_file () =
  let filename = get_userdata_system_filename () in
  load_xml_file filename "system-info"

let load_annotation_system_file () =
  let filename = get_annotation_system_filename () in
  load_xml_file filename "system-info"

let load_userdata_function_file (name:string) =
  let filename = get_userdata_function_filename name in
  load_xml_file filename "function-summary"

let load_userdata_structconstant_file (name:string) =
  let filename = get_userdata_structconstant_filename name in
  load_xml_file filename "struct"

let load_userdata_jumptable_file (jaddr:string) =
  let filename = get_userdata_jumptable_filename jaddr in
  load_xml_file filename "jumptable"

let create_userdata_system_file (appname:string) =
  let filename = get_userdata_system_filename () in
  if Sys.file_exists filename then () else
    let doc = xmlDocument () in
    let root = get_bch_root "system-userdata" in
    let sNode = xmlElement "system-info" in
    let ssNode = xmlElement "settings" in
    let dbNode = xmlElement "data-blocks" in
    let feNode = xmlElement "function-entry-points" in
    let fnNode = xmlElement "function-names" in
    let nrNode = xmlElement "non-returning-functions" in
    let ggNode = xmlElement "disable" in
    begin
      doc#setNode root ;
      root#appendChildren [ sNode ] ;
      sNode#appendChildren [ ssNode ; dbNode ; fnNode ; feNode ; nrNode ] ;
      ssNode#appendChildren [ ggNode ] ;
      sNode#setAttribute "app" appname ;
      ggNode#setAttribute "name" "sideeffects-on-globals" ;
      file_output#saveFile filename doc#toPretty
    end


let load_userdata_cpp_class_file (cname:string) =
  let filename = get_userdata_cpp_class_filename cname in
  load_xml_file filename "cpp-class"


let load_userdata_struct_file (name:string) =
  let filename = get_userdata_struct_filename name in
  load_xml_file filename "struct"


let load_bc_files () =
  let filename = get_bcfiles_filename () in
  let optnode = load_xml_file filename "bcfiles" in
  match optnode with
  | Some bcnode -> bcfiles#read_xml bcnode;
  | _ -> ()


let save_export_function_summary_file (fname:string) (node:xml_element_int) =
  let filename = get_export_function_filename fname in
  let doc = xmlDocument () in
  let root = get_bch_root "exported-function-summary" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_userdata_function_summary_file (fname: string) (node: xml_element_int) =
  let filename = get_userdata_function_filename fname in
  let doc = xmlDocument () in
  let root = get_bch_root "function-summary" in
  begin
    doc#setNode root;
    root#appendChildren [node];
    file_output#saveFile filename doc#toPretty
  end


let save_userdata_function_summaries_file (node: xml_element_int) =
  let filename = get_userdata_filename "cil_summaries_u.xml" in
  let doc = xmlDocument () in
  let root = get_bch_root "cil-summaries" in
  begin
    doc#setNode root;
    root#appendChildren [node];
    file_output#saveFile filename doc#toPretty
  end


let save_export_data_value_file  (dname:string) (node:xml_element_int) =
  let filename = get_export_data_filename dname in
  let doc = xmlDocument () in
  let root = get_bch_root "exported-data-value" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_resultdata_file (node:xml_element_int) =
  let filename = get_resultdata_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "application-results" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_cfgs (node:xml_element_int) =
  let filename = get_cfgs_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "cfgs" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_app_function_results_file (name:string) (node:xml_element_int) =
  let filename = get_app_function_results_filename name in
  let doc = xmlDocument () in
  let root = get_bch_root "application-results" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_export_ordinal_table (node:xml_element_int) =
  let filename = get_export_ordinal_table_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "export-ordinal-table" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_executable_dump (node:xml_element_int) =
  let filename = get_executable_dump_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "executable-dump" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
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

let load_export_ordinal_table (name:string) =
  let path = system_settings#get_summary_paths in
  let filename = name ^ "/" ^ name ^ "_ordinal_table.xml" in
  let optStr = get_file_from_jar path filename in
  match optStr with
  | Some s ->
    let doc = readXmlDocumentString s in
    let root = doc#getRoot in
    if root#hasOneTaggedChild "export-ordinal-table" then
	Some (root#getTaggedChild "export-ordinal-table")
    else
      None
  | _ -> None


let load_pe_header_file () =
  let filename = get_pe_header_filename () in
  load_xml_file filename "pe-header"

let load_elf_header_file () =
  let filename = get_elf_header_filename () in
  load_xml_file filename "elf-header"

let load_section_file (sname:string) =
  let filename = get_section_filename sname in
  load_xml_file filename "raw-section"

let load_segment_file (index:int) =
  let filename = get_segment_filename index in
  load_xml_file filename "raw-segment"

let save_bdictionary () =
  let filename = get_bdictionary_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "bdictionary" in
  let fnode = xmlElement  "bdictionary" in
  begin
    bdictionary#write_xml fnode;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end

let load_bdictionary () =
  let filename = get_bdictionary_filename () in
  let optnode = load_xml_file filename "bdictionary" in
  match optnode with
  | Some bnode -> bdictionary#read_xml bnode
  | _ -> ()


let save_bcdictionary () =
  let filename = get_bcdictionary_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "bcdictionary" in
  let fnode = xmlElement "bcdictionary" in
  begin
    bcdictionary#write_xml fnode;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end


let load_bcdictionary () =
  let filename = get_bcdictionary_filename () in
  let optnode = load_xml_file filename "bcdictionary" in
  match optnode with
  | Some bnode -> bcdictionary#read_xml bnode
  | _ -> ()


let save_interface_dictionary () =
  let filename =  get_interface_dictionary_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root  "interface-dictionary" in
  let fnode = xmlElement "interface-dictionary" in
  begin
    interface_dictionary#write_xml fnode;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end


let load_interface_dictionary () =
  let filename =  get_interface_dictionary_filename () in
  let optnode = load_xml_file filename "interface-dictionary" in
  match optnode with
  | Some inode -> interface_dictionary#read_xml inode
  | _ -> ()


let get_function_file_xnode (fname:string) (ext:string) (tag:string) =
  let exename = get_filename () in
  let basename = exename ^ "_" ^ fname in
  let filename = basename ^ "_" ^ ext in
  let path = get_functions_directory () in
  let filename = path ^ "/" ^ basename ^ "/" ^ filename in
  load_xml_file filename tag

let extract_function_file (fname:string) (ext:string) (tag:string) =
  let exename = get_filename () in
  let basename = exename ^ "_" ^ fname in
  let filename = basename ^ "_" ^ ext in
  let filename = Filename.concat (Filename.concat "functions" basename) filename in
  let path = get_functions_file_path () in
  let optStr = get_file_from_jar path filename in
  match optStr with
  | Some s ->
    let doc = readXmlDocumentString s in
    let root = doc#getRoot in
    if root#hasOneTaggedChild tag then
      Some (root#getTaggedChild tag)
    else
      begin
	ch_error_log#add
          "xml from jar"
	  (LBLOCK [
               STR "No node found in ";
               STR filename;
               STR " with tag ";
               STR tag]) ;
	None
      end
  | _ -> None

let save_vars (fname:string) (vard:vardictionary_int) =
  let filename = get_vars_filename fname in
  let doc = xmlDocument () in
  let root = get_bch_root "function" in
  let fnode = xmlElement "function" in
  begin
    vard#write_xml fnode ;
    fnode#setAttribute "fname" fname ;
    doc#setNode root ;
    root#appendChildren [ fnode ] ;
    file_output#saveFile filename doc#toPretty
  end


let load_function_vard_file (fname: string): xml_element_int option =
  try
    extract_function_file fname "vars.xml" "function"
  with
  | Zip.Error (_, s, _) ->
     begin
       ch_error_log#add "zip error" (LBLOCK [STR fname; STR ": "; STR s]);
       None
     end


let save_invs (fname:string) (invio:invariant_io_int) =
  let filename = get_invs_filename fname in
  let doc = xmlDocument () in
  let root = get_bch_root "function" in
  let fnode = xmlElement "function" in
  begin
    invio#write_xml fnode ;
    fnode#setAttribute "fname" fname ;
    doc#setNode root ;
    root#appendChildren [ fnode ] ;
    file_output#saveFile filename doc#toPretty
  end


let read_invs (fname:string) (vard:vardictionary_int):invariant_io_int =
  let optnode = extract_function_file fname "invs.xml" "function" in
  mk_invariant_io optnode vard fname


let save_tinvs (fname:string) (tinvio:type_invariant_io_int) =
  let filename = get_tinvs_filename fname in
  let doc = xmlDocument () in
  let root = get_bch_root "function" in
  let tnode = xmlElement "function" in
  begin
    tinvio#write_xml tnode ;
    tnode#setAttribute "fname" fname ;
    doc#setNode root ;
    root#appendChildren [ tnode ] ;
    file_output#saveFile filename doc#toPretty
  end


let read_tinvs (fname:string) (vard:vardictionary_int):type_invariant_io_int =
  let optnode = extract_function_file fname "tinvs.xml" "function" in
  mk_type_invariant_io optnode vard fname


let save_varinvs (fname: string) (varinvio: var_invariant_io_int) =
  let filename = get_varinvs_filename fname in
  let doc = xmlDocument () in
  let root = get_bch_root "function" in
  let fnode = xmlElement "function" in
  begin
    varinvio#write_xml fnode;
    fnode#setAttribute "fname" fname;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end


let read_varinvs (fname: string) (vard: vardictionary_int): var_invariant_io_int =
  (* let optnode = extract_function_file fname "varinvs.xml" "function" in *)
  mk_var_invariant_io None vard fname

let extract_function_info_file (fname:string) =
  try
    extract_function_file fname "finfo.xml" "function-info"
  with
  | Zip.Error _ ->
     get_function_file_xnode fname "finfo.xml" "function-info"


let extract_inferred_function_summary_file (fname:string) =
  extract_function_file fname "fsum.xml" "function-summary"


let extract_inferred_function_arguments_from_summary_file (fname:string) =
  extract_function_file fname "fsum.xml" "function-arguments"


let save_log_files name =
  let exename = get_filename () in
  let fdir = get_analysis_dir () in
  let _ = create_directory fdir in
  let name = exename ^ "_" ^ name in
  let logfilename = Filename.concat fdir (name ^ ".chlog") in
  let errorlogfilename = Filename.concat fdir (name ^ ".ch_error_log") in
  begin
    file_output#saveFile logfilename chlog#toPretty ;
    file_output#saveFile errorlogfilename ch_error_log#toPretty;
    (if collect_diagnostics () then
       let diagnosticsfilename =
         Filename.concat fdir (name ^ ".ch_diagnostics_log") in
       file_output#saveFile diagnosticsfilename ch_diagnostics_log#toPretty)
  end


let read_memory_string_file (address:string) =
  let filename = get_memory_string_filename address in
  read_hex_stream_file filename


let save_function_info_file (fname: string) (node: xml_element_int) =
  let filename = get_function_filename fname "finfo.xml" in
  let doc = xmlDocument () in
  let root = get_bch_root "function-info" in
  begin
    doc#setNode root;
    root#appendChildren [node];
    file_output#saveFile filename doc#toPretty
  end
