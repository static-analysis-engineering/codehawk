(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHPrettyUtil
open CHXmlDocument

(* chlib *)
open BCHSystemInfo
open BCHSystemSettings

(* bchlib *)
open BCHBasicTypes
open BCHDataExportSpec
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHPreFileIO
open BCHSystemData

(* bchlibpe *)
open BCHPEHeader
open BCHPESections

(* chlibx86 *)
open BCHAssemblyFunctions
open BCHAssemblyInstructions
open BCHDisassemble

let export_dir = ref ""

let speclist = [
  ("-summaries",Arg.String system_settings#set_summary_jar, "location of summary jar");
  ("-appsdir", Arg.String system_settings#set_apps_dir,
   "location of application-dependent summaries and java native method signatures");
  ("-o", Arg.String (fun s -> export_dir := s),
   "non-default location to save the exported summaries");
  ("-verbose", Arg.Unit (fun () -> system_settings#set_verbose), "print intermediate results");
]

let usage_msg = "chx86_save_exports <exe file>"
let read_args () = Arg.parse speclist system_info#set_filename usage_msg


let get_log_filename () =
  "chanalysis/" ^ (get_filename ()) ^ "_sx.chlog"

let get_errorlog_filename () =
  "chanalysis/" ^ (get_filename ()) ^ "_sx.ch_error_log"

let is_java_native_method (name:string) =
  ((String.length name) > 6 && (String.sub name 0 6) = "_Java_") ||
  ((String.length name) > 5 && (String.sub name 0 5) = "Java_")


let disassemble () =
  let entryPointVA = system_info#get_address_of_entry_point in
  let codeSectionHeaders =
    List.find_all (fun h -> h#is_executable || h#includes_VA entryPointVA)
      pe_header#get_section_headers in
  match codeSectionHeaders with
  | [] -> pr_debug [STR "No executable sections found "; NL]
  | l ->
    try
      let numSections = List.length l in
      let _ =
	if numSections > 1 then
	  pr_debug [STR "Disassembling "; INT numSections; STR " executable sections"; NL] in
      let size = disassemble_sections codeSectionHeaders in
      pr_debug [STR "Disassembled "; INT size; STR " bytes into ";
		 INT !assembly_instructions#get_num_instructions; STR " instructions"; NL]
    with
    | Invocation_error s -> pr_debug [STR "Failure in disassembly: "; STR s]
    | BCH_failure p -> pr_debug [STR "Failure in disassembly: "; p; NL]

let construct_functions () =
  try
    begin
      construct_functions ();
      decorate_functions ();
      pr_debug [STR "Constructed "; INT (List.length assembly_functions#get_functions);
		 STR " functions"; NL]
    end
  with
  | Invocation_error s -> pr_debug [STR "Failure in construct functions: "; STR s; NL]
  | BCH_failure p -> pr_debug [STR "Failure in constructing functions: "; p; NL]


let save_library_function_reference
      (_dir:string) (dll:string) (fname:string) (fnames:string list) =
  if function_summary_library#has_dll_function dll fname then
    begin
      List.iter (fun fsname ->
	let node = xmlElement "libfun" in
	let rNode = xmlElement "refer-to" in
	let exename = Filename.chop_extension system_data#get_filename in
	begin
	  node#appendChildren [rNode];
	  node#setAttribute "lib" exename;
	  node#setAttribute "name" fsname;
	  rNode#setAttribute "name" fname;
	  rNode#setAttribute "lib" dll;
	  save_export_function_summary_file fsname  node
	end) fnames;
      List.length fnames
    end
  else
    0


let save_function_exports (dir:string) =
  let pri i = fixed_length_pretty ~alignment:StrRight (INT i) 10 in
  let exportedFunctions = pe_sections#get_exported_functions in
  let exename = Filename.chop_extension system_data#get_filename in
  let sum_count = ref 0 in
  let nosum_count = ref 0 in
  begin
    List.iter (fun a ->
      try
	let finfo = load_function_info a in
	let fnames = (* system_info#get_exported_function_names a*) [] in
	let _ = pverbose [STR a#to_hex_string; STR "  "; INT (List.length fnames );
			   STR " names"; NL] in
	let fnames = List.filter (fun name -> not (is_java_native_method name)) fnames in
	match fnames with
	| [] -> ()
	| _ ->
	  let optDll = List.fold_left (fun acc fname ->
	    match acc with Some _ -> acc | _ ->
	      match function_summary_library#search_for_library_function fname with
	      | Some dll -> Some (dll,fname)
	      | _ -> None) None fnames in
	  match optDll with
	  | Some (dll,fname) ->
	    let saved = save_library_function_reference dir dll fname fnames in
	    sum_count := !sum_count + saved
	  | _ ->
	    let summary = finfo#get_summary in
	    match summary#get_stack_adjustment with
	    | None -> nosum_count := (List.length fnames) + !nosum_count
	    | _ ->
	      List.iter (fun fname ->
		let node = xmlElement "libfun" in
		let _ = pverbose [STR "  "; pri !sum_count; STR "  "; STR fname; NL] in
		begin
		  sum_count := !sum_count + 1;
		  (finfo#get_summary)#write_xml node;
		  node#setAttribute "lib" exename;
		  save_export_function_summary_file fname  node
		end) fnames
      with _ ->
	pr_debug [STR "Failure exporting functions for "; a#toPretty; NL]
    ) exportedFunctions;
    pr_debug [STR "Exported    : "; INT !sum_count; STR " functions"; NL;
	       STR "Not exported: "; INT !nosum_count; STR " functions"; NL]
  end


let save_data_exports (dir:string) =
  let exportedDataItems = pe_sections#get_exported_data_values in
  begin
    List.iter (fun a ->
      if system_info#has_exported_item_name a then
	let name = system_info#get_exported_item_name a in
	if system_info#has_exported_data_spec name then
	  let spec = system_info#get_exported_data_spec name in
	  let exvalues = pe_sections#get_data_values a spec in
	  let exportVal = make_data_export_value spec a exvalues in
	  let node = xmlElement "data-value" in
	  let _ = pverbose [STR "  "; STR name; NL] in
	  let _ = pverbose [STR "Constructing data value for "; STR name; NL;
			     INDENT (3,data_export_spec_to_pretty spec); NL] in
	  let _ = pverbose [pretty_print_list exvalues (fun (i,a) ->
	      LBLOCK [STR "("; INT i; STR ", "; STR a; STR ")"; NL]) "" "" ""] in
	  begin
	    exportVal#write_xml node;
	    save_export_data_value_file name node;
	  end)
      exportedDataItems
  end


let save_exports (dir:string) =
  begin
    save_function_exports dir;
    save_data_exports dir
  end


let has_export_functions () =
  let exportedFunctions = pe_sections#get_exported_functions in
  List.fold_left (fun acc a ->
    if acc then acc else
      let fnames = (* system_info#get_exported_function_names a *) [] in
      let fnames =
        List.filter (fun name -> not (is_java_native_method name)) fnames in
      match fnames with [] -> acc | _ -> true) false exportedFunctions


let has_exported_data_values () =
  match pe_sections#get_exported_data_values with [] -> false | _ -> true


let save_ordinal_table (dir:string) =
  if pe_sections#has_export_directory_table then
    let node = xmlElement "export-ordinal-table" in
    let exports = pe_sections#get_export_directory_table in
      begin
	exports#write_xml_ordinal_table node;
	save_export_ordinal_table node
      end
  else
    pr_debug [STR "No export directory found"; NL]


let main () =
  try
    begin
      read_args ();
      system_info#initialize;
      load_pe_files ();
      if has_export_functions () || has_exported_data_values () then
	let exportDir =
          (* if !export_dir = "" then
	    system_settings#get_export_directory
	  else  *)
          !export_dir in
	begin
	  disassemble ();
	  construct_functions ();
	  save_exports exportDir;
	  save_ordinal_table exportDir;
	  file_output#saveFile (get_log_filename ()) chlog#toPretty;
	  file_output#saveFile (get_errorlog_filename ()) ch_error_log#toPretty;
	end
      else
	pr_debug [STR "No functions to be exported"; NL]
    end
  with
  | XmlDocumentError (line,col,p) ->
    pr_debug [STR "Xml error: ("; INT line; STR ", "; INT col; STR "): "; p; NL]
  | BCH_failure p ->
    begin
      file_output#saveFile (get_log_filename ()) chlog#toPretty;
      file_output#saveFile (get_errorlog_filename ()) ch_error_log#toPretty;
      pr_debug [STR "BCH-failure: "; p]
    end
  | CHXmlReader.XmlReaderError (line,col,p) ->
    pr_debug [STR "Xml error at ("; INT line ; STR ","; INT col; STR "): "; p; NL]
  | Invalid_argument s
  | Invocation_error s ->
    begin
      file_output#saveFile (get_log_filename ()) chlog#toPretty;
      file_output#saveFile (get_errorlog_filename ()) ch_error_log#toPretty;
      pr_debug [STR "Invocation error: "; STR s]
    end

let _ = Printexc.print main ()
