(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHFunctionSummaryLibrary
open BCHDataExportSpec
open BCHFunctionInfo
open BCHJavaSignatures
open BCHPreFileIO   
open BCHSystemData
open BCHSystemInfo
open BCHSystemSettings

module FFU = BCHFileFormatUtil
           
let save_library_function_reference (dir:string) (dll:string) (fname:string) (fnames:string list) =
  let _ = pr_debug [ STR "Save reference to " ; STR fname ; STR " in " ; STR dll ; NL ] in
  if function_summary_library#has_dll_function dll fname then
    begin
      List.iter (fun fsname ->
	let node = xmlElement "libfun" in
	let rNode = xmlElement "refer-to" in
	let exename = Filename.chop_extension system_data#get_filename in
	begin 
	  node#appendChildren [ rNode ] ;
	  node#setAttribute "lib" exename ;
	  node#setAttribute "name" fsname ;
	  rNode#setAttribute "name" fname ;
	  rNode#setAttribute "lib" dll ;
	  save_export_function_summary_file fsname  node
	end) fnames ;
      List.length fnames
    end
  else
    0

let save_function_exports (dir:string) = ()
    
let save_data_exports (dir:string) = ()

let save_exports (dir:string) =
  begin
    save_function_exports dir ;
    save_data_exports dir
  end

let has_export_functions () = false

let has_exported_data_values () =
  match FFU.get_exported_data_values () with [] -> false | _ -> true

let save_ordinal_table (dir:string) =
  if FFU.has_export_directory_table () then
    let node = xmlElement "export-ordinal-table" in
    let exports = FFU.get_export_directory_table () in
      begin 
	exports#write_xml_ordinal_table node ;
	save_export_ordinal_table node
      end
  else
    pr_debug [ STR "No export directory found" ; NL ]
