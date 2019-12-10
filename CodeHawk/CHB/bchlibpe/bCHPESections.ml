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

(* =============================================================================
   The implementation in this file is based on the document:

   Microsoft Portable Executable and Common Object File Format Specification,
   Revision 8.2 - September 21, 2010.
   ============================================================================= *)

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDataBlock
open BCHDataExportSpec
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes
open BCHSystemInfo

(* bchlibpe *)
open BCHPEExportDirectory
open BCHPEImportDirectory
open BCHLibPETypes
open BCHPELoadConfigurationStructure
open BCHPESection
open BCHPESectionHeader

class pe_sections_t:pe_sections_int =
object (self)

  val sections = Hashtbl.create 3

  method reset = Hashtbl.clear sections

  method get_sections = Hashtbl.fold (fun _ v a -> v::a) sections []

  method add_section (header:pe_section_header_int) (exeSectionString:string) =
    let section = make_pe_section header exeSectionString in
    Hashtbl.add sections section#index section

  method get_section (index:int) =
    try
      Hashtbl.find sections index
    with
	Not_found ->
	  raise (BCH_failure (LBLOCK [ STR "No section found with index " ; INT index ]))

  method private block_out_data (rva:doubleword_int) (size:doubleword_int) (name:string) =
    let startAddr = rva#add system_info#get_image_base in
    let endAddr = startAddr#add size in
    let db = make_data_block startAddr endAddr name in
    system_info#add_data_block db

  method read_import_directory_table (address:doubleword_int) (size:doubleword_int) =
    if address#equal wordzero then () else
    try
      let section = 
	List.find (fun s -> s#includes_RVA address) self#get_sections in
      begin
	section#read_import_directory_table address ;
	if section#is_executable then
	  self#block_out_data address size "import directory table"
      end
    with
      Not_found ->
        chlog#add "loading executable"
	  (LBLOCK [ STR "There is no section that contains the address of the import " ;
                    STR "directory table: " ; STR address#to_hex_string ])

  method private record_exported_data_values =
    let exportedDataItems = self#get_exported_data_values in
    List.iter (fun a ->
      if system_info#has_exported_item_name a then
	let name = system_info#get_exported_item_name a in
	if system_info#has_exported_data_spec name then
	  let spec = system_info#get_exported_data_spec name in
	  let exvalues = self#get_data_values a spec in
	  List.iter (fun item ->
	    if item.dex_type = "function-pointer" then
	      if List.exists (fun (i,v) -> i = item.dex_offset) exvalues then
		let (_,v) = List.find (fun (i,v) -> i = item.dex_offset) exvalues in
		begin
		  ignore (functions_data#add_function (string_to_doubleword v)) ;
		  chlog#add "record function entry point from exported item" 
		    (LBLOCK [ STR item.dex_name ; STR ": " ; STR v ])
		end) spec.dex_items ) exportedDataItems

  method read_export_directory_table (address:doubleword_int) (size:doubleword_int) =
    if address#equal wordzero then () else
    try
      let section = 
        List.find (fun s -> s#includes_RVA address) self#get_sections in
      begin
	section#read_export_directory_table address size ;
	if section#is_executable then
	  self#block_out_data address size "export directory table" ;
	self#record_exported_data_values
      end
    with
      Not_found ->
        chlog#add "loading executable"
         (LBLOCK [ STR "There is no section that contains the address of the export " ;
                   STR "directory table: " ; STR address#to_hex_string ])

  method read_load_configuration_structure (address:doubleword_int) (size:doubleword_int) =
    if address#equal wordzero then () else
    try
      let section = 
        List.find (fun s -> s#includes_RVA address) self#get_sections in
      begin
	section#read_load_configuration_structure address ;
	if section#is_executable then
	  self#block_out_data address size "load configuration structure"
      end
    with
      Not_found ->
        chlog#add "loading executable"
         (LBLOCK [ STR "There is no section that contains the address of the " ;
                   STR "load configuration directory: " ; STR address#to_hex_string ]) ;

  method read_resource_directory_table (address:doubleword_int) (size:doubleword_int) =
    if address#equal wordzero || size#equal wordzero then () else
      try
	let section =
	  List.find (fun s -> s#includes_RVA address) self#get_sections in
	begin
	  section#read_resource_directory_table address ;
	  if section#is_executable then
	    self#block_out_data address size "resource directory table"
	end
      with
      | Not_found ->
	 chlog#add "loading executable"
	           (LBLOCK [ STR "There is no section that contains the address of the " ;
		             STR "resource directory table: " ; STR address#to_hex_string ])
      | IO.No_more_input ->
         begin
           ch_error_log#add
             "no more input"
             (LBLOCK [ STR "resource directory table at " ; address#toPretty ;
                       STR " with expected size of " ; size#toPretty ] ) ;
           raise IO.No_more_input
         end

  method get_SE_handlers =
    try
      let section =
	List.find (fun s -> s#has_load_configuration_directory) self#get_sections in
      section#get_SE_handlers
    with
      Not_found -> []


  method get_imported_function_by_index (index:doubleword_int):(string * string) option =
    try
      let section =
	List.find (fun s -> s#has_import_directory_table) self#get_sections in
      section#get_imported_function_by_index index
    with
      Not_found ->
	None

  method get_imported_function (address:doubleword_int):(string * string) option =
    try
      let section =
	List.find (fun s -> s#includes_VA address) self#get_sections in
      section#get_imported_function address
    with
      Not_found -> 
	None

  method get_containing_section(address:doubleword_int):pe_section_int option =
    try
      Some (List.find (fun s -> s#includes_VA address) self#get_sections)
    with
      Not_found -> None
      

  method get_read_only_initialized_doubleword (address:doubleword_int):doubleword_int option =
    try
      let section =
	List.find (fun s -> (s#includes_VA address)  && 
	  (s#is_read_only || s#has_import_directory_table || 
	     system_info#is_in_readonly_range address)  ) self#get_sections in
      section#get_initialized_doubleword address
    with
      Not_found ->
	let _ = chlog#add "section data" (LBLOCK [ STR "No section found that includes " ; 
						   STR address#to_hex_string ]) in
	None

  method get_n_doublewords (address:doubleword_int) (n:int) =
    try
      let section = List.find (fun s -> s#includes_VA address) self#get_sections in
      section#get_n_doublewords address n
    with
      Not_found ->
	let _ = chlog#add "section data" (LBLOCK [ STR "No section found that includes " ;
						   STR address#to_hex_string ]) in
	[]

  method get_string_reference (address:doubleword_int):string option =
    match self#get_wide_string_reference address with
      Some s -> Some s
    | _ ->
      try
	let section =
	  List.find (fun s -> s#includes_VA address) self#get_sections in
	section#get_string_reference address
      with
	Not_found ->
	  None

  method get_wide_string_reference (address:doubleword_int):string option =
    try
      let section =
	List.find (fun s -> s#includes_VA address) self#get_sections in
      section#get_wide_string_reference address
    with
	Not_found ->
	  None

  method get_virtual_function_address (address:doubleword_int):doubleword_int option =
    try
      let section =
	List.find (fun s -> s#includes_VA address) self#get_sections in
      section#get_initialized_doubleword address 
    with
      Not_found ->
	None

  method private evaluate_exported_values  
    (spec:data_export_spec_t) (l:(int * doubleword_int) list) =
    List.map (fun (i,a) -> 
      let ty = 
	try (List.find (fun item -> item.dex_offset = i) spec.dex_items).dex_type 
	with Not_found -> "unknown" in
      let v = match ty with
	| "function-pointer" -> a#to_hex_string 
	| "string" -> 
	  begin match self#get_string_reference a with Some s -> s | _ -> "unknown string" end
	| "int" -> (string_of_int a#to_int)
	| _ -> a#to_hex_string in
      (i,v)) l

  method get_data_values (addr:doubleword_int) (spec:data_export_spec_t) =
    try
      let section =
	List.find (fun s -> s#includes_VA addr) self#get_sections in
      let values = section#get_data_values addr spec in
      self#evaluate_exported_values spec values
    with
      Not_found -> []
	    
  method get_imported_functions =
    try
      let section =
	List.find (fun s -> s#has_import_directory_table) self#get_sections in
      section#get_imported_functions
    with
      Not_found -> []

  method get_exported_functions =
    try
      let section = List.find (fun s -> s#has_export_directory_table) self#get_sections in
      section#get_exported_functions
    with
      Not_found -> []

  method is_exported (dw:doubleword_int) =
    List.exists (fun a -> dw#equal a) self#get_exported_functions

  method get_exported_data_values =
    try
      let section = List.find (fun s -> s#has_export_directory_table) self#get_sections in
      section#get_exported_data_values
    with
      Not_found -> []


  method import_directory_entry_to_pretty (dllName:string) =
    try
      let section = List.find (fun s -> s#has_import_directory_table) self#get_sections in
      section#import_directory_entry_to_pretty dllName
    with
      Not_found -> (LBLOCK [ STR "No import directory table found. " ; NL ] )

  method get_import_directory_table =
    List.concat (List.map (fun s -> s#get_import_directory_table) self#get_sections)

  method get_export_directory_table =
    try
      let section = List.find (fun s -> s#has_export_directory_table) self#get_sections in
      section#get_export_directory_table
    with
      Not_found -> 
	raise (BCH_failure (LBLOCK [ STR "No export directory table found" ]))

  method get_load_configuration_directory =
    try
      let section = List.find (fun s -> s#has_load_configuration_directory) self#get_sections in
      section#get_load_configuration_directory
    with
      Not_found ->
	raise (BCH_failure (LBLOCK [ STR "No load configuration directory found" ]))

  method has_import_directory_table =
    List.exists (fun s -> s#has_import_directory_table) self#get_sections

  method has_export_directory_table =
    List.exists (fun s -> s#has_export_directory_table) self#get_sections

  method has_load_configuration_directory =
    List.exists (fun s -> s#has_load_configuration_directory) self#get_sections 

  method import_directory_table_to_pretty =
    try
      let section = 
	List.find (fun s -> s#has_import_directory_table) self#get_sections in
      section#import_directory_table_to_pretty
    with
      Not_found ->
	(LBLOCK [ STR "No import directory table found. " ; NL ] )

  method export_directory_table_to_pretty =
    try
      let section =
        List.find (fun s -> s#has_export_directory_table) self#get_sections in
      section#export_directory_table_to_pretty
    with
      Not_found ->
        (LBLOCK [ STR "No export directory table found. " ; NL ] )

  method load_configuration_directory_to_pretty =
    try
      let section =
        List.find (fun s -> s#has_load_configuration_directory) self#get_sections in
      section#load_configuration_directory_to_pretty
    with
      Not_found ->
      (LBLOCK [ STR "No load configuration directory found. " ; NL ] )

  method includes_VA (address:doubleword_int) =
    List.exists (fun s -> s#includes_VA address) self#get_sections

  method is_writable_address (address:doubleword_int) =
    List.exists (fun s -> s#includes_VA address && s#is_writable) self#get_sections

  method is_read_only_address (address:doubleword_int):bool =
    List.exists (fun s -> s#includes_VA address && 
      (s#is_read_only || system_info#is_in_readonly_range address)) self#get_sections

  method toPretty = 
    Hashtbl.fold (fun _ v a -> 
      LBLOCK [ a ; NL ; STR v#get_name ])
      sections (STR "Sections:") 

end

let pe_sections = new pe_sections_t
