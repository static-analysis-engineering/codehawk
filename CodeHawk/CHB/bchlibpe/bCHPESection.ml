(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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
open CHPrettyUtil
open CHTraceResult
open CHUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDataBlock
open BCHDataExportSpec
open BCHDemangler
open BCHDoubleword
open BCHFunctionData
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo
open BCHUtilities

(* bchlibpe *)
open BCHLibPETypes
open BCHPEAssemblyTableLayout
open BCHPEExportDirectory
open BCHPEImportDirectory
open BCHPELoadConfigurationStructure
open BCHPEResourceDirectory
open BCHPEStringTable

module TR = CHTraceResult


module DoublewordCollections = CHCollections.Make
  (struct
    type t = doubleword_int
    let compare dw1 dw2 = dw1#compare dw2
    let toPretty dw = STR dw#to_fixed_length_hex_string
   end)


let fail_traceresult (msg: string) (r: 'a traceresult): 'a =
  if Result.is_ok r then
    TR.tget_ok r
  else
    fail_tvalue
      (trerror_record (LBLOCK [STR "BCHPESection:"; STR msg])) r


let is_printable c = (c >= 32 && c < 127) || c = 10

let is_printable_char c = is_printable (Char.code c)


class pe_section_t
        (header:pe_section_header_int) (exeString:string):pe_section_int =
object (self)

  val mutable header = header
  val mutable exe_string = exeString

  val mutable import_directory_table:import_directory_entry_int list = []

  val export_directory_table:export_directory_table_int =
    make_export_directory_table ()

  val load_configuration_directory = make_load_configuration_directory ()

  val mutable has_import_directory_table = false
  val mutable has_export_directory_table = false
  val mutable has_load_configuration_directory = false
  val mutable has_resource_directory_table = false

  method index = header#index

  method get_name = header#get_name

  method get_exe_string = exe_string

  method get_header = header

  method get_section_VA:doubleword_int =
    system_info#get_image_base#add header#get_RVA

  method get_section_RVA:doubleword_int = header#get_RVA

  method get_virtual_size:doubleword_int = header#get_virtual_size

  (* return true if the given relative virtual address is in the address space
     of this section *)
  method includes_RVA (rva:doubleword_int):bool =
    let sectionRVA = header#get_RVA in
    (sectionRVA#le rva) && (rva#lt (sectionRVA#add header#get_virtual_size))

  (* return true if the given virtual address is in the address space of this
     section *)
  method includes_VA (va:doubleword_int):bool =
    let sectionVA = self#get_section_VA in
    (sectionVA#le va) && (va#lt (sectionVA#add header#get_virtual_size))

  (* return true if the given virtual address is within the address space of
     this section as included in the file image *)
  method includes_VA_in_file_image (va:doubleword_int):bool =
    let sectionVA = self#get_section_VA in
    (sectionVA#le va) && (va#lt (sectionVA#add header#get_size_of_raw_data))

  method raw_data_to_string (l:doubleword_int list) =
    rawdata_to_string exe_string ~markwritten:l self#get_section_VA

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let setx t x = set t x#to_hex_string in
    let bNode = xmlElement "hex-data" in
    begin
      write_xml_raw_data bNode exe_string self#get_section_VA;
      append [bNode];
      setx "va" self#get_section_VA;
      setx "size" header#get_size_of_raw_data;
      set "md5" (byte_string_to_printed_string (Digest.string exe_string))
    end

  method is_read_only = header#is_read_only

  method is_writable = header#is_writable

  method is_executable = header#is_executable

  method has_import_directory_table = has_import_directory_table

  method has_export_directory_table = has_export_directory_table

  method has_load_configuration_directory = has_load_configuration_directory

  method private record_exported_item (faddr:doubleword_int) (name:string) =
    let dname = demangle name in
    if dname = "vftable" || dname = "vbtable" then ()
    else if system_info#is_code_address faddr then
      let _ = chlog#add  "add function:exported item" faddr#toPretty in
      (functions_data#add_function faddr)#add_name name
    else
      system_info#add_exported_item_name faddr name

  method read_export_directory_table
           (address:doubleword_int) (size:doubleword_int) =
    let sectionRVA = header#get_RVA in
    let imageBase = system_info#get_image_base in
    try
      begin
        export_directory_table#set_section_RVA sectionRVA;
        export_directory_table#set_export_directory_RVA address;
        export_directory_table#set_export_size size;
        export_directory_table#read exe_string;
        export_directory_table#read_export_address_table exe_string;
        export_directory_table#read_name_ordinal_table exe_string;
	List.iter (fun (a,s) -> self#record_exported_item a s)
	  export_directory_table#get_exported_function_names;
        has_export_directory_table <- true;
        assembly_table_layout#set_export_directory
          (address#add imageBase)
          (TR.tget_ok (int_to_doubleword 40));
        assembly_table_layout#set_export_address_table
          (export_directory_table#get_export_address_table_RVA#add imageBase)
          export_directory_table#get_export_address_table_size;
        assembly_table_layout#set_export_name_pointer_table
          (export_directory_table#get_name_pointer_table_RVA#add imageBase)
          export_directory_table#get_name_pointer_table_size;
        assembly_table_layout#set_export_ordinal_table
          (export_directory_table#get_ordinal_table_RVA#add imageBase)
          export_directory_table#get_ordinal_table_size;
	let (low,high) =
          export_directory_table#get_export_name_low_high exe_string in
	assembly_table_layout#set_export_name_table
          (low#add imageBase)
          (fail_traceresult
             "pe_section#read_export_directory_table"
             (high#subtract low))
      end
    with
    | BCH_failure p ->
       chlog#add
         "loading executable"
         (LBLOCK [p; STR " in data_section#read_export_directory_table"])
    | Invalid_argument s ->
       ch_error_log#add
         "loading executable"
	 (LBLOCK [STR "data-section#read_export_directory_table: "; STR s])

  method read_import_directory_table (address:doubleword_int) =
    let sectionRVA = header#get_RVA in
    let imageBase = system_info#get_image_base in
    let find_low_high init_low init_high lowhighs =
      List.fold_left
	(fun (alow,ahigh) (low,high) ->
	  let l = if low#lt alow then low else alow in
	  let h = if ahigh#lt high then high else ahigh in
	  (l, h)) (init_low, init_high) lowhighs in
    try
      let offset =
        fail_traceresult
          "pe_section#read_import_directory_table offset"
          (address#subtract_to_int sectionRVA) in
      let ch = make_pushback_stream (string_suffix exe_string offset) in
      begin
	self#read_import_directory_table_aux ch;
	assembly_table_layout#set_import_directory
          (address#add imageBase)
          (fail_traceresult
             ("pe_section#read_import_directory_table "
              ^ "assembly_table_layout#set_import_directory")
             (int_to_doubleword
                (20 * ((List.length import_directory_table) + 1))));

        (* initialize the import directory table entries *)
	List.iter (fun i ->
	  try
	    let ch_name = make_pushback_stream exe_string in
	    let ch_ilt = make_pushback_stream exe_string in
	    let ch_iat = make_pushback_stream exe_string in
	    begin
	      i#read_name ch_name;
	      i#read_table ch_ilt ch_iat;
	      assembly_table_layout#add_import_lookup_table
		(i#get_import_lookup_table_RVA#add imageBase)
		i#get_import_lookup_table_size i#get_name;
	    end
	  with
	  | _ ->
	     ch_error_log#add
               "import directory table"
	       (LBLOCK [
                    STR "Error in reading import directory table entry"; NL]))
          import_directory_table;

	(* try to find summaries for the imported functions *)
	List.iter
	  (fun i ->
	    let libname = i#get_name in
	    let libname = String.lowercase_ascii (replace_dot libname) in
	    let functions = i#get_functions in
	    List.iter (fun f ->
	      function_summary_library#load_dll_library_function libname f)
	      functions)
	  import_directory_table;

	(* also import summaries for functions dynamically loaded with
           LoadLibrary *)
	List.iter
	  (fun (dll,functions) ->
	    let libname = String.lowercase_ascii (replace_dot dll) in
	    List.iter (fun f ->
	      function_summary_library#load_dll_library_function libname f)
	      functions)
	  system_info#get_lib_functions_loaded;

	has_import_directory_table <- true;
	let lowhighs = List.map (fun i ->
	  i#get_hint_name_table_low_high) import_directory_table in
	let lowhighs = List.fold_left (fun a v ->
	  match v with Some w -> w::a | _ -> a) [] lowhighs in
	(match lowhighs with
	 | [] -> assembly_table_layout#set_hint_name_table wordzero wordzero
	 | (lo, hi)::_ ->
	    let (low,high) = find_low_high lo hi lowhighs in
	    let high = high#add_int 2 in
	    let offset =
              fail_traceresult
                "pe_section#read_import_directory_table offset"
                (high#subtract_to_int sectionRVA) in
	    let ch = make_pushback_stream (string_suffix exe_string offset) in
	    let s = ch#read_null_terminated_string in
	    let high = high#add_int ((String.length s) + 1) in
	    assembly_table_layout#set_hint_name_table
              (low#add imageBase)
              (fail_traceresult
                 "pe_section#read_import_directory_table high"
                 (high#subtract low)));

	(let rvas = List.map (fun i -> i#get_name_RVA) import_directory_table in
	 match rvas with
	 | [] -> assembly_table_layout#set_dll_name_table wordzero wordzero
	 | rva::_ ->
	    let (low,high) =
              List.fold_left
	        (fun (alow,ahigh) rva ->
	          let l = if rva#lt alow then rva else alow in
	          let h = if ahigh#lt rva then rva else ahigh in
	          (l,h)) (rva,rva) rvas in
	    let offset =
              fail_traceresult
                "pe_section#read_import_directory_table offset"
                (high#subtract_to_int sectionRVA) in
	    let ch = make_pushback_stream (string_suffix exe_string offset) in
	    let s = ch#read_null_terminated_string in
	    let high = high#add_int ((String.length s) + 1) in
	    assembly_table_layout#set_dll_name_table
	      (low#add imageBase)
              (fail_traceresult
                 "pe_section#read_import_directory_table high"
                 (high#subtract low)));

	List.iter (fun i ->
            i#register_bound_library_functions) import_directory_table
      end
    with
    | BCH_failure p ->
       chlog#add
         "loading executable"
         (LBLOCK [p; STR " in pe_section#read_import_directory_table"])
    | Invalid_argument s ->
       ch_error_log#add
         "loading executable"
	 (LBLOCK [STR "pe_section#read_import_directory_table: "; STR s])

  method private block_out_data
                   (va:doubleword_int) (size:doubleword_int) (name:string) =
    let startAddr = va in
    let endAddr = startAddr#add size in
    log_titer
      (mk_tracelog_spec
         ~tag: "disassembly" "BCHPESection:block_out_data")
      (fun db -> system_info#add_data_block db)
      (make_data_block startAddr endAddr name)

  method read_load_configuration_structure (address:doubleword_int) =
    let imageBase = system_info#get_image_base in
    let sectionRVA = header#get_RVA in
    try
      let va a = a#add imageBase in
      begin
        load_configuration_directory#set_section_RVA sectionRVA;
        load_configuration_directory#set_directory_RVA address;
        load_configuration_directory#read exe_string;
        load_configuration_directory#read_SE_handler_table imageBase exe_string;
        assembly_table_layout#set_load_config_directory
          (va address) (TR.tget_ok (make_doubleword 72 0));
        let se_va = load_configuration_directory#get_SE_handler_table_VA in
        let se_size = load_configuration_directory#get_SE_handler_table_size in
	begin
	  (if wordzero#lt se_va && wordzero#lt se_size then
	      self#block_out_data se_va se_size "SE handler table");
	  List.iter
	    (fun a ->
              (functions_data#add_function a)#add_name "__SEHandler__")
	    (List.map (fun a -> a#add system_info#get_image_base)
	       load_configuration_directory#get_SE_handlers);
          assembly_table_layout#set_SE_handler_table se_va se_size;
          has_load_configuration_directory <- true
	end
      end
    with
      BCH_failure p ->
      chlog#add
        "loading executable"
        (LBLOCK [p; STR " in data_section#readLoadConfigurationStructure"])

  method read_resource_directory_table (address:doubleword_int) =
    let sectionRVA = header#get_RVA in
    try
      begin
	resource_directory_table#set_section_RVA sectionRVA;
	resource_directory_table#set_directory_RVA address;
	resource_directory_table#read exe_string;
	has_resource_directory_table <- true;
      end
    with
      BCH_failure p ->
      chlog#add
        "loading executable"
	(LBLOCK [p; STR " in data_section#read_resource_directorytable"])

  method private read_import_directory_table_aux (ch:pushback_stream_int) =
    let sectionRVA = header#get_RVA in
    let e = make_import_directory_entry sectionRVA in
    begin
      e#read ch;
      if e#get_import_lookup_table_RVA#equal wordzero &&
	e#get_import_address_table_RVA#equal wordzero then
	()
      else
	begin
          import_directory_table <- e::import_directory_table;
          self#read_import_directory_table_aux ch
	end
    end

  method get_import_directory_table = import_directory_table

  method get_export_directory_table = export_directory_table

  method get_load_configuration_directory = load_configuration_directory

  method get_SE_handlers =
    if self#has_load_configuration_directory then
      load_configuration_directory#get_SE_handlers
    else
      []

  method get_imported_function_by_index (index:doubleword_int) =
    if system_info#has_bound_library_function index then
      Some (system_info#get_bound_library_function index)
    else
      List.fold_right
	(fun entry result ->
	  match result with
	  | Some _ -> result
	  | _ ->
	    entry#get_imported_function index) import_directory_table None

  method get_imported_function (address:doubleword_int) =
    (* absolute address *)
    match self#get_initialized_doubleword address with
    | Some dw->
       let _ =
         chlog#add
           "resolve" (LBLOCK [address#toPretty; STR " -> "; dw#toPretty]) in
	begin
	  if system_info#has_bound_library_function dw then
	    Some (system_info#get_bound_library_function dw)
	  else
	    self#get_imported_function_by_index dw
	end
    | _ -> None

  method get_initialized_doubleword (address:doubleword_int) =
    (* absolute address *)
    if self#includes_VA_in_file_image address then
      let offset = TR.tget_ok (address#subtract_to_int self#get_section_VA) in
      let ch = make_pushback_stream (string_suffix exe_string offset) in
      Some ch#read_doubleword
    else
      let _ =
        if self#is_read_only then
	  chlog#add
            "section data"
	    (LBLOCK [
                 STR address#to_hex_string;
                 STR " not found in section: ";
		 STR self#get_section_VA#to_hex_string;
                 STR " with size ";
		 STR header#get_size_of_raw_data#to_hex_string]) in
      None

  method get_data_values (addr:doubleword_int) (spec:data_export_spec_t) =
    if self#includes_VA_in_file_image addr then
      let offset = TR.tget_ok (addr#subtract_to_int self#get_section_VA) in
      let ch = make_pushback_stream (string_suffix exe_string offset) in
      extract_export_spec_values spec ch
    else
      []

  method get_n_doublewords (address:doubleword_int) (n:int) =
    if self#includes_VA_in_file_image address then
      let result = ref [] in
      let offset = TR.tget_ok (address#subtract_to_int self#get_section_VA) in
      let ch = make_pushback_stream (string_suffix exe_string offset) in
      begin
	for _i = 1 to n do
	  result := ch#read_doubleword :: !result
	done;
	List.rev !result
      end
    else
      []

  method get_string_reference (address:doubleword_int) =
    (* absolute address *)
    if self#includes_VA_in_file_image address then
      let offset = TR.tget_ok (address#subtract_to_int self#get_section_VA) in
      if is_printable_char exe_string.[offset] then
	let len =
	  let i = ref 0 in
	  begin
	    while is_printable_char exe_string.[offset + !i] do i := !i + 1 done;
	    !i
	  end in
	if Char.code (exe_string.[offset+len]) = 0 then
	  let str = String.sub exe_string offset len in
	  let new_s = string_replace '\n' "\\n" str in
	  begin
	    string_table#add address new_s;
	    Some new_s
	  end
	else
	  None
      else
	None
    else
      None

  method get_wide_string_reference (address:doubleword_int) =
    if self#includes_VA_in_file_image address then
      let offset = TR.tget_ok (address#subtract_to_int self#get_section_VA) in
      let ch = IO.input_string (string_suffix exe_string offset) in
      let i = ref 0 in
      let c = ref (IO.read_ui16 ch) in
      if is_printable !c then
	let len =
	  while is_printable !c do c := IO.read_ui16 ch; i := !i + 1 done;
	  !i in
	if !c = 0 then
	  let ch = IO.input_string (string_suffix exe_string offset) in
	  let str = Bytes.create len in
	  begin
	    for i=0 to len-1 do
	      (* str.[i] <- Char.chr (IO.read_ui16 ch) *)
              Bytes.set str i (Char.chr (IO.read_ui16 ch))
	    done;
	    let new_s = string_replace '\n' "\\n" (Bytes.to_string str) in
	    begin
	      wide_string_table#add address new_s;
	      Some new_s
	    end
	  end
	else
	  None
      else
	None
    else
      None

  method get_imported_functions =
    List.map (fun t -> (t#get_name, t#get_functions)) import_directory_table

  method get_exported_functions =
    let s = new DoublewordCollections.set_t in
    let _ = List.iter (fun a -> if system_info#is_code_address a then s#add a)
      export_directory_table#get_exported_functions in
    s#toList

  method get_exported_data_values =
    List.filter (fun a -> not (system_info#is_code_address a))
      export_directory_table#get_exported_functions

  method import_directory_entry_to_pretty (name:string) =
    try
      (List.find
         (fun entry -> entry#get_name = name) import_directory_table)#toPretty
    with
      Not_found ->
	begin
	  ch_error_log#add
            "invalid argument"
	    (LBLOCK [STR "No import table found with name "; STR name]);
	  raise (Invalid_argument "import_directory_entry_to_pretty")
	end

  method import_directory_table_to_pretty =
    List.fold_left (fun a e ->
        LBLOCK [a; e#toPretty; NL]) (LBLOCK []) import_directory_table

  method export_directory_table_to_pretty = export_directory_table#toPretty

  method load_configuration_directory_to_pretty =
    load_configuration_directory#toPretty

  method toPretty = STR (self#raw_data_to_string [])

end


let make_pe_section (header:pe_section_header_int) (exeString:string) =
  new pe_section_t header exeString
