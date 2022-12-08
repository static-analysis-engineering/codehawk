(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo
open BCHUserProvidedDirections
open BCHUtilities

(* bchlibpe *)
open BCHLibPETypes


module TR = CHTraceResult


class type hint_name_table_entry_int =
object
  (* actions *)
  method read: pushback_stream_int -> unit
  method read_bound_address: pushback_stream_int -> unit

  (* setters *)
  method set_hint: int -> string -> unit

  (* accessors *)
  method get_bound_address: doubleword_int
  method get_name: string

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t
end


class hint_name_table_entry_t rva:hint_name_table_entry_int =
object (self)

  val rva = rva
  val mutable hint = 0
  val mutable name = ""
  val mutable bound_address = wordzero

  method read (ch:pushback_stream_int) =
    begin
      (* 0, 2, Hint ------------------------------------------------------------
	 An index into the export name pointer table. A match is attempted first
	 with this value. If it fails, a binary search is performed on the DLL's
	 export name pointer table.
	 ----------------------------------------------------------------------- *)
      hint <- ch#read_ui16 ;

      (* 2, ?, Name ------------------------------------------------------------
	 An ASCII string that contains the name to import. This is the string 
	 that must be matched to the public name in the DLL. This string is case
	 sensitive and terminated by a null byte.
	 ----------------------------------------------------------------------- *)
      name <- ch#read_null_terminated_string ;
    end

  method read_bound_address (ch:pushback_stream_int) =
    bound_address <- ch#read_doubleword

  method get_bound_address = bound_address

  method set_hint i fname = begin hint <- i ; name <- fname end

  method get_name = name

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti t i = if i = 0 then () else node#setIntAttribute t i in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    let entryname =
      if has_control_characters name then
        "__xx__"  ^ (hex_string name)
      else
        name in
    begin
      setx "rva" rva;
      seti "hint" hint;
      set "name" entryname;
      setx "bound-address" bound_address
    end

  method toPretty =
    LBLOCK [
        STR rva#to_fixed_length_hex_string;
        STR "  ";
        STR (Printf.sprintf "%4d" hint);
        STR "   ";
	fixed_length_pretty (STR name) 30;
        STR "  ";
	(if bound_address#equal wordzero then
           STR ""
         else
	   STR bound_address#to_hex_string)]

end


module DoublewordCollections = CHCollections.Make
  (struct
    type t = doubleword_int
    let compare dw1 dw2 = dw1#compare dw2
    let toPretty dw = STR dw#to_fixed_length_hex_string
   end)


class import_directory_entry_t baseAddress:import_directory_entry_int =
object (self)

  val mutable sectionRVA = wordzero
  val mutable importDirectoryRVA = wordzero

  val baseAddress = baseAddress
  val mutable importLookupTableRVA = wordzero
  val mutable timeDateStamp = wordzero
  val mutable forwarderChain = wordzero
  val mutable nameRVA = wordzero
  val mutable name = ""
  val mutable importAddressTableRVA = wordzero

  val mutable importLookupTable = new DoublewordCollections.table_t

  (* ================================================================ Accessors *)

  method get_name    = name
  method get_name_RVA = nameRVA

  method get_import_lookup_table_RVA = importLookupTableRVA

  method get_import_address_table_RVA = importAddressTableRVA

  method get_import_lookup_table_size = 
    try
      TR.tget_ok (int_to_doubleword ((importLookupTable#size + 1) * 4))
    with
	Invalid_argument _ ->
	  begin
	    ch_error_log#add
              "invalid argument"
	      (STR "import_directory_entry_t#get_import_lookup_table_size") ;
	    raise
              (Invalid_argument
                 "import_directory_entry_t#get_import_lookup_table_size")
	  end

  method get_functions = 
    importLookupTable#fold (fun a _ v -> (v#get_name)::a) []

  method get_hint_name_table_low_high =
    let rvas = importLookupTable#listOfKeys in
    let rvas = List.filter (fun rva -> not rva#is_highest_bit_set) rvas in
    match rvas with
      [] -> None
    | a::_ -> 
	let (low, high) =
	  List.fold_left 
	    (fun (alow, ahigh) rva ->
	      if rva#is_highest_bit_set then
		(alow, ahigh)
	      else
		let low = if rva#lt alow then rva else alow in
		let high = if ahigh#lt rva then rva else ahigh in
		(low, high)) (a,a) rvas in
	Some (low,high)

  method get_imported_function (address:doubleword_int) =
    match importLookupTable#get address with
      Some entry -> 
	Some (self#get_name,entry#get_name)
    | _ -> 
	None

  (* =============================================================== Predicates *)

  (* Import Lookup Table (ILT) vs Import Address Table (IAT)

     According to the Microsoft PE documentation the ILT and IAT on file should
     contain the same information. This is not always the case however. In most
     cases the ILT has either the ordinal number of the library function or the
     index of the name of the library function. In some cases this information
     is not in the ILT, but is in the IAT (corpus example: msvcp60.dll) 

     The current implementation attempts to resolve a library function reference
     first with the ILT, and if that fails, with the IAT.
  *)

  method has_bound_addresses = true (* timeDateStamp#equal wordmax *)

  (* ================================================================== Setters *)

  method set_section_RVA (address:doubleword_int) = sectionRVA <- address

  method set_import_directory_RVA (address:doubleword_int) = 
    importDirectoryRVA <- address

  method register_bound_library_functions =
    let add_value i = 
      system_info#add_bound_library_function 
	i#get_bound_address (self#get_name,i#get_name) in
    List.iter add_value importLookupTable#listOfValues


  (* ================================================================== Readers *)

  method read ch =
    try
      begin
      (* 0, 4, Import Lookup Table RVA -----------------------------------------
	 The RVA of the import lookup table. This table contains a name or
	 ordinal for each import.
	 ----------------------------------------------------------------------- *)
	importLookupTableRVA <- ch#read_doubleword ;
	
      (* 4, 4, Time/Date Stamp -------------------------------------------------
	 The stamp that is set to zero until the image is bound. After the image
	 is bound, this field is set to the time/date stamp of the DLL.
	 ----------------------------------------------------------------------- *)
	timeDateStamp <- ch#read_doubleword ;
	
      (* 8, 4, Forwarder Chain -------------------------------------------------
	 The index of the first forwarder reference.
	 ----------------------------------------------------------------------- *)
	forwarderChain <- ch#read_doubleword ;
	
      (* 12, 4, Name RVA -------------------------------------------------------
	 The address of an ASCII string that contains the name of the DLL. This
	 address is relative to the image base.
	 ----------------------------------------------------------------------- *)
	nameRVA <- ch#read_doubleword ;
	
      (* 16, 4, Import Address Table RVA (Thunk Table) -------------------------
	 The RVA of the import address table. The contents of this table are
	 identical to the contents of the import lookup table until the image is
	 bound.
	 ----------------------------------------------------------------------- *)
	importAddressTableRVA <- ch#read_doubleword ;
      end
    with
	IO.No_more_input ->
	  begin
	    ch_error_log#add "no more input" (STR "import_directory_entry_t#read") ;
	    raise IO.No_more_input
	  end

  method read_name ch =
    try
      let skips = TR.tget_ok (nameRVA#subtract_to_int baseAddress) in
      begin
	ch#skip_bytes skips ;
	name <- ch#read_null_terminated_string;
      end
    with
    | IO.No_more_input ->
      begin
	ch_error_log#add "no more input" (STR "import_directory_entry_t#read_name");
	raise IO.No_more_input
      end
    | Invalid_input _ ->
      begin
	ch_error_log#add "invalid input" (STR "import_directory_entry_t#read_name");
	raise (Invalid_input "import_directory_entry_t#read_name")
      end
    | Invalid_argument s ->
      begin
	ch_error_log#add "invalid argument" (STR "import_directory_entry_t#read_name");
	raise (Invalid_argument ("import_directory_entry_t#read_name " ^ s))
      end
	
  method read_table ch_ilt ch_iat =
    try
      let skips_ilt = 
	if importLookupTableRVA#equal wordzero then
	  TR.tget_ok (importAddressTableRVA#subtract_to_int baseAddress)
	else
	  TR.tget_ok (importLookupTableRVA#subtract_to_int baseAddress) in
      let skips_iat =
        TR.tget_ok (importAddressTableRVA#subtract_to_int baseAddress) in
      let _ = ch_ilt#skip_bytes skips_ilt in
      let _ = ch_iat#skip_bytes skips_iat in
      let ch_iat = if self#has_bound_addresses then Some ch_iat else None in 
      begin
	self#read_table_entry ch_ilt ch_iat ;
	user_provided_directions#load_dll_ordinal_mappings self#get_name;
	List.iter 
          (fun (a,e) -> 
	    if a#is_highest_bit_set then
	      begin
		let hint = a#get_low in
		let name = user_provided_directions#get_dll_ordinal_mapping 
		  self#get_name hint in
		let _ =
                  if name = "" then
		    chlog#add
                      "dll ordinal"
                      (LBLOCK [
                           STR "No name found for ";
                           INT hint;
			   STR " in dll ";
                           STR self#get_name]) in
		e#set_hint hint name
	      end
	    else
	      let rva = TR.tget_ok (a#subtract_to_int baseAddress) in
	      let skips = rva - ch_ilt#pos in
	      if skips >= 0 then
		begin
		  ch_ilt#skip_bytes skips;
		  e#read ch_ilt;
		end
	      else if skips = (-1) then
		(* this case happens if the null-terminating byte of the
                   previous function name is reused as the first byte of
                   the hint word *)
		begin
		  ch_ilt#pushback 1;
		  e#read ch_ilt
		end
	      else
		pr_debug [
                    STR "Skip entry for ";
                    a#toPretty;
                    STR "; skips = ";
                    INT skips;
                    NL]
	  ) (List.sort (fun (a1, _) (a2, _) ->
                 a1#compare a2) importLookupTable#listOfPairs);
      end
    with
    | IO.No_more_input->
      begin
	ch_error_log#add "no more input" 
	  (LBLOCK [STR "import_directory_entry_t#read_table"]) ;
	raise IO.No_more_input
      end
    | Invalid_argument _ ->
      begin
	ch_error_log#add "invalid argument" 
	  (LBLOCK [ STR "import_directory_entry_t#read_table"])  ;
	raise (Invalid_argument "import_directory_entry_t#read_table")
      end
    | Invalid_input _ ->
      begin
	ch_error_log#add "invalid input" (STR "import_directory_entry_t#read_table") ;
	raise (Invalid_input "import_directory_entry_t#read_table")
      end
	
	
  method private read_table_entry 
    (ch_ilt:pushback_stream_int) 
    (ch_iat:pushback_stream_int option) =
    let rva = ch_ilt#read_doubleword in
    if rva#equal wordzero then
      ()
    else
      let hint_name_table_entry = new hint_name_table_entry_t rva in
      begin
        importLookupTable#set rva hint_name_table_entry ;
	(match ch_iat with 
	  Some ch -> hint_name_table_entry#read_bound_address ch
	| _ -> ()) ;
        self#read_table_entry ch_ilt ch_iat
      end

  method private write_xml_hint_name_table (node:xml_element_int) =
    let append = node#appendChildren in
    importLookupTable#iter (fun _ e ->
      let eNode = xmlElement "hint-name-entry" in e#write_xml eNode ; append [ eNode ])

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let setx t x = set t x#to_hex_string in
    let hNode = xmlElement "hint-name-table" in
    let dllname = if has_control_characters name then "__xx__" ^ (hex_string name) else name in
    begin
      self#write_xml_hint_name_table hNode ;
      append [ hNode ] ;
      set "dll-name" dllname ;
      setx "import-lookup-table-rva" importLookupTableRVA ;
      setx "timestamp-dw" timeDateStamp ;
      setx "forwarder-chain" forwarderChain ;
      setx "name-rva" nameRVA ;
      setx "import-address-table-rva" importAddressTableRVA 
    end
	
  (* ========================================================== Pretty printing *)
	
  method toPretty =
    let fls s = STR (fixed_length_int_string s 35) in
    let flsx s v = LBLOCK [ fls s ; STR v#to_fixed_length_hex_string ; NL ] in
    LBLOCK [
      STR "DLL Name: " ; STR name ; NL ;
      flsx "Import Lookup Table RVA" importLookupTableRVA ;
      flsx "Time/Date Stamp" timeDateStamp ;
      flsx "Forwarder Chain" forwarderChain ;
      flsx "Name RVA" nameRVA ;
      flsx "Import Address Table RVA" importAddressTableRVA ; NL ;
      STR "Hint/Name Table" ; NL ;
      importLookupTable#toPretty ; NL ;
    ]
      
end
  
let make_import_directory_entry (sectionRVA:doubleword_int) = 
  new import_directory_entry_t sectionRVA
    
