(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHPrettyUtil
open CHLogger
open CHUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibpe *)
open BCHLibPETypes

type export_address_table_entry_t =
    ExportRVA of doubleword_int
  | ForwarderRVA of doubleword_int * string

type export_name_ordinal_table_entry_t =
    { nameRVA:doubleword_int ; ordinal: int ; exportName: string }

class export_directory_table_t:export_directory_table_int =
object (self)

  val mutable sectionRVA         = wordzero
  val mutable exportDirectoryRVA = wordzero
  val mutable exportSize         = wordzero

  val mutable exportFlags           = wordzero 
  val mutable timeDateStamp         = wordzero 
  val mutable majorVersion          = 0
  val mutable minorVersion          = 0
  val mutable nameRVA               = wordzero
  val mutable ordinalBase           = wordzero
  val mutable addressTableEntries   = wordzero
  val mutable numberOfNamePointers  = wordzero
  val mutable exportAddressTableRVA = wordzero
  val mutable namePointerRVA        = wordzero
  val mutable ordinalTableRVA       = wordzero

  val mutable export_address_table:export_address_table_entry_t array = 
    Array.make 1 (ExportRVA wordzero)
  val mutable export_name_ordinal_table:export_name_ordinal_table_entry_t array =
    Array.make 1 {nameRVA = wordzero ; ordinal = 0 ; exportName = "" }

  method get_export_address_table_RVA= exportAddressTableRVA

  method get_export_address_table_size =
    fail_tvalue
      (trerror_record (STR "export_directory_table#get_export_address_table_size"))
      (addressTableEntries#multiply_int 4)

  method get_name_pointer_table_RVA = namePointerRVA

  method get_name_pointer_table_size =
    fail_tvalue
      (trerror_record (STR "export_directory_table#get_name_pointer_table_size"))
      (numberOfNamePointers#multiply_int 4)

  method get_ordinal_table_RVA = ordinalTableRVA

  method get_ordinal_table_size =
    fail_tvalue
      (trerror_record (STR "export_directory_table#get_ordinal_table_size"))
      (numberOfNamePointers#multiply_int 2)

  method get_export_name_low_high (byte_string:string) =
    let lst = Array.to_list export_name_ordinal_table in
    let rvas = List.map (fun e -> e.nameRVA) lst in
    let (low,high) = match rvas with
      [] -> (wordzero, wordzero)
    | rva::_ ->
	List.fold_left
	  (fun (alow,ahigh) rva ->
	    let lo = if rva#lt alow then rva else alow in
	    let hi = if ahigh#lt rva then rva else ahigh in
	    (lo,hi)) (rva,rva) rvas in
    let troffset = high#subtract_to_int sectionRVA in
    fail_tfold
      (trerror_record (STR "BCHPEExportDirector.get_export_name_low_high"))
      (fun offset ->
        let ch = make_pushback_stream (string_suffix byte_string offset) in
        let s = ch#read_null_terminated_string  in
        let high = high#add_int ((String.length s) + 1) in
        (low, high))
      troffset
    
  method set_section_RVA (address:doubleword_int)          = sectionRVA <- address
  method set_export_directory_RVA (address:doubleword_int) = exportDirectoryRVA <- address
  method set_export_size (size:doubleword_int)             = exportSize <- size

  method read (byte_string:string) =
    if exportDirectoryRVA#equal wordzero then
      ()
    else
      let offset =
        fail_tvalue
          (trerror_record (STR "BCHPEExportDirectory.read"))
          (exportDirectoryRVA#subtract_to_int sectionRVA) in
      let ch = make_pushback_stream (string_suffix byte_string offset) in
      begin
        (* 0, 4, Export flags -----------------------------------------------
	   Reserved, must be 0
	   ------------------------------------------------------------------ *)
        exportFlags <- ch#read_doubleword;

        (* 4, 4, Time/Date Stamp --------------------------------------------
	   The time and date that the export was created.
	   ------------------------------------------------------------------ *)
        timeDateStamp <- ch#read_doubleword;

        (* 8, 2, Major version ----------------------------------------------
	   The major version number.
	   ------------------------------------------------------------------ *)
        majorVersion <- ch#read_ui16;

        (* 10, 2, Minor version ---------------------------------------------
	   The minor version number
	   ------------------------------------------------------------------ *)
        minorVersion <- ch#read_ui16;

        (* 12, 4, Name RVA --------------------------------------------------
	   The address of the ascii string that contains the name of the DLL.
           This address is relative to the image base.
	   ------------------------------------------------------------------ *)
        nameRVA <- ch#read_doubleword;

        (* 16, 4, Ordinal base ----------------------------------------------
	   The starting ordinal number for exports in this image. This field
	   specifies the starting ordinal number for the export address table.
           It  is usually set to 1.
	   ------------------------------------------------------------------ *)
        ordinalBase <- ch#read_doubleword ;

        (* 20, 4, Address Table Entries -------------------------------------
	   The number of entries in the export address table.
	   ------------------------------------------------------------------ *)
        addressTableEntries <- ch#read_doubleword ;

        (* 24, 4, Number of Name Pointers -----------------------------------
	   The number of entries in the name pointer table. This is also the
	   number of entries in the ordinal table.
	   ------------------------------------------------------------------ *)
        numberOfNamePointers <- ch#read_doubleword ;

        (* 28, 4, Export Address Table RVA ----------------------------------
	   The address of the export address table, relative to the image base.
	   ------------------------------------------------------------------ *)
        exportAddressTableRVA <- ch#read_doubleword ;

        (* 32, 4, Name Pointer RVA ------------------------------------------
	   The address of the export name pointer table, relative to the image
	   base. The table size is given by the Number of Name Pointers field.
	   ------------------------------------------------------------------ *)
        namePointerRVA <- ch#read_doubleword ;

        (* 36, 4, Ordinal Table RVA -----------------------------------------
	   The address of the ordinal table, relative to the image base.
	   ------------------------------------------------------------------ *)
        ordinalTableRVA <- ch#read_doubleword ;
      end

  method get_name_RVA = nameRVA

  method read_export_address_table (byte_string:string) =
    if exportAddressTableRVA#equal wordzero then
      ()
    else
      try
        let endRVA = exportDirectoryRVA#add exportSize in
        let inExportSection a = exportDirectoryRVA#le a && a#le endRVA in
        let offset =
          fail_tvalue
            (trerror_record (STR "BCHPEExportDirectory.read_export_address_table"))
            (exportAddressTableRVA#subtract_to_int sectionRVA) in
        let ch = make_pushback_stream (string_suffix byte_string offset) in
        let entries  = addressTableEntries#to_int in
        begin
	  export_address_table <- Array.make entries (ExportRVA wordzero) ;
	  for i = 0 to entries - 1 do
            let entry = ch#read_doubleword in
            if inExportSection entry then
              let name_offset =
                fail_tvalue
                  (trerror_record
                     (STR "BCHPEExportDirectory.read_export_address_table"))
                  (entry#subtract_to_int sectionRVA) in
              let name_ch = make_pushback_stream (string_suffix byte_string name_offset) in
              let name = name_ch#read_null_terminated_string in
              export_address_table.(i) <- ForwarderRVA (entry, name)
            else
              export_address_table.(i) <- ExportRVA entry
	  done
        end
      with
      | IO.No_more_input ->
         ch_error_log#add
           "invalid input"
	   (LBLOCK [STR "No more input in read_export_address_table"])
      | Invalid_input e ->
         ch_error_log#add
           "invalid input"
	   (LBLOCK [
                STR "export_directory_table_t#read_export_address_table: ";
                STR e])
      | Invalid_argument e ->
         ch_error_log#add
           "invalid argument"
	   (LBLOCK [
                STR "export_directory_table_t#read_export_address_table: ";
                STR e])

  method read_name_ordinal_table (byte_string:string) =
    if namePointerRVA#equal wordzero then
      ()
    else
      try
        let nametable_offset =
          fail_tvalue
            (trerror_record
               (STR "BCHPEExportDirectory.read_name_ordinal_table"))
            (namePointerRVA#subtract_to_int sectionRVA) in
        let ordinaltable_offset =
          fail_tvalue
            (trerror_record
               (STR "BCHPEExportDirectory.read_name_ordinal_table"))
            (ordinalTableRVA#subtract_to_int sectionRVA) in
        let nametable_ch =
          make_pushback_stream (string_suffix byte_string nametable_offset) in
        let ordinaltable_ch =
          make_pushback_stream (string_suffix byte_string ordinaltable_offset) in
        let entries = numberOfNamePointers#to_int in
        begin
	  export_name_ordinal_table <-
	    Array.make entries {nameRVA = wordzero; ordinal = 0; exportName = ""};
	  for i = 0 to entries - 1 do
            let nameRVA = nametable_ch#read_doubleword in
            let ordinal = ordinaltable_ch#read_ui16 in
            let name_offset =
              fail_tvalue
                (trerror_record
                   (STR "BCHPEExportDirectory.read_name_ordinal_table"))
                (nameRVA#subtract_to_int sectionRVA) in
            let name_ch =
              make_pushback_stream (string_suffix byte_string name_offset) in
            let exportName = name_ch#read_null_terminated_string  in
            export_name_ordinal_table.(i) <-
	      {nameRVA = nameRVA; ordinal = ordinal; exportName = exportName}
	  done
        end
      with
	IO.No_more_input ->
	 ch_error_log#add
           "invalid input"
	   (LBLOCK [STR "No more input in read_name_ordinal_table"])
      | Invalid_argument e ->
	 ch_error_log#add
           "invalid argument"
	   (LBLOCK [
                STR "export_directory_table_t#read_name_ordinal_table: ";
                STR e])

  method get_exported_function_names =
    let imageBase = system_info#get_image_base in
    let exportNameOrdinals = Array.to_list export_name_ordinal_table in
    array_fold_lefti (fun acc i v ->
      match v with 
      | ExportRVA rva when rva#equal wordzero -> acc
      | ExportRVA rva ->
	  let functionAddress = rva#add imageBase in
	  let ordinal = i in
	  begin
	    try
	      let entry = List.find (fun e -> e.ordinal = ordinal) exportNameOrdinals in
	      (functionAddress, entry.exportName) :: acc
	    with
	      Not_found ->
		(functionAddress, "_ordinal_" ^ 
		  (string_of_int (i + ordinalBase#to_int))) :: acc
	  end
      | _ -> acc) [] export_address_table

  method get_exported_functions =
    let imageBase = system_info#get_image_base in
    Array.fold_left (fun acc v -> 
      match v with 
      | ExportRVA address when address#equal wordzero -> acc
      | ExportRVA address ->
	(address#add imageBase) :: acc | _ -> acc) [] export_address_table 

  method private export_name_ordinal_table_to_pretty =
    array_fold_lefti
      (fun a i v ->
         let vp v = LBLOCK [ STR v.nameRVA#to_fixed_length_hex_string ; STR "    " ;
                             fixed_length_pretty (INT v.ordinal) 8 ; STR "    " ;
                             STR v.exportName ] in
           LBLOCK [ a ; NL ; vp v ]) 
           (LBLOCK [ STR "name RVA   " ; STR "ordinal " ; STR "   name" ]) 
      export_name_ordinal_table

  method private export_address_table_to_pretty =
    let base = ordinalBase#to_int in
    array_fold_lefti
      (fun a i v ->
         let vp v = match v with 
           | ExportRVA a -> STR a#to_hex_string
           | ForwarderRVA (a, name) -> 
	     LBLOCK [ STR name ; STR " (" ; STR a#to_hex_string ; STR ")" ] in
         LBLOCK [ a ; NL ; fixed_length_pretty (INT (i + base)) 8 ; vp v ]) (STR "") 
      export_address_table 
      
  method private write_xml_export_name_ordinal_table (node:xml_element_int) =
    let append = node#appendChildren in
    Array.iteri 
      (fun i v ->
	let nNode = xmlElement "name-ordinal" in
	let set = nNode#setAttribute in
	let seti = nNode#setIntAttribute in
	begin 
	  append [ nNode ] ;
	  set "name-rva" v.nameRVA#to_hex_string ; 
	  seti "ordinal" v.ordinal ; 
	  seti "index" i ;
	end) export_name_ordinal_table
	  

  method private write_xml_export_address_table (node:xml_element_int) =
    let append = node#appendChildren in
    let base = ordinalBase#to_int in
    Array.iteri
      (fun i v ->
	match v with
	| ExportRVA a -> 
	  let aNode = xmlElement "export-rva" in 
	  begin 
	    aNode#setIntAttribute "entry" (i+base) ;
	    aNode#setAttribute "rva" a#to_hex_string ; 
	    append [ aNode ] 
	  end
	| ForwarderRVA (a,name) ->
	  chlog#add "leave out forwarder rva" a#toPretty
	  (* let fNode = xmlElement "forwarder-rva" in
	  begin 
	    fNode#setIntAttribute "entry" (i + base) ;
	    fNode#setAttribute "name" name ; 
	    fNode#setAttribute "rva" a#to_hex_string ;
	    append [ fNode ]
	  end *) ) export_address_table

  method write_xml_ordinal_table (node:xml_element_int) =
    let append = node#appendChildren in
    let ordinalLst = Array.to_list export_name_ordinal_table in
    let ordinalLst = List.sort (fun e1 e2 -> Stdlib.compare e1.ordinal e2.ordinal)
      ordinalLst in
    begin
      append (List.map (fun e ->
	let eNode = xmlElement "entry" in
	begin 
	  eNode#setIntAttribute "ordinal" (e.ordinal + ordinalBase#to_int) ;
	  eNode#setAttribute "name" e.exportName ;
	  eNode
	end) ordinalLst) ;
      node#setIntAttribute "size" (List.length ordinalLst)
    end

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti t i = if i = 0 then () else node#setIntAttribute t i in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    let aNode = xmlElement "export-address-table" in
    let nNode = xmlElement "export-name-ordinal-table" in
    begin
      self#write_xml_export_address_table aNode ;
      self#write_xml_export_name_ordinal_table nNode ;
      append [ aNode ; nNode ] ;
      setx "export-flags" exportFlags ;
      setx "time-stamp-dw" timeDateStamp ;
      set "time-stamp" timeDateStamp#to_time_date_string ;
      seti "major-version" majorVersion ;
      seti "minor-version" minorVersion ;
      setx "name-rva" nameRVA ;
      setx "ordinal-base" ordinalBase ;
      setx "address-table-entries" addressTableEntries ;
      setx "number-of-name-pointers" numberOfNamePointers ;
      setx "export-address-table-rva" exportAddressTableRVA ;
      setx "name-pointer-rva" namePointerRVA ;
      setx "ordinal-table-rva" ordinalTableRVA ;
    end

  method toPretty =
    LBLOCK [
      STR "Export flags           " ; STR exportFlags#to_hex_string ; NL ;
      STR "Time/date stamp        " ; STR timeDateStamp#to_time_date_string ; NL ;
      STR "Major/minor version    " ; INT majorVersion ; STR "/" ; INT minorVersion ; NL ;
      STR "Name                   " ; STR nameRVA#to_hex_string  ; NL ;
      STR "Ordinal base           " ; INT ordinalBase#to_int ; NL ;
      STR "Address table entries  " ; INT addressTableEntries#to_int ; NL ;
      STR "Name pointers          " ; INT numberOfNamePointers#to_int ; NL ;
      STR "Export address table   " ; STR exportAddressTableRVA#to_hex_string ; NL ;
      STR "Name pointer rva       " ; STR namePointerRVA#to_hex_string ; NL ;
      STR "Ordinal table rva      " ; STR ordinalTableRVA#to_hex_string ; NL ; NL ;
      STR "Export address table   " ; NL ; 
      INDENT (5, self#export_address_table_to_pretty) ; NL ; NL ;
      STR "Export Name/Ordinal Table" ; NL ;
      INDENT (5, self#export_name_ordinal_table_to_pretty) ; NL ; NL ]

end

let make_export_directory_table () = new export_directory_table_t
