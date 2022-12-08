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
open BCHXmlUtil

(* bchlibpe *)
open BCHLibPETypes


module TR = CHTraceResult


let section_index = ref 0

class pe_section_header_t:pe_section_header_int =
object (self)
    
  val index = let i = !section_index in begin section_index := !section_index + 1 ; i end
  val mutable name = ""
  val mutable virtualSize = wordzero
  val mutable virtualAddress = wordzero
  val mutable sizeOfRawData = wordzero
  val mutable pointerToRawData = wordzero
  val mutable pointerToRelocations = wordzero
  val mutable pointerToLineNumbers = wordzero
  val mutable numberOfRelocations = 0
  val mutable numberOfLineNumbers = 0
  val mutable characteristics = wordzero

  method index = index

  method private read_name ch = 
    let rawstring = ch#really_nread 8 in
    let len = 
      let i = ref 0 in
      begin
	while !i < 8 && rawstring.[!i] != (Char.chr 0) do i := !i + 1 done ;
	!i
      end in
    let s = Bytes.create len in
    begin
      for i=0 to (len-1) do
        (* s.[i] <- rawstring.[i] *)
        Bytes.set s i (rawstring.[i])
      done ;                      
      s
    end

  method read ch =
    begin
      (* 0, 8, Name ------------------------------------------------------------
	 An 8-byte, null-padded UTF-8 encoded string. If the string is exactly
	 8 characters long, there is no terminating null.
	 ----------------------------------------------------------------------- *)
      name <- Bytes.to_string (self#read_name ch) ;

      (* 8, 4, VirtualSize -----------------------------------------------------
	 The total size of the section when loaded into memory. If this value is
	 greater than SizeOfRawData, the section is zero-padded. 
	 ----------------------------------------------------------------------- *)
      virtualSize <- ch#read_doubleword;

      (* 12, 4, VirtualAddress ------------------------------------------------- 
	 The address of the first byte of the section relative to the image base
	 when the section is loaded into memory.
	 ----------------------------------------------------------------------- *)
      virtualAddress <- ch#read_doubleword ;

      (* 16, 4, SizeOfRawData --------------------------------------------------
	 The size of the initialized data on disk. This must be a multiple of 
	 FileAlignment from the optional header. If this is less than 
	 VirtualSize, the remainder of the section is zero-filled.  Because the
	 SizeOfRawData field is rounded but the VirtualSize field is not, it is
	 possible for SizeOfRawData to be greater then VirtualSize as well. When
	 a section contains only uninitialized data, this field should be zero
	 ----------------------------------------------------------------------- *)
      sizeOfRawData <- ch#read_doubleword ;

      (* 20, 4, PointerToRawData -----------------------------------------------
	 The file pointer to the first page of the section within the COFF file.
	 This must be a multiple of FileAlignment from the optional header. When
	 a section contains only uninitialized data, this field should be zero.
	 ----------------------------------------------------------------------- *)
      pointerToRawData <- ch#read_doubleword ;

      (* 24, 4, PointerToRelocations -------------------------------------------
	 The file pointer to the beginning of relocation entries for the 
	 section. This is set to zero for executable images.
	 ----------------------------------------------------------------------- *)
      pointerToRelocations <- ch#read_doubleword ;

      (* 28, 4, PointerToLineNumbers -------------------------------------------
	 The file pointer to the beginning of line number entries for the 
	 section. This is set to zero if there are no COFF line numbers. This
	 value should be zero for an image because COFF debugging information is
	 deprecated.
	 ----------------------------------------------------------------------- *)
      pointerToLineNumbers <- ch#read_doubleword ;

      (* 32, 2, NumberOfRelocations --------------------------------------------
	 The number of relocation entries for the section. This is set to zero
	 for executable images.
	 ----------------------------------------------------------------------- *)
      numberOfRelocations <- ch#read_ui16 ;
      
      (* 34, 2, NumberOfLineNumbers --------------------------------------------
	 The number of line-number entries for the section. This value should be
	 zero for an image because COFF debugging information is deprecated.
	 ----------------------------------------------------------------------- *)
      numberOfLineNumbers <- ch#read_ui16 ;

      (* 36, 4, Characteristics ------------------------------------------------
	 The flags that describe the characteristics of the section.
	 ----------------------------------------------------------------------- *)
      characteristics <- ch#read_doubleword ;
  end

  method get_name = name
  method get_virtual_size = virtualSize
  method get_RVA = virtualAddress
  method get_size_of_raw_data = sizeOfRawData
  method get_pointer_to_raw_data = pointerToRawData

  method get_size =
    if sizeOfRawData#lt virtualSize then virtualSize else sizeOfRawData

  method is_read_only =
    (self#is_initialized || self#is_executable)
    && self#is_readable
    && (not self#is_writable)

  method is_writable = characteristics#is_nth_bit_set 31

  method is_initialized = characteristics#is_nth_bit_set 6

  method is_readable = characteristics#is_nth_bit_set 30

  method is_executable = 
    (characteristics#is_nth_bit_set 5) || (characteristics#is_nth_bit_set 29)

  method includes_RVA (rva:doubleword_int):bool =
    (virtualAddress#le rva) && (rva#lt (virtualAddress#add virtualSize))

  method includes_VA (va:doubleword_int):bool =
    TR.tfold_default
      (fun rva -> self#includes_RVA rva)
      false
      (va#subtract system_info#get_image_base)

  method private characteristic_to_string n =
    match n with
    |  5 -> "IMAGE_SCN_CNT_CODE"
    |  6 -> "IMAGE_SCN_CNT_INITIALIZED_DATA"
    |  7 -> "IMAGE_SCN_CNT_UNINITIALIZED_DATA"
    | 12 -> "IMAGE_SCN_LNK_COMDAT"
    | 15 -> "IMAGE_SCN_GPREL"
    | 20 -> "IMAGE_SCN_ALIGNED_1BYTE"
    | 21 -> "IMAGE_SCN_ALIGNED_2BYTE"
    | 22 -> "IMAGE_SCN_ALIGNED_8BYTE"
    | 23 -> "IMAGE_SCN_ALIGNED_128BYTE"
    | 24 -> "IMAGE_SCN_LNK_NRELOC_OVFL"
    | 25 -> "IMAGE_SCN_MEM_DISCARDABLE"
    | 26 -> "IMAGE_SCN_MEM_NOT_CACHED"
    | 27 -> "IMAGE_SCN_MEM_NOT_PAGED"
    | 28 -> "IMAGE_SCN_MEM_SHARED"
    | 29 -> "IMAGE_SCN_MEM_EXECUTE"
    | 30 -> "IMAGE_SCN_MEM_READ"
    | 31 -> "IMAGE_SCN_MEM_WRITE"
    | _ -> "(not used: " ^ (string_of_int n) ^ ")" 

  method private characteristic_to_char n =
    match n with
    |  5 -> "C"
    |  6 -> "I"
    |  7 -> "U"
    | 12 -> "L"
    | 15 -> "G"
    | 25 -> "D"
    | 28 -> "S"
    | 29 -> "X"
    | 30 -> "R"
    | 31 -> "W"
    | _ -> ""

  method get_characteristics_digest =
    String.concat
      ""
      (List.map self#characteristic_to_char characteristics#get_bits_set)

  method private characteristics_to_pretty =
    let descr = self#characteristic_to_string in
    let bitsSet = characteristics#get_bits_set in
    List.fold_left (fun a i -> LBLOCK [a; NL; STR (descr i)]) (STR "") bitsSet

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let sethex t x = if has_control_characters x then set t (hex_string x) else set t x in
    let setx t x = set t x#to_hex_string in
    let cNode = xmlElement "section-charxs" in
    begin
      cNode#appendChildren (List.map (fun i ->
	let ccNode = xmlElement "charx" in
	begin
          ccNode#setAttribute "name" (self#characteristic_to_string i);
          ccNode
        end) characteristics#get_bits_set);
      append [cNode];
      sethex "name" name;
      setx "virtual-size" virtualSize;
      setx "virtual-address" virtualAddress;
      setx "size-of-raw-data" sizeOfRawData;
      setx "pointer-to-raw-data" pointerToRawData;
      setx "pointer-to-relocations" pointerToRelocations;
      seti "number-of-relocations" numberOfRelocations;
      seti "number-of-line-numbers" numberOfLineNumbers;
      setx "characteristics" characteristics ;
    end

  method read_xml (node:xml_element_int) = 
    let get = node#getAttribute in
    let has = node#hasNamedAttribute in
    let geti t = if has t then node#getIntAttribute t else 0 in
    let getx t =
      if has t then
        TR.tget_ok (string_to_doubleword (get t))
      else
        wordzero in
    begin
      name <- get "name";
      virtualSize <- getx "virtual-size";
      virtualAddress <- getx "virtual-address";
      sizeOfRawData <- getx "size-of-raw-data";
      pointerToRawData <- getx "pointer-to-raw-data";
      pointerToRelocations <- getx "pointer-to-relocations";
      numberOfRelocations <- geti "number-of-relocations";
      numberOfLineNumbers <- geti "number-of-line-numbers";
      characteristics <- getx "characteristics"
    end

  method toPretty = 
    let fls s = STR (fixed_length_int_string s 25) in
    let flsx s v = LBLOCK [ fls s ; STR v#to_hex_string ; NL ] in
    let flsi s v = LBLOCK [ fls s ; INT v ; NL ] in
    LBLOCK [
      fls "Name" ; STR name ; NL ;
      flsx "VirtualSize" virtualSize ;
      flsx "VirtualAddress" virtualAddress ;
      flsx "SizeOfRawData" sizeOfRawData ;
      flsx "PointerToRawData" pointerToRawData ;
      flsx "PointerToRelocations" pointerToRelocations ;
      flsx "PointerToLineNumbers" pointerToLineNumbers ;
      flsi "NumberOfRelocations" numberOfRelocations ;
      flsi "NumberOfLineNumbers" numberOfLineNumbers ;
      flsx "Characteristics" characteristics ;
      self#characteristics_to_pretty; NL ;
      if self#is_read_only then STR "READONLY DATA" else STR "" ; NL ;
  ]

end


let make_pe_section_header () = new pe_section_header_t


