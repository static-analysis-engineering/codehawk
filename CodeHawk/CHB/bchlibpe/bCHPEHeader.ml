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
open CHUtils

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHLibTypes
open BCHPreFileIO
open BCHStreamWrapper
open BCHSystemSettings


(* bchlibpe *)
open BCHPESymbolTable
open BCHPEAssemblyTableLayout
open BCHLibPETypes
open BCHPESectionHeader
open BCHPEResourceDirectory
open BCHPESection
open BCHPESections
open BCHSystemInfo

module H = Hashtbl
module TR = CHTraceResult


(*
let attribute_formats = [ ("coff-file-header", [ RightJustifiedColumn ]) ;
			  ("directory-entry", [ RightJustifiedColumn ]) ;
			  ("optional-header", [ RightJustifiedColumn ]) ;
			  ("section", [ RightJustifiedColumn ]) ; ]
let _ = List.iter (fun (e,f) -> set_attribute_format e f) attribute_formats
*)


class pe_coff_file_header_t =
object (self)

  val mutable machine = 0
  val mutable numberOfSections = 0
  val mutable timeDateStamp = wordzero
  val mutable pointerToSymbolTable = wordzero
  val mutable numberOfSymbols = wordzero
  val mutable sizeOfOptionalHeader = 0
  val mutable characteristics = 0

  method reset =
    begin
      machine <- 0 ;
      numberOfSections <- 0 ;
      timeDateStamp <- wordzero ;
      pointerToSymbolTable <- wordzero ;
      numberOfSymbols <- wordzero ;
      sizeOfOptionalHeader <- 0 ;
      characteristics <- 0
    end

  method read (ch:pushback_stream_int) =
    begin
      (* 0, 2, Machine ---------------------------------------------------------
	 The number that identifies the type of target machine.
	 ----------------------------------------------------------------------- *)
      machine <- ch#read_ui16 ;

      (* 2, 2, NumberOfSections ------------------------------------------------
	 The number of sections. This indicates the size of the section table,
	 which immediately follows the headers.
	 ----------------------------------------------------------------------- *)
      numberOfSections <- ch#read_ui16 ;

      (* 4, 4, TimeDateStamp ---------------------------------------------------
	 The low 32 bits of the number of seconds since 00:00 January 1, 1970
	 (a C run-time time_t value), that indicates when the file was created.
	 ----------------------------------------------------------------------- *)
      timeDateStamp <- ch#read_doubleword ;

      (* 8, 4, PointerToSymbolTable --------------------------------------------
	 The file offset of the COFF symbol table, or zero if no COFF symbol 
	 table is present. This value should be zero for an image because COFF
	 debugging information is deprecated.
	 ----------------------------------------------------------------------- *)
      pointerToSymbolTable <- ch#read_doubleword ;
  
      (* 12, 4, NumberOfSymbols ------------------------------------------------
	 The number of entries in the symbol table. This data can be used to
	 locate the string table, which immediately follows the symbol table. 
	 This value should be zero for an image because COFF debugging
	 information is deprecated.
	 ----------------------------------------------------------------------- *)
      numberOfSymbols <- ch#read_doubleword ;

      (* 16, 2, SizeOfOptionalHeader -------------------------------------------
	 The size of the optional header, which is required for executable 
	 files. 
	 ----------------------------------------------------------------------- *)
      sizeOfOptionalHeader <- ch#read_ui16 ;

      (* 18, 2, Characteristics ------------------------------------------------
	 The flags that indicate the attributes of the file.
	 ----------------------------------------------------------------------- *)
      characteristics <- ch#read_ui16 ;

      self#set_characteristics
  end

  method private set_characteristics = ()
    (* let bits = (int_to_doubleword characteristics)#get_bits_set in ()
    if List.mem 13 bits then BCHAssemblyData.characteristics#setDll   TBD *)

  method get_number_of_sections = numberOfSections
  method get_pointer_to_symbol_table = pointerToSymbolTable
  method get_number_of_symbols = numberOfSymbols
  method get_time_date_stamp = timeDateStamp

  method private characteristic_to_string n =
    match n with
      0 -> "IMAGE_FILE_RELOCS_STRIPPED"
    | 1 -> "IMAGE_FILE_EXECUTABLE_IMAGE"
    | 2 -> "IMAGE_FILE_LINENUMS_SKIPPED"
    | 3 -> "IMAGE_FILE_LOCAL_SYMS_SKIPPED"
    | 4 -> "IMAGE_FILE_AGGRESSIVE_WS_TRIM"
    | 5 -> "IMAGE_FILE_LARGE_ADDRESS_AWARE"
    | 6 -> "not used"
    | 7 -> "IMAGE_FILE_BYTES_REVERSED_LO"
    | 8 -> "IMAGE_FILE_32BIT_MACHINE"
    | 9 -> "IMAGE_FILE_DEBUG_STRIPPED"
    | 10 -> "IMAGE_FILE_REMOVABLE_RUN_FROM_SWAP"
    | 11 -> "IMAGE_FILE_NET_RUN_FROM_SWAP"
    | 12 -> "IMAGE_FILE_SYSTEM"
    | 13 -> "IMAGE_FILE_DLL"
    | 14 -> "IMAGE_FILE_UP_SYSTEM_ONLY"
    | 15 -> "IMAGE_FILE_BYTES_REVERSED_HI" 
    | _ -> ("Unexpected pos: " ^ (string_of_int n))

  method private characteristics_to_pretty =
    let descr  = self#characteristic_to_string in
    let c = TR.tget_ok (int_to_doubleword characteristics) in
    let bitsSet = c#get_bits_set in
    List.fold_left
      (fun a i -> LBLOCK [a; NL; STR (descr i)]) (STR "") bitsSet

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    let cNode = xmlElement "file-characteristics" in
    begin
      cNode#appendChildren
        (List.map (fun b ->
	     let ccNode = xmlElement "charx" in
	     begin
               ccNode#setAttribute
                 "name"
                 (self#characteristic_to_string b);
               ccNode
             end)
	   ((TR.tget_ok (int_to_doubleword characteristics))#get_bits_set));
      append [cNode];
      seti "machine" machine;
      seti "number-of-sections" numberOfSections;
      setx "timestamp-dw" timeDateStamp;
      set "time-stamp" timeDateStamp#to_time_date_string;
      setx "pointer-to-symbol-table" pointerToSymbolTable;
      setx "number-of-symbols" numberOfSymbols;
      seti "size" sizeOfOptionalHeader;
      seti "characteristics" characteristics;
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
      machine <- geti "machine";
      numberOfSections <- geti "number-of-sections";
      timeDateStamp <- getx "timestamp-dw";
      pointerToSymbolTable <- getx "pointer-to-symbol-table";
      numberOfSymbols <- getx "number-of-symbols";
      sizeOfOptionalHeader <- geti "size";
      characteristics <- geti "characteristics"
    end

  method toPretty =
    let fls s = STR (fixed_length_int_string s 35) in
    let flsx s v = LBLOCK [ fls s ; STR v#to_hex_string ; NL ] in
    let flsi s i = LBLOCK [ fls s ; INT i ; NL ] in
    LBLOCK [
    flsi "Machine" machine ;
    flsi "Number of sections" numberOfSections ;
    flsx "Pointer to symbol table" pointerToSymbolTable ;
    flsx "Number of symbols" numberOfSymbols ;
    flsi "Size of optional header" sizeOfOptionalHeader ;
    fls "Time/Date" ; STR timeDateStamp#to_time_date_string ; NL ;
    flsi "Characteristics" characteristics ;
    INDENT(3, self#characteristics_to_pretty) ; NL
  ]

end

class pe_optional_header_t =
object (self)

  val mutable magicNumber = 0
  val mutable majorLinkerVersion = 0
  val mutable minorLinkerVersion = 0
  val mutable sizeOfCode = wordzero 
  val mutable sizeOfInitializedData = wordzero
  val mutable sizeOfUninitializedData = wordzero
  val mutable addressOfEntryPoint = wordzero
  val mutable baseOfCode = wordzero
  val mutable baseOfData = wordzero
  val mutable imageBase = wordzero
  val mutable sectionAlignment = wordzero
  val mutable fileAlignment = wordzero
  val mutable majorOperatingSystemVersion = 0
  val mutable minorOperatingSystemVersion = 0
  val mutable majorImageVersion = 0
  val mutable minorImageVersion = 0
  val mutable majorSubsystemVersion = 0
  val mutable minorSubsystemVersion = 0
  val mutable win32VersionValue = wordzero
  val mutable sizeOfImage = wordzero
  val mutable sizeOfHeaders = wordzero
  val mutable checkSum = wordzero
  val mutable subsystem = 0
  val mutable dllCharacteristics = 0
  val mutable sizeOfStackReserve = wordzero
  val mutable sizeOfStackCommit = wordzero
  val mutable sizeOfHeapReserve = wordzero
  val mutable sizeOfHeapCommit = wordzero
  val mutable loaderFlags = wordzero
  val mutable numberOfRvaAndSizes = wordzero

  method reset =
    begin
      magicNumber <- 0 ;
      majorLinkerVersion <- 0 ;
      minorLinkerVersion <- 0 ;
      sizeOfCode <- wordzero ;
      sizeOfInitializedData <- wordzero ;
      sizeOfUninitializedData <- wordzero ;
      addressOfEntryPoint <- wordzero ;
      baseOfCode <- wordzero ;
      baseOfData <- wordzero ;
      imageBase <- wordzero ;
      sectionAlignment <- wordzero ;
      fileAlignment <- wordzero ;
      majorOperatingSystemVersion <- 0 ;
      minorOperatingSystemVersion <- 0 ;
      majorImageVersion <- 0 ;
      minorImageVersion <- 0 ;
      majorSubsystemVersion <- 0 ;
      minorSubsystemVersion <- 0 ;
      win32VersionValue <- wordzero ;
      sizeOfImage <- wordzero ;
      sizeOfHeaders <- wordzero ;
      checkSum <- wordzero ;
      subsystem <- 0 ;
      dllCharacteristics <- 0 ;
      sizeOfStackReserve <- wordzero ;
      sizeOfStackCommit <- wordzero ;
      sizeOfHeapReserve <- wordzero ;
      sizeOfHeapCommit <- wordzero ;
      loaderFlags <- wordzero ;
      numberOfRvaAndSizes <- wordzero
    end

  method read (ch:pushback_stream_int) =
  begin
    (* 0, 2, Magic -------------------------------------------------------------
       The usigned integer that identifies the state of the image file.  The 
       most common number is 0x10b, which identifies it as a normal executable
       file. 0x107 identifies it as a ROM image, and 0x20b identifies it as a
       PE32+ executable.
       ------------------------------------------------------------------------- *)
    magicNumber <- ch#read_ui16 ;

    (* 2, 1, MajorLinkerVersion ------------------------------------------------
       The linker major version number.
       ------------------------------------------------------------------------- *)
    majorLinkerVersion <- ch#read_byte ;

    (* 3, 1, MinorLinkerVersion ------------------------------------------------
       The linker minor version number.
       ------------------------------------------------------------------------- *)
    minorLinkerVersion <- ch#read_byte ;

    (* 4, 4, SizeOfCode -------------------------------------------------------- 
       The size of the code (text) section, or the sum of all code sections if
       there are multiple sections.
       ------------------------------------------------------------------------- *)
    sizeOfCode <- ch#read_doubleword ;

    (* 8, 4, SizeOfInitializedData ---------------------------------------------
       The size of the initialized data section, or the sum of all such sections
       if there are multiple data sections.
       ------------------------------------------------------------------------- *)
    sizeOfInitializedData <- ch#read_doubleword ;

    (* 12, 4, SizeOfUninitializeData -------------------------------------------
       The size of the uninitialized data section (BSS), or the sum of all such
       sections if there are multiple BSS sections.
       ------------------------------------------------------------------------- *)
    sizeOfUninitializedData <- ch#read_doubleword ;

    (* 16, 4, AddressOfEntryPoint ----------------------------------------------
       The address of the entry point relative to the image based when the
       executable file is loaded into memory. For program images, this is the 
       starting address. For device drivers, this is the address of the 
       initialization function. An entry point is optional for DLLs. When no
       entry point is present, this field must be zero.
       ------------------------------------------------------------------------- *)
    addressOfEntryPoint <- ch#read_doubleword ;

    (* 20, 4, BaseOfCode -------------------------------------------------------
       The address that is relative to the image base of the beginning of code
       section when it is loaded into memory.
       ------------------------------------------------------------------------- *)
    baseOfCode <- ch#read_doubleword ;

    (* 24, 4, BaseOfData -------------------------------------------------------
       The address that is relative to the image base of the beginning of the
       data section when it is loaded into memory.
       ------------------------------------------------------------------------- *)
    baseOfData <- ch#read_doubleword ;

    (* 28, 4, ImageBase -------------------------------------------------------- 
       The preferred address of the first byte of image when loaded into memory;
       must be a multiple of 64K. The default for DLLs is 0x10000000. The 
       default for Windows CE EXEs is 0x00010000. The default for Windows NT,
       Windows 2000, Windows XP, Windows 95, Windows 98, and Windows Me is
       0x00400000.
       ------------------------------------------------------------------------- *)
    imageBase <- ch#read_doubleword ;

    (* 32, 4, SectionAlignment -------------------------------------------------
       The alignment (in bytes) of sections when they are loaded into memory. It
       must be greater than or equal to FileAlignment. The default is the page
       size for the architecture.
       ------------------------------------------------------------------------- *)
    sectionAlignment <- ch#read_doubleword ;

    (* 36, 4, FileAlignment ----------------------------------------------------
       The alignment factor (in bytes) that is used to align the raw data of
       sections in the image file. The value should be a power of 2 between 512
       and 64K, inclusive. The default is 512. If the SectionAlignment is less
       than the architecture's page size, then FileAlignment must match
       SectionAlignment.
       ------------------------------------------------------------------------- *)
    fileAlignment <- ch#read_doubleword ;

    (* 40, 2, MajorOperatingSystemVersion --------------------------------------
       The major version number of the required operating system.
       ------------------------------------------------------------------------- *)
    majorOperatingSystemVersion <- ch#read_ui16 ;

    (* 42, 2, MinorOperationgSystemVersion -------------------------------------
       The minor version number of the required operating system.
       ------------------------------------------------------------------------- *)
    minorOperatingSystemVersion <- ch#read_ui16 ;

    (* 44, 2, MajorImageVersion ------------------------------------------------
       The major version number of the image.
       ------------------------------------------------------------------------- *)
    majorImageVersion <- ch#read_ui16 ;

    (* 46, 2, MinorImageVersion ------------------------------------------------
       The minor version number of the image.
       ------------------------------------------------------------------------- *)
    minorImageVersion <- ch#read_ui16 ;

    (* 48, 2, MajorSubsystemVersion --------------------------------------------
       The major version number of the subsystem.
       ------------------------------------------------------------------------- *)
    majorSubsystemVersion <- ch#read_ui16 ;

    (* 50, 2, MinorSubsystemVersion --------------------------------------------
       The minor version number of the subsystem.
       ------------------------------------------------------------------------- *)
    minorSubsystemVersion <- ch#read_ui16 ;

    (* 52, 4, Win32VersionValue ------------------------------------------------
       Reserved, must be zero.
       ------------------------------------------------------------------------- *)
    win32VersionValue <- ch#read_doubleword ;

    (* 56, 4, SizeOfImage ------------------------------------------------------
       The size (in bytes) fo the image, including all headers, as the image is
       loaded in memory. It must be a multiple of SectionAlignment.
       ------------------------------------------------------------------------- *)
    sizeOfImage <- ch#read_doubleword ;

    (* 60, 4, SizeOfHeaders ----------------------------------------------------
       The combined size of an MS-DOS stub, PE header, and section headers
       rounded up to a multiple of FileAlignment.
       ------------------------------------------------------------------------- *)
    sizeOfHeaders <- ch#read_doubleword ;

    (* 64, 4, CheckSum ---------------------------------------------------------
       The image file checksum. The algorithm for computing the checksum is
       incorporated into IMAGHELP.DLL. The following are checked for validation
       at load time: all drivers, any DLL loaded at boot time, and any DLL that
       is loaded into a critical Windows process
       ------------------------------------------------------------------------- *)
    checkSum <- ch#read_doubleword ;

    (* 68, 2, Subsystem --------------------------------------------------------
       The subsystem that is required to run this image.
       ------------------------------------------------------------------------- *)
    subsystem <- ch#read_ui16 ;

    (* 70, 2, DllCharacteristics -----------------------------------------------
       ------------------------------------------------------------------------- *)
    dllCharacteristics <- ch#read_ui16 ;

    (* 72, 4, SizeOfStackReserve -----------------------------------------------
       The size of the stack to reserve. Only SizeOfStackCommit is committed; 
       the rest is made available one page at a time until the reserve size is
       reached.
       ------------------------------------------------------------------------- *)
    sizeOfStackReserve <- ch#read_doubleword ;

    (* 76, 4, SizeOfStackCommit ------------------------------------------------
       The size of the stack commit.
       ------------------------------------------------------------------------- *)
    sizeOfStackCommit <- ch#read_doubleword ;

    (* 80, 4, SizeOfHeapReserve ------------------------------------------------
       The size of the local heap space to reserve. Only SizeOfHeapCommit is
       committed; the rest is made available one page at a time until the 
       reserve size is reached.
       ------------------------------------------------------------------------- *)
    sizeOfHeapReserve <- ch#read_doubleword ;

    (* 84, 4, SizeOfHeapCommit -------------------------------------------------
       The size of the local heap space to commit.
       ------------------------------------------------------------------------- *)
    sizeOfHeapCommit <- ch#read_doubleword ;

    (* 88, 4, LoaderFlags ------------------------------------------------------
       Reserved, must be zero.
       ------------------------------------------------------------------------- *)
    loaderFlags <- ch#read_doubleword ;
  
    (* 92, 4, NumberOfRvaAndSizes ----------------------------------------------
       The number of data-directory entries in the remainder of the optional
       header. Each describes a location and a size.
       ------------------------------------------------------------------------- *)
    numberOfRvaAndSizes <- ch#read_doubleword ;

  end

  method get_image_base = imageBase
  method get_base_of_code = baseOfCode
  method get_address_of_entry_point = addressOfEntryPoint

  method private dll_characteristic_to_string n =
    match n with
      6 -> "IMAGE_DLL_CHARACTERISTICS_DYNAMIC_BASE"
    | 7 -> "IMAGE_DLL_CHARACTERISTICS_FORCE_INTEGRITY"
    | 8 -> "IMAGE_DLL_CHARACTERISTICS_NX_COMPAT"
    | 9 -> "IMAGE_DLL_CHARACTERISTICS_NO_ISOLATION"
    | 10 -> "IMAGE_DLL_CHARACTERISTICS_NO_SEH"
    | 11 -> "IMAGE_DLL_CHARACTERISTICS_NO_BIND"
    | 13 -> "IMAGE_DLL_CHARACTERISTICS_WDM_DRIVER"
    | 15 -> "IMAGE_DLL_CHARACTERISTICS_TERMINAL_SERVER_AWARE" 
    | _ -> ("Unexpected pos: " ^ (string_of_int n))

  method private dll_characteristics_to_pretty =
    let descr = self#dll_characteristic_to_string in
    let c = TR.tget_ok (int_to_doubleword dllCharacteristics) in
    let bitsSet = c#get_bits_set in
    List.fold_left
      (fun a i -> LBLOCK [a; NL; STR (descr i)]) (STR "") bitsSet

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti t i = if i = 0 then () else node#setIntAttribute t i in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    let cNode = xmlElement "dll-charxs" in
    begin
      cNode#appendChildren
        (List.map (fun i ->
	     let ccNode = xmlElement "dll-charx" in
	     begin
               ccNode#setAttribute "name" (self#dll_characteristic_to_string i);
               ccNode
             end)
	   (TR.tget_ok (int_to_doubleword dllCharacteristics))#get_bits_set);
      append [cNode];
      seti "magic-number" magicNumber;
      seti "major-linker-version" majorLinkerVersion;
      seti "minor-linker-version" minorLinkerVersion;
      setx "size-of-code" sizeOfCode;
      setx "size-of-initialized-data" sizeOfInitializedData;
      setx "size-of-uninitialized-data" sizeOfUninitializedData;
      setx "address-of-entry-point" addressOfEntryPoint;
      setx "base-of-code" baseOfCode;
      setx "base-of-data" baseOfData;
      setx "image-base" imageBase;
      setx "section-alignment" sectionAlignment;
      setx "file-alignment" fileAlignment;
      seti "major-os-version" majorOperatingSystemVersion;
      seti "minor-os-version" minorOperatingSystemVersion;
      seti "major-image-version" majorImageVersion;
      seti "minor-image-version" minorImageVersion;
      seti "major-subsystem-version" majorSubsystemVersion;
      seti "minor-subsystem-version" minorSubsystemVersion;
      setx "win32-version-value" win32VersionValue;
      setx "size-of-image" sizeOfImage;
      setx "size-of-headers" sizeOfHeaders;
      setx "checksum" checkSum;
      seti "subsystem" subsystem;
      seti "dll-characteristics" dllCharacteristics;
      setx "size-of-stack-reserve" sizeOfStackReserve;
      setx "size-of-stack-commit" sizeOfStackCommit;
      setx "size-of-heap-reserve" sizeOfHeapReserve;
      setx "size-of-heap-commit" sizeOfHeapCommit;
      setx "loader-flags" loaderFlags;
      setx "number-of-rva-and-sizes" numberOfRvaAndSizes
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
      magicNumber <- geti "magic-number";
      majorLinkerVersion <- geti "major-linker-version";
      minorLinkerVersion <- geti "minor-linker-version";
      sizeOfCode <- getx "size-of-code";
      sizeOfInitializedData <- getx "size-of-initialized-data";
      sizeOfUninitializedData <- getx "size-of-uninitialized-data";
      addressOfEntryPoint <- getx "address-of-entry-point";
      baseOfCode <- getx "base-of-code";
      baseOfData <- getx "base-of-data";
      imageBase <- getx "image-base";
      sectionAlignment <- getx "section-alignment";
      fileAlignment <- getx "file-alignment";
      majorOperatingSystemVersion <- geti "major-os-version";
      minorOperatingSystemVersion <- geti "minor-os-version";
      majorImageVersion <- geti "major-image-version";
      minorImageVersion <- geti "minor-image-version";
      majorSubsystemVersion <- geti "major-subsystem-version";
      minorSubsystemVersion <- geti "minor-subsystem-version";
      win32VersionValue <- getx "win32-version-value";
      sizeOfImage <- getx "size-of-image";
      sizeOfHeaders <- getx "size-of-headers";
      checkSum <- getx "checksum";
      subsystem <- geti "subsystem";
      dllCharacteristics <- geti "dll-characteristics";
      sizeOfStackReserve <- getx "size-of-stack-reserve";
      sizeOfStackCommit <- getx "size-of-stack-commit";
      sizeOfHeapReserve <- getx "size-of-heap-reserve";
      sizeOfHeapCommit <- getx "size-of-heap-commit";
      loaderFlags <- getx "loader-flags";
      numberOfRvaAndSizes <- getx "number-of-rva-and-sizes"
    end

  method toPretty =
    let fls s = STR (fixed_length_int_string s 35) in
    let flsx s v = LBLOCK [fls s; STR v#to_hex_string; NL] in
    let flsi s i = LBLOCK [fls s; INT i; NL] in
    LBLOCK [
    flsi "Magic" magicNumber;
    flsi "Major Linker Version" majorLinkerVersion;
    flsi "Minor Linker Version" minorLinkerVersion;
    flsx "Size of Code" sizeOfCode;
    flsx "Size of Initialized Data" sizeOfInitializedData;
    flsx "Size of Uninitialized Data" sizeOfUninitializedData;
    flsx "Address of Entry Point" addressOfEntryPoint;
    flsx "Base of Code" baseOfCode;
    flsx "Base of Data" baseOfData;
    flsx "Image Base" imageBase;
    flsx "Section Alignment" sectionAlignment;
    flsx "File Alignment" fileAlignment;
    flsi "Major Operating System Version" majorOperatingSystemVersion;
    flsi "Minor Operating System Version" minorOperatingSystemVersion;
    flsi "Major Image Version" majorImageVersion;
    flsi "Minor Image Version" minorImageVersion;
    flsi "Major Subsystem Version" majorSubsystemVersion;
    flsi "Minor Subsystem Version" minorSubsystemVersion;
    flsx "Win32 Version Value" win32VersionValue;
    flsx "Size of Image" sizeOfImage;
    flsx "Size of Headers" sizeOfHeaders;
    flsx "Checksum" checkSum;
    flsi "Subsystem" subsystem;
    LBLOCK [ fls "Dll characteristics"; INT dllCharacteristics ];
    INDENT (3, self#dll_characteristics_to_pretty); NL; NL;
    flsx "Size of Stack Reserve" sizeOfStackReserve;
    flsx "Size of Stack Commit" sizeOfStackCommit;
    flsx "Size of Heap Reserve" sizeOfHeapReserve;
    flsx "Size of Heap Commit" sizeOfHeapCommit;
    flsx "Loader flags" loaderFlags;
    flsx "Number of Rva and Sizes" numberOfRvaAndSizes 
  ]
    
end

class pe_data_directory_t =
object (self)

  val mutable exportTable = (wordzero, wordzero)
  val mutable importTable = (wordzero, wordzero)
  val mutable resourceTable = (wordzero, wordzero)
  val mutable exceptionTable = (wordzero, wordzero)
  val mutable certificateTable = (wordzero, wordzero)
  val mutable baseRelocationTable = (wordzero, wordzero)
  val mutable debugData = (wordzero, wordzero)
  val mutable architecture = (wordzero, wordzero)
  val mutable globalPtr = (wordzero, wordzero)
  val mutable tlsTable = (wordzero, wordzero)
  val mutable loadConfigTable = (wordzero, wordzero)
  val mutable boundImport = (wordzero, wordzero)
  val mutable iat = (wordzero, wordzero)
  val mutable delayImportDescriptor = (wordzero, wordzero)
  val mutable clrRuntimeHeader = (wordzero, wordzero)
  val mutable reserved = (wordzero, wordzero)

  method reset =
    begin
      exportTable <- (wordzero, wordzero);
      importTable <- (wordzero, wordzero);
      resourceTable <- (wordzero, wordzero);
      exceptionTable <- (wordzero, wordzero);
      certificateTable <- (wordzero, wordzero);
      baseRelocationTable <- (wordzero, wordzero);
      debugData <- (wordzero, wordzero);
      architecture <- (wordzero, wordzero);
      globalPtr <- (wordzero, wordzero);
      tlsTable <- (wordzero, wordzero);
      loadConfigTable <- (wordzero, wordzero);
      boundImport <- (wordzero, wordzero);
      iat <- (wordzero, wordzero);
      delayImportDescriptor <- (wordzero, wordzero);
      clrRuntimeHeader <- (wordzero, wordzero);
      reserved <- (wordzero, wordzero)
    end
	

  method private read_entry ch = 
    let addr = ch#read_doubleword in
    let size = ch#read_doubleword in
    (addr, size)

  method read (ch:pushback_stream_int) =
    begin
      (* 96, 8, Export Table ---------------------------------------------------
	 The export table address and size.
	 ----------------------------------------------------------------------- *)
      exportTable <- self#read_entry ch;
      
      (* 104, 8, Import Table --------------------------------------------------
	 The import table address and size.
	 ----------------------------------------------------------------------- *)
      importTable <- self#read_entry ch;

      (* 112, 8, Resource Table ------------------------------------------------
	 The resource table address and size.
	 ----------------------------------------------------------------------- *)
      resourceTable <- self#read_entry ch;

      (* 120, 8, Exception Table -----------------------------------------------
	 The exception table address and size.
	 ----------------------------------------------------------------------- *)
      exceptionTable <- self#read_entry ch;

      (* 128, 8, Certificate Table ---------------------------------------------
	 The attribute certificate table address and size.
	 ----------------------------------------------------------------------- *)
      certificateTable <- self#read_entry ch;

      (* 136. 8, Base Relocation Table -----------------------------------------
	 The base relocation table address and size.
	 ----------------------------------------------------------------------- *)
      baseRelocationTable <- self#read_entry ch;

      (* 144, 8, Debug ---------------------------------------------------------
	 The debug starting address and size.
	 ----------------------------------------------------------------------- *)
      debugData <- self#read_entry ch;
										
      (* 152, 8, Architecture --------------------------------------------------
	 Reserved, must be 0.
	 ----------------------------------------------------------------------- *)
      architecture <- self#read_entry ch;

      (* 160, 8, Global Ptr ----------------------------------------------------
	 The RVA of the value to be stored in the global pointer register. The
	 size member of this structure must be set to zero.
	 ----------------------------------------------------------------------- *)
      globalPtr <- self#read_entry ch;

      (* 168, 8, TLS Table -----------------------------------------------------
	 The thread local storage (TLS) table address and size.
	 ----------------------------------------------------------------------- *)
      tlsTable <- self#read_entry ch;

      (* 176, 8, Load Config Table ---------------------------------------------
	 The load configuration table address and size.
	 ----------------------------------------------------------------------- *)
      loadConfigTable <- self#read_entry ch;

      (* 184, 8, Bound Import -------------------------------------------------- 
	 The bound import table address and size.
	 ----------------------------------------------------------------------- *)
      boundImport <- self#read_entry ch;

      (* 192, 8, IAT -----------------------------------------------------------
	 The import address table address and size.
	 ----------------------------------------------------------------------- *)
      iat <- self#read_entry ch;

      (* 200, 8, Delay Import Descriptor ---------------------------------------
	 The delay import descriptor address and size.
	 ----------------------------------------------------------------------- *)
      delayImportDescriptor <- self#read_entry ch;

      (* 208, 8, CLR Runtime Header --------------------------------------------
	 The CLR runtime header address and size.
	 ----------------------------------------------------------------------- *)
      clrRuntimeHeader <- self#read_entry ch;

      (* 216, 8, Reserved, must be zero ---------------------------------------- *)
      reserved <- self#read_entry ch;

    end

  method get_import_table = importTable
  method get_export_table = exportTable
  method get_IAT = iat
  method get_debug_data = debugData
  method get_load_config_table = loadConfigTable
  method get_resource_table  = resourceTable

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set n = n#setAttribute in
    let setx n t x = set n t x#to_hex_string in
    let sete n (a,s) = begin setx n "va" a; setx n "size" s end in
    let is_zero (a,s) = a#equal wordzero && s#equal wordzero in
    let f i e t = 
      if is_zero e then () else
	let eNode = xmlElement "entry" in 
	begin set eNode "index" i; set eNode "tag" t; sete eNode e; append [ eNode ] end in
    begin
      f "0" exportTable "export-table";
      f "1" importTable "import-table";
      f "2" resourceTable "resource-table";
      f "3" exceptionTable "exception-table";
      f "4" certificateTable "certificate-table";
      f "5" baseRelocationTable "base-relocation-table";
      f "6" debugData "debug-data";
      f "7" architecture "architecture";
      f "8" globalPtr "global-ptr";
      f "9" tlsTable "TLS-table";
      f "a" loadConfigTable "load-config-table";
      f "b" boundImport "bound-import";
      f "c" iat "IAT";
      f "d" delayImportDescriptor "delay-import-descriptor";
      f "e" clrRuntimeHeader "clr-runtime-header";
      f "f" reserved "reserved";
    end   

  method read_xml (node:xml_element_int) =
    let entries = node#getTaggedChildren "entry" in
    let get t = 
      try
	let entry = List.find (fun n -> (n#getAttribute "tag") = t) entries in
	let getx t = TR.tget_ok (string_to_doubleword (entry#getAttribute t)) in
	(getx "va", getx "size")
      with
      | Not_found -> (wordzero, wordzero) in
    begin
      exportTable <- get "export-table";
      importTable <- get "import-table";
      resourceTable <- get "resource-table";
      exceptionTable <- get "exception-table";
      certificateTable <- get "certificate-table";
      baseRelocationTable <- get "base-relocation-table";
      debugData <- get "debug-data";
      architecture <- get "architecture";
      globalPtr <- get "global-ptr";
      tlsTable <- get "TLS-table";
      loadConfigTable <- get "load-config-table";
      boundImport <- get "bound-import";
      iat <- get "IAT";
      delayImportDescriptor <-get "delay-import-descriptor";
      clrRuntimeHeader <- get "clr-runtime-header";
      reserved <- get "reserved"
    end

  method toPretty =
    let f e (a,s) t =
      LBLOCK [
          STR "Entry ";
          STR e;
          STR "  ";
          STR a#to_fixed_length_hex_string;
          STR "  ";
          STR s#to_fixed_length_hex_string;
          STR "  ";
          STR t;
          NL] in
    LBLOCK [
      f "0" exportTable "Export Table";
      f "1" importTable "Import Table";
      f "2" resourceTable "Resource Table";
      f "3" exceptionTable "ExceptionTable";
      f "4" certificateTable "CertificateTable";
      f "5" baseRelocationTable "Base Relocation Table";
      f "6" debugData "Debug Data";
      f "7" architecture "Architecture";
      f "8" globalPtr "Global Ptr";
      f "9" tlsTable "TLS Table";
      f "a" loadConfigTable "Load Config Table";
      f "b" boundImport "Bound Import";
      f "c" iat "IAT";
      f "d" delayImportDescriptor "Delay Import Descriptor";
      f "e" clrRuntimeHeader "CLR Runtime Header";
      f "f" reserved "Reserved, must be zero";
    ]
end

class pe_header_t:pe_header_int =
object (self)

  val coff_file_header = new pe_coff_file_header_t
  val optional_header = new pe_optional_header_t
  val data_directory = new pe_data_directory_t
  val section_headers = H.create 3

  method reset = 
    begin
      coff_file_header#reset;
      optional_header#reset;
      data_directory#reset;
      H.clear section_headers
    end

  method get_number_of_sections = coff_file_header#get_number_of_sections
  method get_time_date_stamp = coff_file_header#get_time_date_stamp

  method get_containing_section_name (va: doubleword_int) =
    let result = ref None in
    let _  = H.iter (fun _ v -> if v#includes_VA va then result := Some v#get_name) section_headers in
    !result

  method get_section_headers = H.fold (fun _ v a -> v::a) section_headers []

  method read  =
    let exeString = system_info#get_file_string wordzero in
    let ch = make_pushback_stream exeString in
    begin
      ch#skip_bytes 0x3c ;   (* file offset to the PE signature is at address 0x3c *)
      let file_offset = ch#read_ui16 in
      let skips = file_offset - ch#pos in
      ch#skip_bytes skips ;
      let _ = ch#read_doubleword in    (* magic *)
      coff_file_header#read ch ;
      optional_header#read ch ;
      system_info#set_image_base optional_header#get_image_base ;
      system_info#set_base_of_code_rva optional_header#get_base_of_code ;
      system_info#set_address_of_entry_point 
	(optional_header#get_address_of_entry_point#add optional_header#get_image_base) ;
      data_directory#read ch ;
      self#set_table_layout ;
      pe_symboltable#set_image_base optional_header#get_image_base ;
      pe_symboltable#set_base_of_code optional_header#get_base_of_code ;
      self#read_section_headers ch ;
      self#read_sections ; 
      self#read_symboltable ;
      let (impAddr, impSize) = data_directory#get_import_table in
      pe_sections#read_import_directory_table impAddr impSize ; 
      let (expAddr, expSize) = data_directory#get_export_table in
        pe_sections#read_export_directory_table expAddr expSize ;
      let (loadCAddr, loadCSize) = data_directory#get_load_config_table in
      pe_sections#read_load_configuration_structure loadCAddr loadCSize ;
      let (resrcAddr, resrcSize) = data_directory#get_resource_table in
      pe_sections#read_resource_directory_table resrcAddr resrcSize ;
      self#set_SE_handlers ;
      system_info#set_code_size self#get_code_size ;      
    end    

  method private read_section_headers ch = 
    for i=0 to self#get_number_of_sections-1 do
       let header = make_pe_section_header () in
       begin
         header#read ch;
         H.add section_headers  header#index header
       end
    done

  method private set_table_layout =
    let (iatRVA, iatsize) = data_directory#get_IAT in
    let (debugRVA, debugsize) = data_directory#get_debug_data in
    let imageBase = optional_header#get_image_base in
    begin
      assembly_table_layout#set_IAT (iatRVA#add imageBase) iatsize ;
      assembly_table_layout#set_debug_data (debugRVA#add imageBase) debugsize 
    end

  method private set_SE_handlers = ()

  method private load_section sectionHeader =
    try
      let fileOffset = sectionHeader#get_pointer_to_raw_data in
      let rawSize = sectionHeader#get_size_of_raw_data in
      let exeString = system_info#get_file_string ~hexSize:rawSize fileOffset in
      pe_sections#add_section sectionHeader exeString
    with
    | BCH_failure p ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "load-section: rawsize: ";
                 sectionHeader#get_size_of_raw_data#toPretty;
                 STR "; offset: ";
                 sectionHeader#get_pointer_to_raw_data#toPretty;
                 STR ": ";
                 p]))

  method private read_sections =
    List.iter (fun h -> 
      if h#get_size_of_raw_data#equal wordzero then () else self#load_section h)
      self#get_section_headers

  method private read_symboltable =
    if coff_file_header#get_number_of_symbols#equal wordzero then 
      ()
    else
      let fileOffset = coff_file_header#get_pointer_to_symbol_table in
      let nSymbols = coff_file_header#get_number_of_symbols in
      try
        let exeString = system_info#get_file_string fileOffset in
        pe_symboltable#read fileOffset nSymbols exeString
      with
      | BCH_failure p ->
         ch_error_log#add
           "read symbol table"
           (LBLOCK [
                STR "read-symboltable: fileOffset: ";
                fileOffset#toPretty;
                STR  ": ";
                p])

  method coff_file_header_to_pretty = coff_file_header#toPretty

  method optional_header_to_pretty = optional_header#toPretty

  method data_directory_to_pretty = data_directory#toPretty

  method section_headers_to_pretty =
    let countSectionHeaders = H.length section_headers in
    H.fold
      (fun k v a ->
        LBLOCK [a; NL; NL; STR v#get_name; NL; INDENT (5, v#toPretty)])
      section_headers (LBLOCK [INT countSectionHeaders; STR " sections: "])
      
  method resource_directory_to_pretty = resource_directory_table#toPretty

  method table_layout_to_pretty = assembly_table_layout#toPretty

  method private write_xml_section_headers (node:xml_element_int) = 
    let append = node#appendChildren in
    let seti = node#setIntAttribute in
    begin
      H.iter (fun k v ->
	let sNode = xmlElement "section-header" in 
	begin
          v#write_xml sNode;
          append [sNode]
        end) section_headers;
      seti "number" (H.length section_headers)
    end

  method private write_xml_export_directory_table (node:xml_element_int) = 
    if pe_sections#has_export_directory_table then
      pe_sections#get_export_directory_table#write_xml node
    else
      ()

  method private write_xml_import_directory_table (node:xml_element_int) = 
    if pe_sections#has_import_directory_table then
      let entries = pe_sections#get_import_directory_table in
      node#appendChildren
        (List.map (fun e ->
	     let eNode = xmlElement "directory-entry" in
             begin
               e#write_xml eNode;
               eNode
             end) entries)
    else
      ()

  method private write_xml_load_configuration_directory (node:xml_element_int) = 
    if pe_sections#has_load_configuration_directory then
      let d = pe_sections#get_load_configuration_directory in
      d#write_xml node
    else
      ()

  method private get_code_size =
    let imageBase = optional_header#get_image_base in
    let entrypointVA = optional_header#get_address_of_entry_point#add imageBase in
    let baseOfCodeRVA = optional_header#get_base_of_code in
    let execHeaders = List.find_all (fun h -> 
      h#is_executable || (h#includes_VA entrypointVA)) self#get_section_headers in
    let sortedHeaders = List.sort (fun h1 h2 -> h2#get_RVA#compare h1#get_RVA) execHeaders in
    let highest = List.hd sortedHeaders in
    let diff = TR.tget_ok (highest#get_RVA#subtract baseOfCodeRVA) in
    diff#add highest#get_size

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let cfhNode = xmlElement "coff-file-header" in
    let ohNode = xmlElement "optional-header" in
    let ddNode = xmlElement "data-directory" in
    let shNode = xmlElement "section-headers" in
    let etNode = xmlElement "export-table" in
    let idNode = xmlElement "import-directory" in
    let lcdNode = xmlElement "load-configuration-directory" in
    let rtNode = xmlElement "resource-directory-table" in
    let tlNode = xmlElement "table-layout" in
    let sNode = xmlElement "symbol-table" in
    begin
      coff_file_header#write_xml cfhNode;
      optional_header#write_xml ohNode;
      data_directory#write_xml ddNode;
      self#write_xml_section_headers shNode;
      self#write_xml_export_directory_table etNode;
      self#write_xml_import_directory_table idNode;
      self#write_xml_load_configuration_directory lcdNode;
      resource_directory_table#write_xml rtNode;
      assembly_table_layout#write_xml tlNode;
      pe_symboltable#write_xml sNode;
      append [
          cfhNode;
          ohNode;
          ddNode;
          shNode;
          etNode;
          idNode;
	  lcdNode;
          rtNode;
          tlNode;
          sNode ];
      node#setAttribute "code-size" self#get_code_size#to_hex_string
    end

  method private read_xml_section_headers (node:xml_element_int) =
    let hNodes = node#getTaggedChildren "section-header" in
    List.iter (fun hNode -> 
      let header = make_pe_section_header () in
      begin
	header#read_xml hNode;
	H.add section_headers header#index header
      end) hNodes

  method private read_xml_sections =
    let headers = self#get_section_headers in
    List.iter (fun h -> 
      if h#get_size_of_raw_data#equal wordzero then 
	pe_sections#add_section h ""
      else 
	let hname =
          h#get_characteristics_digest ^ "_" ^ h#get_RVA#to_hex_string in
	match load_section_file hname with
	  Some node ->
	    let exeString = read_xml_raw_data (node#getTaggedChild "hex-data") in
	    pe_sections#add_section h exeString
	| _ ->
           pr_debug [STR "Section not found: "; STR hname; NL]) headers

  method private read_xml_import_directory_table (node:xml_element_int) = ()

  method read_xml node =
    let getc = node#getTaggedChild in
    begin
      coff_file_header#read_xml (getc "coff-file-header");
      optional_header#read_xml (getc "optional-header");
      data_directory#read_xml (getc "data-directory");
      self#read_xml_section_headers (getc "section-headers");
      system_info#set_image_base optional_header#get_image_base;
      system_info#set_base_of_code_rva optional_header#get_base_of_code;
      system_info#set_address_of_entry_point 
	(optional_header#get_address_of_entry_point#add optional_header#get_image_base);
      system_info#set_code_size
        (TR.tget_ok (string_to_doubleword (node#getAttribute "code-size")));
      self#read_xml_sections;
      let (impAddr, impSize) = data_directory#get_import_table in
      pe_sections#read_import_directory_table impAddr impSize;
      let (expAddr, expSize) = data_directory#get_export_table in
      pe_sections#read_export_directory_table expAddr expSize;
      let (loadCAddr, loadCSize) = data_directory#get_load_config_table in
      pe_sections#read_load_configuration_structure loadCAddr loadCSize;
      let (resrcAddr, resrcSize) = data_directory#get_resource_table in
      pe_sections#read_resource_directory_table resrcAddr resrcSize;
      pe_symboltable#set_image_base optional_header#get_image_base;
      pe_symboltable#set_base_of_code optional_header#get_base_of_code;
      pe_symboltable#read_xml (getc "symbol-table")
    end

  method toPretty = 
    LBLOCK [
        STR "COFF File Header"; NL; coff_file_header#toPretty; NL;
        STR "Optional Header"; NL; optional_header#toPretty; NL;
        STR "Data Directory"; NL; data_directory#toPretty; NL;
        STR "Section Headers"; NL; self#section_headers_to_pretty; NL; NL;
        STR "Export Table"; NL; NL;
        pe_sections#export_directory_table_to_pretty; NL; NL; NL;
        STR "Import Tables"; NL; NL;
        pe_sections#import_directory_table_to_pretty; NL; NL;
        STR "Load Configuration Directory"; NL; NL;
        pe_sections#load_configuration_directory_to_pretty; NL; NL;
        STR "Resource Table"; NL; NL; resource_directory_table#toPretty; NL; NL;
        STR "Table Layout "; NL; INDENT (5, assembly_table_layout#toPretty ); NL; NL;
      ]
end


let pe_header = new pe_header_t

let save_pe_header () =
  let filename = get_pe_header_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "pe-header" in
  let hNode = xmlElement "pe-header" in
  begin
    doc#setNode root;
    pe_header#write_xml hNode;
    root#appendChildren [ hNode ];
    file_output#saveFile filename doc#toPretty
  end

let save_pe_section (s:pe_section_int) =
  let header = s#get_header in
  let sname = header#get_characteristics_digest ^ "_" ^ header#get_RVA#to_hex_string in
  let _ =
    pr_debug [
        STR "Saving section ";
        STR sname;
	STR " (size: ";
        INT (String.length s#get_exe_string);
        STR ")";
        NL] in
  let filename = get_section_filename sname in
  let doc = xmlDocument () in
  let root = get_bch_root "raw-section" in
  let sNode = xmlElement "raw-section" in
  begin
    s#write_xml sNode ;
    doc#setNode root ;
    root#appendChildren [ sNode ] ;
    let p = doc#toPretty in
    file_output#saveFile filename p
  end


let save_pe_files () =
  begin
    save_pe_header () ;
    List.iter save_pe_section pe_sections#get_sections
  end


let load_pe_files () =
  match load_pe_header_file () with
  | Some node -> pe_header#read_xml node
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "Unable to load pe file for ";
	       STR system_info#get_filename;
               STR ". Make sure xml representation of the executable ";
               STR "has been created."]))


let read_pe_file (filename:string) (optmaxsize:int option) =
  let maxStringSize = 100000000 in
  let ch = open_in_bin filename in
  let ch = IO.input_channel ch in
  let exeString = IO.nread ch maxStringSize in
  let filesize = Bytes.length exeString in
  let default () = 
    let hexsize = TR.tget_ok (int_to_doubleword filesize) in
    begin
      system_info#set_file_string (Bytes.to_string exeString);
      pe_header#read;
      (true,
       LBLOCK [
           STR "File: ";
           STR filename;
           NL;
	   STR "Size: ";
           INT filesize;
           STR " (";
           hexsize#toPretty;
	   STR ") bytes" ; NL])
    end in
  match optmaxsize with
  | Some maxsize ->
    if filesize > maxsize then
      (false,
       LBLOCK [
           STR "Filesize of ";
           STR filename;
           STR " is ";
           INT filesize;
	   STR ", which exceeds upper file size limit of ";
	   INT maxsize;
           NL])
    else
      default ()
  | _ -> default ()


let read_hexlified_pe_file (filename:string) =
  let ch = open_in filename in
  let outch = IO.output_string () in
  let _ = try
      while true do
        let line = input_line ch in
        for i = 0 to 39 do
          let s = "0x" ^ (String.sub line (i*2) 2) in
          try
            let b = int_of_string s in IO.write_byte outch b
          with
            Failure _ ->
            begin
              pr_debug [STR "Failure in read_hex_file: "; STR s; NL];
              raise (Failure "read_hex:int_of_string")
            end
        done
      done
    with _ -> () in
  let exeString = IO.close_out outch in
  let filesize =  String.length exeString in
  let hexsize = TR.tget_ok (int_to_doubleword filesize) in
  begin
    system_info#set_file_string exeString;
    pe_header#read;
    (true,
     LBLOCK [
         STR "File: ";
         STR filename;
         NL;
         STR "Size: ";
         INT filesize;
         STR " (";
         hexsize#toPretty;
         STR ") bytes";
         NL])
  end
       

let dump_pe_file filename =
  let maxStringSize = 100000000 in
  let ch = open_in_bin filename in
  let ch = IO.input_channel ch in
  let exeString = IO.nread ch maxStringSize in
  let filesize = Bytes.length exeString in
  if filesize > 1000000 then
    pr_debug [
        STR "Refuse to dump file of ";
        INT filesize;
        STR " bytes. ";
	STR "Maximum size of dumping is 1,000,000 bytes";
        NL]
  else
    let node = xmlElement "executable-dump" in
    begin
      write_xml_raw_data node (Bytes.to_string exeString) wordzero;
      node#setIntAttribute "size" filesize;
      save_executable_dump node
    end
