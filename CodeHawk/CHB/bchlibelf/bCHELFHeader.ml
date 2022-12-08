(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
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

(* 
   References used:

   The standard /usr/include/elf.h in Arch Linux
   The latest draft of the System V Application Binary Interface: 
   http://www.sco.com/developers/gabi/latest/contents.html
   March 19, 1997 draft copy of the Intel Supplement to the System V 
   Application Binary Interface
*) 

(* chlib *)
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHFileIO
open CHLogger   
open CHXmlDocument

(* bchcil *)
open BCHBCFiles
open BCHBCUtil

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHCallbackTables
open BCHDoubleword
open BCHLibTypes
open BCHPreFileIO
open BCHSectionHeadersInfo
open BCHStreamWrapper
open BCHStructTables
open BCHSystemInfo
open BCHVariableType

(* bchlibelf *)
open BCHELFTypes
open BCHELFDictionary
open BCHELFDynamicSegment
open BCHELFDynamicTable
open BCHELFUtil
open BCHELFProgramHeader
open BCHELFProgramSection
open BCHELFRelocationTable
open BCHELFSection
open BCHELFSegment
open BCHELFSectionHeader
open BCHELFSectionHeaderCreator
open BCHELFStringTable
open BCHELFSymbolTable
open BCHELFPrettyStrings

module H = Hashtbl
module TR = CHTraceResult


type object_file_type = 
  | NoFileType 
  | RelocatableFile 
  | ExecutableFile 
  | SharedObjectFile 
  | CoreFile 
  | OSSpecificFile of int 
  | ProcessorSpecificFile of int

type elf_symbol_type = 
  | NoSymbolType
  | ObjectSymbol 
  | FunctionSymbol 
  | SectionSymbol 
  | FileSymbol
  | UnknownSymbol of int

(* Based on the Intel-specific part of the ABI *)
type elf_relocation_type_i386 = 
  | R_386_NONE 
  | R_386_32 
  | R_386_PC32 
  | R_386_GOT32 
  | R_386_PLT32 
  | R_386_COPY 
  | R_386_GLOB_DAT
  | R_386_JMP_SLOT 
  | R_386_RELATIVE 
  | R_386_GOTOFF 
  | R_386_GOTPC


let make_elf_section (sh:elf_section_header_int) (s:string) =
  let t = sh#get_section_type in
  let vaddr = sh#get_addr in
  match t with
  | SHT_StrTab -> ElfStringTable (mk_elf_string_table s vaddr)
  | SHT_SymTab -> ElfSymbolTable (mk_elf_symbol_table s sh vaddr)
  | SHT_DynSym -> ElfDynamicSymbolTable (mk_elf_symbol_table s sh vaddr)
  | SHT_Rel -> ElfRelocationTable (mk_elf_relocation_table s sh vaddr)
  (* | SHT_Rela | SHT_Rel -> ElfSymbolTable (new elf_relocation_table_t s vaddr) *)
  | SHT_Dynamic -> ElfDynamicTable (mk_elf_dynamic_table s sh vaddr)
  | SHT_ProgBits -> ElfProgramSection (mk_elf_program_section s sh vaddr)
  | _ -> ElfOtherSection (new elf_raw_section_t s vaddr)


let read_xml_elf_section (sh:elf_section_header_int) (node:xml_element_int) =
  let t = sh#get_section_type in
  match t with
  | SHT_StrTab -> ElfStringTable (read_xml_elf_string_table node)
  | SHT_SymTab -> ElfSymbolTable (read_xml_elf_symbol_table node)
  | SHT_DynSym -> ElfDynamicSymbolTable (read_xml_elf_symbol_table node)
  | SHT_Rel -> ElfRelocationTable (read_xml_elf_relocation_table node)
  | SHT_Dynamic -> ElfDynamicTable (read_xml_elf_dynamic_table node)
  | SHT_ProgBits  -> ElfProgramSection (read_xml_elf_program_section node)
  | _ -> ElfOtherSection (read_xml_elf_raw_section node)


let read_xml_elf_segment (ph:elf_program_header_int) (node:xml_element_int) =
  let t =  ph#get_program_header_type in
  match t with
  | PT_Dynamic -> ElfDynamicSegment (read_xml_elf_dynamic_segment node)
  | _ -> ElfOtherSegment (read_xml_elf_raw_segment node)


let make_elf_segment (ph:elf_program_header_int) (s:string) =
  let t = ph#get_program_header_type in
  let vaddr = ph#get_vaddr in
  match t with
  | PT_Dynamic -> ElfDynamicSegment (mk_elf_dynamic_segment s ph vaddr)
  | _ -> ElfOtherSegment (new elf_raw_segment_t s vaddr)

    
class elf_file_header_t:elf_file_header_int =
object

  val mutable e_type = 0
  val mutable e_machine = 0
  val mutable e_version = wordzero
  val mutable e_entry = wordzero
  val mutable e_phoff = wordzero
  val mutable e_shoff = wordzero
  val mutable e_flags = wordzero
  val mutable e_ehsize = 0
  val mutable e_phentsize = 0
  val mutable e_phnum = 0
  val mutable e_shentsize = 0
  val mutable e_shnum = 0
  val mutable e_shstrndx = 0


  method read =
    let input = system_info#get_file_input (TR.tget_ok (int_to_doubleword 16)) in
    begin
      (* 16, 2  --------------------------------------------------------------
	 Specifies the object file type.
	 ET_NONE     0    No file type
	 ET_REL      1    Relocatable file
	 ET_EXEC     2    Executable file
	 ET_DYN      3    Shared object file
	 ET_CORE     4    Core file
	 --------------------------------------------------------------------- *)
      e_type <- input#read_ui16 ;

      (* 18, 2  --------------------------------------------------------------
	 Specifies the required architecture for an individual file. 
	 EM_NONE     0    No machine
	 EM_M32      1    AT&T WE 32100
	 EM_SPARC    2    SUN SPARC
	 EM_386      3    Intel 80386
         EM_MIPS     8    MIPS
         EM_ARM     40    ARM
	 EM_X86_64  62    AMD x86-64
         EM_AVR     83    AVR
	 --------------------------------------------------------------------- *)
      e_machine <- input#read_ui16;
  
      (* 20, 4  --------------------------------------------------------------
	 Identifies the object file version. 
	 EV_NONE     0    Invalid
	 EV_CURRENT  1    Current version
	 EV_NUM      2
	 --------------------------------------------------------------------- *)
      e_version <- input#read_doubleword;

      (* 24, 4  --------------------------------------------------------------
	 Virtual address to which the system first transfers control, thus
	 starting the process. If the file has no associated entry point, this
	 value is zero
	 --------------------------------------------------------------------- *)
      e_entry <- input#read_doubleword;
  
      (* 28, 4  --------------------------------------------------------------
	 Program header table's file offset in bytes. 
	 If the file has no program header table, this member holds zero. 
         --------------------------------------------------------------------- *)
      e_phoff <- input#read_doubleword;
  
      (* 32, 4  --------------------------------------------------------------
	 Section header table's file offset in bytes. 
	 If the file has no section header table, this member holds zero. 
         --------------------------------------------------------------------- *)
      e_shoff <- input#read_doubleword;
  
      (* 36, 4  --------------------------------------------------------------
	 Processor-specific flags associated with the file. 
         --------------------------------------------------------------------- *)
      e_flags <- input#read_doubleword;
  
      (* 40, 2  --------------------------------------------------------------
	 ELF header's size in bytes 
         --------------------------------------------------------------------- *)
      e_ehsize <- input#read_ui16;
  
      (* 42, 2  --------------------------------------------------------------
	 Size in bytes of one entry in the file's program header table; all 
	 entries are the same size. 
         --------------------------------------------------------------------- *)
      e_phentsize <- input#read_ui16;
  
      (* 44, 2 --------------------------------------------------------------
	 Number of entries in the program header table.
	 Thus the product of phentsize and phnum gives the table's size 
	 in bytes. If a file has no program header table, phnum holds the 
	 value zero. 
         --------------------------------------------------------------------- *)
      e_phnum <- input#read_ui16;
  
     (* 46, 2  ---------------------------------------------------------------
	Section header's table entry size in bytes. A section header is 
	one entry in the section header table; all entries are the same size. 
        ---------------------------------------------------------------------- *)
      e_shentsize <- input#read_ui16;
  
     (* 48, 2  ---------------------------------------------------------------
	Number of entries in the section header table. Thus the product of 
	e_shentsize and e_shnum gives the section header table's size in bytes. 
	If a file has no section header table, e_shnum holds the value zero. 
     
	If the number of sections is greater than or equal to SHN_LORESERVE(0xff00),
	this member has the value zero and the actual number of section header table 
	entries is contained in the size field of the section header at index 0.
	(Otherwise, the size member of the initial entry contains a zero). 
        ---------------------------------------------------------------------- *)
      e_shnum <- input#read_ui16;
  
      (* 50, 2  --------------------------------------------------------------
	 Section header table index of the entry associated with the section name 
	 string table. If the file has no section name string table, this member 
	 holds the value SHN_UNDEF.
     
	 If the section name string table section index is greater than or
	 equal to SHN_LORESERVE(0xff00), this member has the value 
	 SHN_XINDEX(0xffff) and the actual index of the section name string 
	 table is contained in the link field of the section header at index 0. 
	 (Otherwise, the link member of the initial entry contains 0). 
         --------------------------------------------------------------------- *)
      e_shstrndx <- input#read_ui16
    end

  method get_type = e_type
    
  method get_machine = e_machine
    
  method get_version = e_version
    
  method get_program_entry_point = e_entry
    
  method get_program_header_table_offset = e_phoff
    
  method get_section_header_table_offset = e_shoff
    
  method get_flags = e_flags
    
  method get_header_size = e_ehsize
    
  method get_program_header_table_entry_size = e_phentsize
    
  method get_program_header_table_entry_num = e_phnum
    
  method get_section_header_table_entry_size = e_shentsize
    
  method get_section_header_table_entry_num = e_shnum
    
  method get_section_header_string_table_index = e_shstrndx

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    begin
      seti "e_type" e_type ;
      seti "e_machine" e_machine ;
      setx "e_version" e_version ;
      setx "e_entry" e_entry ;
      setx "e_phoff" e_phoff ;
      setx "e_shoff" e_shoff ;
      setx "e_flags" e_flags ;
      seti "e_ehsize" e_ehsize ;
      seti "e_phentsize" e_phentsize ;
      seti "e_phnum" e_phnum ;
      seti "e_shentsize" e_shentsize ;
      seti "e_shnum" e_shnum ;
      seti "e_shstrndx" e_shstrndx
    end

  method read_xml (node:xml_element_int) =
    let get = node#getAttribute in
    let geti = node#getIntAttribute in
    let has = node#hasNamedAttribute in
    let getx t =
      if has t then
        TR.tget_ok (string_to_doubleword (get t))
      else
        wordzero in
    begin
      e_type <- geti "e_type" ;
      e_machine <- geti "e_machine" ;
      e_version <- getx "e_version" ;
      e_entry <- getx "e_entry" ;
      e_phoff <- getx "e_phoff" ;
      e_shoff <- getx "e_shoff" ;
      e_flags <- getx "e_flags" ;
      e_ehsize <- geti "e_ehsize" ;
      e_phentsize <- geti "e_phentsize" ;
      e_phnum <- geti "e_phnum" ;
      e_shentsize <- geti "e_shentsize" ;
      e_shnum <- geti "e_shnum" ;
      e_shstrndx <- geti "e_shstrndx";

      if e_entry#equal wordzero then
        ()
      else
        system_info#set_address_of_entry_point e_entry
    end

  method toPretty =
    LBLOCK [
      STR "ELF file type: "; STR (file_type_string e_type); NL;
      STR "Machine      : "; STR (machine_to_string e_machine); NL;
      STR "Version      : "; STR e_version#to_hex_string; NL;
      STR "Entry point  : "; STR e_entry#to_hex_string; NL;
      STR "Program Header Table offset: "; STR e_phoff#to_hex_string; NL;
      STR "Section Header Table offset: "; STR e_shoff#to_hex_string; NL;
      STR "Flags          : "; STR e_flags#to_hex_string; NL;
      STR "ELF header size: "; INT e_ehsize; NL;
      STR "Program Header Table Entry size   : "; INT e_phentsize; NL;
      STR "Program Header Table Entry number : "; INT e_phnum; NL;
      STR "Section Header Table Entry size   : "; INT e_shentsize; NL;
      STR "Section Header Table Entry number : "; INT e_shnum; NL;
      STR "Section Header String Table index : "; INT e_shstrndx; NL;
    ]
end


class elf_header_t:elf_header_int =
object(self)

  val mutable e_ident = ""
  val elf_file_header = new elf_file_header_t
  val program_header_table = H.create 3
  val section_header_table = H.create 3
  val section_table = H.create 3
  val segment_table = H.create 3

  method get_program_entry_point = elf_file_header#get_program_entry_point

  method read =
    let fileString = system_info#get_file_string wordzero in
    let input = IO.input_string fileString in
    begin
      e_ident <- Bytes.to_string (IO.really_nread input 16);
      self#check_elf;
      self#set_endianness;
      elf_file_header#read;

      pr_debug [STR "File header"; NL; elf_file_header#toPretty; NL];

      (if elf_file_header#get_type = 1 then
         pr_debug [STR "File is an object file, not an executable!"; NL]);

      self#read_program_headers;
      H.iter (fun k v -> pr_debug [v#toPretty; NL]) program_header_table;

      (if elf_file_header#get_section_header_table_entry_num = 0 then
         self#create_section_headers
       else
         begin
           self#read_section_headers;

           (* check if the user defined some additional section headers *)
           (if section_header_infos#has_section_header_infos then
              self#add_user_defined_section_headers)
         end);

      pr_debug [
        STR "Number of sections: "; INT (H.length section_header_table); NL];

      self#set_section_header_names;
      self#set_symbol_names;
      self#set_dynamic_symbol_names;
      self#set_relocation_symbols;
    end

  method has_sections = (H.length section_header_table) > 0

  method private create_section_headers =
    let segments = self#get_program_segments in
    let sectionheaders = create_section_headers segments elf_file_header in
    List.iter
      (fun (index, sh) -> H.add section_header_table index sh)
      sectionheaders

  method get_sections =
    let result = ref [] in
    let _ = H.iter (fun k v -> result := (k,v) :: !result) section_header_table in
    let compare = fun (i1,_) (i2,_) -> Stdlib.compare i1 i2 in
    let result = List.sort compare !result in
    List.map (fun (index, sh) -> 
        (index, sh, self#get_section index)) result

  method get_program_segments =
    let result = ref [] in
    let _ = H.iter (fun k v -> result := (k,v) :: !result) program_header_table in
    let compare = fun (i1,_) (i2,_) -> Stdlib.compare i1 i2 in
    let result = List.sort compare !result in
    List.map (fun (index,ph)  ->
        (index, ph, self#get_segment index)) result

  method get_relocation (dw:doubleword_int) =
    let relocationsections =
      List.filter (fun (index,sh,_) -> sh#is_relocation_table) self#get_sections in
    List.fold_left (fun result (_,_,s) ->
        match result with
        | Some _ -> result
        | _ ->
           match s with
           | ElfRelocationTable t ->
              if t#has_offset dw then
                Some (t#get_offset_symbol dw)
              else
                None
           | _ ->
              raise
                (BCH_failure
                   (STR "Internal error in get_relocation")))
      None relocationsections

  method set_code_extent =
    let lb = ref wordmax in
    let ub = ref wordzero in
    let xsections = self#get_executable_sections in
    begin
      List.iter (fun (h,_) ->
          let lba = h#get_addr in
          let uba = lba#add h#get_size in
          begin
            (if lba#lt !lb then lb := lba) ;
            (if !ub#lt uba then ub := uba)
          end) xsections ;
      system_info#set_elf_is_code_address !lb !ub
    end

  method initialize_jump_tables =
    let xstrings =
      List.fold_left (fun result (_,header,section) ->
          if header#is_executable || header#get_section_name = ".rodata" then
            match section with
            | ElfOtherSection t -> (t#get_vaddr,t#get_xstring) :: result
            | _ -> result
          else
            result) [] self#get_sections in
    system_info#initialize_jumptables system_info#is_code_address xstrings

  method private extract_call_back_table
                   (callbacktable: call_back_table_int)
                   (va: doubleword_int)
                   (extractor: string list) =
    let nullrecord = ref false in
    let currva = ref va in
    while not !nullrecord do
      let cbvalues = ref [] in
      begin
        List.iteri (fun i s ->
            let pv = self#get_program_value (!currva#add_int (4 * i)) in
            let cbv =
              if pv#equal wordzero then
                CBValue numerical_zero
              else
                match s with
                | "address" -> CBAddress pv#to_hex_string
                | "string" ->
                   (match self#get_string_at_address pv with
                    | Some s -> CBTag s
                    | _ -> CBTag "**unknown**")
                | "value" -> CBValue (mkNumerical pv#to_int)
                | _ -> CBValue numerical_zero in
            cbvalues := ((i * 4), cbv) :: !cbvalues) extractor;
        (if List.for_all (fun (_, v) ->
                match v with
                | CBValue n -> n#equal numerical_zero
                | _ -> false) !cbvalues then
           nullrecord := true
         else
           begin
             callbacktable#add_record !currva#to_hex_string !cbvalues;
             currva := !currva#add_int ((List.length extractor) * 4)
           end)
      end
    done

  method private extract_struct_table
                   (structtable: struct_table_int)
                   (va: doubleword_int)
                   (recordsize: int)
                   (extractor: (int * string) list) =
    let nullrecord = ref false in
    let currva = ref va in
    while not !nullrecord do
      let stvalues = ref [] in
      begin
        List.iter (fun (offset, s) ->
            let pv = self#get_program_value (!currva#add_int offset) in
            let stv =
              if pv#equal wordzero then
                STVNum numerical_zero
              else
                match s with
                | "string-address" ->
                   (match self#get_string_at_address pv with
                    | Some s ->
                       STVStringAddress s
                    | _ -> STVStringAddress "**unknown**")
                | "string" ->
                   let stringaddr = !currva#add_int offset in
                   (match self#get_string_at_address stringaddr with
                    | Some s ->
                       STVString s
                    | _ -> STVString "**unknown**")
                | "value" -> STVNum (mkNumerical pv#to_int)
                | _ -> STVNum numerical_zero in
            stvalues := (offset, stv) :: !stvalues) extractor;
        (if List.for_all (fun (_, v) ->
                match v with
                | STVNum n -> n#equal numerical_zero
                | _ -> false) !stvalues then
           nullrecord := true
         else
           begin
             structtable#add_record !currva#to_hex_string !stvalues;
             currva := !currva#add_int recordsize
           end)
      end
    done

  method initialize_call_back_tables =
    let tvars = callbacktables#table_variables in
    begin
      List.iter (fun (addr, vname) ->
          if bcfiles#has_varinfo vname then
            let varinfo = bcfiles#get_varinfo vname in
            let extractor = get_struct_extractor varinfo.bvtype in
            let callbacktable = callbacktables#new_table addr varinfo.bvtype in
            let va = TR.tget_ok (string_to_doubleword addr) in
            self#extract_call_back_table callbacktable va extractor
          else
            chlog#add
              "call-back-table-variable"
              (LBLOCK [
                   STR "Variable "; STR vname; STR " not found"])) tvars;
      callbacktables#set_function_pointers
    end

  method initialize_struct_tables =
    let svars = structtables#table_variables in
    begin
      List.iter (fun (addr, (vname, size)) ->
          if bcfiles#has_varinfo vname then
            let varinfo = bcfiles#get_varinfo vname in
            let extractor = get_struct_offset_extractor varinfo.bvtype in
            let structtable = structtables#new_table addr varinfo.bvtype in
            let va = TR.tget_ok (string_to_doubleword addr) in
            self#extract_struct_table structtable va size extractor
          else
            chlog#add
              "struct-table-variable"
              (LBLOCK [
                   STR "Variable "; STR vname; STR " not found"])) svars
    end
          
  method get_executable_sections =
    let result = ref [] in
    let _ = H.iter (fun k v -> if v#is_executable then result := (k,v) :: !result)
      section_header_table in
    List.map (fun (index,sh) -> 
        (sh, (elf_section_to_raw_section (self#get_section index))#get_xstring))
      !result

  method get_executable_segments =
    let result = ref []  in
    let _ =
      H.iter
        (fun k v ->
          if v#is_executable && v#is_loaded then
            result := (k,v) :: !result)
        program_header_table in
    List.map (fun (index,ph) ->
        (ph, (elf_segment_to_raw_segment (self#get_segment index))#get_xstring))
      !result

  method private has_string_table =
    H.fold (fun _ v r ->
        r || v#get_section_name = ".strtab") section_header_table false

  method private has_symbol_table =
    H.fold (fun _ v r ->
        r || v#get_section_name = ".symtab") section_header_table false

  method private has_dynamic_symbol_table =
    H.fold (fun _ v r ->
        r || v#get_section_name = ".dynsym") section_header_table false

  method get_string_at_address (a:doubleword_int) =
    try
      H.fold (fun k v result ->
          match result with
          | Some _ -> result
          | _ ->
             if v#get_section_name = ".bss" then
               None
             else
               match self#get_section k with
               | ElfOtherSection t when not (v#get_addr#equal wordzero) ->
                  t#get_string_reference a
               | ElfStringTable t when not (v#get_addr#equal wordzero)->
                  t#get_string_reference a
               | ElfProgramSection s when not (v#get_addr#equal wordzero) ->
                  s#get_string_reference a
               | _ -> None) section_header_table None
    with
    | _ ->
       begin
         ch_error_log#add
           "get_string_at_address"
           (LBLOCK [a#toPretty]);
         None
       end

  method has_xsubstring (a:doubleword_int) (size:int) =
    match self#get_containing_section a with
    | Some s ->
       let diff = a#subtract_to_int s#get_vaddr in
       if Result.is_ok diff then
         (TR.tget_ok diff) + size < s#get_size
       else
         raise
           (BCH_failure
              (LBLOCK [
                   STR "ELFHeader:has_xsubstring: interal error: ";
                   STR "subtraction"]))
  | _ -> false

  (* return a substring of the section starting at virtual address a
     of size bytes *)
  method get_xsubstring (a:doubleword_int) (size:int) =
    match self#get_containing_section a with
    | Some s ->
       if s#get_size >= size then
         s#get_xsubstring a size
       else
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Error in xsubstring request: ";
                   STR "Size of section ";
                   s#get_vaddr#toPretty;
                   STR ": ";
                   INT s#get_size;
                   STR " does not cover request of ";
                   INT size]))
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in xsubstring request. ";
                 STR "No section found that includes virtual address ";
                 a#toPretty ]))

  method get_containing_section (a:doubleword_int) =
    H.fold (fun k v result ->
        match result with
        | Some _ -> result
        | _ ->
           match self#get_section k with
           | ElfProgramSection t when t#includes_VA a ->
              Some ( t :> elf_raw_section_t )
           | ElfOtherSection t when t#includes_VA a -> Some t
           | _ -> None) section_header_table None

  method get_program_value (a:doubleword_int) =
    let section =
      H.fold (fun k v result ->
          match result with
          | Some _ -> result
          | _ ->
             match self#get_section k with
             | ElfProgramSection s when s#includes_VA a -> Some s
             | _ -> None) section_header_table None in
    match section with
    | Some s -> s#get_value a
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Address " ; a#toPretty ;
                      STR " is not included in a program section" ]))

  method is_program_address (a:doubleword_int) =
    H.fold (fun k v result ->
        result
        || match self#get_section k with
           | ElfProgramSection s -> s#includes_VA a
           | _ -> false) section_header_table false

  method private get_string_table =
    let result = ref [] in
    let _ = H.iter (fun k v ->
                if v#get_section_name = ".strtab" then result :=  k :: !result)
                   section_header_table in
    match !result with
    | [] -> raise (BCH_failure (LBLOCK [ STR "No string table found" ]))
    | [ index ] ->
       begin
         match self#get_section index with
         | ElfStringTable t -> t
         | _ ->
            raise
              (BCH_failure
                 (STR "Unexpected section type: string table expected"))
       end
    | l ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Found multiple string tables: ";
                 pretty_print_list l (fun i -> INT i) "" "," "" ]))

  method private get_symbol_table =
    let result = ref [] in
    let _ = H.iter (fun k v ->
                if v#get_section_name = ".symtab" then result := (k,v) :: !result)
                   section_header_table in
    match !result with
    | [] -> raise (BCH_failure (LBLOCK [ STR "No symbol table found" ]))
    | [ (index,h) ] ->
       begin
         match self#get_section index with
         | ElfSymbolTable t -> (h,t)
         | _ ->
            raise
              (BCH_failure
                 (STR "Unexpected section type: symbol table expected"))
       end
    | l ->
       raise (BCH_failure
                (LBLOCK [
                     STR "found multiple symbol  tables: ";
                     pretty_print_list l (fun (i,_) -> INT i) "" "," ""]))
      
  method private get_dynamic_symbol_table =
    let result = ref [] in
    let _ = H.iter (fun k v ->
                if v#get_section_name = ".dynsym" then result := (k,v) :: !result)
                   section_header_table in
    match !result with
    | [] -> raise (BCH_failure (LBLOCK [ STR "No symbol table found" ]))
    | [ (index,h) ] ->
       begin
         match self#get_section index with
         | ElfDynamicSymbolTable t -> (h,t)
         | _ ->
            raise
              (BCH_failure
                 (STR "Unexpected section type: symbol table expected"))
       end
    | l -> raise
             (BCH_failure
                (LBLOCK [
                     STR "found multiple symbol  tables: ";
                     pretty_print_list l (fun (i,_) -> INT i) "" "," ""]))
    

  (* Each symbol table has an associated string table, referred to by the sh_link
     item in the symbol table section header *)
  method private get_associated_string_table (h:elf_section_header_int) =
    let link = h#get_link#to_int in
    match self#get_section link with
    | ElfStringTable t -> t
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Link item of symbol table does not refer ";
                 STR "to a string table: ";
                 INT link]))

  method private get_associated_symbol_table (h:elf_section_header_int) =
    let link = h#get_link#to_int in
    match self#get_section link with
    | ElfSymbolTable t -> t
    | ElfDynamicSymbolTable t -> t
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Link item does not refer to a symbol table: ";
                 INT link]))

  method private set_symbol_names =
    if self#has_symbol_table then
      let (header,symboltable) = self#get_symbol_table in
      let stringtable = self#get_associated_string_table header in
      begin
        symboltable#set_symbol_names stringtable ;
        symboltable#set_function_entry_points ;
        symboltable#set_function_names;
        (if system_info#is_arm then symboltable#set_mapping_symbols);
      end
    else
      chlog#add "no symbols found" (STR "No symbols found")

  method private set_dynamic_symbol_names =
    if self#has_dynamic_symbol_table then
      let (header,symboltable) = self#get_dynamic_symbol_table in
      let stringtable = self#get_associated_string_table header in
      begin
        symboltable#set_symbol_names stringtable ;
        symboltable#set_function_entry_points ;
        symboltable#set_function_names
      end
    else
      chlog#add "no symbols found" (STR "No symbols found")

  method private set_relocation_symbols =
    H.iter (fun index h ->
        match h#get_section_type with
        | SHT_Rel ->
           let reltable =
             match self#get_section index with
             | ElfRelocationTable t -> t
             | _ ->
                 raise (BCH_failure (LBLOCK [ STR "Section with index: " ; INT index ;
                                              STR " is not a relocation table" ])) in
           if h#get_link#equal wordzero then
             ()
           else
             let symboltable = self#get_associated_symbol_table h in
             begin
               reltable#set_symbols symboltable;
               reltable#set_function_entry_points
             end
        | _ -> ()) section_header_table
      

  method private get_section (index:int):elf_section_t =
    let _ = self#add_section index in (H.find section_table index)

  method private get_segment (index:int):elf_segment_t =
    let _ = self#add_segment index in (H.find segment_table index)

  method private set_section_header_names =
    if (H.length section_header_table) > 0 then
      let strindex  = elf_file_header#get_section_header_string_table_index in
      if strindex > 0 then
        let s = self#get_section strindex in
        let get_name = match s with
          | ElfStringTable t -> t#get_string 
          | _ ->
	     raise
               (BCH_failure 
		  (LBLOCK [
                       STR "Unexpected section type; ";
                       STR "string table expected"])) in
        H.iter (fun _ sh ->
            sh#set_name (get_name sh#get_name#to_int)) section_header_table
      else
        pr_debug [STR "String table index is zero"; NL]
    else
      pr_debug [STR "No section headers present."; NL]
      

  method private check_elf =
    begin
      (if (String.sub e_ident 1 3) = "ELF" then () else 
	  raise (BCH_failure (STR "ELF header is missing"))) ;
      (if (String.get e_ident 4) = '\001' then () else
	 raise (BCH_failure (STR "ELF file is not a 32 bit executable")));
      (if elf_file_header#get_type = 1 then
         chlog#add "disassembly" (STR "Object file"))
    end

  method private set_endianness =
    let endianness = String.get e_ident 5 in
    if endianness = '\001' then 
      let _ =
        pr_debug [STR "Little endian (default)"; NL] in ()   (* default case *)
    else if endianness = '\002' then 
      let _ = pr_debug [STR "Set big endian"; NL] in
      system_info#set_big_endian
    else raise (BCH_failure (STR ("Unknown endianness in ELF file")))

  method private read_program_headers =
    let phoff = elf_file_header#get_program_header_table_offset in
    let phentsize = elf_file_header#get_program_header_table_entry_size in
    let phnum = elf_file_header#get_program_header_table_entry_num in
    for i=0 to (phnum - 1) do
      let ph = mk_elf_program_header () in
      let offset = phoff#add_int (phentsize * i) in
      begin 
	ph#read offset phentsize; 
	H.add program_header_table i ph
      end
    done

  method private read_section_headers =
    let shoff = elf_file_header#get_section_header_table_offset in
    let shentsize = elf_file_header#get_section_header_table_entry_size in
    let shnum = elf_file_header#get_section_header_table_entry_num in
    let _ = pr_debug [STR  "Number of section headers: "; INT shnum; NL] in
    for i = 0 to (shnum - 1) do
      let sh = mk_elf_section_header () in
      let offset = shoff#add_int (shentsize * i) in
      begin
	sh#read offset shentsize;
	H.add section_header_table i sh
      end
    done

  method private add_user_defined_section_headers =
    let shnum = elf_file_header#get_section_header_table_entry_num in
    try
      List.iteri
        (fun i name ->
          let sh = mk_elf_section_header () in
          let shinfo = section_header_infos#get_section_header_info name in
          let name = shinfo#get_name in
          let addr = shinfo#get_addr in
          let size = shinfo#get_size in
          let stype = shinfo#get_type in
          let offset = shinfo#get_offset in
          let flags = shinfo#get_flags in
          begin
            sh#set_fields
              ~stype:stype
              ~size:size
              ~addr:addr
              ~offset:offset
              ~flags:flags
              ~sectionname:name ();
            chlog#add "user-defined section" (LBLOCK [sh#toPretty]);
            H.add section_header_table (shnum + i) sh
          end) section_header_infos#get_section_header_names
    with
    | BCH_failure p ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in creating user-defined section headers: ";
                 p]))

  method private add_section (index:int) =
    if H.mem section_table index then
      ()
    else
      if H.mem section_header_table index then
	let sh = H.find section_header_table index in
	let xString =
          if sh#get_size#equal wordzero then
            ""
          else
	    system_info#get_file_string ~hexSize:sh#get_size sh#get_offset in
	let section = make_elf_section sh xString in
	H.add section_table index section
      else
	raise
          (BCH_failure
             (LBLOCK [STR "No section header found for "; INT index]))

  method private add_segment (index:int) =
    if H.mem segment_table index then
      ()
    else
      if H.mem program_header_table index then
        let ph = H.find program_header_table index  in
        let xString =
          if ph#get_file_size#equal wordzero then
            ""
          else
            system_info#get_file_string ~hexSize:ph#get_file_size ph#get_offset in
        let segment = make_elf_segment ph xString in
        H.add segment_table index segment
      else
        raise
          (BCH_failure
             (LBLOCK [STR "No segment header found for index "; INT index]))

  method private write_xml_program_headers (node:xml_element_int) =
    let headers = ref [] in
    let compare = fun (i1,_) (i2,_) -> Stdlib.compare i1 i2 in
    let _ = H.iter (fun k v -> headers := (k,v) :: !headers) program_header_table in
    let headers = List.sort compare !headers in
    node#appendChildren (List.map (fun (k,h) ->
      let hNode = xmlElement "program-header" in
      begin
	h#write_xml hNode ; 
	hNode#setIntAttribute "index" k ; 
	hNode
      end) headers)

  method private read_xml_program_headers (node:xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun hNode ->
      let geti = hNode#getIntAttribute in
      let index = geti "index" in
      let header = mk_elf_program_header () in
      begin 
	header#read_xml hNode ; 
	H.add program_header_table index header
      end) (getcc "program-header")

  method private write_xml_section_headers (node:xml_element_int) =
    let headers = ref [] in
    let compare = (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) in
    let _ =
      H.iter (fun k v ->
          headers := (k,v) :: !headers) section_header_table in
    let headers = List.sort compare !headers in
    node#appendChildren (List.map (fun (k,h) ->
      let hNode = xmlElement "section-header" in
      begin
	h#write_xml hNode ;
	hNode#setIntAttribute "index" k;
	hNode
      end) headers)

  method private read_xml_section_headers (node:xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun sNode ->
      let geti = sNode#getIntAttribute in
      let index = geti "index" in
      let header = mk_elf_section_header () in
      begin
	header#read_xml sNode ;
	H.add section_header_table index header
      end) (getcc "section-header")

  method private read_xml_sections =
    H.iter (fun index h ->
      if h#get_size#equal wordzero then () else
	match load_section_file (string_of_int index) with
	| Some node ->
           let section = read_xml_elf_section h node in
	   H.add section_table index section
	| _ -> 
	   pr_debug [
               STR "Section ";
               STR h#get_section_name;
               STR " not found";
               NL])
           section_header_table

  method private read_xml_segments =
    H.iter (fun index h ->
        if h#get_file_size#equal wordzero then
          ()
        else
          match load_segment_file index with
          | Some node  ->
             let segment = read_xml_elf_segment h node in
             H.add segment_table index segment
          | _ ->
             pr_debug [STR "Segment "; INT index; STR " not found"; NL])
           program_header_table

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let append = node#appendChildren in
    let hNode = xmlElement "elf-file-header" in
    let pNode = xmlElement "elf-program-headers" in
    let sNode = xmlElement "elf-section-headers" in
    begin
      elf_file_header#write_xml hNode ;
      self#write_xml_program_headers pNode ;
      self#write_xml_section_headers sNode ;
      append [ hNode ; pNode ; sNode ] ;
      if system_info#is_little_endian then () else set "endian" "big"
    end

  method read_xml (node:xml_element_int) =
    let has = node#hasNamedAttribute in
    let get = node#getAttribute in
    let getc = node#getTaggedChild in
    let hNode = getc "elf-file-header" in
    let pNode = getc "elf-program-headers" in
    let sNode = getc "elf-section-headers" in
    begin
      (if (has "endian") && ((get "endian") = "big") then
         system_info#set_big_endian) ;
      elf_file_header#read_xml hNode ;
      self#read_xml_program_headers pNode ;
      self#read_xml_section_headers sNode ;
      (if (H.length section_header_table > 0) then
         self#read_xml_sections
       else
         begin
           self#read_xml_segments;
           H.iter (fun index ph ->
               match ph#get_program_header_type with
               | PT_Dynamic ->
                  (match self#get_segment index with
                  | ElfDynamicSegment t -> pr_debug [ t#toPretty ]
                  | _ -> ())
               | _ -> ()) program_header_table
         end);
      self#set_symbol_names ;
      self#set_dynamic_symbol_names ;
      self#set_relocation_symbols 
    end
      
  method toPretty = 
    let programHeaders = ref [] in
    let sectionHeaders = ref [] in
    let _ = H.iter (fun k v -> 
      programHeaders := (k,v) :: !programHeaders) program_header_table in
    let _ = H.iter (fun k v ->
      sectionHeaders := (k,v) :: !sectionHeaders) section_header_table in
    let compare = fun (i1,_) (i2,_) -> Stdlib.compare i1 i2 in
    let programHeaders = List.sort compare !programHeaders in
    let sectionHeaders = List.sort compare !sectionHeaders in
    let prProgramHeader (i, h) = 
      LBLOCK [STR "Program header "; INT i; NL; INDENT (3, h#toPretty); NL] in
    let prSectionHeader (i, h) = 
      LBLOCK [STR "Section header "; INT i; NL; INDENT (3, h#toPretty); NL] in
    LBLOCK [
        STR "File header:";
        NL;
        INDENT (3, elf_file_header#toPretty);
        NL;
        STR "Program headers: ";
        NL;
        pretty_print_list programHeaders prProgramHeader "" "" "";
        NL;
        STR "Section headers: ";
        NL;
        pretty_print_list sectionHeaders prSectionHeader "" "" "";
        NL]

end


let elf_header = new elf_header_t


let save_elf_header () =
  let filename = get_elf_header_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root "elf-header" in
  let hNode = xmlElement "elf-header" in
  begin
    doc#setNode root ;
    elf_header#write_xml hNode ;
    root#appendChildren [ hNode ] ;
    file_output#saveFile filename doc#toPretty
  end


let save_elf_dictionary () =
  let filename = get_elf_dictionary_filename () in
  let doc = xmlDocument () in
  let root = get_bch_root  "elf-dictionary" in
  let hNode = xmlElement "elf-dictionary" in
  begin
    doc#setNode root ;
    elfdictionary#write_xml hNode ;
    root#appendChildren [ hNode ] ;
    file_output#saveFile filename doc#toPretty
  end


let save_elf_section
      (index:int) (header:elf_section_header_int) (s:elf_section_t) =
  let filename = get_section_filename (string_of_int index) in
  let doc = xmlDocument () in
  let rawsection = elf_section_to_raw_section s in
  let root = get_bch_root "raw-section" in
  let sNode = xmlElement "raw-section" in
  let hNode = xmlElement "section-header" in
  let add_string_table () =
    let dNode = xmlElement "data" in
    let stNode = xmlElement "string-table" in
    let stringtable = elf_section_to_string_table s in
    begin
      stringtable#write_xml_strings stNode ;
      dNode#appendChildren [ stNode ] ;
      sNode#appendChildren [ dNode ]
    end in
  let add_symbol_table () =
    let dNode = xmlElement "data" in
    let syNode = xmlElement "symbol-table" in
    let symboltable = elf_section_to_symbol_table s in
    begin
      sNode#setIntAttribute "entrysize" header#get_entry_size#to_int;
      symboltable#write_xml_symbols syNode ;
      dNode#appendChildren [ syNode ] ;
      sNode#appendChildren [ dNode ]
    end in
  let add_relocation_table () =
    let dNode = xmlElement "data"  in
    let rNode = xmlElement "relocation-table" in
    let relocationtable = elf_section_to_relocation_table s in
    begin
      sNode#setIntAttribute "entrysize" header#get_entry_size#to_int;
      relocationtable#write_xml_entries rNode ;
      dNode#appendChildren [ rNode ] ;
      sNode#appendChildren [ dNode ]
    end in
  let add_dynamic_table () =
    let dNode = xmlElement "data" in
    let rNode = xmlElement "dynamic-table" in
    let dynamictable = elf_section_to_dynamic_table s in
    begin
      sNode#setIntAttribute "entrysize" header#get_entry_size#to_int;
      dynamictable#write_xml_entries rNode ;
      dNode#appendChildren [ rNode ] ;
      sNode#appendChildren [ dNode ]
    end in
  begin
    (let sname = header#get_section_name in
     if (String.length sname) > 6
        && (String.sub header#get_section_name 0 6) = ".debug" then
       let hexdata = xmlElement "hex-data" in
       begin
         sNode#appendChildren [ hexdata ];
         sNode#setAttribute "vaddr" header#get_addr#to_hex_string;
         sNode#setIntAttribute "size" 0
       end
     else
       rawsection#write_xml sNode) ;
    header#write_xml hNode ;
    sNode#setIntAttribute "index" index ;
    sNode#appendChildren [ hNode ] ;
    (match header#get_section_type with
     | SHT_StrTab -> add_string_table ()
     | SHT_SymTab -> add_symbol_table ()
     | SHT_DynSym -> add_symbol_table ()
     | SHT_Rel -> add_relocation_table ()
     | SHT_Dynamic -> add_dynamic_table ()
     | _ -> ()) ;
    doc#setNode root ;
    root#appendChildren [ sNode ] ;
    file_output#saveFile filename doc#toPretty
  end


let save_elf_program_segment
      (header:elf_program_header_int) (index:int) (s:elf_segment_t) =
  let filename = get_segment_filename index in
  let doc = xmlDocument () in
  let rawsegment = elf_segment_to_raw_segment s in
  let root = get_bch_root "raw-segment" in
  let sNode = xmlElement "raw-segment" in
  let hNode = xmlElement "program-header" in
  let add_dynamic_table () =
    let dNode = xmlElement "data" in
    let rNode = xmlElement "dynamic-table" in
    let dynamictable = elf_segment_to_dynamic_segment s in
    begin
      dynamictable#write_xml_entries rNode ;
      dNode#appendChildren [ rNode ] ;
      sNode#appendChildren [ dNode ]
    end in
  begin
    rawsegment#write_xml sNode ;
    header#write_xml hNode ;
    sNode#setIntAttribute "index" index ;
    sNode#appendChildren [ hNode ]  ;
    (match header#get_program_header_type with
     | PT_Dynamic -> add_dynamic_table  ()
     | _ -> ()) ;
    doc#setNode root ;
    root#appendChildren [ sNode ] ;
    file_output#saveFile filename doc#toPretty
  end


let save_elf_program_segments () =
  List.iter (fun (index,header,segment) ->
      save_elf_program_segment
        header index segment) elf_header#get_program_segments
  

let save_elf_files () =
  begin
    save_elf_header () ;
    (if elf_header#has_sections then
       List.iter (fun (index, header, s) ->
           save_elf_section index header s) elf_header#get_sections
     else
       save_elf_program_segments ());
    save_elf_dictionary ()
  end


let load_elf_files () =
  match load_elf_header_file () with
  | Some node ->
     (try
        begin
          elf_header#read_xml node;
          elf_header#set_code_extent;
          elf_header#initialize_jump_tables;
          elf_header#initialize_call_back_tables;
          elf_header#initialize_struct_tables
        end
      with
      | CHXmlReader.XmlParseError(line,col,p) ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Xml Parse Error in elf header file (line: ";
                   INT line;
                   STR ", col: ";
                   INT col; STR "): ";
                   p])))
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Unable to load elf file "; STR (get_filename ())]))


let read_elf_file (filename: string) (xsize: int) =
  let ch = open_in_bin filename in
  let ch = IO.input_channel ch in
  let exeString = IO.nread ch (2 * xsize) in
  let filesize = Bytes.length exeString in
  let default () =
    begin
      system_info#set_file_string  (Bytes.to_string exeString);
      elf_header#read;
      elf_header#set_code_extent;
      elf_header#initialize_jump_tables;
      elf_header#initialize_call_back_tables;
      elf_header#initialize_struct_tables;
      (true,
       LBLOCK [
           STR "File: ";
           STR  filename;
           NL;
           STR "Size: ";
           INT filesize;
           NL])
    end in
  default ()
