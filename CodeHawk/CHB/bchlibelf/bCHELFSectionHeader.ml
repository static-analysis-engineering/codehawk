(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
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
open CHXmlDocument

(* bchlib *)
open BCHDoubleword
open BCHLibTypes
open BCHSystemInfo

(* bchlibelf *)
open BCHELFTypes
open BCHELFUtil

module TR = CHTraceResult


class elf_section_header_t:elf_section_header_int =
object (self)

  val mutable sh_name = wordzero
  val mutable sh_type = wordzero
  val mutable sh_flags = wordzero
  val mutable sh_addr = wordzero
  val mutable sh_offset = wordzero
  val mutable sh_size = wordzero
  val mutable sh_link = wordzero
  val mutable sh_info = wordzero
  val mutable sh_addralign = wordzero
  val mutable sh_entsize = wordzero
  val mutable name = ""

  method set_fields
           ?(sname=wordzero)
           ?(stype=wordzero)
           ?(flags=wordzero)
           ?(addr=wordzero)
           ?(offset=wordzero)
           ?(size=wordzero)
           ?(link=wordzero)
           ?(info=wordzero)
           ?(addralign=wordzero)
           ?(entsize=wordzero)
           ~(sectionname:string) () =
    begin
      sh_name <- sname ;
      sh_type <- stype ;
      sh_flags <- flags ;
      sh_addr <- addr ;
      sh_offset <- offset ;
      sh_size <- size ;
      sh_link <- link ;
      sh_info <- info ;
      sh_addralign <- addralign ;
      sh_entsize <- entsize ;
      name <- sectionname
    end

  method read (offset:doubleword_int) (size:int) =
    let input =
      system_info#get_file_input
        ~hexSize:(TR.tget_ok (int_to_doubleword size)) offset in
    begin
      (* 0, 4, sh_name -------------------------------------------------------
	 Specifies the name of the section. Its value is an index into the 
	 section header string table section, giving the location of a null-
	 terminated string
	 --------------------------------------------------------------------- *)
      sh_name <- input#read_doubleword ;

      (* 4, 4, sh_type -------------------------------------------------------
	 Categorizes the section's contents and semantics.
	 SHT_NULL                0  section header is inactive; it does not have
	                            an associated section
	 SHT_PROGBITS            1  section holds information defined by the 
                                    program, whose format and meaning are
                                    determined solely by the program
         SHT_SYMTAB              2  section holds a symbol table. An object file
                                    may have only one section of each type.
                                    Typically, SHT_SYMTAB provides symbols for
                                    link editing, though it may also be used for
                                    dynamic linking. 
         SHT_STRTAB              3  section holds a string table. An object file
                                    may have multiple string tables
         SHT_RELA                4  section holds relocation entries with explicit
                                    addends, such as type Elf32_Rela for the 32-bit
                                    class of object files. An object file may have
                                    multiple relation sections
         SHT_HASH                5  section holds a symbol has table. Currently, an
                                    object file may have only one hash table.
         SHT_DYNAMIC             6  section holds information for dynamic linking. 
                                    Currently, an object file may have only one
                                    dynamic section.
         SHT_NOTE                7  section holds information that marks the file
                                    in some way.
         SHT_NOBITS              8  section of this type occupies no space in the
                                    file but otherwise resembles SHT_PROGBITS.
                                    Although this section contains no bytes, the
                                    sh_offset member contains the conceptual file
                                    offset
         SHT_REL                 9  section holds relocation entries without explicit
                                    addends. An object file may have multiple 
                                    relocation sections
         SHT_SHLIB              10  section type is reserved but has unspecified
                                    semantics
         SHT_DYNSYM             11  see SHT_SYMTAB
         SHT_INIT_ARRAY         14  section contains an array of pointers to 
                                    initialization functions. Each pointer in the
                                    array is taken as a parameterless procedure 
                                    with a void return
         SHT_FINI_ARRAY         15  section contains an array of pointers to
                                    termination function. Each pointer in the array
	                            is taken as a parameterless procedures with
                                    a void return
         SHT_PREINIT_ARRAY      16  section contains an array of pointers to 
                                    functions that are invoked before all other
                                    initialization function. Each pointer is taken
                                    as a parameterless procedure with a void return.
         SHT_GROUP              17  section defines a section group. A section group
                                    is a set of sections that are related and that
                                    must be treated specially by the linker. 
                                    Sections of this type may appear only in relocatable
                                    objects (objects with the ELF header e_type
                                    member set to ET_REL). The section header table
                                    entry for a group section must appear in the
                                    section header table before the entries for any
                                    of the sections that are members of the group.
         SHT_SYMTAB_SHNDX       18  section is associated with a section of type
                                    SHT_SYMTAB and is required if any of the section
                                    header indexes referenced by that symbol table
                                    contain the escape value SHN_XINDEX. The section
                                    is an array of Elf32_Word values. Each value
                                    corresponds one to one with a symbol table entry
                                    and appear in the same order as those entries.
                                    The values represent the section header indexes
                                    against which the symbol table entries are
                                    defined. Only if corresponding symbol table entry's
                                    st_shndx field contains the escape value
                                    SHN_XINDEX will the matching Elf32_Word hold the
                                    actual section header index; otherwise, the entry
                                    must be SHN_UNDEF (0)
         SHT_LOOS       0x60000000  values SHT_LOOS through SHT_HIOS are reserved for
         SHT_HIOS       0x6fffffff  operating system semantics  
	 SHT_LOPROC     0x70000000  values SHT_LOPROC through SHT_HIPROC are reserved
         SHT_HIPROC     0x7fffffff  for processor-specific semantics
         SHT_LOUSER     0x80000000  specifies the lower bound of the range of indexes
                                    reserved for application programs
         SHT_HIUSER     0xffffffff  specifies the upper bound of the range of indexes
                                    reserved for application programs.
         --------------------------------------------------------------------- *)
      sh_type <- input#read_doubleword ;

      (* 8, 4, sh_flags ------------------------------------------------------
	 1-bit flags that describe miscellaneous attributes.
	 SHF_WRITE             0x1  section contains data that should be writable 
                                    during process execution
         SHF_ALLOC             0x2  section occupies memory during process exeuction
         SHF_EXECINSTR         0x4  section contains executable machine instructions
         SHF_MERGE            0x10  the data in the setion may be merged to eliminate
                                    duplication. Unless the SHF_STRINGS flag is also
                                    set, the data elements in the section are of a 
                                    uniform size. The size of each element is specified
                                    in the section header's sh_entsize field. If the
                                    SHF_STRINGS flag is also set, the data elements
                                    consist of null-terminated character strings.
                                    The size of each character is specified in the
                                    section header's sh_entsize field.
            
                                    Each element in the section is compared against
                                    other elements in sections with the same name,
                                    type and flags. Elements that would have identical
                                    values at program run-time may be merged. Relocations
                                    referencing elements of such sections must be 
                                    resolved to the merged locations of the referenced
                                    values. Note that any relocatable values, including
                                    values that would result in run-time relocations,
                                    must be analyzed to determine whether the run-time
                                    values would actually be identical. An ABI-conforming
                                    object file may not depend on specific elements
                                    being merged, and an ABI-conforming link editor 
                                    may choose not to merge specific elements.
           SHF_STRINGS        0x20  the data elements in the section consist of
                                    null-terminated character strings. The size of 
                                    each character is specified in the section header's
                                    sh_entsize field.
           SHF_INFO_LINK      0x40  the sh_info field of this section header holds a
                                    section header table index
           SHF_LINK_ORDER     0x80  this flag adds special ordering requirements for
                                    link editors. The requirements apply if the
                                    sh_link field of this section's header references
                                    another section (the linked-to section). If this
                                    section is combined with other sections in the
                                    output file, it must appear in the same relative
                                    order with respect to those sections, as the
                                    linked-to section appears with respect to sections
                                    the linked-to section is combined with.
           SHF_OS_NONCONFORMING 0x100 the section requires special OS-specific processing
                                    to avoid incorrect behavior. If this section has
                                    either an sh_type value or contains sh_flags bits
                                    in the OS-specific ranges for those fields, and a
                                    link editor processing this section does not 
                                    recognize those values, then the link editor should
                                    reject the object file containing this section with
                                    an error.
           SHF_GROUP         0x200  the section is a member (perhaps the only one) of a
                                    section group. The section must be referenced by a
                                    section of type SHT_GROUP. The SHF_GROUP flag may
                                    be set only for sections contained in relocatable
                                    objects (objects with the ELF header e_type member
                                    set to ET_REL).
           SHF_TLS           0x400  the section holds Thread Local Storage, meaning that
                                    each separate execution flow has its own distinct
                                    instance of this data
           SHF_COMPRESSED    0x800  identifies a section containing compressed data.
	                            SHF_COMPRESSED applies only to non-allocable sections
                                    and cannot be used in conjunction with SHF_ALLOC.
	                            In addition SHF_COMPRESSED cannot be applied to
                                    sections of type SHT_NOBITS.
                                    All relocations to a compressed section specify
                                    offsets to the uncompressed section data. It is
                                    therefore necessary to decompress the section data
                                    before relocations can be applied. Each decompressed
                                    section specifies the algorithm independently. It
                                    is permissible for different sections in a given
                                    ELF object to employ different compression 
                                    algorithms. 
                                    Compressed sections begin with a compression header
                                    structure that identifies the compression algorithm.
          SHF_PPC_VLE   0x10000000  marks ELF sections containing powerpc VLE
                                    instructions.
	 --------------------------------------------------------------------- *)
      sh_flags <- input#read_doubleword ;

      (* 12, 4, sh_addr ------------------------------------------------------
	 If the section will appear in the memory image of a process, this member
         gives the address at which the section's first byte should reside. 
	 Otherwise, the member contains 0.
	 --------------------------------------------------------------------- *)
      sh_addr <- input#read_doubleword ;

      (* 16, 4, sh_offset ----------------------------------------------------
	 Byte offset from the beginning of the file to the first byte in the
	 section. One section type, SHT_NOBITS, occupies no space in the file, and
	 its sh_offset member locates the conceptual placement in the file.
	 --------------------------------------------------------------------- *)
      sh_offset <- input#read_doubleword ;

      (* 20, 4, sh_size ------------------------------------------------------
	 Section's size in bytes. Unless the section type is SHT_NOBITS, the
	 section occupies sh_size bytes in the file. A section of type SHT_NOBITS
	 may have a non-zero size, but it occupies no space in the file.
	 --------------------------------------------------------------------- *)
      sh_size <- input#read_doubleword ;

      (* 24, 4, sh_link ------------------------------------------------------
	 Section header table index link, whose interpretation depends on the 
	 section type.
	 sh_type           sh_link
	 SHT_DYNAMIC       section header index of the string table used by 
                           entries in the section
	 SHT_HASH          section header index of the symbol table to which the
                           hash table applies
	 SHT_REL           section header index of the associated symbol table
	 SHT_RELA          idem
	 SHT_GROUP         idem
	 SHT_SYMTAB        section header index of the associated string table
	 SHT_DYNSYM        idem
	 SHT_SYMTAB_SHNDX  section header index of the associated symbol table section
	 --------------------------------------------------------------------- *)
      sh_link <- input#read_doubleword ;

      (* 28, 4, sh_info ------------------------------------------------------
	 This member holds extra information, whose interpretation depends on
	 the section type; If the sh_flags field for this section header includes
	 the attribute SHF_INFO_LINK, then this member represents a section header
	 table index
	 sh_type           sh_info
	 SHT_DYNAMIC       0
	 SHT_HASH          0
	 SHT_SYMTAB_SHNDX  0

	 SHT_REL           section header index of the section to which the
	 SHT_RELA          relocation applies

	 SHT_SYMTAB        one greater than the symbol table index of the last
         SHT_DYNSYM        local symbol (binding STB_LOCAL)

	 SHT_GROUP         symbol table index of an entry in the associated symbol
                           table. The name of the specified symbol table entry
	                   provides a signature for the section group.
	 --------------------------------------------------------------------- *)
      sh_info <- input#read_doubleword ;

      (* 32, 4, sh_addralign -------------------------------------------------
	 Some sections have address alignment constraints. For example, if a 
	 section holds a doubleword, the system must ensure doubleword alignment
	 for the entire section. The value of sh_addr must be congruent to 0,
	 modulo the value of sh_addralign. Currently, only 0 and positive
	 integral powers of two are allowed. Values 0 and 1 mean the section
	 has no alignment constraints.
	 --------------------------------------------------------------------- *)
      sh_addralign <- input#read_doubleword ;

      (* 36, 4, sh_entsize ---------------------------------------------------
	 Some sections hold a table of fixed-size entries, such as a symbol table.
	 For such a section, this member gives the size in bytes of each entry.
	 The member contains 0 if the section does not hold a table of fixed-size
	 entries.
	 --------------------------------------------------------------------- *)
      sh_entsize <- input#read_doubleword 
    end

  method set_name s = name <- s

  method set_link d = sh_link <- d

  method get_name = sh_name 

  method get_type = sh_type

  method get_flags = sh_flags

  method get_addr = sh_addr

  method get_offset = sh_offset

  method get_size = sh_size

  method get_link = sh_link

  method get_info = sh_info

  method get_addralign = sh_addralign

  method get_entry_size = sh_entsize

  method get_section_type = doubleword_to_elf_section_header_type sh_type

  method get_section_name = name

  method is_executable = sh_flags#is_nth_bit_set 2

  method is_readonly = not (sh_flags#is_nth_bit_set 0)

  method is_string_table =
    match self#get_section_type with SHT_StrTab -> true | _ -> false

  method is_symbol_table =
    match self#get_section_type with SHT_SymTab -> true | _ -> false

  method is_relocation_table =
    match self#get_section_type with SHT_Rel -> true | _ -> false

  method is_uninitialized_data_section =
    match self#get_section_type with SHT_NoBits -> true | _ -> false

  method is_program_section =
    match self#get_section_type with SHT_ProgBits -> true | _ -> false

  method is_pwr_vle = List.mem 28 sh_flags#get_bits_set

  method is_debug_info = self#get_section_name = ".debug_info"

  method is_debug_abbrev = self#get_section_name = ".debug_abbrev"

  method is_debug_aranges = self#get_section_name = ".debug_aranges"

  method is_debug_loc = self#get_section_name = ".debug_loc"

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    begin
      set "name" name;
      setx "sh_type" sh_type;
      setx "sh_name" sh_name;
      setx "sh_flags" sh_flags;
      setx "sh_addr" sh_addr;
      setx "sh_offset" sh_offset;
      setx "sh_size" sh_size;
      setx "sh_info" sh_info;
      setx "sh_link" sh_link;
      setx "sh_addralign" sh_addralign;
      setx "sh_entsize" sh_entsize
    end

  method read_xml (node:xml_element_int) =
    let get = node#getAttribute in
    let has = node#hasNamedAttribute in
    let getx t =
      if has t then
        TR.tget_ok (string_to_doubleword (get t))
      else
        wordzero in
    begin
      name <- get "name";
      sh_type <- getx "sh_type";
      sh_name <- getx "sh_name";
      sh_flags <- getx "sh_flags";
      sh_addr <- getx "sh_addr";
      sh_offset <- getx "sh_offset";
      sh_size <- getx "sh_size";
      sh_info <- getx "sh_info";
      sh_link <- getx "sh_link";
      sh_addralign <- getx "sh_addralign";
      sh_entsize <- getx "sh_entsize"
    end

  method private characteristic_to_string n =
    match n with
    | 0 -> "WRITE"
    | 1 -> "ALLOC"
    | 2 -> "EXECINSTR"
    | 4 -> "MERGE"
    | 5 -> "STRINGS"
    | 6 -> "INFO_LINK"
    | 7 -> "LINK_ORDER"
    | 8 -> "OS_NONCORMING"
    | 9 -> "GROUP"
    | 10 -> "TLS"
    | 11 -> "COMPRESSED"
    | 28 -> "VLE(PowerPC)"    (* 0x10000000 *)
    | _ -> "(not used: " ^ (string_of_int n) ^ ")"

  method private characteristics_to_pretty =
    let descr = self#characteristic_to_string in
    let bitsSet = sh_flags#get_bits_set in
    List.fold_left
      (fun a i -> LBLOCK [a; NL; INDENT (3, STR (descr i))])
      (STR "Characteristics") bitsSet

  method toPretty = LBLOCK [
    STR "Name             : "; STR name;
    STR " ("; STR sh_name#to_fixed_length_hex_string; STR ")";  NL;
    STR "Type             : ";
    STR (doubleword_to_elf_section_header_string sh_type); NL;
    STR "Flags            : "; STR sh_flags#to_fixed_length_hex_string; NL;
    self#characteristics_to_pretty; NL;
    STR "Address          : "; STR sh_addr#to_fixed_length_hex_string; NL;
    STR "Offset           : "; STR sh_offset#to_fixed_length_hex_string; NL;
    STR "Size             : "; STR sh_size#to_fixed_length_hex_string;
                                STR " ("; INT sh_size#to_int; STR ")"; NL;
    STR "Link             : "; STR sh_link#to_fixed_length_hex_string; NL;
    STR "Info             : "; STR sh_info#to_fixed_length_hex_string; NL;
    STR "Address alignment: "; STR sh_addralign#to_fixed_length_hex_string; NL;
    STR "Entry size       : "; STR sh_entsize#to_fixed_length_hex_string;
                                STR " ("; INT sh_entsize#to_int; STR ")"; NL ]
end


let mk_elf_section_header () = new elf_section_header_t
