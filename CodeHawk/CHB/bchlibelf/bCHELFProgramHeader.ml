(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
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
open CHUtils

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHDoubleword
open BCHLibTypes
open BCHSystemInfo

(* bchlibx86 *)
open BCHBasicTypes
open BCHDoubleword

(* bchlibelf *)
open BCHELFTypes
open BCHELFUtil


class elf_program_header_t:elf_program_header_int =
object (self)

  val mutable p_type = wordzero
  val mutable p_offset = wordzero
  val mutable p_vaddr = wordzero
  val mutable p_paddr = wordzero
  val mutable p_filesz = wordzero
  val mutable p_memsz = wordzero
  val mutable p_flags = wordzero
  val mutable p_align = wordzero

  method read (offset:doubleword_int) (size:int) =
    let input = system_info#get_file_input ~hexSize:(int_to_doubleword size) offset in
    begin
      (* 0, 4, p_type --------------------------------------------------------
	 Tells what kind of segment this array element describes or how to
	 interpret the array element's information
	 PT_NULL     0   array element is unused; other members' values are
                         undefined
	 PT_LOAD     1   array element specifies a loadable segment, described
                         by p_filesz and p_memsz. The bytes from the file are
                         mapped to the beginning of the memory segment. If the
                         segment's memory size (p_memsz) is larger than the
	                 file size (p_filesz), the extra bytes are defined to
	                 hold the value 0 and to follow the segment's initialized
	                 area. The file size may not be larger than the memory
                         size. Loadable segment entries in the program header
	                 table appear in ascending order, sorted on the p_vaddr
                         member
	 PT_DYNAMIC   2  array element specifies dynamic linking information
	 PT_INTERP    3  array element specifies the location and size of a 
                         null-terminated path name to invoke as an interpreter.
	                 This segment type is meaningful only for executable
                         files (though it may occur for shared objects); it 
                         may not occur more than once in a file. If it is
                         present, it must precede any loadable segment entry.
	 PT_NOTE      4  array element specifies the location and size of 
                         auxiliary information
	 PT_SHLIB     5  this segment type is reserved but has unspecified
                         semantics. Programs that contain an array element of
	                 this type do not conform to the ABI
	 PT_PHDR      6  array element, if present, specifies the location and
	                 size of the program header table itself, both in the
                         file and in the memory image of the program. This 
                         segment may not occur more than once in a file. 
                         Moreover, it may occur only if the program header table
                         is part of the memory image of the program. If it is
                         present, it must precede any loadable segment entry.
	 PT_TLS       7  array element specifies the Tread-Local Storage
                         template. Implementations need not support this program
	                 table entry.
	 PT_LOOS - PT_HIOS values in this inclusive range are reserved for
                           operating system-specific semantics.
	 PT_LOPROC - PT_HIPROC values in this inclusive range are reserved for
                               processor-specific semantics. 
	 --------------------------------------------------------------------- *)
      p_type <- input#read_doubleword ;

      (* 4, 4, p_offset ------------------------------------------------------
	 Gives the offset from the beginning of the file at which the first 
	 byte of the segment resides
	 --------------------------------------------------------------------- *)
      p_offset <- input#read_doubleword ;

      (* 8, 4, p_vaddr -------------------------------------------------------
	 Gives the virtual address at which the first byte of the segment resides
	 in memory
	 --------------------------------------------------------------------- *)
      p_vaddr <- input#read_doubleword ;

      (* 12, 4, p_paddr ------------------------------------------------------
	 On systems for which physical addressing is relevant, this member is
	 reserved for the segment's physical address.
	 Because System V ignores physical address for application programs,
	 this member has unspecified contents for executable files and shared
	 objects 
	 --------------------------------------------------------------------- *)
      p_paddr <- input#read_doubleword ;

      (* 16, 4, filesz -------------------------------------------------------
	 Gives the number of bytes in the file image of the segment; may be zero
	 --------------------------------------------------------------------- *)
      p_filesz <- input#read_doubleword ;

      (* 20, 4, memsz --------------------------------------------------------
	 Gives the number of bytes in the memory image of the segment; may be zero
	 --------------------------------------------------------------------- *)
      p_memsz <- input#read_doubleword ;

      (* 24, 4, flags --------------------------------------------------------
	 Flags relevant to the segment.
	 none            0  All access denied
	 PF_X            1  Execute only (read, execute)
	 PF_W            2  Write only (read, write, execute)
	 PF_R            4  Read only (read, execute)
	 --------------------------------------------------------------------- *)
      p_flags <- input#read_doubleword ;

      (* 28, 4, p_align ------------------------------------------------------
	 Loadable process segments must have congruent values for p_vaddr and
	 p_offset, modulo the page size. This member gives the value to which 
	 the segments are aligned in memory and in the file. Values 0 and 1 mean
	 no alignment is required. Otherwise, p_align should be a positive,
	 integral power of 2, and p_vaddr should equal p_offset, modulo p_align
	 --------------------------------------------------------------------- *)
      p_align <- input#read_doubleword
    end

  method get_type = p_type
  
  method get_offset = p_offset

  method get_vaddr = p_vaddr

  method get_paddr = p_paddr

  method get_file_size = p_filesz

  method get_memory_size = p_memsz

  method get_flags = p_flags

  method get_align = p_align

  method get_program_header_type = doubleword_to_elf_program_header_type p_type

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    begin
      setx "p_type" p_type ;
      setx "p_offset" p_offset ;
      setx "p_vaddr" p_vaddr ;
      setx "p_paddr" p_paddr ;
      setx "p_filesz" p_filesz ;
      setx "p_memsz" p_memsz ;
      setx "p_flags" p_flags ;
      setx "p_align" p_align 
    end

  method read_xml (node:xml_element_int) =
    let get = node#getAttribute in
    let has = node#hasNamedAttribute in
    let getx t = if has t then string_to_doubleword (get t) else wordzero in
    begin
      p_type <- getx "p_type" ;
      p_offset <- getx "p_offset" ;
      p_vaddr <- getx "p_vaddr" ;
      p_paddr <- getx "p_paddr" ;
      p_filesz <- getx "p_filesz" ;
      p_memsz <- getx "p_memsz" ;
      p_flags <- getx "p_flags" ;
      p_align <- getx "p_align"
    end

  method toPretty = LBLOCK [
    STR "Type               : " ; STR (elf_program_header_type_to_string 
                                    self#get_program_header_type) ; NL ;
    STR "Offset             : " ; p_offset#toPretty ; NL ;
    STR "Virtual address    : " ; p_vaddr#toPretty ; NL ;
    STR "Physical address   : " ; p_paddr#toPretty ; NL ;
    STR "File size          : " ; p_filesz#toPretty ; STR " (" ;
                                  INT p_filesz#to_int ; STR ")" ; NL ;
    STR "Memory size        : " ; p_memsz#toPretty ; STR " (" ;
                                  INT p_memsz#to_int ; STR ")" ; NL ;
    STR "Flags              : " ; p_flags#toPretty ; NL ;
    STR "Alignment          : " ; p_align#toPretty ; NL ]


end

let mk_elf_program_header () = new elf_program_header_t
