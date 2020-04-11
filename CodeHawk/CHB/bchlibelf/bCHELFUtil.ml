(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes

(* bchlibelf *)
open BCHELFTypes

let makeOffsetString
      ?(hexSize=wordzero) (hexOffset:doubleword_int) (file_as_string: string) () =
  let offset = hexOffset#to_int in
  let size = hexSize#to_int in
  if size > 0 then
    let len = String.length file_as_string in
    if offset > len then
      let hexLen = int_to_doubleword len in
      begin
	ch_error_log#add "invalid argument"
	  (LBLOCK [ STR "Unable to return input at offset " ; hexOffset#toPretty ;
		    STR " -- file size = " ; hexLen#toPretty ]);
	pr_debug [LBLOCK [ STR "Unable to return input at offset " ; hexOffset#toPretty ;
			   STR " -- file size = " ; hexLen#toPretty ]];
	raise (Invalid_argument "assembly_xreference_t#get_exe_string_at_offset")
      end
    else
      if offset + size > len then
	let sizeAvailable = len - offset in
	begin
	  ch_error_log#add
            "continue operation with error"
	    (LBLOCK [ STR "Unable to return the requested size " ;
                      STR " (" ; INT size ; STR " ); " ;
		      STR "only returning " ; INT sizeAvailable ; STR ")" ; NL ] ) ;
	  string_suffix file_as_string offset 
	end
      else
	String.sub file_as_string offset size
  else
    string_suffix file_as_string offset

let makeOffsetInput
      ?(hexSize=wordzero) (hexOffset:doubleword_int) (file_as_string: string) () =
  IO.input_string (makeOffsetString ~hexSize:hexSize hexOffset file_as_string ())

let memoize fn = 
  let cache = Hashtbl.create 10 in
  fun n ->
    if Hashtbl.mem cache n then
      Hashtbl.find cache n
    else
      let result = fn n in
      Hashtbl.add cache n result; result

(*
  Decode unsigned LEB128 number:
  result = 0;
  shift = 0;
  while(true) {
  byte = next byte in input;
  result |= (low order 7 bits of byte << shift);
  if (high order bit of byte == 0)
  break;
  shift += 7;
  }
  Decode signed LEB128 number:
  result = 0;
  shift = 0;
  size = no. of bits in signed integer;
  while(true) {
  byte = next byte in input;
  result |= (low order 7 bits of byte << shift);
  shift += 7;
  /* sign bit of byte is 2nd high order bit (0x40) */
  if (high order bit of byte == 0)
  break;
  }
  if ((shift < size) && (sign bit of byte is set))
  /* sign extend */
  result |= - (1 << shift);
*)

let decodeUnsignedLEB128 input =
  let result = ref 0 in
  let shift = ref 0 in
  let ongoing = ref true in
  while !ongoing do
    let byte = IO.read_byte input in
    result := !result lor ((byte land 0x7f) lsl !shift); (* 7f has all bits set except the highest *)
    shift := !shift + 7;
    ongoing := (byte land 0x80) = 0x80; (* 0x80 has only the highest bit set *)
  done;
  !result

let decodeSignedLEB128 input =
  let result = ref 0 in
  let shift = ref 0 in
  let size = 32 in
  let ongoing = ref true in
  let byte = ref 0 in
  while !ongoing do
    byte := IO.read_byte input;
    result := !result lor ((!byte land 0x7f) lsl !shift);
    shift := !shift + 7;
    ongoing := (!byte land 0x80) = 0x80;
  done;
  if ((!shift < size) && ((!byte land 0x40) = 0x40)) (* sign bit of byte is 2nd high order bit (0x40) *)
  then !result lor -(1 lsl !shift)
  else !result


let doubleword_to_elf_section_header_type v =
  match v#to_int with
  | 0 -> SHT_NullSection
  | 1 -> SHT_ProgBits
  | 2 -> SHT_SymTab
  | 3 -> SHT_StrTab
  | 4 -> SHT_Rela
  | 5 -> SHT_Hash
  | 6 -> SHT_Dynamic
  | 7 -> SHT_Note
  | 8 -> SHT_NoBits
  | 9 -> SHT_Rel
  | 10 -> SHT_ShLib
  | 11 -> SHT_DynSym
  | 14 -> SHT_InitArray
  | 15 -> SHT_FiniArray
  | 16 -> SHT_PreinitArray
  | 17 -> SHT_Group
  | 18 -> SHT_SymTabShndx
  | _ -> 
    if (string_to_doubleword "0x60000000")#le v &&
      v#lt (string_to_doubleword "0x70000000") then SHT_OSSection v
    else if (string_to_doubleword "0x70000000")#le v &&
	v#lt (string_to_doubleword "0x80000000") then SHT_ProcSection v
    else if (string_to_doubleword "0x80000000")#le v &&
	v#le (string_to_doubleword "0xffffffff") then SHT_UserSection v
    else SHT_UnknownType v

let num_to_dynamic_tag i = DT_Needed      (* TBD *)

let elf_section_header_type_to_string = function
  | SHT_NullSection -> "SHT_NULL"
  | SHT_ProgBits -> "SHT_PROGBITS"
  | SHT_SymTab -> "SHT_SYMTAB"
  | SHT_StrTab -> "SHT_STRTAB"
  | SHT_Rela -> "SHT_RELA"
  | SHT_Hash -> "SHT_HASH"
  | SHT_Dynamic -> "SHT_DYNAMIC"
  | SHT_Note -> "SHT_NOTE"
  | SHT_NoBits -> "SHT_NOBITS"
  | SHT_Rel -> "SHT_REL"
  | SHT_ShLib -> "SHT_SHLIB"
  | SHT_DynSym -> "SHT_DYNSYM"
  | SHT_InitArray -> "SHT_INIT_ARRAY"
  | SHT_FiniArray -> "SHT_FINI_ARRAY"
  | SHT_PreinitArray -> "SHT_PREINIT_ARRAY"
  | SHT_Group -> "SHT_GROUP"
  | SHT_SymTabShndx -> "SHT_SYMTAB_SHNDX"
  | SHT_OSSection v -> "SHT_OS(" ^ v#to_fixed_length_hex_string ^ ")"
  | SHT_ProcSection v -> "SHT_PROC(" ^ v#to_fixed_length_hex_string ^ ")"
  | SHT_UserSection v -> "SHT_USER(" ^ v#to_fixed_length_hex_string ^ ")"
  | SHT_UnknownType v -> "SHT_UNKNOWN(" ^ v#to_fixed_length_hex_string ^ ")"
                       
let string_to_elf_section_header_type (s:string) =
  match s with
  | "SHT_NULL" -> SHT_NullSection
  | "SHT_PROGBITS" -> SHT_ProgBits
  | "SHT_SYMTAB" -> SHT_SymTab
  | "SHT_STRTAB" -> SHT_StrTab
  | "SHT_RELA"   -> SHT_Rela
  | "SHT_HASH"   -> SHT_Hash
  | "SHT_DYNAMIC" -> SHT_Dynamic
  | "SHT_NOTE"    -> SHT_Note
  | "SHT_NOBITS"  -> SHT_NoBits
  | "SHT_REL"     -> SHT_Rel
  | "SHT_SHLIB"   -> SHT_ShLib
  | "SHT_DYNSYM"  -> SHT_DynSym
  | "SHT_INIT_ARRAY" -> SHT_InitArray
  | "SHT_FINI_ARRAY" -> SHT_FiniArray
  | "SHT_PREINIT_ARRAY" -> SHT_PreinitArray
  | "SHT_GROUP" -> SHT_Group
  | "SHT_SYMTAB_SHNDX" -> SHT_SymTabShndx
  | _ -> SHT_UnknownType wordzero

let write_xml_elf_section_header_type (node:xml_element_int) (t:elf_section_header_type_t) =
  let sett = node#setAttribute "type" in
  let setx x = node#setAttribute "value" x#to_hex_string in
  match t with
  | SHT_OSSection v   -> begin sett "SHT_OS"   ; setx v end
  | SHT_ProcSection v -> begin sett "SHT_PROC" ; setx v end
  | SHT_UserSection v -> begin sett "SHT_USER" ; setx v end
  | SHT_UnknownType v -> begin sett "SHT_UNKNOWN" ; setx v end
  | _ -> sett (elf_section_header_type_to_string t)

let read_xml_elf_section_header_type (node:xml_element_int):elf_section_header_type_t =
  let getx () = string_to_doubleword (node#getAttribute "value") in
  let sType = node#getAttribute "type" in
  match sType with
  | "SHT_OS" -> SHT_OSSection (getx ())
  | "SHT_PROC" -> SHT_ProcSection (getx ())
  | "SHT_USER" -> SHT_UserSection (getx ())
  | "SHT_UNKNOWN" -> SHT_UnknownType (getx ())
  | _ -> string_to_elf_section_header_type sType

let doubleword_to_elf_program_header_type v =
  match v#to_int with
  | 0 -> PT_Null
  | 1 -> PT_Load
  | 2 -> PT_Dynamic
  | 3 -> PT_Interpreter
  | 4 -> PT_Note
  | 6 -> PT_Reference
  | 7 -> PT_ThreadLocalStorage
  | _ ->
    if (string_to_doubleword "0x70000000")#le v then
      PT_ProcSpecific v
    else if (string_to_doubleword "0x6000000")#le v then
      PT_OSSpecific v
    else
      raise (BCH_failure 
	       (LBLOCK [ STR "invalid program header type: " ; v#toPretty]))
	

let elf_program_header_type_to_string = function
  | PT_Null -> "PT_NULL"
  | PT_Load -> "PT_LOAD"
  | PT_Dynamic  -> "PT_DYNAMIC"
  | PT_Interpreter -> "PT_INTERP"
  | PT_Note -> "PT_NOTE"
  | PT_Reference -> "PT_PHDR"
  | PT_ThreadLocalStorage -> "PT_TLS"
  | PT_OSSpecific v -> "PT_OS_" ^ v#to_hex_string
  | PT_ProcSpecific v -> "PT_PROC_" ^ v#to_hex_string

let elf_section_to_raw_section (s:elf_section_t):elf_raw_section_int =
  match s with
  | ElfStringTable t -> (t :> elf_raw_section_int)
  | ElfSymbolTable t -> (t :> elf_raw_section_int)
  | ElfDynamicSymbolTable t -> (t :> elf_raw_section_int)
  | ElfRelocationTable t -> (t :> elf_raw_section_int)
  | ElfDynamicTable t -> (t :> elf_raw_section_int)
  | ElfProgramSection s -> (s :> elf_raw_section_int)
  | ElfOtherSection s -> s

let elf_section_to_string_table (s:elf_section_t):elf_string_table_int =
  match s with
  | ElfStringTable t -> t
  | _ ->
     raise (BCH_failure
           (LBLOCK [ STR "section is not a string table" ]))

let elf_section_to_symbol_table (s:elf_section_t):elf_symbol_table_int =
  match s with
  | ElfSymbolTable t -> t
  | ElfDynamicSymbolTable t -> t
  | _ ->
     raise (BCH_failure
           (LBLOCK [ STR "section is not a symbol table" ]))

let elf_section_to_relocation_table (s:elf_section_t):elf_relocation_table_int =
  match s with
  | ElfRelocationTable t -> t
  | _ ->
     raise (BCH_failure
           (LBLOCK [ STR "section is not a relocation table" ]))

let elf_section_to_dynamic_table (s:elf_section_t):elf_dynamic_table_int =
  match s with
  | ElfDynamicTable t -> t
  | _ ->
     raise (BCH_failure
           (LBLOCK [ STR "section is not a dynamic table" ]))
