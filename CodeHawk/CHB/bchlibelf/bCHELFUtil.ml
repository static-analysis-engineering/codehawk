(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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
open BCHSystemInfo

(* bchlibelf *)
open BCHELFTypes

module H = Hashtbl
module TR = CHTraceResult


(* Unsafe call to string to doubleword; may raise Invalid_argument. *)
let constant_string_to_doubleword (s: string) =
  TR.tget_ok (string_to_doubleword s)


let makeOffsetString
      ?(hexSize=wordzero) (hexOffset:doubleword_int) (file_as_string: string) () =
  let offset = hexOffset#to_int in
  let size = hexSize#to_int in
  if size > 0 then
    let len = String.length file_as_string in
    if offset > len then
      let hexLen = TR.tget_ok (int_to_doubleword len) in
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [
               STR "Unable to return input at offset ";
               hexOffset#toPretty;
	       STR " -- file size = ";
               hexLen#toPretty]);
	pr_debug [
            LBLOCK [
                STR "Unable to return input at offset ";
                hexOffset#toPretty;
		STR " -- file size = ";
                hexLen#toPretty]];
	raise
          (Invalid_argument "assembly_xreference_t#get_exe_string_at_offset")
      end
    else
      if offset + size > len then
	let sizeAvailable = len - offset in
	begin
	  ch_error_log#add
            "continue operation with error"
	    (LBLOCK [
                 STR "Unable to return the requested size ";
                 STR " (";
                 INT size;
                 STR " ); ";
		 STR "only returning ";
                 INT sizeAvailable;
                 STR ")";
                 NL]);
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
    result :=
      !result lor ((byte land 0x7f) lsl !shift); (* 7f has all bits set except the highest *)
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
  (* sign bit of byte is 2nd high order bit (0x40) *)
  if ((!shift < size) && ((!byte land 0x40) = 0x40))
  then !result lor -(1 lsl !shift)
  else !result


let section_header_tag_table = H.create 31
let mips_section_header_tag_table = H.create 3


let _ =
  List.iter (fun (dw,tag,tagstr) ->
      H.add section_header_tag_table dw (tag,tagstr))
            [ ("0x0", SHT_NullSection, "SHT_NULL")
            ; ("0x1", SHT_ProgBits, "SHT_PROGBITS")
            ; ("0x2", SHT_SymTab, "SHT_SYMTAB")
            ; ("0x3", SHT_StrTab, "SHT_STRTAB")
            ; ("0x4", SHT_Rela, "SHT_RELA")
            ; ("0x5", SHT_Hash, "SHT_HASH")
            ; ("0x6", SHT_Dynamic, "SHT_DYNAMIC")
            ; ("0x7", SHT_Note, "SHT_Note")
            ; ("0x8", SHT_NoBits, "SHT_NOBITS")
            ; ("0x9", SHT_Rel, "SHT_REL")
            ; ("0xa", SHT_ShLib, "SHT_SHLIB")
            ; ("0xb", SHT_DynSym, "SHT_DYNSYM")
            ; ("0xe", SHT_InitArray, "SHT_INITARRAY")
            ; ("0xf", SHT_FiniArray, "SHT_FINIARRAY")
            ; ("0x10", SHT_PreinitArray, "SHT_PREINITARRAY")
            ; ("0x11", SHT_Group, "SHT_GROUP")
            ; ("0x12", SHT_SymTabShndx, "SHT_SYMTAB_SHNDX")
            ; ("0x6ffffffd", SHT_GNU_verdef, "SHT_GNU_verdef")
            ; ("0x6ffffffe", SHT_GNU_verneed, "SHT_GNU_verneed")
            ; ("0x6fffffff", SHT_GNU_versym, "SHT_GNU_versym")
            ]

let _ =
  List.iter (fun (dw,tag,tagstr) ->
      H.add mips_section_header_tag_table dw (tag,tagstr))
            [ ("0x70000006", SHT_MIPS_RegInfo, "SHT_MIPS_REGINFO")
            ]


let doubleword_to_elf_section_header_tag_record (v:doubleword_int) =
  let tag = v#to_hex_string in
  let default sht shtstr =
    (sht, shtstr ^ "(" ^ v#to_fixed_length_hex_string ^ ")") in
  if H.mem section_header_tag_table tag then
    H.find section_header_tag_table tag
  else if system_info#is_mips then
    if H.mem mips_section_header_tag_table tag then
      H.find mips_section_header_tag_table tag
    else
      if (constant_string_to_doubleword "0x60000000")#le v
         && v#lt (constant_string_to_doubleword "0x70000000") then
        default (SHT_OSSection v) "SHT_OS"
      else if (constant_string_to_doubleword "0x70000000")#le v
              && v#lt (constant_string_to_doubleword "0x80000000") then
        default (SHT_ProcSection v) "SHT_PROC"
      else if (constant_string_to_doubleword "0x80000000")#le v
              && v#le (constant_string_to_doubleword "0xffffffff") then
        default (SHT_UserSection v) "SHT_USER"
      else
        default (SHT_UnknownType v) "SHT_MIPS_UNKNOWN"
  else
    default (SHT_UnknownType v) "SHT_UNKNOWN"


let doubleword_to_elf_section_header_type (v:doubleword_int) =
  let (shtag,_) = doubleword_to_elf_section_header_tag_record v in shtag

let doubleword_to_elf_section_header_string (v:doubleword_int) =
  let (_,s) = doubleword_to_elf_section_header_tag_record v in s

let dynamic_tag_table = H.create 31
let mips_dynamic_tag_table = H.create 31

let _ =
  List.iter
    (fun (dw,tag,tagvalue,tagstr) ->
      H.add dynamic_tag_table dw (tag,tagvalue,tagstr))
    [ ("0x0", DT_Null, DTV_d_none, "DT_NULL")
    ; ("0x1", DT_Needed, DTV_d_val, "DT_NEEDED")
    ; ("0x2", DT_PltRelSz, DTV_d_val, "DT_PLTRELSZ")
    ; ("0x3", DT_PltGot, DTV_d_ptr, "DT_PLTGOT")
    ; ("0x4", DT_Hash, DTV_d_ptr, "DT_HASH")
    ; ("0x5", DT_StrTab, DTV_d_ptr, "DT_STRTAB")
    ; ("0x6", DT_SymTab, DTV_d_ptr, "DT_SYMTAB")
    ; ("0x7", DT_Rela, DTV_d_ptr, "DT_RELA")
    ; ("0x8", DT_RelaSz, DTV_d_val, "DT_RELASZ")
    ; ("0x9", DT_RelaEnt, DTV_d_val, "DT_RELAENT")
    ; ("0xa", DT_StrSz, DTV_d_val, "DT_STRSZ")
    ; ("0xb", DT_SymEnt, DTV_d_val, "DT_SYMENT")
    ; ("0xc", DT_Init, DTV_d_ptr, "DT_INIT")
    ; ("0xd", DT_Fini, DTV_d_ptr, "DT_FINI")
    ; ("0xe", DT_SoName, DTV_d_val, "DT_SONAME")
    ; ("0xf", DT_RPath, DTV_d_val, "DT_RPATH")
    ; ("0x10", DT_Symbolic, DTV_d_none, "DT_SYMBOLIC")
    ; ("0x11", DT_Rel, DTV_d_ptr, "DT_REL")
    ; ("0x12", DT_RelSz, DTV_d_val, "DT_RELSZ")
    ; ("0x13", DT_RelEnt, DTV_d_val, "DT_RELENT")
    ; ("0x14", DT_PltRel, DTV_d_val, "DT_PLTREL")
    ; ("0x15", DT_Debug, DTV_d_ptr, "DT_DEBUG")
    ; ("0x16", DT_TextRel, DTV_d_none, "DT_TEXTREL")
    ; ("0x17", DT_JmpRel, DTV_d_ptr, "DT_JMPREL")
    ; ("0x6ffffff0", DT_VerSym, DTV_d_ptr, "DT_VERSYM") 
    ; ("0x6ffffffe", DT_VerNeed, DTV_d_ptr, "DT_VERNEED")
    ; ("0x6fffffff", DT_VerNeedNum, DTV_d_val, "DT_VERNEEDNUM")
    ; ("0x70000000", DT_LoProc, DTV_d_none, "DT_LOPROC")
    ; ("0x7fffffff", DT_HiProc, DTV_d_none, "DT_HIPROC")
    ]

let _ =
  List.iter
    (fun (dw,tag,tagvalue,tagstr) ->
      H.add mips_dynamic_tag_table dw (tag,tagvalue,tagstr))
    [ ("0x70000001", DT_MIPS_Rld_Version, DTV_d_val, "DT_MIPS_RLD_VERSION")
    ; ("0x70000005", DT_MIPS_Flags, DTV_d_val, "DT_MIPS_FLAGS")
    ; ("0x70000006", DT_MIPS_Base_Address, DTV_d_ptr, "DT_MIPS_BASE_ADDRESS")
    ; ("0x7000000a", DT_MIPS_LocalGotNo, DTV_d_val, "DT_MIPS_LOCALGOTNO")
    ; ("0x70000011", DT_MIPS_SymTabNo, DTV_d_val, "DT_MIPS_SYMTABNO")
    ; ("0x70000012", DT_MIPS_UnrefExtNo, DTV_d_val, "DT_MIPS_UNREFEXTNO")
    ; ("0x70000013", DT_MIPS_GotSym,DTV_d_val, "DT_MIPS_GOTSYM")
    ; ("0x70000016", DT_MIPS_Rld_Map, DTV_d_ptr, "DT_MIPS_RLD_MAP")
    ]


let doubleword_to_dynamic_tag_record (tag:doubleword_int) =
  let s_tag = tag#to_hex_string in  
  let default = (DT_Unknown s_tag, DTV_d_none, "DT_Unknown:" ^ s_tag) in
  if H.mem dynamic_tag_table s_tag then
    H.find dynamic_tag_table s_tag
  else if system_info#is_mips then
    if H.mem mips_dynamic_tag_table s_tag then
      H.find mips_dynamic_tag_table s_tag
    else
      begin
        chlog#add "dynamic tag unknown" (STR s_tag);
        default
      end
  else
    begin
      chlog#add "dynamic tag unknown" (STR s_tag);
      default
    end


let doubleword_to_dynamic_tag (tag:doubleword_int) =
  let (dtag,_,_) = doubleword_to_dynamic_tag_record tag in dtag


let doubleword_to_dynamic_tag_name (tag:doubleword_int) =
  let (_,_,s_tag) = doubleword_to_dynamic_tag_record tag in s_tag


let doubleword_to_dynamic_tag_value (tag:doubleword_int) =
  let (_,dval,_) = doubleword_to_dynamic_tag_record tag in dval


let arm_relocation_tag_table = H.create 93

(* rtype: S: Static, D: Dynamic, Dep: Deprecated, Obs: Obsolete *)
(* rclass: A: Arm, D: Data, T32: Thumb32, T16: Thumb16, M: Miscellaneous *)
let _ =
  List.iter
    (fun (dw, tag, tagstr, rtype, rclass) ->
      H.add arm_relocation_tag_table dw (tag, tagstr, rtype, rclass))
    [("0x0", R_ARM_NONE, "R_ARM_NONE", "S", "M");
     ("0x1", R_ARM_PC24, "R_ARM_PC24", "Dep", "A");
     ("0x2", R_ARM_ABS32, "R_ARM_ABS32", "S", "D");
     ("0x3", R_ARM_REL32, "R_ARM_REL32", "S", "D");
     ("0x4", R_ARM_LDR_PCG0, "R_ARM_LDR_PCG0", "S", "A");
     ("0x5", R_ARM_ABS16, "R_ARM_ABS16", "S", "D");
     ("0x6", R_ARM_ABS12, "R_ARM_ABS12", "S", "A");
     ("0x7", R_ARM_THM_ABS5, "R_ARM_THM_ABS5", "S", "T16");
     ("0x8", R_ARM_ABS8, "R_ARM_ABS8", "S", "D");
     ("0x9", R_ARM_SBREL32, "R_ARM_SBREL32", "S", "D");
     ("0xa", R_ARM_THM_CALL, "R_ARM_THM_CALL", "S", "T32");
     ("0xb", R_ARM_THM_PC8, "R_ARM_THM_PC8", "S", "T16");
     ("0xc", R_ARM_BREL_ADJ, "R_ARM_BREL_ADJ", "D", "D");
     ("0xd", R_ARM_TLS_DESC, "R_ARM_TLS_DESC", "D", "D");
     ("0xe", R_ARM_THM_SW18, "R_ARM_THM_SW18", "Obs", "X");
     ("0xf", R_ARM_XPC25, "R_ARM_XPC25", "Obs", "X");
     ("0x10", R_ARM_THM_XPC22, "R_ARM_XPC22", "Obs", "X");
     ("0x11", R_ARM_TLS_DTPMOD32, "R_ARM_TLS_DTPMOD32", "D", "D");
     ("0x12", R_ARM_TLS_DTPOFF32, "R_ARM_TLS_DTPOFF32", "D", "D");
     ("0x13", R_ARM_TLS_TPOFF32, "R_ARM_TLS_TPOFF32", "D", "D");
     ("0x14", R_ARM_COPY, "R_ARM_COPY", "D", "D");
     ("0x15", R_ARM_GLOB_DAT, "R_ARM_GLOB_DAT", "D", "D");
     ("0x16", R_ARM_JUMP_SLOT, "R_ARM_JUMP_SLOT", "D", "D");
     ("0x17", R_ARM_RELATIVE, "R_ARM_RELATIVE", "D", "D");
     ("0x18", R_ARM_GOTOFF32, "R_ARM_GOTOFF32", "S", "D");
     ("0x19", R_ARM_BASE_PREL, "R_ARM_BASE_PREL", "S", "D");
     ("0x1a", R_ARM_GOT_BREL, "R_ARM_GOT_BREL", "S", "D");
     ("0x1b", R_ARM_PLT32, "R_ARM_PLT32", "Dep", "A");
     ("0x1c", R_ARM_CALL, "R_ARM_CALL", "S", "A");
     ("0x1d", R_ARM_JUMP24, "R_ARM_JUMP24", "S", "A");
     ("0x1e", R_ARM_THM_JUMP24, "R_ARM_THM_JUMP24", "S", "T32");
     ("0x1f", R_ARM_BASE_ABS, "R_ARM_BASE_ABS", "S", "D");
     ("0x20", R_ARM_ALU_PCREL_7_0, "R_ARM_ALU_PCREL_7_0", "Obs", "X");
     ("0x21", R_ARM_ALU_PCREL_15_8, "R_ARM_ALU_PCREL_15_8", "Obs", "X");
     ("0x22", R_ARM_ALU_PCREL_23_15, "R_ARM_ALU_PCREL_23_15", "Obs", "X");
     ("0x23", R_ARM_LDR_SBREL_11_0_NC, "R_ARM_LDR_SBREL_11_0_NC", "Dep", "A");
     ("0x24", R_ARM_ALU_SBREL_19_12_NC, "R_ARM_ALU_SBREL_19_12_NC", "Dep", "A");
     ("0x25", R_ARM_ALU_SBREL_27_20_CK, "R_ARM_ALU_SBREL_27_20_CK", "Dep", "A");
     ("0x26", R_ARM_TARGET1, "R_ARM_TARGET1", "S", "M");
     ("0x27", R_ARM_SBREL31, "R_ARM_SBREL31", "Dep", "D");
     ("0x28", R_ARM_V4BX, "R_ARM_V4BX", "S", "M");
     ("0x29", R_ARM_TARGET2, "R_ARM_TARGET2", "S", "M");
     ("0x2a", R_ARM_PREL31, "R_ARM_PREL31", "S", "D");
     ("0x2b", R_ARM_MOVW_ABS_NC, "R_ARM_MOVW_ABS_NC", "S", "A");
     ("0x2c", R_ARM_MOVT_ABS, "R_ARM_MOVT_ABS", "S", "A");
     ("0x2d", R_ARM_MOVW_PREL_NC, "R_ARM_MOVW_PREL_NC", "S", "A");
     ("0x2e", R_ARM_MOVT_PREL, "R_ARM_MOVT_PREL", "S", "A");
     ("0x2f", R_ARM_THM_MOVW_ABS_NC, "R_ARM_THM_MOVW_ABS_NC", "S", "T32");
     ("0x30", R_ARM_THM_MOVT_ABS, "R_ARM_THM_MOVT_ABS", "S", "T32");
     ("0x31", R_ARM_THM_MOVW_PREL_NC, "R_ARM_THM_MOVW_PREL_NC", "S", "T32");
     ("0x32", R_ARM_THM_MOVT_PREL, "R_ARM_THM_MOVT_PREL", "S", "T32");
     ("0x33", R_ARM_THM_JUMP19, "R_ARM_THM_JUMP19", "S", "T32");
     ("0x34", R_ARM_THM_JUMP6, "R_ARM_THM_JUMP6", "S", "T16");
     ("0x35", R_ARM_THM_ALU_PREL_11_0, "R_ARM_THM_ALU_PREL_11_0", "S", "T32");
     ("0x36", R_ARM_THM_PC12, "R_ARM_THM_PC12", "S", "T32")
    ]


let doubleword_to_arm_relocation_tag_record (tag: doubleword_int) =
  let s_tag = tag#to_hex_string in
  let default = (R_ARM_Unknown s_tag, "R_ARM_Unknown:" ^ s_tag, "?", "?") in
  if H.mem arm_relocation_tag_table s_tag then
    H.find arm_relocation_tag_table s_tag
  else
    begin
      chlog#add "arm relocation tag unknown" (STR s_tag);
      default
    end


let doubleword_to_arm_relocation_tag (tag: doubleword_int) =
  let (dtag, _, _, _) = doubleword_to_arm_relocation_tag_record tag in dtag


let doubleword_to_arm_relocation_tag_name (tag: doubleword_int) =
  let (_, s, _, _) = doubleword_to_arm_relocation_tag_record tag in s


let doubleword_to_elf_program_header_type v =
  match v#to_hex_string with
  | "0x0" -> PT_Null
  | "0x1" -> PT_Load
  | "0x2" -> PT_Dynamic
  | "0x3" -> PT_Interpreter
  | "0x4" -> PT_Note
  | "0x6" -> PT_Reference
  | "0x7" -> PT_ThreadLocalStorage
  | "0x70000000" -> PT_RegInfo
  | _ ->
    if (constant_string_to_doubleword "0x70000000")#le v then
      PT_ProcSpecific v
    else if (constant_string_to_doubleword "0x6000000")#le v then
      PT_OSSpecific v
    else
      raise
        (BCH_failure
	   (LBLOCK [STR "invalid program header type: "; v#toPretty]))


let elf_program_header_type_to_string = function
  | PT_Null -> "PT_NULL"
  | PT_Load -> "PT_LOAD"
  | PT_Dynamic  -> "PT_DYNAMIC"
  | PT_Interpreter -> "PT_INTERP"
  | PT_Note -> "PT_NOTE"
  | PT_Reference -> "PT_PHDR"
  | PT_ThreadLocalStorage -> "PT_TLS"
  | PT_RegInfo -> "PT_REGINFO"
  | PT_OSSpecific v -> "PT_OS_" ^ v#to_hex_string
  | PT_ProcSpecific v -> "PT_PROC_" ^ v#to_hex_string


let elf_segment_to_raw_segment (s:elf_segment_t):elf_raw_segment_int =
  match s with
  | ElfDynamicSegment t ->  (t :> elf_raw_segment_int)
  | ElfOtherSegment t -> (t :> elf_raw_segment_int)


let elf_section_to_raw_section (s:elf_section_t):elf_raw_section_int =
  match s with
  | ElfStringTable t -> (t :> elf_raw_section_int)
  | ElfSymbolTable t -> (t :> elf_raw_section_int)
  | ElfDynamicSymbolTable t -> (t :> elf_raw_section_int)
  | ElfRelocationTable t -> (t :> elf_raw_section_int)
  | ElfDynamicTable t -> (t :> elf_raw_section_int)
  | ElfProgramSection s -> (s :> elf_raw_section_int)
  | ElfDebugARangesSection s -> (s :> elf_raw_section_int)
  | ElfDebugInfoSection s -> (s :> elf_raw_section_int)
  | ElfDebugAbbrevSection s -> (s :> elf_raw_section_int)
  | ElfDebugLocSection s -> (s :> elf_raw_section_int)
  | ElfDebugStringSection s -> (s :> elf_raw_section_int)
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


let elf_segment_to_dynamic_segment (s:elf_segment_t):elf_dynamic_segment_int =
  match s with
  | ElfDynamicSegment t -> t
  | _ ->
     raise (BCH_failure
           (LBLOCK [ STR "segment is not a dynamic segment"  ]))
