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
open CHLogger
open CHNumRecordTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings

(* bchlibelf *)
open BCHELFDictionary
open BCHELFSection
open BCHELFTypes

module TR = CHTraceResult


class elf_relocation_table_entry_t (index:int):elf_relocation_table_entry_int =
object (self)

  val mutable symbol = None
  val mutable r_offset = wordzero
  val mutable r_info = wordzero

  method id = index

  method read (ch:pushback_stream_int) =
    try
      begin
        (* 0, 4, Offset --------------------------------------------------------
           This member gives the location at which to apply the relocation action.
           For a relocatable file, the value is the byte offset from the beginning
           of the section to the storage unit affected by the relocation. For an
           executable file or a shared object, the value is the virtual address of
           the storage unit affected by the relocation.
           ---------------------------------------------------------------------- *)
        r_offset <- ch#read_doubleword;

        (* 4, 4, Info -----------------------------------------------------------
           This member gives both the symbol table index with respect to which the
           relocation must be made, and the type of relocation to apply.
           For example,
           a call instruction's relocation entry would hold the symbol table index
           of the function being called. If the index is STN_UNDEF, the undefined
           symbol index, the relocation uses 0 as the "symbol value." Relocation
           types are processor-specific. When the text refers to a relocation
           entry's relocation type or symbol table index, it means the result of
           applying ELF32_R_TYPE or ELF32_R_SYM, respectively, to the entry's
           r_info member.
           #define ELF32_R_SYM(i) ((i)>>8)
           #define ELF32_R_TYPE(i) ((unsigned char)(i))
           #define ELF32_R_INFO(s,t) (((s)<<8)+(unsigned char)(t))
           ---------------------------------------------------------------------- *)
        r_info <- ch#read_doubleword
      end
    with
    | IO.No_more_input ->
       begin
         ch_error_log#add "no more input" (STR "elf_symbol_table_entry_t#read");
         raise IO.No_more_input
       end

  method get_symbol_index = r_info#to_int lsr 8

  method get_type = r_info#to_int land 255

  method set_symbol (s:elf_symbol_table_entry_int) = symbol <- Some s

  method get_address = r_offset

  method has_offset (dw:doubleword_int) = dw#equal r_offset

  method get_symbol_string =
    match symbol with
    | Some s -> s#get_name
    | _ -> raise (BCH_failure (STR "symbol not found"))

  method has_symbol = match symbol with Some _ -> true | _ -> false

  method get_symbol =
    match symbol with
    | Some s -> s
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Relocation entry ";
                 INT index;
                 STR " does not have a symbol"]))

  method is_function =
    self#has_symbol && self#get_symbol#is_function

  method has_address = not (r_offset#equal wordzero)

  method to_rep_record =
    let tags = [r_offset#to_hex_string; r_info#to_hex_string] in
    let args = [self#get_type] in
    match symbol with
    | Some s ->
       let nameix = elfdictionary#index_string s#get_name in
       let tags = tags @ [s#get_value#to_hex_string] in
       let args = args @ [nameix] in
       (tags, args)
    | _ -> (tags, args)


end


class elf_relocation_table_t
        (s:string)
        (entrysize:int)
        (vaddr:doubleword_int):elf_relocation_table_int =
object

  val mutable entries = []

  inherit elf_raw_section_t s vaddr

  method read =
    try
      let ch =
        make_pushback_stream ~little_endian:system_info#is_little_endian s in
      let n = (String.length s) / entrysize in
      let c = ref 0 in
      begin
        while !c < n do
          let entry = new elf_relocation_table_entry_t !c in
          begin
            entry#read ch ;
            c :=  !c + 1 ;
            entries <- entry :: entries
          end
        done;
      end
    with
    | IO.No_more_input ->
       ch_error_log#add
         "no more input"
         (LBLOCK [STR "Unable to read the relocation table"])

  method set_symbols (t:elf_symbol_table_int) =
    List.iter (fun e ->
        e#set_symbol (t#get_symbol e#get_symbol_index)) entries

  method has_offset (dw:doubleword_int) =
    List.fold_left (fun result e -> result || e#has_offset dw) false entries

  method get_offset_symbol (dw:doubleword_int) =
    try
      let e = List.find (fun e ->  e#has_offset dw) entries in
      e#get_symbol_string
    with
    | Not_found ->
       raise
         (BCH_failure
            (LBLOCK [STR "Error in get_offset_symbol: "; dw#toPretty]))

  method set_function_entry_points =
    List.iter (fun e ->
        if e#is_function
           && e#has_address
           && (system_settings#is_arm || system_settings#is_mips) then
          let fndata = functions_data#add_function e#get_address in
          begin
            fndata#set_library_stub;
            if e#has_symbol then
              let _ =
                chlog#add
                  "set elf stub name"
                  (LBLOCK [
                       e#get_address#toPretty;
                       STR ": ";
                       STR e#get_symbol_string]) in
              fndata#add_name e#get_symbol_string
          end
      ) entries

  method write_xml_entries (node:xml_element_int) =
    let table = mk_num_record_table "relocation-table" in
    begin
      List.iter (fun e -> table#add e#id e#to_rep_record) entries;
      table#write_xml node
    end

end


let mk_elf_relocation_table s h vaddr =
  let entrysize = h#get_entry_size#to_int in
  let table = new elf_relocation_table_t s entrysize vaddr in
  begin
    table#read;
    table
  end


let read_xml_elf_relocation_table (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  let vaddr = TR.tget_ok (string_to_doubleword (node#getAttribute "vaddr")) in
  let entrysize = node#getIntAttribute "entrysize" in
  let table = new elf_relocation_table_t s entrysize vaddr in
  begin
    table#read;
    table
  end
