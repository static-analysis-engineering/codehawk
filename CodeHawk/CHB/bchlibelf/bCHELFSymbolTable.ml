(* =============================================================================
   CodeHawk Binary Analyzer
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDataBlock
open BCHDoubleword
open BCHFunctionData
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings

(* bchlibelf *)
open BCHELFDictionary
open BCHELFSection
open BCHELFTypes

module H = Hashtbl
module TR = CHTraceResult


class elf_symbol_table_entry_t (index:int):elf_symbol_table_entry_int =
object (self)

  val mutable name = ""
  val mutable st_name = wordzero
  val mutable st_value = wordzero
  val mutable st_size = wordzero
  val mutable st_info = 0
  val mutable st_other = 0
  val mutable st_shndx = 0

  method id = index

  method read (ch:pushback_stream_int) =
    try
      begin
        (* 0, 4, Name ----------------------------------------------------------
           This member holds an index into the object file's symbol string table,
           which holds the character representations of the symbol names. If the
           value is non-zero, it represents a string table index that gives the
           symbol name. Otherwise, the symbol table entry has no name.
           --------------------------------------------------------------------- *)
        st_name <- ch#read_doubleword;

        (* 4, 4, Value ---------------------------------------------------------
           This member gives the value of the associated symbol. Depending on the
           context, this may be an absolute value, an address, etc.
           --------------------------------------------------------------------- *)
        st_value <- ch#read_doubleword;

        (* 8, 4, Size ----------------------------------------------------------
           Many symbols have associated sizes. For example, a data object's size
           is the number of bytes contained in the object. This member holds 0 if
           the symbol has no size or an unknown size.
           --------------------------------------------------------------------- *)
        st_size <- ch#read_doubleword;

        (* 12, 1, Info ---------------------------------------------------------
           This member specifies the symbol's type and binding attributes. A list
           of the values and meanings appears below. The following code shows how
           to manipulate the values.
           #define ELF32_ST_BIND(i) ((i)>>4)
           #define ELF32_ST_TYPE(i) ((i)&0xf)
           #define ELF32_ST_INFO(b,t) (((b)<<4)+((t)&0xf))
           --------------------------------------------------------------------- *)
        st_info <- ch#read_byte;

        (* 13, 1, Other --------------------------------------------------------
           This member currently holds 0 and has no defined meaning.
           --------------------------------------------------------------------- *)
        st_other <- ch#read_byte;

        (* 14, 2, Section index ------------------------------------------------
           Every symbol table entry is "defined" in relation to some section;
           this member holds the relevant section header table index. As Figure
           1-7 and the related text describe, some section indexes indicate
           special meanings.
           --------------------------------------------------------------------- *)
        st_shndx <- ch#read_ui16;

      end
    with
    | IO.No_more_input ->
       begin
         ch_error_log#add "no more input" (STR "elf_symbol_table_entry_t#read") ;
         raise IO.No_more_input
       end

  method get_st_name = st_name

  method has_name = not (name = "")

  method set_name s = name <- s

  method get_name = name

  method get_st_binding = st_info lsr 4

  method get_st_type = st_info land 15

  method get_st_value = st_value

  method get_value = st_value

  method is_function = self#get_st_type = 2

  method has_address_value = not (st_value#equal wordzero)

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setx t x = set t x#to_hex_string in
    begin
      setx "name" st_name;
      setx "value" st_value;
      setx "size" st_size;
      seti "info" st_info;
      seti "other" st_other;
      seti "shndx" st_shndx;
      seti "ix" index;
    end

  method to_rep_record =
    let nameix = elfdictionary#index_string name in
    let tags = [
        st_name#to_hex_string;
        st_value#to_hex_string;
        st_size#to_hex_string] in
    let args = [nameix; st_info; st_other; st_shndx] in
    (tags,args)

end


class elf_symbol_table_t
        (s:string)
        (entrysize:int)
        (vaddr:doubleword_int):elf_symbol_table_int =
object (self)

  val entries = H.create 3

  inherit elf_raw_section_t s vaddr as super

  method read =
    try
      let ch =
        make_pushback_stream ~little_endian:system_info#is_little_endian s in
      let n = (String.length s) / entrysize in
      let c = ref 0 in
      begin
        while !c < n do
          let entry = new elf_symbol_table_entry_t !c in
          begin
            entry#read ch;
            H.add entries !c entry;
            c := !c + 1
          end
        done;
      end
    with
    | IO.No_more_input ->
       ch_error_log#add
         "no more input"
         (LBLOCK [STR "Unable to read the symbol table "])

  method set_symbol_names (t:elf_string_table_int) =
    if system_settings#is_mips || system_settings#is_arm then
      H.iter (fun _ e ->
          e#set_name (t#get_string e#get_st_name#to_int)) entries
    else
      H.iter (fun _ e ->
        let s_opt = t#get_string_at_address e#get_st_name in
        match s_opt with
        | Some s -> e#set_name s
        | _ -> ()) entries

  method set_function_entry_points =
    let align (a: int) (size: int): int = (a / size) * size in
    let align_dw dw = TR.tget_ok (int_to_doubleword (align dw#to_int 2)) in
    H.iter (fun _ e ->
        if e#is_function && e#has_address_value then
          let addr =
            let v = e#get_st_value in
            if system_settings#is_arm then
              align_dw v
            else
              v in
          ignore (functions_data#add_function addr)) entries

  method set_function_names =
    let align (a: int) (size: int): int = (a / size) * size in
    let align_dw dw = TR.tget_ok (int_to_doubleword (align dw#to_int 2)) in
    H.iter (fun _ e ->
        if e#is_function && e#has_address_value && e#has_name then
          let addr =
            let v = e#get_st_value in
            if system_settings#is_arm then
              align_dw v
            else
              v in
          (functions_data#add_function addr)#add_name e#get_name) entries

  method set_mapping_symbols =
    let symbols = H.create 13 in
    let _ =
      H.iter
        (fun _ e ->
          if e#get_st_binding = 0 && e#get_st_type = 0 && e#has_address_value then
            match e#get_name with
            | "$a" | "$a.0" | "$a.1" | "$a.2" | "$d" | "$d.1" | "$t" ->
               H.add symbols e#get_st_value#index e#get_name
            | _ -> ()) entries in
    let symbols =
      List.sort Stdlib.compare (H.fold (fun k v a -> (k, v) :: a) symbols []) in
    let indata = ref None in
    let inarm = ref true in
    let make_db addr =
      match !indata with
      | Some addr_d ->
         log_titer
           (mk_tracelog_spec
              ~tag:"disassembly"
              "elf_symbol_table#set_mapping_symbols make_db")
           (fun db ->
             begin
               (if collect_diagnostics () then
                  ch_diagnostics_log#add
                    "data block from symbol table"
                    (LBLOCK [addr_d#toPretty; STR " - "; addr#toPretty]));
               system_info#add_data_block db;
               indata := None
             end)
           (make_data_block addr_d addr "symbol-table")
      | _ -> () in
    List.iter
      (fun (addrix, name) ->
        match name with
        | "$d" | "$d.1" ->
           (match !indata with
            | Some _ -> ()
            | None -> indata := Some (TR.tget_ok (index_to_doubleword addrix)))
        | "$t" when system_settings#has_thumb ->
           begin
             let addr = TR.tget_ok (index_to_doubleword addrix) in
             (if !inarm then
                begin
                  system_settings#set_thumb;
                  system_info#set_arm_thumb_switch addr "T";
                  inarm := false
                end);
             make_db addr
           end
        (* $a.0,1,2 llvm-generated code? *)
        | "$a" | "$a.0" | "$a.1" | "$a.2" when system_settings#has_thumb ->
           begin
             let addr = TR.tget_ok (index_to_doubleword addrix) in
             (if not (!inarm) then
                begin
                  system_info#set_arm_thumb_switch addr "A";
                  inarm := true
                end);
             make_db addr
           end
        | _ -> ()) symbols

  method get_symbol (index:int) =
    if H.mem entries index then
      H.find entries index
    else
      raise
        (BCH_failure
           (LBLOCK [STR "Symbol with index "; INT index; STR " not found"]))

  method write_xml_symbols (node:xml_element_int) =
    let table = mk_num_record_table "symbol-table" in
    begin
      H.iter (fun _ e -> table#add e#id e#to_rep_record) entries;
      table#write_xml node
    end

end


let mk_elf_symbol_table s h vaddr =
  let entrysize = h#get_entry_size#to_int in
  let table = new elf_symbol_table_t s entrysize vaddr in
  begin
    table#read;
    table
  end


let read_xml_elf_symbol_table (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  let vaddr = TR.tget_ok (string_to_doubleword (node#getAttribute "vaddr")) in
  let entrysize = node#getIntAttribute "entrysize" in
  let table = new elf_symbol_table_t s entrysize vaddr in
  begin
    table#read;
    table
  end
