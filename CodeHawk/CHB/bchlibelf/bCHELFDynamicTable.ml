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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHNumRecordTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibelf *)
open BCHELFDictionary
open BCHELFSection
open BCHELFTypes
open BCHELFUtil

module H = Hashtbl

class elf_dynamic_table_entry_t (index:int):elf_dynamic_table_entry_int =
object (self)

  val mutable d_tag = numerical_zero
  val mutable d_un = wordzero

  method id = index

  method read (ch:pushback_stream_int) =
    try
      begin
        (* 0,4, Tag ------------------------------------------------------------
           Dynamic Array Tag
           --------------------------------------------------------------------- *)
        d_tag <- ch#read_num_signed_doubleword ;

        (* 4, 4, Value/Address -------------------------------------------------
           d_val These Elf32_Word objects represent integer values with various 
                  interpretations.
           d_ptr  These Elf32_Addr objects represent program virtual addresses. 
                  As mentioned previously, a file’s virtual addresses might not 
                  match the memory virtual addresses during execution. When 
                  interpreting addresses contained in the dynamic structure, 
                  the dynamic linker com- putes actual addresses, based on the 
                  original file value and the memory base address. For consistency, 
                  files do not contain relocation entries to ‘‘correct’’ addresses 
                  in the dynamic structure.
            ----------------------------------------------------------------------- *)
        d_un <- ch#read_doubleword
      end
    with
    | IO.No_more_input ->
       begin
         ch_error_log#add "no more input" (STR "elf_symbol_table_entry_t#read") ;
         raise IO.No_more_input
       end

  method get_d_tag = d_tag

  method get_tag = num_to_dynamic_tag d_tag

  method get_d_un = d_un

  method get_d_ptr =
    match self#get_tag with
    | DT_PltGot
      | DT_Hash
      | DT_StrTab
      | DT_SymTab
      | DT_Rela
      | DT_Init
      | DT_Fini
      | DT_Rel
      | DT_Debug
      | DT_JmpRel -> d_un
    | _ ->
       raise (BCH_failure (LBLOCK [ STR "Value cannot be interpreted as pointer" ]))

  method get_d_val =
    match self#get_tag with
    | DT_Needed
      | DT_PltRelSz
      | DT_RelaSz
      | DT_RelaEnt
      | DT_StrSz
      | DT_SymEnt
      | DT_SoName
      | DT_RPath
      | DT_RelSz
      | DT_RelEnt
      | DT_PltRel -> d_un
    | _ ->
       raise (BCH_failure (LBLOCK [ STR "Value cannot be interpreted as value" ]))

  method to_rep_record =
    let args = [ ] in
    let tags = [ d_tag#toString ;  d_un#to_hex_string ] in
    (tags,args)

end
    
class elf_dynamic_table_t
        (s:string)
        (vaddr:doubleword_int):elf_dynamic_table_int =
object (self)

  val mutable entries = []

  inherit elf_raw_section_t s vaddr as super

  method read =
    try
      let entrysize = 8 in
      let ch =
        make_pushback_stream ~little_endian:system_info#is_little_endian s in
      let n = (String.length s) / entrysize in
      let c = ref 0 in
      begin
        while !c < n do
          let entry = new elf_dynamic_table_entry_t !c in
          begin
            entry#read ch ;
            c :=  !c + 1 ;
            entries <- entry :: entries
          end
        done;
      end
    with
    | IO.No_more_input ->
       ch_error_log#add "no more input"
                        (LBLOCK [ STR "Unable to read the relocation table" ])

  method write_xml_entries (node:xml_element_int) =
    let table = mk_num_record_table "dynamic-table" in
    begin
      List.iter (fun e -> table#add e#id e#to_rep_record) entries ;
      table#write_xml node
    end

end

let mk_elf_dynamic_table s h vaddr =
  let table = new elf_dynamic_table_t s vaddr in
  begin
    table#read ;
    table
  end

let read_xml_elf_dynamic_table (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  let vaddr = string_to_doubleword (node#getAttribute "vaddr") in
  let table = new elf_dynamic_table_t s vaddr in
  begin
    table#read ;
    table
  end
