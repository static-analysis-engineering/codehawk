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

  val mutable d_tag = wordzero
  val mutable d_un = numerical_zero

  method id = index

  method read (ch:pushback_stream_int) =
    try
      begin
        (* 0,4, Tag ------------------------------------------------------------
           Dynamic Array Tag
           --------------------------------------------------------------------- *)
        d_tag <- ch#read_doubleword ;

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
        d_un <- ch#read_num_signed_doubleword
      end
    with
    | IO.No_more_input ->
       begin
         ch_error_log#add "no more input" (STR "elf_symbol_table_entry_t#read") ;
         raise IO.No_more_input
       end

  method get_d_tag = d_tag

  method get_tag = doubleword_to_dynamic_tag d_tag

  method get_tag_name = doubleword_to_dynamic_tag_name d_tag

  method get_d_un = d_un

  method get_d_ptr =
    let tagval = doubleword_to_dynamic_tag_value d_tag in
    match tagval with
    | DTV_d_ptr | DTV_d_none -> numerical_to_doubleword d_un
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Value of " ; STR self#get_tag_name ;
                      STR " cannot be interpreted as pointer" ]))

  method get_d_val =
    let tagval = doubleword_to_dynamic_tag_value d_tag in
    match tagval with
    | DTV_d_val | DTV_d_none -> d_un
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Value of " ; STR self#get_tag_name ;
                      STR " cannot be interpreted as value" ]))

  method to_rep_record =
    let tagval =
      match doubleword_to_dynamic_tag_value d_tag with
      | DTV_d_ptr | DTV_d_none -> (numerical_to_doubleword d_un)#to_hex_string
      | DTV_d_val -> d_un#toString in
    let args = [ ] in
    let tags = [ self#get_tag_name ;  tagval ] in
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
