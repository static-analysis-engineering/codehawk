(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023-2024  Aarno Labs LLC

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
open BCHByteUtilities
open BCHDoubleword
open BCHStreamWrapper

(* bchlibelf *)
open BCHDwarfTypes
open BCHDwarfUtils
open BCHELFSection
open BCHELFTypes

module H = Hashtbl
module TR = CHTraceResult


class elf_debug_abbrev_section_t (s:string):elf_debug_abbrev_section_int =
object (self)

  val mutable ch = make_pushback_stream ~little_endian:true s

  inherit elf_raw_section_t s wordzero

  method initstream (offset: int) =
    begin
      ch <- make_pushback_stream ~little_endian:true s;
      ch#skip_bytes offset
    end

  method get_abbrev_entry =
    let index = ch#read_dwarf_leb128 in
    let tag = int_to_dwarf_tag_type ch#read_dwarf_leb128 in
    let hasc = (ch#read_byte = 1) in
    let attrspecs =
      let specs = ref [] in
      let morespecs = ref true in
      begin
        while !morespecs do
          let attr = ch#read_dwarf_leb128 in
          let form = ch#read_dwarf_leb128 in
          if attr = 0 && form = 0 then
            morespecs := false
          else
            specs :=
              (int_to_dwarf_attr_type attr, int_to_dwarf_form_type form)::!specs
        done;
        List.rev !specs
      end in
    {
      dabb_index = index;
      dabb_tag = tag;
      dabb_has_children = hasc;
      dabb_attr_specs = attrspecs
    }

  method private length = String.length s

  method get_abbrev_table (offset: int): debug_abbrev_table_entry_t list =
    let _ = pr_debug [STR "Get abbrev table at: ";
                      (TR.tget_ok (int_to_doubleword offset))#toPretty; NL] in
    let table = H.create 3 in
    let _ = self#initstream offset in
    let entry = ref self#get_abbrev_entry in
    begin
      while (not (H.mem table !entry.dabb_index)) && ch#pos < (self#length - 1) do
        begin
          H.add table !entry.dabb_index !entry;
          entry := self#get_abbrev_entry
        end
      done;
      (if ch#pos >= self#length - 1 then
        H.add table !entry.dabb_index !entry);
      H.fold (fun _ v a -> v::a) table []
    end

end


let mk_elf_debug_abbrev_section (s: string) (_h: elf_section_header_int) =
  new elf_debug_abbrev_section_t s


let read_xml_elf_debug_abbrev_section (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  new elf_debug_abbrev_section_t s
  
