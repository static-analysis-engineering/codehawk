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
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibelf *)
open BCHELFSection
open BCHELFTypes

module H = Hashtbl
module TR = CHTraceResult


class elf_debug_aranges_entry_t =
object

  val mutable unit_length = wordzero
  val mutable version = 0
  val mutable debug_info_offset = wordzero
  val mutable address_size = 0
  val mutable segment_size = 0
  val mutable address_ranges: (doubleword_int * doubleword_int) list = []

  method read (ch: pushback_stream_int) =
    try
      begin
        (* 0, 4, unit_length -------------------------------------------------
           A 4-byte length containing the length of the set of entries for this
           compilation unit, not including the length field itself.
           ------------------------------------------------------------------- *)
        unit_length <- ch#read_doubleword;

        (* 4, 2, version -----------------------------------------------------
           A 2-byte version identifier containing the value 2.
           ------------------------------------------------------------------- *)
        version <- ch#read_ui16;

        (* 6, 4, debug_info_offset (section offset) --------------------------
           A 4-byte offset into the .debug_info section of the compilation unit
           header.
           ------------------------------------------------------------------- *)
        debug_info_offset <- ch#read_doubleword;

        (* 10, 1, address_size (ubyte) ---------------------------------------
           A 1-byte unsigned integer containing the size in bytes of an address
           on the target system.
           ------------------------------------------------------------------- *)
        address_size <- ch#read_byte;

        (* 11, 1, segment_size (ubyte) ---------------------------------------
           A 1-byte unsigned integer containing the size in bytes of a segment
           selector on the target system.
           ------------------------------------------------------------------- *)
        segment_size <- ch#read_byte;

        (* 12, 4, alignment --------------------------------------------------
           Align to 8-byte boundary (if segment size is zero)
           ------------------------------------------------------------------- *)
        (if segment_size = 0 then ch#skip_bytes 4);

        (* 16, .. address tuples ---------------------------------------------
           A series of tuples. Each tuple consists of a segment (if segment size
           is larger than zero), an address, and a length. The series of tuples
           is terminated by a (0, 0, 0) or (0, 0) tuple.
           ------------------------------------------------------------------- *)
        (let active = ref true in
         let _ =
           if segment_size > 0 then
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Non-zero segment-size not supported in aranges"])) in
         while !active do
           let addr = ch#read_doubleword in
           let size = ch#read_doubleword in
           begin
             address_ranges <- (addr, size) :: address_ranges;
             active := not (addr#equal wordzero && size#equal wordzero)
           end
         done)
      end
    with
    | IO.No_more_input ->
       begin
         ch_error_log#add "no more input" (STR "debug_aranges_entry#read");
         raise IO.No_more_input
       end

  method address_size = address_size

  method segment_size = segment_size

  method unit_length = unit_length

  method debug_info_offset = debug_info_offset

  method address_ranges: (doubleword_int * doubleword_int) list =
    address_ranges

  method toPretty =
    LBLOCK [
        fixed_length_pretty (STR "Length:") 32;
        unit_length#toPretty; NL;
        fixed_length_pretty (STR "Version:") 32;
        INT version; NL;
        fixed_length_pretty (STR "Offset into .debug_info") 32;
        debug_info_offset#toPretty; NL;
        fixed_length_pretty (STR "Pointer size:") 32;
        INT address_size; NL;
        fixed_length_pretty (STR "Segment size:") 32;
        INT segment_size; NL;
        NL;
        LBLOCK
          (List.map (fun (addr, size) ->
               LBLOCK [STR "     ";
                       fixed_length_pretty addr#toPretty 12;
                       STR "  ";
                       fixed_length_pretty size#toPretty 12;
                       NL])
             address_ranges);
        NL; NL]

end


class elf_debug_aranges_section_t (s:string):elf_debug_aranges_section_int =
object

  val mutable entries = H.create 5

  inherit elf_raw_section_t s wordzero

  method read =
    try
      let slen = String.length s in
      let ch =
        make_pushback_stream ~little_endian:system_info#is_little_endian s in
      begin
        while ch#pos < (slen - 12) do
          let entry = new elf_debug_aranges_entry_t in
          begin
            entry#read ch;
            H.add entries entry#debug_info_offset#index entry
          end
        done;
        chlog#add
          "debug data processing"
          (LBLOCK [
               STR "debug_aranges: ";
               INT (H.length entries);
               STR " entries"])
      end
    with
    | IO.No_more_input ->
       ch_error_log#add
         "no more input"
         (LBLOCK [STR "Unable to read the debug_aranges section"])

  method debug_info_compilation_unit_offsets =
    let cunits = H.fold (fun k _ a -> k::a) entries [] in
    List.map
      (fun index -> TR.tget_ok (index_to_doubleword index))
      (List.sort Stdlib.compare cunits)

  method !toPretty =
    let cunits = H.fold (fun _ v a -> v::a) entries [] in
    LBLOCK (List.map (fun e -> LBLOCK [e#toPretty; NL]) cunits)

end


let mk_elf_debug_aranges_section (s: string) (_h: elf_section_header_int) =
  let section = new elf_debug_aranges_section_t s in
  begin
    section#read;
    section
  end


let read_xml_elf_debug_aranges_section (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  let section = new elf_debug_aranges_section_t s in
  begin
    section#read;
    section
  end
  
