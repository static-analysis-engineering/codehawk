(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibelf *)
open BCHDwarfTypes
open BCHELFDictionary
open BCHELFSection
open BCHELFTypes

module H = Hashtbl
module TR = CHTraceResult


let fail_traceresult (msg: string) (r: 'a traceresult): 'a =
  if Result.is_ok r then
    TR.tget_ok r
  else
    fail_tvalue
      (trerror_record (LBLOCK [STR "BCHELFDebugInfoSection: "; STR msg])) r


class elf_debug_compilation_unit_header_t =
object

  val mutable unit_length = wordzero
  val mutable version = 0
  val mutable debug_abbrev_offset = wordzero
  val mutable address_size = 0

  method read (ch: pushback_stream_int) =
    try
      begin
        (* 0, 4, unit_length -------------------------------------------------
           A 4-byte unsigned integer representing the length of the 
           .debug_info contribution for the at compilation unit, not
           including the length field itself.
           ------------------------------------------------------------------- *)
        unit_length <- ch#read_doubleword;

        (* 4, 2, version -----------------------------------------------------
           A 2-byte unsigned integer representing the version of the DWARF
           information for the compilation unit.
           ------------------------------------------------------------------- *)
        version <- ch#read_ui16;

        (* 6, 4, debug_abbrev_offset (section offset) ------------------------
           A 4-byte unsigned offset into the .debug_abbrev section. This offset
           associates the compilation unit with a particular debugging
           information entry abbrevations. 
         --------------------------------------------------------------------- *)
        debug_abbrev_offset <- ch#read_doubleword;

        (* 10, 1 -------------------------------------------------------------
           A 1-byte unsigned integer represeting the size in bytes of an
           address on the target architecture.
           ------------------------------------------------------------------- *)
        address_size <- ch#read_byte;
      end
    with
    | IO.No_more_input ->
       begin
         ch_error_log#add
           "no more input" (STR "debug_info compilation_unit_header#read");
         raise IO.No_more_input
       end

  method unit_length: doubleword_int = unit_length

  method version:int = version

  method debug_abbrev_offset: doubleword_int = debug_abbrev_offset

  method address_size:int = address_size

  method toPretty =
    LBLOCK [
        fixed_length_pretty (STR "Length:") 32;
        unit_length#toPretty; NL;
        fixed_length_pretty (STR "Version:") 32;
        INT version; NL;
        fixed_length_pretty (STR "Abbrev offset:") 32;
        debug_abbrev_offset#toPretty; NL;
        fixed_length_pretty (STR "Pointer size:") 32;
        INT address_size; NL]

end


class elf_debug_info_section_t (s:string):elf_debug_info_section_int =
object (self)

  inherit elf_raw_section_t s wordzero as super

  method compilation_unit_stream (offset: doubleword_int) =
    let index = offset#index in
    if String.length s > index + 11 then
      let ch =
        make_pushback_stream ~little_endian:system_info#is_little_endian s in
      begin
        (* skip the 11-byte compilation-unit header *)
        ch#skip_bytes (index + 11);
        ch
      end
    else
      raise (Invalid_argument "elf_debug_info_section:compilation_unit_stream")

  method compilation_unit_headers (offsets: doubleword_int list) =
    let table = H.create 5 in
    let ch =
      make_pushback_stream ~little_endian:system_info#is_little_endian s in
    begin
      List.iter (fun dw ->
          let cu_header = new elf_debug_compilation_unit_header_t in
          let skips = dw#index - ch#pos in
          let _ = ch#skip_bytes skips in
          begin
            cu_header#read ch;
            H.add table dw#index cu_header
          end) offsets;
      chlog#add
        "debug data processing"
        (LBLOCK [
             STR "debug_compilation_unit_headers: ";
             INT (H.length table);
             STR " headers"]);
      H.fold (fun k v a ->
          let d = {
              dwcu_length = v#unit_length;
              dwcu_offset = TR.tget_ok (index_to_doubleword k);
              dwcu_version = v#version;
              dwcu_abbrev_offset = v#debug_abbrev_offset;
              dwcu_address_size = v#address_size
            } in
          d::a) table []
    end

end


let mk_elf_debug_info_section (s:string) (h:elf_section_header_int) =
  new elf_debug_info_section_t s


let read_xml_elf_debug_info_section (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  new elf_debug_info_section_t s
  
