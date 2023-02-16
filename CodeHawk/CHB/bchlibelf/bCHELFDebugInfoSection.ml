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
open BCHELFDictionary
open BCHELFSection
open BCHELFTypes

module TR = CHTraceResult


let fail_traceresult (msg: string) (r: 'a traceresult): 'a =
  if Result.is_ok r then
    TR.tget_ok r
  else
    fail_tvalue
      (trerror_record (LBLOCK [STR "BCHELFDebugInfoSection: "; STR msg])) r


class elf_debug_info_section_t (s:string):elf_debug_info_section_int =
object (self)

  inherit elf_raw_section_t s wordzero as super

end


let mk_elf_debug_info_section (s:string) (h:elf_section_header_int) =
  new elf_debug_info_section_t s


let read_xml_elf_debug_info_section (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  new elf_debug_info_section_t s
  
