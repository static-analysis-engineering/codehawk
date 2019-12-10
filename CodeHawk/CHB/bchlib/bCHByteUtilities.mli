(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

val get_aligned_address  : doubleword_int -> doubleword_int
  
val get_1kaligned_address: doubleword_int -> doubleword_int 

val rawdata_to_string:
  ?markwritten:doubleword_int list -> string -> doubleword_int -> string

val write_xml_raw_data: xml_element_int -> string -> doubleword_int -> unit
  
val read_xml_raw_data : xml_element_int -> string

val byte_string_to_spaced_string: string -> string

val byte_string_to_printed_string: string -> string

val littleendian_hexstring_todwstring: string -> string
  
val littleendian_hexstring_towstring: string -> string

val decode_string:
  string
  -> doubleword_int
  -> (string * doubleword_int * doubleword_int * doubleword_int * int) list
  -> string

val read_hex_stream_file: string -> string
