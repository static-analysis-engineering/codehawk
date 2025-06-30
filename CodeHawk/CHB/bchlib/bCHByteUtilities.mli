(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(** Utility functions to read and write binary data *)


(** [get_aligned_address dw] returns the smallest multiple of 16 greater than
    or equal to the value of dw, represented as a doubleword *)
val get_aligned_address: doubleword_int -> doubleword_int


(** [get_1kaligned_address dw] returns the smallest multiple of 1024 greater than
    or equal to the value of dw, represented as a doubleword *)
val get_1kaligned_address: doubleword_int -> doubleword_int 


val rawdata_to_string:
  ?markwritten:doubleword_int list -> string -> doubleword_int -> string


(** [write_xml_raw_data elt s dw] writes byte string [s] to the xml element
    [elt] in the form of sub elements with tag [aline] and attributes
    [bytes] and [print] that contain 4 space-separated groups of 4 bytes in
    hexadecimal and a print represenation of those 16 bytes, respectively.

    This format is used in saving binary content of the sections to xml.*)
val write_xml_raw_data: xml_element_int -> string -> doubleword_int -> unit


(** [write_doubleword_to_bytestring dw] writes the constituting four bytes
    to a bytestring, least significant byte first.*)
val write_doubleword_to_bytestring: doubleword_int -> string


(** [write_hex_bytes_to_bytestring s] converts the hexadecimal byte
    representation in [s] to a string of bytes.*)
val write_hex_bytes_to_bytestring: string -> string


(** [read_xml_raw_data elt] reads data written by write_xml_raw_data and
    returns the original byte string.*)
val read_xml_raw_data : xml_element_int -> string


(** [byte_string_to_spaced_string s] writes the byte string [s] to hexadecimal
    bytes separated by spaces.*)
val byte_string_to_spaced_string: string -> string


(** [byte_string_to_printed_string s] writes the byte string [s] to hexadecimal
    bytes as a continuous string.*)
val byte_string_to_printed_string: string -> string

val littleendian_hexstring_todwstring: string -> string
  
val littleendian_hexstring_towstring: string -> string

val decode_string:
  string
  -> doubleword_int
  -> (string * doubleword_int * doubleword_int * doubleword_int * int) list
  -> string

val read_hex_stream_file: string -> string
