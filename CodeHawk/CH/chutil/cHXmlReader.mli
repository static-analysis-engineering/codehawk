(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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

(** Utilities to read xml files *)

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument

exception XmlParseError of int * int * pretty_t
exception IllFormed

val readXmlDocument      : string -> xml_document_int    (* raises XmlParseError *)
val readXmlDocumentString: string -> xml_document_int    (* raises XmlParseError *)

class xml_reader_t :
  IO.input ->
object
  method fill_data_buffer : int -> unit
  method fill_data_strip : int -> unit
  method fill_name_buffer : int -> unit
  method getDocument : CHXmlDocument.xml_document_int
  method input_unicode : int
  method readAttribute : String.t * String.t
  method readCharData : string
  method readCharRef : string
  method readContent : CHXmlDocument.xml_element_int list
  method readDoctypeDecl : unit
  method readDocument : unit
  method readElement : CHXmlDocument.xml_element_int
  method readEndTag : String.t -> unit
  method readEntityRef : string
  method readEntityReference : string
  method readStartTag : String.t * (String.t * String.t) list
  method end_of_file: bool
end
    
