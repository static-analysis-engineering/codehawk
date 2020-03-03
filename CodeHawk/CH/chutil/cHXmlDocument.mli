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

(** Utilities to build xml files *)

(* chlib *)
open CHIntervals
open CHPretty

exception XmlDocumentError of int * int * pretty_t

type attribute_format_t = 
| FANL
| FAttr of string
| FAttrL of string * int   (* minimum length *)

type attribute_format_list_t = attribute_format_t list

val set_attribute_format: string -> attribute_format_list_t -> unit

class type xml_element_int =
object ('a)

  (* setters *)
  method appendChildren: 'a list -> unit
  method setText: string -> unit
  method setNameString: string -> unit
  method setGroupString: string -> unit
  method setAttribute: string -> string -> unit
  method setIntAttribute: string -> int -> unit
  method setPrettyAttribute: string -> pretty_t -> unit
  method setYesNoAttribute: string -> bool -> unit
	method setBoolAttribute: string -> bool -> unit
  method setLineNumber: int -> unit
  method setColumnNumber: int -> unit

  (* accessors *)
  method getTag: string
  method getChild: 'a
  method getTaggedChild: string -> 'a 
  method getChildren: 'a list
  method getTaggedChildren: string -> 'a list
  method getAttribute: string -> string
  method getIntAttribute: string -> int
  method getYesNoAttribute: string -> bool
  method getBoolAttribute: string -> bool
  method getDefaultAttribute: string -> string -> string
  method getDefaultIntAttribute: string -> int -> int
  method getOptAttribute: string -> string option
  method getOptIntAttribute: string -> int option
  method getText: string
  method getLineNumber: int
  method getColumnNumber: int

  (* predicates *)
  (** has exactly one child *)
  method hasOneChild: bool
  (** has one or more children *)
  method hasChildren: bool
  (** has exactly one child with the given tag *)
  method hasOneTaggedChild: string -> bool
  (** has one or more children with the given tag *)
  method hasTaggedChildren: string -> bool
  method hasAttributes: bool
  method hasNamedAttribute: string -> bool
  method hasText: bool
  method isEmpty: bool

  (* printing *)
  method toPretty: pretty_t
end

class type xml_document_int =
object
  method setNode: xml_element_int -> unit
  method getRoot: xml_element_int
  method toPretty: pretty_t
end

val replace: char -> string -> string -> string

val stri: int -> string
val time_to_string: float -> string
val current_time_to_string: unit -> string

val xmlDocument: unit -> xml_document_int
val xmlElement: string -> xml_element_int

val xml_string: string -> string -> xml_element_int
val xml_pretty: string -> pretty_t -> xml_element_int
val xml_attr_string: string -> string -> string -> xml_element_int
val xml_attr_int: string -> string -> int -> xml_element_int
val xml_interval: interval_t -> xml_element_int

val ch_xml_header: unit -> xml_element_int

val write_xml_indices: xml_element_int -> int list -> unit
