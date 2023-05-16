(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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

(* cil *)
open GoblintCil

(* chutil *)
open CHXmlDocument

type funarg = string * typ * attributes
type enumitem = string * exp * location


class type cildictionary_int =
  object

    method index_attrparam: attrparam -> int
    method index_attribute: attribute -> int
    method index_attributes: attributes -> int         
    method index_attrparam: attrparam -> int
    method index_constant: constant -> int
    method index_exp: exp -> int
    method index_funarg: funarg -> int
    method index_funargs: funarg list -> int
    method index_lhost: lhost -> int
    method index_lval: lval -> int
    method index_offset: offset -> int        
    method index_typ: typ -> int
    method index_typsig: typsig -> int
    method index_string: string -> int

    method write_xml_attributes: ?tag:string -> xml_element_int -> attributes -> unit
    method write_xml_exp: ?tag:string -> xml_element_int -> exp -> unit
    method write_xml_funarg_list: ?tag:string -> xml_element_int -> funarg list -> unit
    method write_xml_lval: ?tag:string -> xml_element_int -> lval -> unit
    method write_xml_offset: ?tag:string -> xml_element_int -> offset -> unit
    method write_xml_typ : ?tag:string -> xml_element_int -> typ -> unit
    method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
         
    method write_xml: xml_element_int -> unit

  end


class type cildeclarations_int =
  object

    method index_typeinfo: typeinfo -> int
    method index_varinfo: varinfo -> int
    method index_init_opt: init option -> int
    method index_init: init -> int
    method index_offset_init: (offset * init) -> int
    method index_fieldinfo: fieldinfo -> int
    method index_compinfo: compinfo -> int
    method index_enumitem: enumitem -> int
    method index_enuminfo: enuminfo -> int
    method index_location: location -> int
    method index_filename: string -> int

    method write_xml_typeinfo: ?tag:string -> xml_element_int -> typeinfo -> unit
    method write_xml_varinfo: ?tag:string -> xml_element_int -> varinfo -> unit
    method write_xml_init: ?tag:string -> xml_element_int -> init -> unit
    method write_xml_fieldinfo: ?tag:string -> xml_element_int -> fieldinfo -> unit
    method write_xml_compinfo: ?tag:string -> xml_element_int -> compinfo -> unit
    method write_xml_enumitem: ?tag:string -> xml_element_int -> enumitem -> unit
    method write_xml_enuminfo: ?tag:string -> xml_element_int -> enuminfo -> unit
    method write_xml_location: ?tag:string -> xml_element_int -> location -> unit

    method write_xml: xml_element_int -> unit

  end


class type cilfundeclarations_int =
  object

    method index_formal: varinfo -> int -> int
    method index_local : varinfo -> int

    method write_xml_formal: ?tag:string -> xml_element_int -> varinfo -> int -> unit
    method write_xml_local : ?tag:string -> xml_element_int -> varinfo -> unit

    method write_xml: xml_element_int -> unit

  end
