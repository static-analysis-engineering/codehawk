(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchcil *)
open BCHCBasicTypes


class type bcdictionary_int =
  object

    method index_attrparam: b_attrparam_t -> int
    method index_attribute: b_attribute_t -> int
    method index_attributes: b_attributes_t -> int         
    method index_constant: bconstant_t -> int
    method index_exp: bexp_t -> int
    method index_funarg: bfunarg_t -> int
    method index_funargs: bfunarg_t list -> int
    method index_lhost: blhost_t -> int
    method index_lval: blval_t -> int
    method index_opt_lval: blval_t option -> int
    method index_offset: boffset_t -> int        
    method index_typ: btype_t -> int
    method index_typsig: btypsig_t -> int
    method index_string: string -> int
    method index_location: b_location_t -> int
    method index_tname: tname_t -> int

    method index_typeinfo: btypeinfo_t -> int
    method index_varinfo: bvarinfo_t -> int
    method index_init_opt: binit_t option -> int
    method index_init: binit_t -> int
    method index_offset_init: (boffset_t * binit_t) -> int
    method index_fieldinfo: bfieldinfo_t -> int
    method index_compinfo: bcompinfo_t -> int
    method index_enumitem: beitem_t -> int
    method index_enuminfo: benuminfo_t -> int

    method get_attrparam: int -> b_attrparam_t
    method get_attribute: int -> b_attribute_t
    method get_attributes: int -> b_attributes_t
    method get_attrparam: int -> b_attrparam_t
    method get_constant: int -> bconstant_t
    method get_exp: int -> bexp_t
    method get_funarg: int -> bfunarg_t
    method get_funargs: int -> bfunarg_t list
    method get_lhost: int -> blhost_t
    method get_lval: int -> blval_t
    method get_opt_lval: int -> blval_t option
    method get_offset: int -> boffset_t
    method get_typ: int -> btype_t
    method get_typsig: int -> btypsig_t
    method get_string: int -> string
    method get_location: int -> b_location_t

    method get_varinfo: int -> bvarinfo_t
    method get_init: int -> binit_t
    method get_offset_init: int -> (boffset_t * binit_t)
    method get_enuminfo: int -> benuminfo_t
    method get_enumitem: int -> beitem_t
    method get_compinfo: int -> bcompinfo_t
    method get_fieldinfo: int -> bfieldinfo_t
    method get_typeinfo: int -> btypeinfo_t
         
    method write_xml_attributes:
             ?tag:string -> xml_element_int -> b_attributes_t -> unit
    method read_xml_attributes:
             ?tag:string -> xml_element_int -> b_attributes_t
    method write_xml_exp:
             ?tag:string -> xml_element_int -> bexp_t -> unit
    method read_xml_exp:
             ?tag:string -> xml_element_int -> bexp_t
    method write_xml_funarg_list:
             ?tag:string -> xml_element_int -> bfunarg_t list -> unit
    method read_xml_funarg_list:
             ?tag:string -> xml_element_int -> bfunarg_t list
    method write_xml_lval:
             ?tag:string -> xml_element_int -> blval_t -> unit
    method read_xml_lval:
             ?tag:string -> xml_element_int -> blval_t
    method write_xml_offset:
             ?tag:string -> xml_element_int -> boffset_t -> unit
    method read_xml_offset:
             ?tag:string -> xml_element_int -> boffset_t
    method write_xml_typ:
             ?tag:string -> xml_element_int -> btype_t -> unit
    method read_xml_typ:
             ?tag:string -> xml_element_int -> btype_t
    method write_xml_string:
             ?tag:string -> xml_element_int -> string -> unit

    method write_xml_typeinfo:
             ?tag:string -> xml_element_int -> btypeinfo_t -> unit
    method read_xml_typeinfo:
             ?tag:string -> xml_element_int -> btypeinfo_t
    method write_xml_varinfo:
             ?tag:string -> xml_element_int -> bvarinfo_t -> unit
    method read_xml_varinfo:
             ?tag:string -> xml_element_int -> bvarinfo_t
    method write_xml_init:
             ?tag:string -> xml_element_int -> binit_t -> unit
    method read_xml_init:
             ?tag:string -> xml_element_int -> binit_t
    method write_xml_fieldinfo:
             ?tag:string -> xml_element_int -> bfieldinfo_t -> unit
    method read_xml_fieldinfo:
             ?tag:string -> xml_element_int -> bfieldinfo_t
    method write_xml_compinfo:
             ?tag:string -> xml_element_int -> bcompinfo_t -> unit
    method read_xml_compinfo:
             ?tag:string -> xml_element_int -> bcompinfo_t
    method write_xml_enumitem:
             ?tag:string -> xml_element_int -> beitem_t -> unit
    method write_xml_enuminfo:
             ?tag:string -> xml_element_int -> benuminfo_t -> unit
    method read_xml_enuminfo:
             ?tag:string -> xml_element_int -> benuminfo_t
    method write_xml_location:
             ?tag:string -> xml_element_int -> b_location_t -> unit
    method read_xml_location:
             ?tag:string -> xml_element_int -> b_location_t
         
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type bcfundeclarations_int =
  object

    method index_formal: bvarinfo_t -> int -> int
    method index_local: bvarinfo_t -> int

    method write_xml_formal:
             ?tag:string -> xml_element_int -> bvarinfo_t -> int -> unit
    method write_xml_local:
             ?tag:string -> xml_element_int -> bvarinfo_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type bcfiles_int =
  object

    (* setters *)
    method add_bcfile: bcfile_t -> unit
    method add_fundef: string -> btype_t -> unit

    (* getters *)
    method get_gfun_names: string list
    method get_gfun: string -> bcfundec_t
    method get_typedef: string -> btype_t    (* retrieve by name *)
    method get_compinfo: int -> bcompinfo_t  (* retrieve by key *)
    method get_varinfo: string -> bvarinfo_t (* retrieve by name *)

    (* predicates *)
    method has_gfun: string -> bool
    method has_typedef: string -> bool
    method has_compinfo: int -> bool
    method has_varinfo: string -> bool

    (* saving *)
    method write_xml_function: xml_element_int -> string -> unit
    method read_xml_function: xml_element_int -> string -> unit
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end
