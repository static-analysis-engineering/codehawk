(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

let write_xml_class_property (node:xml_element_int) (p:class_property_t) =
  match p with
  | LogicalSize (MethodAccessor ms) ->
     let snode = xmlElement "signature" in
     begin
       ms#write_xmlx snode ;
       node#appendChildren [ snode ] ;
       node#setAttribute "name" "size" ;
       node#setAttribute "method" ms#name
     end

class class_summary_t
  ~(class_name:class_name_int)
  ~(is_interface:bool)
  ~(is_abstract:bool)
  ~(is_final:bool)
  ~(is_immutable:bool)
  ~(is_dispatch:bool)
  ~(super_class:class_name_int option)
  ~(interfaces:class_name_int list)
  ~(class_properties:class_property_t list)
  ~(default_implementations:class_name_int list)
  ~(method_summaries:method_signature_int list)
  ~(fields:field_signature_int list):class_summary_int =
object
  method get_class_name = class_name

  method is_interface = is_interface

  method is_final = is_final

  method is_abstract = is_abstract

  method is_immutable = is_immutable

  method is_dispatch = is_dispatch

  method get_super_class = match super_class with Some sc -> sc | _ ->
    raise (JCH_failure (LBLOCK [ STR "Class " ; class_name#toPretty ;
				 STR " does not have a superclass" ]))
  method get_interfaces = interfaces

  method get_default_implementations = default_implementations

  method get_methods = method_summaries

  method get_fields = fields

  method has_super_class = match super_class with Some _ -> true | _ -> false

  method get_class_properties = class_properties

  method defines_method (ms:method_signature_int) =
    List.exists (fun sg -> ms#equal sg) method_summaries

  method defines_field (fs:field_signature_int) = 
    List.exists (fun sg -> fs#equal sg) fields

  method toPretty =
    LBLOCK [ class_name#toPretty ; 
	     (if is_final then STR " (final)" else STR "") ;
	     (if is_immutable then STR " (immutable)" else STR "" ) ]
end

let make_class_summary 
    ?(is_interface=false)
    ?(is_final=false)
    ?(is_abstract=false)
    ?(is_immutable=false)
    ?(is_dispatch=false)
    ?(super_class=None)
    ?(interfaces=[])
    ?(class_properties=[])
    ?(default_implementations=[])
    ?(method_summaries=[])
    ?(fields=[])
    (cn:class_name_int) =
  new class_summary_t 
    ~is_interface:is_interface 
    ~is_final:is_final 
    ~is_abstract:is_abstract 
    ~is_immutable:is_immutable 
    ~is_dispatch:is_dispatch
    ~super_class:super_class 
    ~interfaces:interfaces
    ~class_properties:class_properties
    ~default_implementations:default_implementations
    ~method_summaries:method_summaries
    ~fields:fields
    ~class_name:cn
