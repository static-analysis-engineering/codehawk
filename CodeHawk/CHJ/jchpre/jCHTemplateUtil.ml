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
open JCHDictionary

(* jchpre *)
open JCHApplication

module FieldSignatureCollections =
  CHCollections.Make (
      struct
        type t = field_signature_int
        let compare fs1 fs2 = fs1#compare fs2
        let toPretty fs = fs#toPretty
      end)

let get_inherited_fields ?(allfields=true) (cn:class_name_int) =
  try
    let inheritedFields = new FieldSignatureCollections.table_t in
    let definedFields = new FieldSignatureCollections.set_t in
    let cInfo = ref (app#get_class cn) in
    let _ = List.iter definedFields#add !cInfo#get_fields_defined in
    begin
      while !cInfo#has_super_class do
        let sc = !cInfo#get_super_class in
        let _ = cInfo := app#get_class sc in
        let scDefined = !cInfo#get_fields_defined in
        List.iter (fun fs ->
            if !cInfo#defines_field fs then
              if definedFields#has fs || inheritedFields#has fs then
                ()
              else
                let cfs = make_cfs sc fs in
                let _ =
                  if app#has_field cfs then
                    ()
                  else
                    app#add_field (!cInfo#get_field cfs#field_signature) in
                let fInfo = app#get_field cfs in
                if allfields || fInfo#is_public  then
                  inheritedFields#set fs sc
            else
              ()) scDefined
      done;
      inheritedFields#listOfPairs
    end
  with
  | JCHFile.No_class_found  s ->
     raise (JCH_failure
              (LBLOCK [ STR "get inherited fields: " ; cn#toPretty ;
                        STR "; No class found: " ; STR s ]))

let write_xmlx_inherited_field
      (node:xml_element_int) (fs:field_signature_int) (defining_class:class_name_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sNode = xmlElement "signature" in
  begin
    write_xmlx_value_type sNode fs#descriptor ;
    append [ sNode ] ;
    set "name" fs#name ;
    set "inherited" "yes" ;
    set "from" defining_class#name ;
    node#setNameString ("(inherited) field:" ^ fs#name)
  end


let write_xmlx_inherited_method 
      (node:xml_element_int)
      (ms:method_signature_int)
      (defining_class:class_name_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sNode = xmlElement "signature" in
  begin
    ms#write_xmlx sNode ;
    append [ sNode ] ;
    set "name" ms#name ;
    set "inherited" "yes" ;
    set "from" defining_class#name ;
    node#setNameString ("(inherited) " ^ ms#name)
  end
