(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
(** Utility program to produce signatures of Java native methods *)


(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHAnnotationsPre
open JCHApplication
open JCHClassLoader
open JCHPreAPI
open JCHPreFileIO


let loadlibrarycalls = ref []

let get_loadlibrarycalls () = !loadlibrarycalls


let is_load_library_method (_cn: class_name_int) (ms: method_signature_int)  =
  (* cn#name = "java.lang.System" &&   *)
  (ms#name = "loadLibrary"  || ms#name = "mapLibraryName")


let check_for_native_library (cInfo: class_info_int) =
  let mss = cInfo#get_methods_defined in
  List.iter (fun ms ->
    let cms = make_cms cInfo#get_class_name ms in
    let mInfo = app#get_method cms in
    if mInfo#has_bytecode then
      mInfo#bytecode_iteri (fun pc opc ->
	match opc with
	| OpInvokeStatic (cn,msi) when is_load_library_method cn msi  ->
	   loadlibrarycalls :=
             (get_static_call_value mInfo pc cn msi) :: !loadlibrarycalls
	| _ -> ())
    else
      ()) mss


let save_native_signatures (dir: string) (jars: string list) =
  let _ = List.iter (fun jar -> ignore(load_classes_in_jar jar)) jars in
  let _ = process_classes () in
  List.iter (fun cInfo ->
    let cn = cInfo#get_class_name in
    let sc = cInfo#get_super_class in
    let _ = check_for_native_library cInfo in
    let nmss = cInfo#get_native_methods_defined in
    match nmss with [] -> () | l ->
      let node = xmlElement "class" in
      let mmNode = xmlElement "native-methods" in
      begin
	mmNode#appendChildren (List.map (fun (ms:method_signature_int) ->
	  let m = cInfo#get_method ms in
	  let mNode = xmlElement "method" in
	  let set = mNode#setAttribute in
	  let sety tag = set tag "yes" in
	  begin
	    ms#write_xmlx ~varnamemapping:None mNode;
	    write_xml_visibility mNode m#get_visibility;
	    (if m#has_varargs then sety "has-varargs");
	    (if m#is_static then sety "static");
	    (if m#is_synchronized then sety "synchronized");
	    set "name" ms#name;
	    mNode
	  end) l);
	node#appendChildren [mmNode];
	node#setAttribute "name" cn#simple_name;
	node#setAttribute "package" cn#package_name;
	node#setAttribute "super" sc#name;
	node#setIntAttribute "count" (List.length l);
	save_class_xml_file dir cn node "native-methods"
      end) app#get_application_classes
