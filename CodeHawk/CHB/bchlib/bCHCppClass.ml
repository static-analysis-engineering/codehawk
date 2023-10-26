(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeXml
open BCHDoubleword
open BCHFunctionInterface
open BCHFunctionSummary
open BCHLibTypes
open BCHPreFileIO
open BCHTypeDefinitions

module H = Hashtbl
module TR = CHTraceResult


let get_vtable_summaries (t:cppvf_table_t) =
  let result = ref [] in
  let _ = H.iter (fun k v -> result := (k,v) :: !result) t in
  !result


class cpp_class_t 
  (cname:string) 
  (cmembers:cpp_member_t list)
  (cstatic_functions: (doubleword_int * function_interface_t) list)
  (cconstructors: (doubleword_int * function_interface_t) list)
  (cnon_virtual_functions:
     (doubleword_int * function_interface_t) list): cpp_class_int =
object (self)

  val members =                        (* offset -> data/vtable member *)
    let t = H.create 3 in
    let add offset m = if H.mem t offset then
	raise (BCH_failure (LBLOCK [ STR "Duplicate offset in class " ; STR cname ; 
				     STR ": " ; INT offset ]))
      else H.add t offset m in
    let _ = List.iter (fun m ->
      match m with
      | DataMember dm -> add dm.cppdm_offset m
      | VFPtr p -> add p.cppvf_offset m) cmembers in
    t
  val function_interfaces = H.create 3

  method get_name = cname

  method initialize_function_interfaces
           (retrieve: doubleword_int -> doubleword_int option) =
    if H.length function_interfaces > 0 then
      ()
    else
      let add l =
        List.iter (fun (dw, fintf) ->
            H.add function_interfaces dw#index fintf) l in
      begin
        add cstatic_functions ;
        add cconstructors ;
        add cnon_virtual_functions ;
        add (self#get_virtual_entry_points retrieve)
      end
      
  method get_function_interface (fa: doubleword_int): function_interface_t =
    if H.mem function_interfaces fa#index then
      H.find function_interfaces fa#index
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Class function address: ";
                fa#toPretty;
                STR " not found"]))      

  method private get_virtual_entry_points retrieve = 
    let result = ref [] in
    begin
      self#vf_iter (fun vfp -> 
	let vfa = vfp.cppvf_address in
	H.iter (fun offset api ->
	  match retrieve (vfa#add_int offset) with
	  | Some fe -> result := (fe,api) :: !result
	  | _ -> ()) vfp.cppvf_table) ;
      !result
    end

  method get_instance_functions =
    H.fold (fun dwindex fintf acc ->
        let fa = TR.tget_ok (index_to_doubleword dwindex) in
        if self#is_class_function fa then
          acc
        else (fa, fintf.fintf_name) :: acc)
      function_interfaces []

  method get_class_functions =
    List.map (fun (fa, fintf) -> (fa, fintf.fintf_name)) cstatic_functions

  method is_class_function (fa: doubleword_int) =
    List.exists (fun (dw, _) -> dw#equal fa) cstatic_functions

  method get_member (offset:int) =
    if H.mem members offset then
      H.find members offset
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No class member found in class ";
                STR cname;
		STR " at offset ";
                INT offset]))

  method has_member (offset:int) = H.mem members offset

  method dm_iter (f:(cpp_datamember_t -> unit)) =
    let dataMembers = ref [] in
    let _ =
      H.iter
        (fun _ m ->
          match m with
          | DataMember dm -> dataMembers := dm :: !dataMembers
          | _ -> ()) members in
    List.iter f !dataMembers

  method vf_iter (f:(cpp_vfpointer_t -> unit)) =
    let vfMembers = ref [] in
    let _ = H.iter (fun _ m ->
      match m with VFPtr vf -> vfMembers := vf :: !vfMembers | _ -> ()) members in
    List.iter f !vfMembers

  method stats_to_pretty =
    let is_data_member m = match m with DataMember _ -> true | _ -> false in
    let nDataMembers = List.length (List.filter is_data_member cmembers) in
    let nVtables =
      List.length (List.filter (fun m -> not (is_data_member m)) cmembers) in
    let nVFunctions = List.fold_left (fun a m ->
      match m with
      | DataMember _ -> a
      | VFPtr p -> a + H.length p.cppvf_table) 0 cmembers in
    let prQ n s m =
      if n = 0 then
        STR ""
      else
	if n = 1 then
          LBLOCK [INT n; STR " "; STR s; STR "; "] 
	else
          LBLOCK [INT n; STR " "; STR m; STR "; "] in
    LBLOCK [
        prQ nDataMembers "data member" "data members";
	prQ nVtables "vtable" "vtables";
	prQ (List.length cconstructors) "constructor" "constructors";
	prQ nVFunctions "virtual function" "virtual functions";
	prQ (List.length cnon_virtual_functions) 
	  "non-virtual function" "non-virtual functions";
	prQ (List.length cstatic_functions) "static function" "static functions"]

end


let cpp_classes = H.create 3


let get_cpp_class name = 
  try
    H.find cpp_classes name 
  with
    Not_found ->
    raise (BCH_failure (LBLOCK [STR "Class "; STR name; STR " not found"]))


let get_cpp_classes () =  H.fold (fun _ v a -> v :: a) cpp_classes []


let is_class_type (ty:btype_t) =
  match ty with
  | TPtr (TNamed (name,_),_) -> H.mem cpp_classes name 
  | _ -> false


let get_class_from_type (ty:btype_t) =
  match ty with
  | TPtr (TNamed (name,_),_) -> get_cpp_class name
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "No class found for type ";
	       STR (btype_to_string ty)]))


let read_xml_cpp_data_member (node:xml_element_int) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let getc = node#getTaggedChild in
  { cppdm_name = get "name" ;
    cppdm_offset = geti "offset" ;
    cppdm_size = geti "size" ;
    cppdm_type = read_xml_type (getc "type") }    

let read_xml_vtable (node:xml_element_int) (cname:string) =
  let table = H.create 5 in
  let getcc = node#getTaggedChildren in
  let  _ = List.iter (fun n ->
    let geti = n#getIntAttribute in
    let getc = n#getTaggedChild in
    let offset = geti "offset" in
    let fintf = read_xml_function_interface (getc "api") in
    let fintf = { fintf with fintf_name = cname ^ "::" ^ fintf.fintf_name } in
    if H.mem table offset then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Duplicate offset in vtable for ";
		STR fintf.fintf_name;
		STR " at offset ";
                INT offset]))
    else
      H.add table offset fintf) (getcc "vf") in
  table


let read_xml_vfpointer (node:xml_element_int) (cname:string) =
  let geti = node#getIntAttribute in
  let geta n = string_to_doubleword (node#getAttribute "a") in
  { cppvf_offset = geti "offset";
    cppvf_address = TR.tget_ok (geta node);
    cppvf_table = read_xml_vtable node cname}


let read_xml_cpp_class_members (node:xml_element_int) (cname:string) =
  List.map (fun n ->
    match n#getAttribute "kind" with
    | "data" -> DataMember (read_xml_cpp_data_member n)
    | "vfptr" -> VFPtr (read_xml_vfpointer n cname)
    | s ->
       raise
         (BCH_failure
	    (LBLOCK [STR s; STR " not recognized for class member kind "])))
    (node#getTaggedChildren "member")


let read_xml_static_functions (node:xml_element_int) (cname:string) =
  List.map (fun n ->
    let get n = n#getAttribute in
    let getc = n#getTaggedChild  in
    let geta n = TR.tget_ok (string_to_doubleword (get n "a")) in
    let fintf = read_xml_function_interface (getc "api") in
    let fintf = { fintf with fintf_name = cname ^ "::" ^ fintf.fintf_name } in
    (geta n, fintf)) (node#getTaggedChildren "sf")


let read_xml_constructors (node:xml_element_int) (cname:string) =
  List.map (fun n ->
    let get n = n#getAttribute in
    let getc = n#getTaggedChild in
    let geta n = TR.tget_ok (string_to_doubleword (get n "a")) in
    let fintf = read_xml_function_interface (getc "api") in
    let fintf = { fintf with fintf_name = cname ^ "::" ^ fintf.fintf_name } in
    (geta n, fintf)) (node#getTaggedChildren "cf")


let read_xml_non_virtual_functions (node:xml_element_int) (cname:string) =
  List.map (fun n ->
    let get n = n#getAttribute in
    let getc = n#getTaggedChild in
    let geta n = TR.tget_ok (string_to_doubleword (get n "a")) in
    let fintf = read_xml_function_interface (getc "api") in
    let fintf = { fintf with fintf_name = cname ^ "::" ^ fintf.fintf_name } in
    (geta n, fintf)) (node#getTaggedChildren "nvf")
  

let read_xml_cpp_class (node:xml_element_int) =
  let getc = node#getTaggedChild in
  let name = node#getAttribute "name" in
  let members = read_xml_cpp_class_members (getc "members") name in
  let staticFunctions =
    (fun n -> read_xml_static_functions n name) (getc "static-functions") in
  let constructors =
    (fun n -> read_xml_constructors n name) (getc "constructors") in
  let nonVirtualFunctions =
    (fun n -> read_xml_non_virtual_functions n name)
      (getc "non-virtual-functions") in
  new cpp_class_t name members staticFunctions constructors nonVirtualFunctions


let add_user_cpp_class_file (name:string) =
  if H.mem cpp_classes name then () else
    match load_userdata_cpp_class_file name with
    | Some node ->
      let c = read_xml_cpp_class node in
      begin
	H.add cpp_classes c#get_name c ;
	chlog#add "user cpp class" 
	  (LBLOCK [STR c#get_name; STR ": "; c#stats_to_pretty])
      end
    | _ ->
      raise (BCH_failure (LBLOCK [STR "No class file found for "; STR name]))
