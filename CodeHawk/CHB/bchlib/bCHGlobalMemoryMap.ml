(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024 Aarno Labs LLC

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
open BCHBCTypeUtil
open BCHDoubleword
open BCHLibTypes

module H = Hashtbl
module TR = CHTraceResult


let globalvalue_to_pretty (gv: globalvalue_t): pretty_t =
  match gv with
  | GConstantString s -> STR s
  | GScalarValue dw -> dw#toPretty


let global_location_rec_to_pretty (grec: global_location_rec_t): pretty_t =
  LBLOCK [
      STR "addr: "; grec.gloc_address#toPretty; NL;
      STR "name: "; STR grec.gloc_name; NL;
      STR "type: "; STR (btype_to_string grec.gloc_btype); NL;
      (match grec.gloc_size with
       | Some s -> LBLOCK [STR "size: "; INT s; NL]
       | _ -> STR "");
      (match grec.gloc_initialvalue with
       | Some init -> LBLOCK [STR "init: "; globalvalue_to_pretty init; NL]
       | _ -> STR "");
      (match grec.gloc_desc with
       | Some desc -> LBLOCK [STR "desc: "; STR desc; NL]
       | _ -> STR "");
      (if grec.gloc_is_readonly then LBLOCK [STR "readonly"; NL] else STR "");
      (if grec.gloc_is_initialized then LBLOCK [STR "initialized"; NL] else STR "")
    ]
         

class global_location_t (grec: global_location_rec_t): global_location_int =
object (self)

  method grec: global_location_rec_t = grec

  method name: string = grec.gloc_name

  method address: doubleword_int = grec.gloc_address

  method btype: btype_t = grec.gloc_btype

  method size: int option = grec.gloc_size

  method is_readonly: bool = grec.gloc_is_readonly

  method is_initialized: bool = grec.gloc_is_initialized

  method initialvalue: globalvalue_t option = grec.gloc_initialvalue

  method desc: string option = grec.gloc_desc

  method has_elf_symbol: bool =
    match self#desc with
    | Some "symbol-table" -> true
    | _ -> false

end


class global_memory_map_t: global_memory_map_int =
object (self)

  val locations = H.create 51
  val namedlocations = H.create 51   (* name -> ix *)

  method add_location
           ?(name = None)
           ?(desc = None)
           ?(is_readonly = false)
           ?(is_initialized = false)
           ?(btype = t_unknown)
           ?(initialvalue = None)
           ?(size = None)
           (address: doubleword_int) =
    if H.mem locations address#index then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Global location at address ";
                address#toPretty;
                STR " already exists"]))
    else
      let gname =
        match name with
        | Some name -> name
        | _ -> "gv_" ^ address#to_hex_string in
      let grec = {
          gloc_name = gname;
          gloc_address = address;          
          gloc_is_readonly = is_readonly;
          gloc_is_initialized = is_initialized;
          gloc_btype = btype;
          gloc_initialvalue = initialvalue;
          gloc_size = size;
          gloc_desc = desc
        } in
      let gloc = new global_location_t grec in
      begin
        H.add locations address#index gloc;
        H.add namedlocations gname address#index;
        chlog#add
          "global-memory-map:add-location"
          (LBLOCK [
               address#toPretty;
               STR ": ";
               STR gname;
               STR ":";
               STR (btype_to_string btype);
               STR "; ";
               (match size with
                | Some s -> LBLOCK [STR " (size: "; INT s; STR ")"]
                | _ -> STR "");
               (if is_readonly then STR " (RO) " else STR "");
               (if is_initialized then STR " (IV) " else STR "");
               (match desc with
                | Some desc -> LBLOCK [STR " ("; STR desc; STR ")"]
                | _ -> STR "")
          ])
      end

  method update_named_location (name: string) (vinfo: bvarinfo_t) =
    if self#has_name name then
      let ix = H.find namedlocations name in
      let grec = (H.find locations ix)#grec in
      let size = TR.to_option (size_of_btype vinfo.bvtype) in
      let newgrec = {
          grec with
          gloc_btype = vinfo.bvtype;
          gloc_size = size
        } in
      let newgloc = new global_location_t newgrec in
      begin
        H.replace locations ix newgloc;
        chlog#add
          "global-memory-map:update-location"
          (LBLOCK [
               newgrec.gloc_address#toPretty;
               STR ": ";
               STR newgrec.gloc_name;
               STR ":";
               STR (btype_to_string newgrec.gloc_btype);
               (match size with
                | Some s -> LBLOCK [STR " (size: "; INT s; STR ")"]
                | _ -> STR "")
          ])
      end
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No location found with name ";
                STR name;
                STR " in global memory map"]))               

  method has_name (name: string) = H.mem namedlocations name

  method has_elf_symbol (v: doubleword_int): bool =
    (H.mem locations v#index)
    && (H.find locations v#index)#has_elf_symbol

  method get_elf_symbol (v: doubleword_int): string =
    if self#has_elf_symbol v then
      (H.find locations v#index)#name
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Memory location at ";
                v#toPretty;
                STR " does not have an elf symbol"]))
                

end
    

let global_memory_map = new global_memory_map_t


let read_xml_symbolic_addresses (node: xml_element_int) =
  let get = node#getAttribute in
  let getx t =
    let tx = get t in
    fail_tvalue
      (trerror_record
         (STR ("BCHGlobalMemory.read_xml_symbolic_addresses:" ^ tx)))
      (string_to_doubleword tx) in
  let name = Some (get "name") in
  let address = getx "a" in
  global_memory_map#add_location ~name ~desc:(Some "userdata") address

                      
let read_xml_symbolic_addresses (node: xml_element_int) =
  List.iter read_xml_symbolic_addresses (node#getTaggedChildren "syma")


let update_global_location_type (vinfo: bvarinfo_t) =
  let name = vinfo.bvname in
  if global_memory_map#has_name name then
    global_memory_map#update_named_location name vinfo
  else if String.length name > 3 && (String.sub name 0 3) = "gv_" then
    let index = String.index name '_' in
    if String.contains_from name (index + 1) '_' then
      let eindex = String.index_from name (index + 1) '_' in
      let hex = String.sub name (index + 1) ((eindex - index) - 1) in
      let hex = "0x" ^ hex in
      match (string_to_doubleword hex) with
      | Error e ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Address: ";
                   STR hex;
                   STR " in global variable name ";
                   STR name;
                   STR " not recognized: ";
                   STR (String.concat "; " e)
           ]))
      | Ok dw ->
         global_memory_map#add_location
           ~name:(Some name)
           ~desc:(Some "header file")
           ~btype: vinfo.bvtype
           ~size:(TR.to_option (size_of_btype vinfo.bvtype))
           dw
    else
      chlog#add
        "global location not updated"
        (LBLOCK [STR vinfo.bvname; STR ": "; STR (btype_to_string vinfo.bvtype)])
  else
      chlog#add
        "global location not updated"
        (LBLOCK [STR vinfo.bvname; STR ": "; STR (btype_to_string vinfo.bvtype)])
         
                     
            
    
  
