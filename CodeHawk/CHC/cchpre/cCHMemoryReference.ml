(* =============================================================================
   CodeHawk C Analyzer 
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
open CHLanguage
open CHPretty

(* chutil *)
open CHXmlDocument
   
(* xprlib *)
open Xprt

(* cchlib *)
open CCHBasicTypes
open CCHDictionary
open CCHTypesCompare
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHPreTypes
open CCHIndexedCollections
open CCHMemoryBase

module H = Hashtbl
module P = Pervasives

let cd = CCHDictionary.cdictionary
    	
class memory_reference_t
        ~(vard:vardictionary_int)
        ~(index:int)
        ~(data:memory_reference_data_t):memory_reference_int =
object (self:'a)
  
  method index = index
    
  method compare (other:'a) = P.compare index other#index

  method get_data = data
    
  method get_base = data.memrefbase 
    
  method get_type = data.memreftype
    
  method get_name = memory_base_to_string data.memrefbase

  method has_base_variable =
    match data.memrefbase with
    | CStackAddress _
      | CGlobalAddress _
      | CBaseVar _ -> true
    | _ -> false

  method get_base_variable =
    match  data.memrefbase with
    | CStackAddress v
      | CGlobalAddress v
      | CBaseVar v -> v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Memory reference does not have a base variable: " ;
                          self#toPretty ]))
    
  method get_stack_address_var =
    match data.memrefbase with
    | CStackAddress v -> v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Not a regular stack address: " ;
                          STR self#get_name ]))

  method get_global_address_var =
    match data.memrefbase with
    | CGlobalAddress v -> v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Not a global address: " ; STR self#get_name ]))
      
  method get_external_basevar =
    match data.memrefbase with
    | CBaseVar v -> v
    | _ ->
       raise (CCHFailure 
		(LBLOCK [ STR "Not a base variable: " ; STR self#get_name ]))
      
  method has_external_base =
    match data.memrefbase with CBaseVar _ -> true | _ -> false
    
  method is_stack_reference =
    match data.memrefbase with CStackAddress _ -> true | _ -> false

  method is_global_reference =
    match data.memrefbase with CGlobalAddress _ -> true | _ -> false

  method write_xml (node:xml_element_int) =
    begin
      vard#write_xml_memory_reference_data node data ;
      node#setIntAttribute "index" index
    end
    
  method toPretty = STR self#get_name 
    
end

  
class memory_reference_manager_t
        (vard:vardictionary_int):memory_reference_manager_int =
object (self)
  
  val table = H.create 3
  val vard = vard

  initializer
    List.iter
      (fun (index,data) ->
        H.add table index (new memory_reference_t ~vard ~index ~data))
      vard#get_indexed_memory_reference_data

  method get_memory_reference (index:int) =
    if H.mem table index then
      H.find table index
    else
      raise
        (CCHFailure
           (LBLOCK [ STR "No memory reference found with index: "  ; INT index ]))

  method private mk_memory_reference (data:memory_reference_data_t) =
    let index = vard#index_memory_reference_data data in
    if H.mem table index then
      H.find table index
    else
      let memref = new memory_reference_t ~vard ~index ~data in
      begin
        H.add table index memref;
        memref
      end

  method mk_string_reference (s:string) (typ:typ) =
    let data = { memrefbase = CStringLiteral s ; memreftype = typ } in
    self#mk_memory_reference data
    
  method mk_stack_reference (v:variable_t) (typ:typ) =
    let data = { memrefbase = CStackAddress v ; memreftype = typ } in
    self#mk_memory_reference data

  method mk_global_reference (v:variable_t) (typ:typ) =
    let data = { memrefbase = CGlobalAddress v ; memreftype = typ } in
    self#mk_memory_reference data
      
  method mk_external_reference (v:variable_t) (typ:typ) =
    let data = { memrefbase = CBaseVar v ; memreftype = typ } in
    self#mk_memory_reference data

end
  
let mk_memory_reference_manager = new memory_reference_manager_t
  
