(* =============================================================================
   CodeHawk C Analyzer 
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
  
let read_xml_memory_reference
      (vard:vardictionary_int) (node:xml_element_int):memory_reference_int =
  let data = vard#read_xml_memory_reference_data node in
  let index = node#getIntAttribute "index" in
  new memory_reference_t ~vard ~index ~data
  
module MemoryReferenceDataCollections = CHCollections.Make
  (struct
    type t = memory_reference_data_t
    let compare m1 m2 = memory_base_compare m1.memrefbase m2.memrefbase 
    let toPretty m =
      LBLOCK [ STR "(" ; memory_base_to_pretty m.memrefbase ; STR ")" ]
   end)
  
class memory_reference_table_t =
object (self)
  
  inherit [ memory_reference_data_t, memory_reference_int ] indexed_table_with_retrieval_t as super
    
  val map = new MemoryReferenceDataCollections.table_t
    
  method insert = map#set
  method lookup = map#get
  method values = map#listOfValues
    
  method reset = begin map#removeList map#listOfKeys ; super#reset end
    
end
  	
class memory_reference_manager_t (vard:vardictionary_int):memory_reference_manager_int =
object (self)
  
  val table = new memory_reference_table_t
    
  method reset = table#reset

  method mk_string_reference (s:string) (typ:typ) =
    let data = { memrefbase = CStringLiteral s ; memreftype = typ } in
    table#add data (fun index -> new memory_reference_t ~vard ~index ~data)
    
  method mk_stack_reference (v:variable_t) (typ:typ) =
    let data = { memrefbase = CStackAddress v ; memreftype = typ } in
    table#add data (fun index -> new memory_reference_t ~vard ~index ~data)

  method mk_global_reference (v:variable_t) (typ:typ) =
    let data = { memrefbase = CGlobalAddress v ; memreftype = typ } in
    table#add data (fun index -> new memory_reference_t ~vard ~index ~data)
      
  method mk_external_reference (v:variable_t) (typ:typ) =
    let data = { memrefbase = CBaseVar v ; memreftype = typ } in
    table#add data (fun index -> new memory_reference_t ~vard ~index ~data)
      
  method get_memory_reference (index:int) =
    try
      table#retrieve index
    with
      CCHFailure p ->
      raise (CCHFailure (LBLOCK [ STR "Memory reference not found: " ; p ]))

  method write_xml (node:xml_element_int) =
    table#write_xml node "reference" (fun node r -> r#write_xml node)

  method read_xml (node:xml_element_int) =
    let get_value = read_xml_memory_reference vard in
    let get_key r = r#get_data in
    let get_index r = r#index in
    table#read_xml node get_value get_key get_index
	  
end
  
let mk_memory_reference_manager = new memory_reference_manager_t
  
