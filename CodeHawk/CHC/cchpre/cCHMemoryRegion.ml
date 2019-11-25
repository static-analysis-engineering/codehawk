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
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHPreTypes
open CCHIndexedCollections
open CCHMemoryBase

module P = Pervasives

let pr2s = CHPrettyUtil.pretty_to_string

module MemoryBaseCollections =
  CHCollections.Make (
      struct
        type t = memory_base_t
        let compare = memory_base_compare
        let toPretty = memory_base_to_pretty
      end)

class memory_region_t
        ~(vard:vardictionary_int)
        ~(index:int)
        ~(memory_base:memory_base_t):memory_region_int =
object (self:'a)

  method index = index
  method compare (other:'a) = P.compare index other#index

  method is_valid =
    match memory_base with
    | CNull _
      | CStringLiteral _
      | CStackAddress _
      | CGlobalAddress _
      | CBaseVar _  -> true
    | CUninterpreted _ -> false


  method get_memory_base = memory_base

  method get_base_var =
    match memory_base with
    | CBaseVar v -> v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "memory region is not a base variable: " ;
                          self#toPretty ]))

  method get_stack_var =
    match memory_base with
    | CStackAddress v -> v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "memory region is not a stack variable: " ;
                          self#toPretty ]))

  method get_null_region =
    match memory_base with
    | CNull i -> i
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "memory region is not a null region: " ;
                          self#toPretty ]))

  method is_stack_region =
    match memory_base with CStackAddress _ -> true | _ -> false

  method is_string_region =
    match memory_base with CStringLiteral _ -> true | _ -> false

  method is_basevar_region =
    match memory_base with CBaseVar _ -> true | _ -> false

  method is_null = match memory_base with CNull _ -> true | _ -> false

  method is_not_null =
    match memory_base with
    | CNull _
      | CBaseVar _
      | CUninterpreted _ -> false
    | _ -> true

  method is_uninterpreted =
    match memory_base with CUninterpreted _ -> true | _ -> false

  method write_xml (node:xml_element_int) =
    begin
      vard#write_xml_memory_base node memory_base ;
      node#setIntAttribute "index" index
    end      
                                   
  method toPretty = memory_base_to_pretty memory_base
end

let read_xml_memory_region
      (vard:vardictionary_int) (node:xml_element_int):memory_region_int =
  let memory_base = vard#read_xml_memory_base node in
  let index = node#getIntAttribute "index" in
  new memory_region_t ~vard ~index ~memory_base

class memory_region_table_t =
object (self)

  inherit [ memory_base_t, memory_region_int ] indexed_table_with_retrieval_t as super

  val map = new MemoryBaseCollections.table_t

  method insert = map#set
  method lookup = map#get
  method values = map#listOfValues

  method reset = begin map#removeList map#listOfKeys ; super#reset end

end

class memory_region_manager_t (vard:vardictionary_int):memory_region_manager_int =
object (self)

  val table = new memory_region_table_t

  method get_memory_region (index:int) =
    try
      table#retrieve index
    with
      _ -> raise (CCHFailure
                    (LBLOCK [ STR "No memory region found with index " ;
                              INT index ]))

  method mk_base_region memory_base  =
    table#add memory_base (fun index ->
                new memory_region_t ~vard ~index ~memory_base)

  method mk_null i =
    let memory_base = CNull i in
    table#add memory_base (fun index ->
                new memory_region_t ~vard ~index ~memory_base)

  method mk_string_region (s:string)  =
    let memory_base = CStringLiteral s in
    table#add memory_base (fun index ->
                new memory_region_t ~vard ~index ~memory_base)

  method mk_stack_region (v:variable_t) =
    let memory_base = CStackAddress v in
    table#add memory_base (fun index ->
                new memory_region_t ~vard ~index ~memory_base)

  method mk_global_region (v:variable_t) =
    let memory_base = CGlobalAddress v in
    table#add memory_base (fun index ->
                new memory_region_t ~vard ~index ~memory_base)

  method mk_external_region (v:variable_t) =
    let memory_base = CBaseVar v in
    table#add memory_base (fun index ->
                new memory_region_t ~vard ~index ~memory_base)

  method mk_uninterpreted_region (s:string) =
    let s = if s = "" then "none" else s in
    let memory_base = CUninterpreted s in
    table#add memory_base (fun index ->
                new memory_region_t ~vard ~index ~memory_base)

  method private mk_sym r =
    new symbol_t ~seqnr:r#index (pr2s r#toPretty)

  method mk_base_region_sym b =
    self#mk_sym (self#mk_base_region b)

  method mk_null_sym i =
    self#mk_sym (self#mk_null i)

  method mk_string_region_sym (s:string) =
    self#mk_sym (self#mk_string_region s)

  method mk_stack_region_sym (v:variable_t) =
    self#mk_sym (self#mk_stack_region v)

  method mk_global_region_sym (v:variable_t) =
    self#mk_sym (self#mk_global_region v)

  method mk_external_region_sym (v:variable_t) =
    self#mk_sym (self#mk_external_region v)

  method mk_uninterpreted_sym (s:string) =
    self#mk_sym (self#mk_uninterpreted_region s)

  method get_null_syms =
    List.fold_left (fun acc v ->
        match v#get_memory_base with
        | CNull i -> (self#mk_null_sym i) :: acc
        | _ -> acc) [] table#values

  method get_basevar_regions =
    List.filter (fun r -> r#is_basevar_region) table#values

  method is_null (index:int) =
    (self#get_memory_region index)#is_null

  method is_string_region (index:int) =
    (self#get_memory_region index)#is_string_region

  method is_not_null (index:int) =
    (self#get_memory_region index)#is_not_null

  method is_valid (index:int) =
    (self#get_memory_region index)#is_valid

  method is_uninterpreted (index:int) =
    (self#get_memory_region index)#is_uninterpreted

  method write_xml (node:xml_element_int) =
    table#write_xml node "region" (fun node r -> r#write_xml node)

  method read_xml (node:xml_element_int) =
    let get_value = read_xml_memory_region vard in
    let get_key r = r#get_memory_base in
    let get_index r = r#index in
    table#read_xml node get_value get_key get_index


end

let mk_memory_region_manager = new memory_region_manager_t
