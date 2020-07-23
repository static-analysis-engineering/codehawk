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

module H = Hashtbl
module P = Pervasives

let pr2s = CHPrettyUtil.pretty_to_string

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


class memory_region_manager_t
        (vard:vardictionary_int):memory_region_manager_int =
object (self)

  val table = H.create 3
  val vard = vard

  initializer
    List.iter
      (fun (index,memory_base) ->
        H.add table index (new memory_region_t ~vard ~index ~memory_base))
      vard#get_indexed_memory_bases

  method get_memory_region (index:int) =
    if H.mem table index then
      H.find table index
    else
      raise
        (CCHFailure
           (LBLOCK [ STR "No memory region found with index: " ; INT index ]))

  method private mk_memory_region (memory_base:memory_base_t) =
    let index = vard#index_memory_base memory_base in
    if H.mem table index then
      H.find table index
    else
      let region = new memory_region_t ~vard ~index ~memory_base in
      begin
        H.add table index region;
        region
      end

  method mk_base_region memory_base =
    self#mk_memory_region memory_base

  method mk_null i =
    self#mk_memory_region (CNull i)

  method mk_string_region (s:string) =
    self#mk_memory_region (CStringLiteral s)

  method mk_stack_region (v:variable_t) =
    self#mk_memory_region (CStackAddress v)

  method mk_global_region (v:variable_t) =
    self#mk_memory_region (CGlobalAddress v)

  method mk_external_region (v:variable_t) =
    self#mk_memory_region (CBaseVar v)

  method mk_uninterpreted_region (s:string) =
    let s = if s = "" then "none" else s in
    self#mk_memory_region (CUninterpreted s)

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
    H.fold (fun k v acc ->
        match v#get_memory_base with
        | CNull i -> (self#mk_null_sym i) :: acc
        | _ -> acc) table []

  method get_basevar_regions =
    H.fold (fun k v acc ->
        if v#is_basevar_region then
          v :: acc
        else
          acc) table []

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

end

let mk_memory_region_manager = new memory_region_manager_t
