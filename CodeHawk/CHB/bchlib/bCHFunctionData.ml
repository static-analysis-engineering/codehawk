(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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

(* chlib *)
open CHPretty

(* chutil *)
open CHIndexTable
open CHNumRecordTable
open CHXmlDocument

(* bchcil *)
open BCHCBasicTypes

(* bchlib *)
open BCHBasicTypes
open BCHDemangler
open BCHDoubleword
open BCHLibTypes
open BCHVariableType

module H = Hashtbl
module TR = CHTraceResult


let bd = BCHDictionary.bdictionary


class function_data_t (fa:doubleword_int) =
object (self)

  val mutable names = []
  val mutable non_returning = false
  val mutable incomplete = false
  val mutable ida_provided = false
  val mutable user_provided = false
  val mutable by_preamble = false
  val mutable virtual_function = false
  val mutable classinfo = None
  val mutable inlined = false
  val mutable library_stub = false
  val mutable inlined_blocks = []
  val mutable functiontype = t_unknown

  method set_function_type (ty: btype_t) = functiontype <- ty

  method set_non_returning = non_returning <- true

  method set_inlined = inlined <- true

  method set_by_preamble = by_preamble <- true

  method set_incomplete = incomplete <- true

  method set_ida_provided = ida_provided <- true

  method set_user_provided = user_provided <- true

  method set_virtual = virtual_function <- true

  method set_library_stub = library_stub <- true

  method add_name (s:string) =
    if List.mem s names then () else names <- s::names

  method set_class_info ~(classname:string) ~(isstatic:bool) =
    classinfo <- Some (classname,isstatic)

  method add_inlined_block (baddr:doubleword_int) =
    inlined_blocks <- baddr :: inlined_blocks

  method is_inlined_block (baddr:doubleword_int) =
    List.exists (fun a -> a#equal baddr) inlined_blocks

  method get_inlined_blocks = inlined_blocks

  method has_inlined_blocks =
    match inlined_blocks with [] -> false | _ -> true

  method get_names = names

  method get_function_type = functiontype

  method has_function_type =
    match functiontype with
    | TUnknown _ -> false
    | _ -> true

  method get_function_name =
    if self#has_name then
      let make_name name = demangle name in
      let rec aux thisnames =
        match thisnames with
        | [ name ] -> make_name name
        | name :: tl ->
           let name = make_name name in
           if String.contains name '@' then
             aux tl
           else
             name
        | _ -> raise (BCH_failure (STR "Internal error in get_function_name")) in
      aux names
    else
      raise (BCH_failure
               (LBLOCK [
                    STR "Function at address: ";
                    fa#toPretty;
                    STR " does not have a name"]))

  method has_name = (List.length names) > 0

  method is_non_returning = non_returning

  method is_incomplete = incomplete

  method is_virtual = virtual_function

  method is_user_provided = user_provided

  method is_ida_provided = ida_provided

  method is_inlined = inlined

  method is_library_stub = library_stub

  method has_class_info =
    match classinfo with Some _ -> true | _ -> false

  method to_rep_record =
    let args = [] in
    let tags = [] in
    let tags = if non_returning then "nr" :: tags else tags in
    let tags = if incomplete then "nc" :: tags else tags in
    let tags = if ida_provided then "ida" :: tags else tags in
    let tags = if user_provided then "u" :: tags else tags in
    let tags = if virtual_function then "v" :: tags else tags in
    let tags = if self#has_class_info then "c" :: tags else tags in
    let tags = if library_stub then "l" :: tags else tags in
    let tags = if by_preamble then "pre" :: tags else tags in
    let args =
      match classinfo with
      | Some (cname,isstatic) ->
         args @ [ bd#index_string cname ; (if isstatic then 1 else 0) ]
      | _ -> args in
    let args = args @ (List.map bd#index_string self#get_names) in
    (tags,args)

end


class functions_data_t:functions_data_int =
object (self)

  val table = H.create 5
  val nametable = H.create 5

  method reset = H.clear table

  method add_function (fa:doubleword_int) =
    let ix = fa#index in
    if H.mem table ix then
      H.find table ix
    else
      let fe = new function_data_t fa in
      begin
        H.add table ix fe ;
        fe
      end

  method get_function (fa: doubleword_int) =
    if self#is_function_entry_point fa then
      H.find table fa#index
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Function data not found for address: "; fa#toPretty]))

  method has_function (fa: doubleword_int) =
    self#is_function_entry_point fa

  method get_functions = H.fold (fun _ v a -> v::a) table []

  method get_function_entry_points =
    let inlinedfns = self#retrieve_addresses (fun f -> f#is_inlined) in
    let otherfns = self#retrieve_addresses (fun f -> not f#is_inlined) in
    inlinedfns @ otherfns

  method get_library_stubs =
    self#retrieve_addresses (fun f -> f#is_library_stub)

  method is_function_entry_point (fa:doubleword_int) = H.mem table fa#index

  method has_function_name (fa:doubleword_int) =
    (H.mem table fa#index)
    && (H.find table fa#index)#has_name

  method private initialize_nametable =
    H.iter (fun k v ->
        if v#has_name then H.add nametable (List.hd v#get_names) k) table

  method has_function_by_name (name: string): doubleword_int option =
    let _ =
      if (H.length nametable) = 0 then
        self#initialize_nametable in
    if H.mem nametable name then
      Some (TR.tget_ok (index_to_doubleword (H.find nametable name)))
    else
      None

  method private retrieve (f:function_data_int -> bool) =
    H.fold (fun _ v a -> if f v then v::a else a) table []

  method private retrieve_addresses (f:function_data_int -> bool) =
    H.fold (fun ix v a ->
        if f v then (TR.tget_ok (index_to_doubleword ix))::a else a) table []

  method private count (f:function_data_int -> bool) =
    H.fold (fun _ v a -> if f v then a+1 else a) table 0

  method get_ida_provided_functions =
    self#retrieve (fun fd -> fd#is_ida_provided)

  method get_ida_provided_function_entry_points =
    self#retrieve_addresses (fun fd -> fd#is_ida_provided)

  method get_user_provided_count =
    self#count (fun fd -> fd#is_user_provided)

  method get_ida_provided_count =
    self#count (fun fd -> fd#is_ida_provided)

  method write_xml (node:xml_element_int) =
    let recordtable = mk_num_record_table "function-entries" in
    begin
      H.iter (fun ix e -> recordtable#add ix e#to_rep_record) table ;
      recordtable#write_xml node
    end

  method read_xml (node:xml_element_int) =
    let recordtable = mk_num_record_table "function-entries" in
    begin
      recordtable#read_xml node ;
      List.iter (fun (ix, (tags, args)) ->
          let fa = TR.tget_ok (index_to_doubleword ix) in
          let fe = self#add_function fa in
          let a = a "function-data" args in
          let setnames l = List.iter (fun i -> fe#add_name (bd#get_string i)) l in
          begin
            (if List.mem "nr" tags then fe#set_non_returning);
            (if List.mem "nc" tags then fe#set_incomplete);
            (if List.mem "ida" tags then fe#set_ida_provided);
            (if List.mem "pre" tags then fe#set_by_preamble);
            (if List.mem "u" tags then fe#set_user_provided);
            (if List.mem "v" tags then fe#set_virtual);
            (if List.mem "l" tags then fe#set_library_stub);
            (if List.mem "c" tags then
               let classname = bd#get_string (a 0) in
               let isstatic = (a 1) = 1 in
               begin
                 fe#set_class_info ~classname ~isstatic ;
                 setnames (get_list_suffix args 2)
               end
             else
               setnames args)
          end) recordtable#items
    end

end


let functions_data = new functions_data_t
    
    
