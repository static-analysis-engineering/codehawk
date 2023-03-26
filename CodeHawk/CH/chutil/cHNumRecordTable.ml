(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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

(** data structure to store records identified by numerical id's *)

(* chlib *)
open CHCommon
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

module H = Hashtbl


class type num_record_table_int =
  object
    method reset: unit
    method add: int -> (string list * int list) -> unit
    method get: int -> (string list * int list)
    method items: (int * (string list * int list)) list
    method size: int
    method get_name: string
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
  end


class num_record_table_t (name:string):num_record_table_int =
object (self)

  val table = H.create 3       (* index -> (tags,args) *)

  method reset = H.clear table

  method add (id:int) (data:string list * int list) =
    if H.mem table id then
      raise
        (CHFailure
           (LBLOCK [
                STR "Attempt to add multiple values for id ";
                INT id;
                STR " to record table ";
                STR name]))
    else
      H.add table id data
    
  method get (id:int):(string list * int list) =
    if H.mem table id then
      H.find table id
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "Item with id ";
                INT id;
                STR " not found in table ";
                STR name]))
    
  method size = H.length table

  method get_name = name

  method items = H.fold (fun k v r -> (k,v) :: r) table []

  method write_xml (node:xml_element_int) =
    let items = List.sort Stdlib.compare self#items in
    node#appendChildren
      (List.map (fun (k,(tags,args)) ->
           let knode = xmlElement "n" in
           let set = knode#setAttribute in
           begin
             knode#setIntAttribute "id" k;
             (match tags with
              | [] -> () | _ -> set "t" (String.concat "," tags));
             (match args with
              | [] -> ()
              | _ -> set "a" (String.concat  "," (List.map string_of_int args)));
             knode
           end) items)

  method read_xml (node:xml_element_int) =
    List.iter (fun n ->
        let get = n#getAttribute in
        let has = n#hasNamedAttribute in
        let id = n#getIntAttribute "id" in
        let tags = if has "t" then nsplit '.' (get "t") else [] in
        let args =
          try
            if has "a" then
              List.map int_of_string (nsplit ',' (get "a"))
            else
              []
          with
          | Failure _ ->
             raise
               (CHFailure
                  (LBLOCK [
                       STR "int_of_string on ";
                       STR (get "a");
                       STR " in table ";
                       STR name]))  in
        self#add id (tags, args)) (node#getTaggedChildren "n")
    
end


let mk_num_record_table = new num_record_table_t
