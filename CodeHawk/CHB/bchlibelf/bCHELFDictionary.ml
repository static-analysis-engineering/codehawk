(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHStringIndexTable
open CHXmlDocument

(* bchlibelf *)
open BCHELFTypes

class elf_dictionary_t:elf_dictionary_int =
object (self)

  val string_table = mk_string_index_table "string-table"

  val mutable tables = []

  initializer
    tables <- []

  method reset =
    begin
      string_table#reset ;
      List.iter (fun t ->  t#reset) tables
    end

  method index_string (s:string):int = string_table#add s

  method get_string (index:int) = string_table#retrieve index

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_string s)

  method read_xml_string ?(tag="istr") (node:xml_element_int):string =
    self#get_string (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    let snode = xmlElement string_table#get_name in
    begin
      string_table#write_xml snode;
      node#appendChildren [snode];
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables)
    end    

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      string_table#read_xml (getc string_table#get_name);
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

  method toPretty =
    LBLOCK [
        STR "string-table: ";
        INT string_table#size;
        NL;
        (LBLOCK
           (List.map (fun t ->
                LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables))]

end


let elfdictionary = new elf_dictionary_t
