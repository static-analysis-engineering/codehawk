(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper

(* bchlibelf *)
open BCHELFSection
open BCHELFTypes

module H = Hashtbl
module TR = CHTraceResult


class elf_string_table_t (s:string) (vaddr:doubleword_int):elf_string_table_int =
object (self)

  inherit elf_raw_section_t s vaddr

  val entries = H.create 3

  method set_entries =
    List.iter (fun (p, s) ->
        let strva = vaddr#add_int p in
        H.add entries strva#to_hex_string s) self#get_strings

  method get_string (index:int) =
    if index < 0 || index >= String.length s then
      raise
        (BCH_failure
           (LBLOCK [STR "String index out of bounds: "; INT index]))
    else if index = 0 then
      ""
    else
      let suffix = string_suffix s index in
      let input = IO.input_string suffix in
      IO.read_string input

  method get_string_at_address (a: doubleword_int): string option =
    if H.mem entries a#to_hex_string then
      Some (H.find entries a#to_hex_string)
    else
      None

  method private get_strings =
    let result = ref [] in
    let slen = String.length s in
    let ch = make_pushback_stream s in
    if slen > 0 then
      let _ = ch#skip_bytes 1 in
      begin
        while ch#pos < slen do
          let pos = ch#pos in
          let s = ch#read_string in
          result := (pos, s) :: !result
        done;
        !result
      end
    else
      []

  method write_xml_strings (node:xml_element_int) =
    node#appendChildren
      (List.map (fun (p,s) ->
           let snode = xmlElement "str" in
           begin
             snode#setAttribute "s" s;
             snode#setIntAttribute "p" p;
             snode
           end)
         self#get_strings)

end


let mk_elf_string_table = new elf_string_table_t


let read_xml_elf_string_table (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  let vaddr = TR.tget_ok (string_to_doubleword (node#getAttribute "vaddr")) in
  let stringtable = new elf_string_table_t s vaddr in
  begin
    stringtable#set_entries;
    stringtable
  end
