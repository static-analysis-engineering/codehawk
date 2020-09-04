(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma

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
open CHUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities   
open BCHDoubleword
open BCHLibTypes
open BCHStrings

(* bchlibelf *)
open BCHELFTypes

let is_printable c = (c >= 32 && c < 127) || c = 10
  
let is_printable_char c = is_printable (Char.code c)

class elf_raw_section_t (s:string) (vaddr:doubleword_int):elf_raw_section_int =
object (self)

  method get_xstring = s

  method get_xsubstring (va:doubleword_int) (size:int) =
    if self#includes_VA va then
      try
        let start = (va#subtract vaddr)#to_int in
        String.sub s start size
      with Invalid_argument s ->
        raise
          (BCH_failure
             (LBLOCK [ STR "Invalid section substring request: ";
                       STR "vaddr: "; vaddr#toPretty;
                       STR "; start: "; va#toPretty;
                       STR "; length: "; INT size ;
                       STR ": "; STR s ]))
    else
      raise
        (BCH_failure
           (LBLOCK [ STR "Invalid section substring request: ";
                     STR "start address: "; va#toPretty;
                     STR " not included in section: "; vaddr#toPretty ]))

  method get_vaddr = vaddr

  method includes_VA (va:doubleword_int) =
    vaddr#le va && va#lt (vaddr#add_int (String.length s))

  method get_string_reference  (va:doubleword_int) =   (* absolute address *)
    if self#includes_VA va then
      let offset = (va#subtract vaddr)#to_int in
      if is_printable_char s.[offset] then
        let len =
          let i = ref 0 in
          begin
            while is_printable_char s.[offset + !i] do i := !i+1 done;
            !i
          end in
        if Char.code s.[offset+len] = 0 then
          let str = String.sub s offset len in
          let new_s = string_replace '\n' "\\n" str in
          begin
            string_table#add_string va new_s ;
            Some new_s
          end
        else
          None
      else
        None
    else
      None

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setx t x = set t x#to_hex_string in
    let bNode = xmlElement "hex-data" in
    begin
      write_xml_raw_data bNode s vaddr ;
      setx "vaddr" vaddr ;
      append [ bNode ] ;
      seti "size" (String.length s)
    end

  method toPretty = STR vaddr#to_hex_string

end


let mk_elf_raw_section = new elf_raw_section_t

let read_xml_elf_raw_section (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  let vaddr = string_to_doubleword (node#getAttribute "vaddr") in
  new elf_raw_section_t s vaddr
