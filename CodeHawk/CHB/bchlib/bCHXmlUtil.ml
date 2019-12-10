(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHLogger
open CHXmlDocument

(* xprlib *)
open XprXml

(* bchlibx86 *)
open BCHBasicTypes


(* ================================================================================
 * Xml naming conventions:
 * ------------------------
 * general:
 *    attributes:
 *     a  : address (in hex)
 *     ofs: offset (in decimal)
 * variables: 
 *    element tags:
 *     var : generic variable
 *    lvar : local variable
 *    attributes:
 *    vn : name of the variable
 *    vx : index of the variable
 * functions:
 *    attributes:
 *    fn : name of the function
 * ================================================================================= *)


exception XmlReaderError of int * int * pretty_t

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

class type xml_header_int =
object
  (* setters *)
  method set_header: string -> unit

  (* accessors *)
  method get_header: xml_element_int

  (* predicates *)
  method has_header: bool
end

class xml_header_t =
object

  val mutable header = None
    
  method set_header (name:string) =
    let node = xmlElement "header" in
    begin
      node#setAttribute "name" name ;
      node#setAttribute "date" (time_to_string (Unix.gettimeofday ())) ;
      header <- Some node
    end
      
  method get_header = match header with Some h -> h | _ ->
    raise (Invocation_error "xml_header#get_header")
      
  method has_header = match header with Some _ -> true | _ -> false
    
end
  
let xml_header = new xml_header_t

let variable_type = ref NUM_VAR_TYPE
let set_symbolic_type () =  variable_type := SYM_VAR_TYPE
  
let write_xml_variable (node:xml_element_int) (v:variable_t) (ntag:string) (xtag:string) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  begin
    seti xtag v#getName#getSeqNumber ;
    set ntag v#getName#getBaseName ;
  end
    
let read_xml_variable (node:xml_element_int) (ntag:string) (xtag:string) =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let seqnr = geti xtag in
  let vname = new symbol_t ~seqnr (get ntag) in
  new variable_t vname !variable_type    
    
let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l
    
let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done ;
    !h
  end
    
let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c -> if (Char.code c) < 32 || (Char.code c) > 126 then found  := true) s in
  !found

