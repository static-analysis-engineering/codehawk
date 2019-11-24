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
open CHPretty

(* chutil *)
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes

class virtual ['a, 'b] indexed_table_t :
  object
    val mutable next : int
    method add : 'a -> (int -> 'b) -> 'b
    method virtual add_xref : 'a -> 'b -> unit
    method virtual insert : 'a -> 'b -> unit
    method virtual lookup : 'a -> 'b option
    method reset : unit
  end
            
val table_to_pretty : (int, int) Hashtbl.t -> pretty_t
  
class virtual ['a, 'b] indexed_table_with_retrieval_t :
  object
    val mutable next : int
    val store : (int, 'b) Hashtbl.t
    method add : 'a -> (int -> 'b) -> 'b
    method private get_values : 'b list
    method virtual insert : 'a -> 'b -> unit
    method virtual lookup : 'a -> 'b option
    method read_xml :
      xml_element_int ->
      (xml_element_int -> 'b) ->
      ('b -> 'a) -> ('b -> int) -> unit
    method reset : unit
    method retrieve : int -> 'b
    method virtual values : 'b list
    method write_xml :
      xml_element_int ->
      string ->
      ?filter:('b -> bool) ->
      (xml_element_int -> 'b -> unit) -> unit
  end
