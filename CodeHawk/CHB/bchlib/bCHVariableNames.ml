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
open CHPretty
open CHLanguage
open CHNumerical
open CHNumericalConstraints

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes

(* bchutil *)
open CHLogger

module H = Hashtbl

class variable_names_t =
object (self)

  val table = H.create 53

  method add (index:int) (name:string) = 
    H.replace table index name

  method get (index:int) =
    if H.mem table index then H.find table index else
      raise (Invocation_error "variable_names_int#get")

  method has (index:int) = H.mem table index

  method write_xml (node:xml_element_int) =
    let entries = H.fold (fun k v a -> (k,v)::a) table [] in
    node#appendChildren
      (List.map (fun (k,v) ->
           let n = xmlElement "n" in
           begin
             n#setIntAttribute "vix" k ;
             n#setAttribute "name" v ;
             n
           end) entries)

  method read_xml (node:xml_element_int) =
    List.iter (fun n ->
        self#add (n#getIntAttribute "vix") (n#getAttribute "name"))
              (node#getTaggedChildren "n")

end

let make_variable_names () = new variable_names_t

