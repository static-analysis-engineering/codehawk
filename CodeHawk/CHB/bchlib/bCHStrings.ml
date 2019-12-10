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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHLocation

module H = Hashtbl
   
let bd = BCHDictionary.bdictionary
       
class string_table_t:string_table_int =
object (self)
  
  val stringtable = H.create 3    (* addr-index -> string  *)
  val reftable = H.create 3       (* addr-index -> faddr -> ctxt-iaddress *)
    
  method add_string (a:doubleword_int) (str:string)=
    if H.mem stringtable a#index then () else H.add stringtable a#index str 

  method private add_faddr_entry
                   (a:doubleword_int) (faddr:doubleword_int) (ci:ctxt_iaddress_t)=
    let aentry =
      if H.mem reftable a#index then
        H.find reftable a#index
      else
        let t = H.create 3  in
        let _ = H.add reftable a#index t in
        t in
    let fentry =
      if H.mem aentry faddr#index  then
        H.find aentry faddr#index
      else
        let _ = H.add aentry faddr#index [] in
        H.find aentry faddr#index in
    if List.mem ci fentry then
      ()
    else
      H.replace aentry faddr#index (ci::fentry)
      
  method add_xref
           (stra:doubleword_int)
           (str:string)
           (faddr:doubleword_int)
           (ci:ctxt_iaddress_t) =
    begin
      if self#has_string stra then () else self#add_string stra str ;
      self#add_faddr_entry stra faddr ci
    end
            
  method get_string (a:doubleword_int) =
    if H.mem stringtable a#index then
      H.find stringtable a#index
    else
      raise (BCH_failure
               (LBLOCK [ STR "String not found for address " ; a#toPretty ]))

  method get_strings =
    H.fold (fun i s a -> (index_to_doubleword i,s) :: a) stringtable []

  method private get_string_xrefs
                   (a:doubleword_int):(doubleword_int * ctxt_iaddress_t) list =
    if H.mem reftable a#index then
      List.fold_left
        (fun acc (faddr,cis) ->
          (List.map (fun ci -> (faddr,ci)) cis) @ acc)
        []
        (H.fold
           (fun faddr cis acc ->
             (index_to_doubleword faddr,cis)::acc) (H.find reftable a#index) [])
    else
      []
	
  method has_string (a:doubleword_int) = H.mem stringtable a#index

  method read_xml (node:xml_element_int) =
    List.iter (fun n ->
        let a = string_to_doubleword (n#getAttribute "a") in
        let str = bd#read_xml_string n in
        begin
          self#add_string a str ;
          List.iter (fun x ->
              let f = string_to_doubleword (x#getAttribute "f") in
              let ci = x#getAttribute "ci"  in
              self#add_xref a str f ci) (n#getTaggedChildren "xref")
        end) (node#getTaggedChildren "string-xref")
        
    
  method write_xml (node:xml_element_int) =
    node#appendChildren 
      (List.map (fun (a,s) ->
	let sNode = xmlElement "string-xref" in
	begin
          bd#write_xml_string sNode s ;
          let sxrefs = self#get_string_xrefs a in    
          sNode#appendChildren
            (List.map (fun (faddr,(ci:ctxt_iaddress_t)) ->
                 let xnode = xmlElement "xref" in
                 begin
                   xnode#setAttribute "f" faddr#to_hex_string ;
                   xnode#setAttribute "ci" ci ;
                   xnode
                 end) sxrefs);
          sNode#setAttribute "a" a#to_hex_string ;
          sNode end ) self#get_strings)
end
  
let string_table = new string_table_t
  
