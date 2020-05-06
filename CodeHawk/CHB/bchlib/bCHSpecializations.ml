(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

module H = Hashtbl

let block_restriction_to_string (r:block_restriction_t) =
  match r with
  | BranchAssert true -> "true"
  | BranchAssert false -> "false"

class specialization_t
        (name:string)
        (fns: (string * (string * block_restriction_t) list) list) =
object

  val restrictions =
    let tf = H.create 3 in
    let _ =
      List.iter (fun (fa,blist) ->
          let tb = H.create (List.length blist) in
          let _ = List.iter (fun (ba,r) -> H.add tb ba r) blist in
          H.add tf fa tb) fns in
    tf

  method get_name = name

  method get_functions = H.fold (fun k _ a -> k::a) restrictions []

  method get_blocks (fa:string) =
    if H.mem restrictions fa then
      H.fold (fun k _ a -> k::a) (H.find restrictions fa) []
    else
      raise (BCH_failure (LBLOCK [ STR "No specialization found for " ; STR fa ]))

  method get_block_restriction (fa:string) (ba:string) =
    if H.mem restrictions fa then
      let tb = H.find restrictions fa in
      if H.mem tb ba then
        H.find tb ba
      else
        raise
          (BCH_failure
             (LBLOCK [ STR "Block " ; STR ba ; STR " not present for " ; STR fa ]))
    else
      raise
        (BCH_failure (LBLOCK [ STR "No specialization found for " ; STR fa ]))

  method has_block_restriction (fa:string) (ba:string) =
    (H.mem restrictions fa) && (H.mem (H.find restrictions fa) ba)

  method toPretty =
    LBLOCK [ STR name ; NL ;
    LBLOCK (List.map (fun (fa,blist) ->
                LBLOCK [ STR fa ; NL ;
                         INDENT(3, LBLOCK
                                     (List.map (fun (ba,r) ->
                                          LBLOCK [ STR ba ; STR ": " ; 
                                                   STR (block_restriction_to_string r) ;
                                                   NL ]) blist)) ; NL ]) fns) ]
end
          

class specializations_t:specializations_int =
object (self)

  val specializations = H.create 3   (* specialization name -> specialization *)
  val functions = H.create 3                  (* faddr -> specialization name *)
  val mutable active = []

  method activate_specialization s =
    begin
      chlog#add "use specialization" (STR s) ;
      active <- s :: active
    end

  method has_specialization (fa:string) = H.mem functions fa

  method get_specialization (fa:string) =
    if self#has_specialization fa then
      let name = H.find functions fa in
      H.find specializations name
     else
       raise (BCH_failure
                (LBLOCK [ STR "No specialization active for " ; STR fa ]))

  method private read_xml_specialization (node:xml_element_int) =
    let get = node#getAttribute in
    let getc = node#getTaggedChildren in
    let name = get "name" in
    let fns =
      List.map (fun n ->
          let fa = n#getAttribute "fa" in
          let blist =
            List.map (fun nn ->
                let ba = nn#getAttribute "ba" in
                let r = BranchAssert ((nn#getAttribute "branch") = "true") in
                (ba,r)) (n#getTaggedChildren "block") in
          (fa,blist) ) (getc "fn") in
    let spc = new specialization_t name fns in
    begin
      H.add specializations name spc ;
      (if List.mem name active then
         begin
           chlog#add "activate specialization" (STR name) ;
           List.iter (fun fa -> H.add functions fa name) spc#get_functions
         end)
    end

  method read_xml (node:xml_element_int) =
    begin
      List.iter self#read_xml_specialization
                (node#getTaggedChildren "specialization") ;
      chlog#add "specializations" self#toPretty
    end

  method toPretty =
    LBLOCK [ STR "active: " ; STR (String.concat ", " active) ; NL ;
             LBLOCK (List.map (fun s -> s#toPretty)
                              (H.fold (fun _ v a -> v::a) specializations [])) ]
    
end

let specializations = new specializations_t
