(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2024 Aarno Labs LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes
open BCHLocation

module H = Hashtbl


let id = BCHInterfaceDictionary.interface_dictionary


let write_xml_po_status (node: xml_element_int) (s: po_status_t) =
  match s with
  | Discharged s ->
     begin
       node#setAttribute "s" "dis";
       node#setAttribute "m" s
     end
  | Delegated x ->
     begin
       node#setAttribute "s" "del";
       id#write_xml_xxpredicate node x
     end
  | Requested (dw, x) ->
     begin
       node#setAttribute "s" "req";
       node#setAttribute "fn" dw#to_hex_string;
       id#write_xml_xxpredicate node x
     end
  | DelegatedGlobal (dw, x) ->
     begin
       node#setAttribute "s" "glob";
       node#setAttribute "ga" dw#to_hex_string;
       id#write_xml_xxpredicate node x
     end
  | Violated s ->
     begin
       node#setAttribute "s" "v";
       node#setAttribute "m" s
     end
  | Open -> node#setAttribute "s" "o"


class proofobligation_t
        (xpo: xpo_predicate_t)
        (loc: location_int)
        (status: po_status_t): proofobligation_int =
object

  method xpo = xpo

  method loc = loc

  method status = status

end


class proofobligations_t
        (faddr: doubleword_int)
        (xpod: xpodictionary_int): proofobligations_int =
object (self)

  val store = H.create 3

  method faddr = faddr

  method xpod = xpod

  method add_proofobligation
           (cia: ctxt_iaddress_t)
           (xpo: xpo_predicate_t)
           (status: po_status_t) =
    let loc = ctxt_string_to_location self#faddr cia in
    let po = new proofobligation_t xpo loc status in
    let entry =
      if H.mem store cia then
        H.find store cia
      else
        [] in
    H.replace store cia (po :: entry)

  method loc_proofobligations
           (cia: ctxt_iaddress_t): proofobligation_int list =
    if H.mem store cia then
      H.find store cia
    else
      []

  method private filter_proofobligations (f: proofobligation_int -> bool) =
    let result = ref [] in
    begin
      H.iter (fun _ polist ->
          List.iter
            (fun po ->
              if f po then
                result := po :: !result
              else
                ()) polist) store;
      !result
    end

  method open_proofobligations: proofobligation_int list =
    self#filter_proofobligations
      (fun po -> match po#status with Open -> true | _ -> false)

  method discharged_proofobligations: proofobligation_int list =
    self#filter_proofobligations
      (fun po -> match po#status with Discharged _ -> true | _ -> false)

  method violated_proofobligations: proofobligation_int list =
    self#filter_proofobligations
      (fun po -> match po#status with Violated _ -> true | _ -> false)

  method delegated_proofobligations: proofobligation_int list =
    self#filter_proofobligations
      (fun po -> match po#status with Delegated _ -> true | _ -> false)

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map
         (fun (iaddr, polist) ->
           let anode = xmlElement "loc" in
           begin
             anode#setAttribute "ia" iaddr;
             anode#appendChildren
               (List.map
                  (fun po ->
                    let ponode = xmlElement "po" in
                    begin
                      self#xpod#write_xml_xpo_predicate ponode po#xpo;
                      write_xml_po_status ponode po#status;
                      ponode
                    end) polist);
             anode
           end) (H.fold (fun k v acc -> (k, v) :: acc) store []))

end


let mk_proofobligations = new proofobligations_t
