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
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHDeclarations
open CCHDictionary
open CCHExternalPredicate
open CCHFileContract
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHPreTypes
open CCHProofObligation

module H = Hashtbl

let cd = CCHDictionary.cdictionary
let cdecls = CCHDeclarations.cdeclarations
let id = CCHInterfaceDictionary.interface_dictionary


class callsite_t
    (pod:podictionary_int)
    ?(apispos:(int,proof_obligation_int list) H.t=H.create 1)
    ?(postassumes:annotated_xpredicate_t list=[])
    (loc:location)
    (ctxt:program_context_int)
    (header:string)
    (args:exp list) =
object (self)

  val spos = H.create 3

  initializer
    H.iter (fun k v -> H.add spos k v) apispos ;

  method get_arguments = args

  method get_location = loc

  method get_context = ctxt

  method get_header = header

  method get_spos = H.fold (fun _ v r -> v@r) spos []

  method get_postassumes = postassumes

  method get_spos_table = spos

  method private get_spo_lists = H.fold (fun k v r -> (k,v)::r) spos []

  method write_xml (node:xml_element_int) =
    let iargs = List.map cd#index_exp args in
    let aanode = xmlElement "api-conditions" in
    begin
      aanode#appendChildren
         (List.map (fun (apiid,spos) ->
              let anode = xmlElement "api-c" in
              begin
                anode#appendChildren
                  (List.map (fun spo ->
                       let snode = xmlElement "po" in
                       begin spo#write_xml snode ; snode end) spos) ;
                anode#setIntAttribute "iapi" apiid ;
                anode
              end) self#get_spo_lists) ;
      (if (List.length postassumes) > 0 then
         let ppnode = xmlElement "post-assumes" in    (* TBD: add annotations *)
         let iipcs = List.map (fun (i,_) -> id#index_xpredicate i) postassumes in
         begin
           ppnode#setAttribute "iipcs" (String.concat "," (List.map string_of_int iipcs)) ;
           node#appendChildren [ ppnode ]
         end) ;
      node#appendChildren [ aanode ] ;
      cdecls#write_xml_location node loc ;
      ccontexts#write_xml_context node ctxt ;
      (if header = "" then ()  else  node#setAttribute "header" header);
      node#setAttribute "iargs" (String.concat "," (List.map string_of_int iargs))
    end

end

let read_xml_callsite (node:xml_element_int) (pod:podictionary_int):callsite_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasTaggedChild in
  let iargs =
    try
      List.map int_of_string (nsplit ',' (get "iargs"))
    with
      Failure _ ->
      raise (CCHFailure (LBLOCK [ STR "read_xml_callsite: int_of_string on " ;
                                  STR (get "iargs") ])) in
  try
    let args = List.map cd#get_exp iargs in
    let ctxt = ccontexts#read_xml_context node in
    let loc = cdecls#read_xml_location node in
    let header = if node#hasNamedAttribute "header" then get "header" else "" in
    let apispos = H.create 3 in
    let _ =
      List.iter
        (fun anode ->
          let spos =
            List.map (fun snode -> read_xml_callsite_spo snode pod)
                     (anode#getTaggedChildren "po") in
          let apiid = anode#getIntAttribute "iapi" in
          H.add apispos apiid spos)
        ((node#getTaggedChild "api-conditions")#getTaggedChildren "api-c") in
    let postassumes =
      if hasc "post-assumes" then
        let iipcs =
          List.map int_of_string
                   (nsplit ',' ((getc "post-assumes")#getAttribute "iipcs")) in
        List.map (fun i ->
            (simplify_xpredicate (id#get_xpredicate i),NoAnnotation)) iipcs   (* TBD: add annotations *)
      else
        [] in
    new callsite_t pod ~apispos ~postassumes loc ctxt header args
  with
  | Failure s ->
     raise (CCHFailure (LBLOCK [ STR "Failure in read xml callsite: " ; STR s ]))
  
class direct_callsite_t
        (pod:podictionary_int)
        ?(apispos=H.create 1)
        ?(postassumes=[])
        (loc:location)
        (ctxt:program_context_int)
        (header:string)
        (callee:varinfo)
        (args:exp list):direct_callsite_int =
object

  inherit callsite_t pod ~apispos ~postassumes loc ctxt header args as super

  method get_callee = callee

  method write_xml (node:xml_element_int) =
    begin
      super#write_xml node ;
      cdecls#write_xml_varinfo node callee
    end

end

let read_xml_direct_callsite
      (node:xml_element_int) (pod:podictionary_int):direct_callsite_int =
  try
    let cs = read_xml_callsite node pod in
    let callee = cdecls#read_xml_varinfo node in
    new direct_callsite_t
        pod ~apispos:cs#get_spos_table ~postassumes:cs#get_postassumes
        cs#get_location cs#get_context cs#get_header callee cs#get_arguments
  with
  | Failure s ->
     raise (CCHFailure (LBLOCK [ STR "Failure in read xml direct callsite " ]))

class indirect_callsite_t
        (pod:podictionary_int)
        ?(apispos=H.create 1)
        ?(callees=[])
        ?(postassumes=[])
        (loc:location)
        (ctxt:program_context_int)
        (header:string)
        (callexp:exp)
        (args:exp list):indirect_callsite_int =
object

  val mutable callees = callees

  inherit callsite_t pod ~apispos ~postassumes loc ctxt header args as super

  method set_callees (l:varinfo list) = callees <- l

  method get_callexp = callexp

  method get_callees = callees

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let icallees = List.map cdecls#index_varinfo callees in
    begin
      super#write_xml node ;
      cd#write_xml_exp node callexp ;
      (if header = "" then () else set "header" header) ;
      (match icallees with
       | [] -> ()
       | [c] ->
          begin
            cdecls#write_xml_varinfo node (List.hd callees) ;
            seti "icallees" c
          end
       | l -> set "icallees" (String.concat "," (List.map string_of_int l)))
    end

end

let read_xml_indirect_callsite
      (node:xml_element_int) (pod:podictionary_int):indirect_callsite_int =
  let has = node#hasNamedAttribute in
  try
    let cs = read_xml_callsite node pod in
    let callexp = cd#read_xml_exp node in
    let icallees =
      if has "icallees" then
        try
          List.map int_of_string (nsplit ',' (node#getAttribute "icallees"))
        with
        | Failure _ ->
           raise (CCHFailure
                    (LBLOCK [ STR "read_xml_indirect_callsite: int_of_string on " ;
                              STR (node#getAttribute "icallees") ]))
      else
        [] in
    let callees = List.map cdecls#get_varinfo icallees in
    (try
      new indirect_callsite_t
          pod ~apispos:cs#get_spos_table ~callees ~postassumes:cs#get_postassumes
          cs#get_location cs#get_context cs#get_header callexp cs#get_arguments
     with
     | Failure s ->
        raise (CCHFailure (LBLOCK [ STR "Failure in creating indirect callsite: " ;
                                    STR s ])))
  with
  | Failure s ->
     raise (CCHFailure (LBLOCK [ STR "Failure in read xml indirect callsite: " ; STR s ]))

class callsite_manager_t (fname:string) (pod:podictionary_int):callsite_manager_int =
object (self)

  val directcalls = H.create 13         (* ictxt -> callsite_int *)
  val indirectcalls = H.create 1        (* ictxt -> callsite_int *)

  method add_direct_call
           (loc:location)
           (ctxt:program_context_int)
           ?(header="")
           (callee:varinfo)
           (args:exp list) =
    let ictxt = ccontexts#index_context ctxt in
    let callsite = new direct_callsite_t pod loc ctxt header callee args in
    H.add directcalls ictxt callsite

  method add_indirect_call
           (loc:location)
           (ctxt:program_context_int)
           ?(header="")
           (callee:exp)
           (args:exp list) =
    let ictxt = ccontexts#index_context ctxt in
    let callsite = new indirect_callsite_t pod loc ctxt header callee args in
    H.add indirectcalls ictxt callsite

  method create_contract_proof_obligations = ()

  method get_call_count = (H.length directcalls) + (H.length indirectcalls)

  method get_spos =
    (List.concat (H.fold (fun _ v r -> v#get_spos::r) directcalls [])) @
      (List.concat (H.fold (fun _ v r -> v#get_spos::r) indirectcalls []))

  method get_direct_callsites =
    H.fold (fun _ v a -> v::a) directcalls []

  method get_indirect_callsites =
    H.fold (fun _ v a -> v::a) indirectcalls []

  method get_direct_callsite (ctxt:program_context_int) =
    let ictxt = ccontexts#index_context ctxt in
    if H.mem directcalls ictxt then
      H.find directcalls ictxt
    else
      raise (CCHFailure (LBLOCK [ STR "Callsite not found for context " ; INT ictxt ]))

  method get_indirect_callsite (ctxt:program_context_int) =
    let ictxt = ccontexts#index_context ctxt in
    if H.mem indirectcalls ictxt then
      H.find indirectcalls ictxt
    else
      raise (CCHFailure (LBLOCK [ STR "Indirect callsite not found for context " ;
                                  INT ictxt ]))

  method has_direct_callsite (ctxt:program_context_int) =
    let ictxt = ccontexts#index_context ctxt in
    H.mem directcalls ictxt

  method has_indirect_callsite (ctxt:program_context_int) =
    let ictxt = ccontexts#index_context ctxt in
    H.mem indirectcalls ictxt

  method write_xml (node:xml_element_int) =
    let ddnode = xmlElement "direct-calls" in
    let iinode = xmlElement "indirect-calls" in
    begin
      ddnode#appendChildren
        (List.map (fun d ->
             let dnode = xmlElement "dc" in
             begin d#write_xml dnode ; dnode end)
                  (H.fold (fun _ v r -> v::r) directcalls [])) ;
      iinode#appendChildren
        (List.map (fun i->
             let inode = xmlElement "ic" in
             begin i#write_xml inode ; inode end)
                  (H.fold (fun _ v r -> v::r) indirectcalls [])) ;
      node#appendChildren [ ddnode ; iinode ]
    end

  method read_xml (node:xml_element_int) =
    let hasc = node#hasTaggedChild in
    let getcc tag = (node#getTaggedChild tag)#getTaggedChildren in
    try
      begin
        (if hasc "direct-calls" then
           List.iter (fun dnode ->
               let d = read_xml_direct_callsite dnode pod in
               let ictxt = ccontexts#index_context d#get_context in
               H.add directcalls ictxt d ) (getcc "direct-calls" "dc") );
        (if hasc "indirect-calls" then
           List.iter (fun inode ->
               let i = read_xml_indirect_callsite inode pod in
               let ictxt = ccontexts#index_context i#get_context in
               H.add indirectcalls ictxt i) (getcc "indirect-calls" "ic") )
      end
    with
    | Failure s ->
       raise (CCHFailure
                (LBLOCK [ STR "Failure in callsite manager:read_xml: " ; STR s ]))

end

let mk_callsite_manager = new callsite_manager_t
  
