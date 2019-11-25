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
open CHUtils
   
(* chutil *)
open CHPrettyUtil
open CHXmlDocument
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHUtilities

(* cchpre *)
open CCHPODictionary
open CCHPOPredicate
open CCHPreSumTypeSerializer
open CCHPreTypes

module H = Hashtbl
module P = Pervasives

let contexts = CCHContext.ccontexts
let cdecls = CCHDeclarations.cdeclarations

let join_invs (invs1:int list) (invs2:int list):int list =
  let s = new IntCollections.set_t in
  begin
    s#addList invs1 ;
    s#addList invs2 ;
    List.sort P.compare  s#toList
  end

let join_dependencies (d1:dependencies_t) (d2:dependencies_t) =
  match (d1,d2) with
  | (DStmt, _) -> d2
  | (_, DStmt) -> d1
  | (DUnreachable _, _) -> d2   (* note: it would be better to keep these explicit *)
  | (_, DUnreachable _) -> d1
  | (DLocal invs1, DLocal invs2) -> DLocal (join_invs invs1 invs2)
  | (DLocal invs1, DReduced (invs2,assumptions))
    | (DReduced (invs2,assumptions), DLocal invs1) ->
     DReduced (join_invs invs1 invs2, assumptions)
  | (DReduced (invs1,assumptions1),DReduced (invs2,assumptions2)) ->
     DReduced (join_invs invs1 invs2, assumptions1 @ assumptions2)
  | (DLocal invs1, DEnvC (invs2,assumptions))
    | (DEnvC (invs2, assumptions), DLocal invs1) ->
     DEnvC (join_invs invs1 invs2, assumptions)
  | (DReduced (invs1,assumptions1), DEnvC (invs2,assumptions2))
    | (DEnvC (invs2,assumptions2), DReduced (invs1,assumptions1)) ->
     DEnvC  (join_invs invs1 invs2, assumptions1 @ assumptions2)
  | (DEnvC (invs1,assumptions1), DEnvC (invs2,assumptions2)) ->
     DEnvC (join_invs invs1 invs2, assumptions1 @ assumptions2)

let write_xml_dependencies
      (node:xml_element_int)
      (pod:podictionary_int)
      (d:dependencies_t) =
  let set = node#setAttribute in
  let _ = set "deps" (dependencies_mcts#ts d) in
  match d with
  | DStmt -> ()
  | DLocal invs -> set "invs" (String.concat "," (List.map string_of_int invs))
  | DReduced (invs,assumptions)
    | DEnvC (invs,assumptions) ->
     let ids = List.map pod#index_assumption assumptions in
     begin
       set "invs" (String.concat "," (List.map string_of_int invs)) ;
       set "ids" (String.concat "," (List.map string_of_int ids))
     end
  | DUnreachable domain -> set "domain" domain

let read_xml_dependencies
      (node:xml_element_int)
      (pod:podictionary_int):dependencies_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  try
    let invs =
      if has "invs" then
        let invs = get "invs" in
        if (String.length invs) > 0 then
          List.map int_of_string (nsplit ',' invs)
        else
          []
      else
        [] in
    match get "deps" with
    | "s" -> DStmt
    | "f" -> DLocal invs
    | "r" ->
       let ids =
         if has "ids" then
           List.map pod#get_assumption
                    (List.map int_of_string (nsplit ',' (get "ids")))
         else
           [] in
       DReduced (invs,ids)
    | "a" ->
       let ids =
         if has "ids" then
           List.map pod#get_assumption
                    (List.map int_of_string (nsplit ',' (get "ids")))
         else
           [] in
       DEnvC (invs,ids)
    | "x" -> DUnreachable (get "domain")
    | s ->
       raise (CCHFailure (LBLOCK [ STR "Dependency indicator " ; STR s  ;
                                   STR " not recognized" ]))
  with
    Failure _ ->
    raise (CCHFailure
             (LBLOCK [ STR "read_xml_dependencies: int_of_string on " ;
                       STR (if has "invs" then (get "invs") else " -- ") ;
                       STR " and " ;
                       STR (if has "ids" then (get "ids") else " -- ") ]))

let get_po_type_location (pt:po_type_t) =
  match pt with
  | PPO (PPOprog (loc,_,_))
    | PPO (PPOlib (loc,_,_,_,_))
    | SPO (CallsiteSPO (loc,_,_,_))
    | SPO (ReturnsiteSPO (loc,_,_,_))
    | SPO (LocalSPO (loc,_,_)) -> loc

let get_po_type_context (pt:po_type_t) =
  match pt with
  | PPO (PPOprog (_,ctxt,_))
    | PPO (PPOlib (_,ctxt,_,_,_))
    | SPO (CallsiteSPO (_,ctxt,_,_))
    | SPO (ReturnsiteSPO (_,ctxt,_,_))
    | SPO (LocalSPO (_,ctxt,_)) -> ctxt

let get_po_type_predicate (pt:po_type_t) =
  match pt with
  | PPO (PPOprog (_,_,pred))
    | PPO (PPOlib (_,_,pred,_,_))
    | SPO (CallsiteSPO (_,_,pred,_))
    | SPO (ReturnsiteSPO (_,_,pred,_))
    | SPO (LocalSPO (_,_,pred)) -> pred

class diagnostic_t =
object (self)

  val invarianttable = H.create 1
  val argmessages = H.create 1          (* arg index -> msg list *)
  val keymessages = H.create 1          (* key -> msg list *)
  val messages = new StringCollections.set_t

  method clear =
    begin H.clear invarianttable ; messages#removeList messages#toList end

  method set_invariants (index:int) (invariants:int list) =
    H.replace invarianttable index invariants

  method get_invariants =
    H.fold (fun k v acc -> (k,v) :: acc) invarianttable []

  method add_msg (s:string) = messages#add s

  method add_arg_msg (index:int) (s:string) =
    let entry =
      if H.mem argmessages index then
        H.find argmessages index
      else
        let entry = new StringCollections.set_t in
        begin
          H.add argmessages index entry ;
          entry
        end in
    entry#add s

  method add_key_msg (key:string) (s:string) =
    let entry =
      if H.mem keymessages key then
        H.find keymessages key
      else
        let entry = new StringCollections.set_t in
        begin
          H.add keymessages key entry ;
          entry
        end in
    entry#add s

  method private get_arg_messages =
    H.fold (fun k v acc -> (k,v#toList) :: acc) argmessages []

  method private get_key_messages =
    H.fold (fun k v acc -> (k,v#toList) :: acc) keymessages []
    
  method arg_messages_to_pretty =
    let arg_messages = self#get_arg_messages in
    let flat_messages = List.map ( fun(_, x) -> x) arg_messages in
    let flat_messages = List.flatten flat_messages in
    LBLOCK (List.map ( fun s -> LBLOCK [ STR s ; NL] ) flat_messages )

  method key_messages_to_pretty =
    let key_messages = self#get_key_messages in
    let flat_messages = List.map ( fun(_, x) -> x) key_messages in
    let flat_messages = List.flatten flat_messages in
    LBLOCK (List.map ( fun s -> LBLOCK [ STR s ; NL] ) flat_messages )

  method is_empty =
    (H.length invarianttable) = 0
    && (H.length argmessages = 0)
    && messages#isEmpty

  method write_xml (node:xml_element_int) =
    let inode = xmlElement "invs" in
    let mnode = xmlElement "msgs" in
    let anode = xmlElement "amsgs" in
    let knode = xmlElement "kmsgs" in
    begin
      (inode#appendChildren
        (List.map (fun (index,invs) ->
             let xnode = xmlElement "arg" in
             begin
               xnode#setIntAttribute "a" index ;
               xnode#setAttribute "i" (String.concat "," (List.map string_of_int invs)) ;
               xnode
             end) self#get_invariants)) ;
      (anode#appendChildren
         (List.map (fun (index,msgs) ->
              let xnode = xmlElement "arg" in
              begin
                xnode#setIntAttribute "a" index;
                xnode#appendChildren
                  (List.map (fun msg ->
                       let snode = xmlElement "msg" in
                       begin snode#setAttribute "t" msg ; snode end) msgs) ;
                xnode
              end) self#get_arg_messages)) ;
      (knode#appendChildren
         (List.map (fun (key,msgs) ->
              let xnode = xmlElement "key" in
              begin
                xnode#setAttribute "k" key ;
                xnode#appendChildren
                  (List.map (fun msg ->
                       let snode = xmlElement "msg" in
                       begin snode#setAttribute "t" msg ; snode end) msgs) ;
                xnode
              end) self#get_key_messages)) ;
      (mnode#appendChildren
         (List.map (fun s ->
              let snode = xmlElement "msg" in
              begin snode#setAttribute "t" s ; snode end) messages#toList)) ;
      node#appendChildren [ inode ; mnode ; anode ; knode ]
    end

  method read_xml (node:xml_element_int) =
    let inode = node#getTaggedChild "invs" in
    let mnode = node#getTaggedChild "msgs" in
    let anode = node#getTaggedChild "amsgs" in
    let knode = node#getTaggedChild "kmsgs" in
    begin
      (List.iter (fun n ->
           let invs = List.map int_of_string (nsplit ',' (n#getAttribute "i")) in
           H.add invarianttable (n#getIntAttribute "a") invs)
                 (inode#getTaggedChildren "arg")) ;
      (List.iter (fun n ->
           let amsgs = List.map (fun k -> k#getAttribute "t") (n#getTaggedChildren "msg") in
           List.iter (self#add_arg_msg (n#getIntAttribute "a")) amsgs)
                 (anode#getTaggedChildren "arg")) ;
      (List.iter (fun n ->
           let kmsgs = List.map (fun k -> k#getAttribute "t") (n#getTaggedChildren "msg") in
           List.iter (self#add_key_msg (n#getAttribute "k")) kmsgs)
                 (knode#getTaggedChildren "key")) ;
      (List.iter (fun n -> self#add_msg (n#getAttribute "t"))
                 (mnode#getTaggedChildren "msg")) 
    end

  method toPretty =
    LBLOCK (List.map (fun s -> LBLOCK [ STR s ; NL ]) messages#toList)
        

end
      
         
   
class proof_obligation_t
        (pod:podictionary_int)
        (pt:po_type_t):proof_obligation_int =
object (self)

  val mutable status = Orange
  val mutable dependencies = None
  val mutable diagnostic = new diagnostic_t       (* information on reason for failure of discharge *)
  val mutable explanation = None
  val mutable timestamp = None

  method index = -1

  method set_status s =
    begin
      status <- s ;
      if self#is_closed then diagnostic#clear
    end                      

  method set_dependencies d = dependencies <- Some d

  method set_explanation e = explanation <- Some e

  method add_diagnostic_msg = diagnostic#add_msg

  method set_diagnostic_invariants = diagnostic#set_invariants

  method add_diagnostic_arg_msg = diagnostic#add_arg_msg

  method add_diagnostic_key_msg = diagnostic#add_key_msg

  method set_resolution_timestamp t = timestamp <- Some t

  method get_timestamp =
    match timestamp with
    | Some t -> t
    | _ ->
       raise (CCHFailure (LBLOCK [ STR "Proof obligation has not been resolved yet" ]))

  method get_location = get_po_type_location pt

  method get_context = get_po_type_context pt

  method get_predicate = get_po_type_predicate pt

  method get_explanation = match explanation with Some t -> t | _ -> "none"

  method get_diagnostic = diagnostic

  method get_dependencies = dependencies

  method is_closed = not (status = Orange)

  method is_violation = status = Red

  method is_opaque = is_opaque self#get_predicate

  method get_status = status

  method is_ppo = match pt with | PPO _ -> true | _ -> false

  method write_xml (node:xml_element_int) =
    begin
      (if diagnostic#is_empty then
         ()
       else
         let dnode = xmlElement "d" in
         begin
           diagnostic#write_xml dnode ;
           node#appendChildren [ dnode ] ;
         end) ;
      (match status with
       | Orange -> ()
       | _ -> node#setAttribute "s" (po_status_mfts#ts status)) ;
      (match explanation with
       | Some e ->
          let enode = xmlElement "e" in
          begin enode#setAttribute "txt" e ; node#appendChildren [ enode ] end
       | _ -> ()) ;
      (match dependencies with
       | Some d -> write_xml_dependencies node pod d
       | _ -> ()) ;
      (match timestamp with
       | Some t -> node#setAttribute "ts" t
       | _ -> ()) ;
    end

  method toPretty =
    LBLOCK [ STR "  " ; po_predicate_to_pretty self#get_predicate ; STR "  " ;
             STR (po_status_mfts#ts status) ; NL ]

end

class ppo_t
        (pod:podictionary_int)
        (pt:ppo_type_t): proof_obligation_int =
object

  inherit proof_obligation_t pod (PPO pt) as super

  method is_ppo = true

  method index = pod#index_ppo_type pt

  method write_xml (node:xml_element_int) =
    begin
      super#write_xml node ;
      pod#write_xml_ppo_type node pt
    end

  method toPretty =
    LBLOCK [ STR "ppo " ; INT (pod#index_ppo_type pt) ; super#toPretty ]

end

let mk_ppo = new ppo_t
                                
class callsite_spo_t
        (pod:podictionary_int)
        (st:spo_type_t): proof_obligation_int =
object

  inherit proof_obligation_t pod (SPO st) as super

  method index = pod#index_spo_type st

  method is_ppo = false

  method write_xml (node:xml_element_int) =
    begin
      super#write_xml node ;
      pod#write_xml_spo_type node st
    end

  method toPretty =
    LBLOCK [ STR "spo " ; INT (pod#index_spo_type st) ; super#toPretty ]

end

class returnsite_spo_t
        (pod:podictionary_int)
        (st:spo_type_t): proof_obligation_int =
object

  inherit proof_obligation_t pod (SPO st) as super

  method index = pod#index_spo_type st

  method is_ppo = false

  method write_xml (node:xml_element_int) =
    begin
      super#write_xml node ;
      pod#write_xml_spo_type node st
    end

  method toPretty =
    LBLOCK [ STR "spo " ; INT (pod#index_spo_type st) ; super#toPretty ]

end

let mk_returnsite_spo = new returnsite_spo_t

class local_spo_t
        (pod:podictionary_int)
        (st:spo_type_t): proof_obligation_int =
object

  inherit proof_obligation_t pod (SPO st) as super

  method index = pod#index_spo_type st

  method is_ppo = false

  method  write_xml (node:xml_element_int) =
    begin
      super#write_xml node ;
      pod#write_xml_spo_type node st
    end

  method toPretty =
    LBLOCK [ STR "spo " ; INT (pod#index_spo_type st) ; super#toPretty ]

end

let mk_local_spo = new local_spo_t
                      
let read_xml_proof_obligation
      (node:xml_element_int) (pod:podictionary_int) (po:proof_obligation_int) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasTaggedChild in 
  begin
    (if has "s" then
       let status = po_status_mfts#fs (get "s") in
       po#set_status status) ;
    (if hasc "e" then
       po#set_explanation ((getc "e")#getAttribute "txt")) ;
    (if hasc "d" then
       po#get_diagnostic#read_xml (getc "d")) ;
    (if has "deps" then
       po#set_dependencies (read_xml_dependencies node pod)) ;
    (if has "ts" then
       po#set_resolution_timestamp (node#getAttribute "ts")) 
  end

let read_xml_ppo (node:xml_element_int) (pod:podictionary_int) =
  let ppotype = pod#read_xml_ppo_type node in
  let ppo = new ppo_t pod ppotype in
  begin
    read_xml_proof_obligation node pod ppo ;
    ppo
  end

let read_xml_callsite_spo (node:xml_element_int) (pod:podictionary_int) =
  let spotype = pod#read_xml_spo_type node in
  let spo = new callsite_spo_t pod spotype in
  begin
    read_xml_proof_obligation node pod spo ;
    spo
  end

let read_xml_returnsite_spo (node:xml_element_int) (pod:podictionary_int) =
  let spotype = pod#read_xml_spo_type node in
  let spo = new returnsite_spo_t pod spotype in
  begin
    read_xml_proof_obligation node pod spo ;
    spo
  end

let read_xml_local_spo (node:xml_element_int) (pod:podictionary_int) =
  let spotype = pod#read_xml_spo_type node in
  let spo = new local_spo_t pod spotype in
  begin
    read_xml_proof_obligation node pod spo ;
    spo
  end

