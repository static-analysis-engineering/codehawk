(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2025  Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHUtilities

(* cchpre *)
open CCHPreTypes

module H = Hashtbl

let (let* ) x f = CHTraceResult.tbind f x   

let ccontexts = CCHContext.ccontexts
let cdictionary = CCHDictionary.cdictionary
let fdecls = CCHDeclarations.cdeclarations


class copparam_call_dependency_arg_t
        (_pod: podictionary_int)
        (loc: location)
        (ctxt: program_context_int)
        (argument: exp) =
object (self)

  val mutable status: output_parameter_status_t = OpUnknown

  method loc: location = loc

  method ctxt: program_context_int = ctxt

  method argument: exp = argument

  method write_xml (node: xml_element_int) =
    begin
      fdecls#write_xml_location node self#loc;
      ccontexts#write_xml_context node self#ctxt;
      cdictionary#write_xml_exp node self#argument
    end

end


class copparam_call_dependency_t
        (pod: podictionary_int)
        (loc: location)
        (ctxt: program_context_int)
        (callee: exp) =
object (self)

  val callargs = H.create 3
  val mutable status: output_parameter_status_t = OpUnknown

  method loc: location = loc

  method ctxt: program_context_int = ctxt

  method callee: exp = callee

  method status: output_parameter_status_t = status

  method calldep_args: copparam_call_dependency_arg_t list =
    H.fold (fun _ v a -> v :: a) callargs []

  method add_copparam_call_dependency_arg
           (argloc: location) (argctxt: program_context_int) (arg:exp) =
    let ictxt = ccontexts#index_context argctxt in
    let ccda = new copparam_call_dependency_arg_t pod argloc argctxt arg in
    H.replace callargs ictxt ccda

  method write_xml (node: xml_element_int) =
    let xcallargs = xmlElement "copparam-call-dependency-args" in
    let _ = node#appendChildren [xcallargs] in
    begin
      fdecls#write_xml_location node self#loc;
      ccontexts#write_xml_context node self#ctxt;
      cdictionary#write_xml_exp node self#callee;
      xcallargs#appendChildren
        (List.map (fun callarg ->
             let xcallarg = xmlElement "callarg" in
             begin
               callarg#write_xml xcallarg;
               xcallarg
             end) self#calldep_args)
    end

end


class copparam_returnsite_t
        (pod: podictionary_int)
        (loc: location)
        (ctxt: program_context_int)
        (rv: exp option) =
object (self)

  val mutable status: output_parameter_status_t = OpUnknown

  method loc: location = loc

  method ctxt: program_context_int = ctxt

  method rv: exp option = rv

  method status: output_parameter_status_t = status

  method set_status (s: output_parameter_status_t) = status <- s

  method record_proof_obligation_result (po: proof_obligation_int) =
    match po#get_predicate with
    | POutputParameterInitialized _ when po#is_safe ->
       status <- OpWritten
    | POutputParameterUnaltered _ when po#is_safe ->
       status <- OpUnaltered
    | _ -> ()

  method write_xml (node: xml_element_int) =
    begin
      pod#write_xml_output_parameter_status node self#status;
      fdecls#write_xml_location node self#loc;
      ccontexts#write_xml_context node self#ctxt;
      cdictionary#write_xml_exp_opt node self#rv;
    end    

end


class candidate_output_parameter_t
        (pod: podictionary_int)
        (vinfo: varinfo): candidate_output_parameter_int =
object (self)

  val mutable status: output_parameter_status_t = OpUnknown
  val returnsites = H.create 3 (* ictxt -> copparam_returnsite_t *)
  val calldeps = H.create 3  (* ictxt ->  copparam_call_dependency_t *)
  val mutable reject_reasons: string list = []

  method parameter = vinfo

  method reject (reason: string) =
    begin
      reject_reasons <- reason :: reject_reasons;
      status <- OpRejected reject_reasons
    end

  method record_proof_obligation_result (po: proof_obligation_int) =
    match po#get_predicate with
    | PLocallyInitialized _ ->
       if po#is_violation then
         self#reject
           ("parameter is read at line " ^ (string_of_int po#get_location.line))
    | POutputParameterInitialized _
      | POutputParameterUnaltered _ ->
       let ictxt = ccontexts#index_context po#get_context in
       if H.mem returnsites ictxt then
         (H.find returnsites ictxt)#record_proof_obligation_result po
    | _ -> ()
       

  method is_active (_po_s: proof_obligation_int list) =
    match status with
    | OpUnknown -> true
    | _ -> false

  method status: output_parameter_status_t = status

  method add_returnsite
           (loc: location) (ctxt: program_context_int) (rv: exp option) =
    let rs = new copparam_returnsite_t pod loc ctxt rv in
    let ictxt = ccontexts#index_context ctxt in
    H.replace returnsites ictxt rs

  method private returnsites: copparam_returnsite_t list =
    H.fold (fun _ v a -> v :: a) returnsites []

  method add_call_dependency
           (loc: location)
           (ctxt: program_context_int)
           (callee: exp) =
    let cd: copparam_call_dependency_t =
      new copparam_call_dependency_t pod loc ctxt callee in
    let ictxt = ccontexts#index_context ctxt in
    H.replace calldeps ictxt cd

  method add_call_dependency_arg
           (loc: location)
           (callctxt: program_context_int)
           (argctxt: program_context_int)
           (argument: exp) =
    let ictxt = ccontexts#index_context callctxt in
    if H.mem calldeps ictxt then
      (H.find calldeps ictxt)#add_copparam_call_dependency_arg loc argctxt argument
    else
      raise
        (CCHFailure
           (LBLOCK [
                STR "Call dependency not found in parameter "; STR vinfo.vname]))

  method private call_dependencies: copparam_call_dependency_t list =
    H.fold (fun _ v a -> v :: a) calldeps []

  method private read_xml_returnsite (node: xml_element_int): unit traceresult =
  let loc = fdecls#read_xml_location node in
  let ctxt = ccontexts#read_xml_context node in
  let rv = cdictionary#read_xml_exp_opt node in
  let* status = pod#read_xml_output_parameter_status node in
  let rs = new copparam_returnsite_t pod loc ctxt rv in
  let _ = rs#set_status status in
  let ictxt = ccontexts#index_context ctxt in
  Ok (H.replace returnsites ictxt rs)

  method private read_xml_call_dependency (node: xml_element_int): unit traceresult =
    let loc = fdecls#read_xml_location node in
    let ctxt = ccontexts#read_xml_context node in
    let callee = cdictionary#read_xml_exp node in
    Ok (self#add_call_dependency loc ctxt callee)

  method read_xml (node: xml_element_int) =
    let rrnode = node#getTaggedChild "returnsites" in
    let ccnode = node#getTaggedChild "call-dependencies" in
    let* copstatus = pod#read_xml_output_parameter_status node in
    let* _ =
      tbind_iter_list self#read_xml_returnsite (rrnode#getTaggedChildren "rs") in
    let* _ =
      tbind_iter_list self#read_xml_call_dependency (ccnode#getTaggedChildren "cd") in
    Ok (status <- copstatus)

  method write_xml (node: xml_element_int) =
    let rrnode = xmlElement "returnsites" in
    let ccnode = xmlElement "call-dependencies" in
    let _ = node#appendChildren [rrnode; ccnode] in
    begin
      fdecls#write_xml_varinfo node self#parameter;
      pod#write_xml_output_parameter_status node self#status;
      rrnode#appendChildren
        (List.map (fun rs ->
             let rnode = xmlElement "rs" in
             begin
               rs#write_xml rnode;
               rnode
             end) self#returnsites);
      ccnode#appendChildren
        (List.map (fun cd ->
             let cnode = xmlElement "cd" in
             begin
               cd#write_xml cnode;
               cnode
             end) self#call_dependencies)
    end

end


let mk_candidate_output_parameter (pod: podictionary_int) (vinfo: varinfo) =
  new candidate_output_parameter_t pod vinfo


let read_xml_candidate_output_parameter
      (node: xml_element_int)
      (pod: podictionary_int): candidate_output_parameter_int traceresult =
  let vinfo = fdecls#read_xml_varinfo node in
  let candidate = mk_candidate_output_parameter pod vinfo in
  let* _ = candidate#read_xml node in
  Ok candidate
