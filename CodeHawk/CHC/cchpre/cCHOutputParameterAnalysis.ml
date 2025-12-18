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
open CCHTypesToPretty
open CCHUtilities
   
(* cchpre *)
open CCHCandidateOutputParameter
open CCHPreTypes

module H = Hashtbl

         
let (let* ) x f = CHTraceResult.tbind f x

let p2s = CHPrettyUtil.pretty_to_string

let ccontexts = CCHContext.ccontexts
let cdictionary = CCHDictionary.cdictionary
let fdecls = CCHDeclarations.cdeclarations


let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)
let elocm (line: int): string = (eloc line) ^ ": "


class op_callee_callsite_arg_t
        (pod: podictionary_int)
        (loc: location)
        (ctxt: program_context_int)
        (argument: exp) =
object (self)

  val mutable status: output_parameter_status_t = OpUnknown

  method loc: location = loc

  method ctxt: program_context_int = ctxt

  method argument: exp = argument

  method record_proof_obligation_result (_po: proof_obligation_int) = ()

  method write_xml (node: xml_element_int) =
    begin
      pod#write_xml_output_parameter_status node status;
      fdecls#write_xml_location node self#loc;
      ccontexts#write_xml_context node self#ctxt;
      cdictionary#write_xml_exp node self#argument
    end

end


class op_callee_callsite_t
        (pod: podictionary_int)
        (loc: location)
        (ctxt: program_context_int)
        (callee: exp) =
object (self)

  val callargs = H.create 3
  val mutable status: output_parameter_status_t = OpUnknown

  method callee: exp = callee

  method loc: location = loc

  method ctxt: program_context_int = ctxt

  method record_proof_obligation_result (_po: proof_obligation_int) = ()            

  method is_active (_po_s: proof_obligation_int list): bool =
    match status with
    | OpUnknown -> true
    | _ -> false

  method set_status (s: output_parameter_status_t) =
    status <- s                                   

  method add_callee_callsite_arg
           (argloc: location) (argctxt: program_context_int) (arg: exp) =
    let ictxt = ccontexts#index_context argctxt in
    let ccsa = new op_callee_callsite_arg_t pod argloc argctxt arg in
    H.replace callargs ictxt ccsa

  method callsite_args: op_callee_callsite_arg_t list =
    H.fold (fun _ v a -> v :: a) callargs []

  method write_xml (node: xml_element_int) =
    let xcallargs = xmlElement "callee-callsite-args" in
    let _ = node#appendChildren [xcallargs] in
    begin
      pod#write_xml_output_parameter_status node status;
      fdecls#write_xml_location node self#loc;
      ccontexts#write_xml_context node self#ctxt;
      cdictionary#write_xml_exp node self#callee;
      xcallargs#appendChildren
        (List.map (fun callarg ->
             let xcallarg = xmlElement "callarg" in
             begin
               callarg#write_xml xcallarg;
               xcallarg
             end) self#callsite_args)
    end

end

  
class output_parameter_analysis_digest_t
        (fname: string)
        (pod: podictionary_int): output_parameter_analysis_digest_int =
object (self)

  val params = H.create 3    (* vname -> candidate_output_parameter_int *)
  val callee_callsites = H.create 3  (* ctxt-ix -> op_callee_callsite_t *)

  method fname = fname

  method is_active (po_s: proof_obligation_int list) =
    ((List.length self#active_parameters) > 0)
    || (List.exists (fun cs -> cs#is_active po_s) self#callee_callsites)

  method active_parameters: candidate_output_parameter_int list =
    List.filter (fun param ->
        param#is_active []) (H.fold (fun _ v acc -> v :: acc) params [])

  method active_parameter_varinfos: varinfo list =
    List.map (fun param -> param#parameter) self#active_parameters

  method add_new_parameter (vinfo: varinfo): unit traceresult =
    if not (H.mem params vinfo.vname) then
      let param =
        CCHCandidateOutputParameter.mk_candidate_output_parameter pod vinfo in
      Ok (H.add params vinfo.vname param)
    else
      Error [(elocm __LINE__)
             ^ "Parameter with name " ^ vinfo.vname ^ " already exists"]

  method add_parameter (param: candidate_output_parameter_int): unit traceresult =
    let vname = param#parameter.vname in
    if not (H.mem params vname) then
      Ok (H.add params vname param)
    else
      Error [(elocm __LINE__)
           ^ "Parameter with name " ^ vname ^ " already exists"]

  method add_returnsite
           (loc: location) (ctxt: program_context_int) (rv: exp option) =
    List.iter (fun param ->
        param#add_returnsite loc ctxt rv) self#active_parameters

  method add_call_dependency
           (loc: location)
           (ctxt: program_context_int)
           (callee: exp) =
    List.iter (fun param ->
        param#add_call_dependency loc ctxt callee) self#active_parameters

  method add_call_dependency_arg
           (loc: location)
           (callctxt: program_context_int)
           (argctxt: program_context_int)
           (argument: exp) =
    List.iter (fun param ->
        param#add_call_dependency_arg loc callctxt argctxt argument)
      self#active_parameters

  method add_callee_callsite
           (loc: location)
           (ctxt: program_context_int)
           (callee: exp) =
    let ccs = new op_callee_callsite_t pod loc ctxt callee in
    let ictxt = ccontexts#index_context ctxt in
    H.replace callee_callsites ictxt ccs

  method add_callee_callsite_arg
           (loc: location)
           (callctxt: program_context_int)
           (argctxt: program_context_int)
           (argument: exp) =
    let ictxt = ccontexts#index_context callctxt in
    if H.mem callee_callsites ictxt then
      (H.find callee_callsites ictxt)#add_callee_callsite_arg loc argctxt argument
    else
      raise
        (CCHFailure
           (LBLOCK [
                STR "Callee callsite not found in function "; STR fname]))

  method private callee_callsites =
    H.fold (fun _ v a -> v :: a) callee_callsites []

  method reject_parameter
           (vname: string)
           (reason: output_parameter_rejection_reason_t): unit traceresult =
    if H.mem params vname then
      Ok ((H.find params vname)#reject reason)
    else
      Error [(elocm __LINE__)
             ^ "No parameter found for function " ^ fname ^ " with name " ^ vname]

  method record_proof_obligation_result
           (po: proof_obligation_int): unit traceresult =
    match po#get_predicate with
    | PLocallyInitialized (vinfo, _)
      | POutputParameterInitialized (vinfo, _)
      | POutputParameterUnaltered (vinfo, _)
      | POutputParameterScalar (vinfo, _)
      | POutputParameterNoEscape (vinfo, _) ->
       if H.mem params vinfo.vname then
         Ok ((H.find params vinfo.vname)#record_proof_obligation_result po)
       else
         Error [(elocm __LINE__)
                ^ "No corresponding return site context found for " ^ vinfo.vname]
    | POutputParameterArgument e ->
       let ictxt = ccontexts#index_context po#get_context in
       if H.mem callee_callsites ictxt then
         Ok ((H.find callee_callsites ictxt)#record_proof_obligation_result po)
       else
         Error [(elocm __LINE__)
                ^ "No corresponding callee callsite context found for "
                ^ " expression " ^ (p2s (exp_to_pretty e))]
    | _ -> Ok ()

  method write_xml (node: xml_element_int) =
    let ppnode = xmlElement "candidate-parameters" in
    let ccnode = xmlElement "callee-callsites" in
    let _ = node#appendChildren [ppnode; ccnode] in
    begin
      ppnode#appendChildren
        (List.map (fun param ->
             let pnode = xmlElement "param" in
             begin
               param#write_xml pnode;
               pnode
             end) (H.fold (fun _ v acc -> v :: acc) params []));
      ccnode#appendChildren
        (List.map (fun ccs ->
             let cnode = xmlElement "ccs" in
             begin
               ccs#write_xml cnode;
               cnode
             end) self#callee_callsites)
    end

  method private read_xml_callee_callsite
                   (node: xml_element_int): unit traceresult =
    let loc = fdecls#read_xml_location node in
    let ctxt = ccontexts#read_xml_context node in
    let callee = cdictionary#read_xml_exp node in
    let* status = pod#read_xml_output_parameter_status node in
    let ccs = new op_callee_callsite_t pod loc ctxt callee in
    let _ = ccs#set_status status in
    let ictxt = ccontexts#index_context ctxt in
    Ok (H.replace callee_callsites ictxt ccs)
    
  method read_xml (node: xml_element_int): unit traceresult =
    let ppnode = node#getTaggedChild "candidate-parameters" in
    let ccnode = node#getTaggedChild "callee-callsites" in
    let* _ =
      List.fold_left (fun acc_r pnode ->
          match acc_r with
          | Error _ -> acc_r
          | Ok _ ->
             let* param = read_xml_candidate_output_parameter pnode pod in
             self#add_parameter param)
        (Ok ()) (ppnode#getTaggedChildren "param") in
    tbind_iter_list
      self#read_xml_callee_callsite (ccnode#getTaggedChildren "ccs")

end


let mk_analysis_digest
      (fname: string)
      (pod: podictionary_int): output_parameter_analysis_digest_int =
  new output_parameter_analysis_digest_t fname pod
