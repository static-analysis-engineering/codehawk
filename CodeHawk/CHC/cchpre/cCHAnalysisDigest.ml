(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2025 Aarno Labs LLC

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

(* cchpre *)
open CCHPreTypes


let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)
let elocm (line: int): string = (eloc line) ^ ": "


let analysis_digest_name (kind: analysis_digest_kind_t): string =
  match kind with
  | UndefinedBehaviorAnalysis -> "undefined-behavior"
  | OutputParameterAnalysis _ -> "output parameters"
                             
   
class analysis_digest_t
        (_fname: string)
        (_pod: podictionary_int)
        (kind: analysis_digest_kind_t): analysis_digest_int =
object (self)

  method is_active (po_s: proof_obligation_int list) =
    match kind with
    | UndefinedBehaviorAnalysis -> true
    | OutputParameterAnalysis digest -> digest#is_active po_s

  method kind = kind

  method write_xml (node: xml_element_int) =
    let _ = node#setAttribute "name" (analysis_digest_name self#kind) in
    match self#kind with
    | OutputParameterAnalysis digest -> digest#write_xml node
    | _ -> ()

  method read_xml (node: xml_element_int): unit traceresult =
    match self#kind with
    | UndefinedBehaviorAnalysis -> Ok ()
    | OutputParameterAnalysis digest -> digest#read_xml node 

end


let mk_undefined_behavior_analysis_digest
      (fname: string) (pod: podictionary_int): analysis_digest_int =
  new analysis_digest_t fname pod UndefinedBehaviorAnalysis


let mk_output_parameter_analysis_digest
      (fname: string) (pod: podictionary_int): analysis_digest_int =
  let opdigest = CCHOutputParameterAnalysis.mk_analysis_digest fname pod in
  new analysis_digest_t fname pod (OutputParameterAnalysis opdigest)


let read_xml_analysis_digest
      (node: xml_element_int)
      (fname: string)
      (pod: podictionary_int): analysis_digest_int traceresult =
  let name = node#getAttribute "name" in
  match name with
  | "undefined-behavior" ->
     Ok (mk_undefined_behavior_analysis_digest fname pod)
  | "output parameters" ->
     let digest = mk_output_parameter_analysis_digest fname pod in
     let _ = digest#read_xml node in
     Ok digest
  | _ ->
     Error [(elocm __LINE__) ^ "Name of analysis not recognized: " ^ name]
