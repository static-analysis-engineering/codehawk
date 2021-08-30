(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open BCHFunctionInterface
open BCHLibTypes
open BCHPostcondition
open BCHPrecondition
open BCHSideeffect
open BCHXmlUtil


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

let function_semantics_to_pretty (sem:function_semantics_t) =
  LBLOCK [ 
      (match sem.fsem_pre with
       | [] -> STR ""
       | _ ->
          LBLOCK [
              STR "preconditions: ";
              NL;
	      INDENT (
                  3,
                  LBLOCK [
		      pretty_print_list
                        sem.fsem_pre
		        (fun p -> LBLOCK [precondition_to_pretty p; NL])
                        "" "" ""]);
              NL]);

      (match sem.fsem_post with
       | [] -> STR ""
       | _ ->
          LBLOCK [
              STR "postconditions: ";
              NL;
	      INDENT (
                  3,
                  LBLOCK [
		      pretty_print_list
                        sem.fsem_post
		        (fun p -> LBLOCK [postcondition_to_pretty p; NL])
                        "" "" ""]);
	      NL]);

      (match sem.fsem_errorpost with
       | [] -> STR ""
       | _ ->
          LBLOCK [
              STR "errorpostconditions: ";
              NL;
	      INDENT (
                  3,
                  LBLOCK [
		      pretty_print_list
                        sem.fsem_errorpost
		        (fun p -> LBLOCK [postcondition_to_pretty p; NL])
                        "" "" ""]);
	      NL]);

      (match sem.fsem_sideeffects with
       | [] -> STR ""
       | _ ->
          LBLOCK [
              STR "sideeffects: ";
              NL;
	      INDENT (
                  3,
                  LBLOCK [
		      pretty_print_list
                        sem.fsem_sideeffects
		        (fun s -> LBLOCK [sideeffect_to_pretty s; NL])
                        "" "" ""]); NL])
    ]


let read_xml_io_action
    (node: xml_element_int)
    (parameters: fts_parameter_t list): io_action_t =
  let get = node#getAttribute in
  { iox_cat = get "cat";
    iox_desc = get "desc";
    iox_pre = None;
  }


let read_xml_io_actions (node:xml_element_int) (pars:fts_parameter_t list) =
  List.map
    (fun n -> read_xml_io_action n pars)
    (node#getTaggedChildren "io-action")


let read_xml_function_semantics 
    (node: xml_element_int)
    (parameters: fts_parameter_t list): function_semantics_t =
  let get = node#getAttribute in 
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let (post,errorpost) =
    if hasc "postconditions" then
      let pNode = getc "postconditions" in
      let (sc_post,sc_errorpost) = read_xml_shortcut_postconditions pNode in
      let post = read_xml_postconditions pNode parameters in
      let errorpost = read_xml_errorpostconditions pNode parameters in
      (post @ sc_post, errorpost @ sc_errorpost) 
    else
      ([], []) in
  let io_actions =
    if hasc "io-actions" then
      read_xml_io_actions (getc "io-actions") parameters
    else
      [] in
  { fsem_pre =
      if hasc "preconditions" then
        read_xml_preconditions (getc "preconditions") parameters
      else
        [];
    fsem_post = post ;
    fsem_errorpost = errorpost ;
    fsem_sideeffects =
      if hasc "sideeffects" then
	read_xml_sideeffects (getc "sideeffects") parameters
      else
        [];
    fsem_throws =
      if has "throws" then
        [get "throws"]
      else
	if hasc "throws" then
	  List.map
            (fun n -> n#getAttribute "name")
	    ((getc "throws")#getTaggedChildren "exn")
	else
	  [];
    fsem_desc = (if has "desc" then get "desc" else "");
    fsem_io_actions = io_actions	
  }


let read_xml_function_interface_and_semantics
      (aNode:xml_element_int)
      (sNode:xml_element_int): (function_interface_t * function_semantics_t) =
  let pNodes = aNode#getTaggedChildren "par" in
  let fintf = read_xml_function_interface aNode in
  let parPre = List.concat (List.map read_xml_par_preconditions pNodes) in
  let parSE = List.concat (List.map read_xml_par_sideeffects pNodes) in
  let sem =
    read_xml_function_semantics
      sNode
      fintf.fintf_type_signature.fts_parameters in
  let sem = {
      sem with
      fsem_pre = sem.fsem_pre @ parPre;
      fsem_sideeffects = sem.fsem_sideeffects @ parSE
    } in
  (fintf, sem)


let modify_types_semantics (f:type_transformer_t) (sem:function_semantics_t) =
  { sem with
    fsem_pre = List.map (modify_types_pre f) sem.fsem_pre ;
    fsem_post = List.map (modify_types_post f) sem.fsem_post ;
    fsem_errorpost = List.map (modify_types_post f) sem.fsem_errorpost ;
    fsem_sideeffects = List.map (modify_types_se f) sem.fsem_sideeffects
  }

let join_semantics (sem:function_semantics_t) (optsem:function_semantics_t option) =
  match optsem with
  | Some s -> {
    fsem_pre = sem.fsem_pre @ s.fsem_pre ;
    fsem_post = sem.fsem_post @ s.fsem_post ;
    fsem_errorpost = sem.fsem_errorpost @ s.fsem_errorpost ;
    fsem_sideeffects = sem.fsem_sideeffects @ s.fsem_sideeffects ;
    fsem_io_actions = sem.fsem_io_actions @ s.fsem_io_actions ;
    fsem_throws = sem.fsem_throws @ s.fsem_throws ;
    fsem_desc = sem.fsem_desc ^ "; " ^ s.fsem_desc
    }
  | _ -> sem


let default_function_semantics = {
    fsem_pre = [] ;
    fsem_post = [] ;
    fsem_errorpost = [] ;
    fsem_sideeffects = [] ;
    fsem_io_actions = [] ;
    fsem_throws = [] ;
    fsem_desc = ""
}

