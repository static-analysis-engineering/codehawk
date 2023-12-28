(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open BCHBCTypes
open BCHExternalPredicate
open BCHFunctionInterface
open BCHInterfaceDictionary
open BCHPrecondition
open BCHSideeffect
open BCHLibTypes
open BCHPostcondition
open BCHXmlUtil


let id = BCHInterfaceDictionary.interface_dictionary


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
		        (fun p -> LBLOCK [xxpredicate_to_pretty p; NL])
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
		        (fun p -> LBLOCK [xxpredicate_to_pretty p; NL])
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
		        (fun p -> LBLOCK [xxpredicate_to_pretty p; NL])
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
		        (fun s -> LBLOCK [xxpredicate_to_pretty s; NL])
                        "" "" ""]); NL]);

      (match sem.fsem_postrequests with
       | [] -> STR ""
       | _ ->
          LBLOCK [
              STR "postrequests: ";
              NL;
	      INDENT (
                  3,
                  LBLOCK [
		      pretty_print_list
                        sem.fsem_postrequests
		        (fun p -> LBLOCK [xxpredicate_to_pretty p; NL])
                        "" "" ""]);
	      NL]);

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
      (fname: string)
      (parameters: fts_parameter_t list): function_semantics_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let thisf = NamedConstant fname in
  let (post, errorpost) =
    if hasc "postconditions" then
      let pNode = getc "postconditions" in
      let (sc_post, sc_errorpost) =
        read_xml_shortcut_postconditions pNode thisf in
      let post = read_xml_postconditions pNode thisf parameters in
      let errorpost =
        read_xml_errorpostconditions pNode thisf parameters in
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
        read_xml_preconditions (getc "preconditions") thisf parameters
      else
        [];
    fsem_post = post;
    fsem_errorpost = errorpost;
    fsem_postrequests = [];
    fsem_sideeffects =
      if hasc "sideeffects" then
	read_xml_sideeffects (getc "sideeffects") thisf parameters
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
  let fname = aNode#getAttribute "name" in
  let thisf = NamedConstant fname in
  let pNodes = aNode#getTaggedChildren "par" in
  let fintf = read_xml_function_interface aNode in
  let ftspars = get_fts_parameters fintf in
  let parPre =
    List.concat
      (List.map (fun n ->
           read_xml_par_preconditions n thisf ftspars) pNodes) in
  let parSE =
    List.concat
      (List.map (fun n ->
           read_xml_par_sideeffects n thisf) pNodes) in
  let sem =
    read_xml_function_semantics
      sNode
      fname
      ftspars in
  let sem = {
      sem with
      fsem_pre = sem.fsem_pre @ parPre;
      fsem_sideeffects = sem.fsem_sideeffects @ parSE
    } in
  (fintf, sem)


let write_xml_function_semantics
      (node: xml_element_int) (sem: function_semantics_t) =
  let pre = List.map id#index_xxpredicate sem.fsem_pre in
  let post = List.map id#index_xxpredicate sem.fsem_post in
  let epost = List.map id#index_xxpredicate sem.fsem_errorpost in
  let sidee = List.map id#index_xxpredicate sem.fsem_sideeffects in
  let setlist t l =
    node#setAttribute t (String.concat "," (List.map string_of_int l)) in
  begin
    (if (List.length pre) > 0 then setlist "pre" pre);
    (if (List.length post) > 0 then setlist "post" post);
    (if (List.length epost) > 0 then setlist "epost" epost);
    (if (List.length sidee) > 0 then setlist "sidee" sidee)
  end


let modify_types_semantics (f:type_transformer_t) (sem:function_semantics_t) =
  { sem with
    fsem_pre = List.map (modify_types_xxp f) sem.fsem_pre ;
    fsem_post = List.map (modify_types_xxp f) sem.fsem_post ;
    fsem_errorpost = List.map (modify_types_xxp f) sem.fsem_errorpost ;
    fsem_sideeffects = List.map (modify_types_xxp f) sem.fsem_sideeffects
  }


let add_function_precondition
      (fsem: function_semantics_t) (pre: xxpredicate_t): function_semantics_t =
  let fsempre = fsem.fsem_pre in
  let newpre =
    if List.exists (fun p -> (xxpredicate_compare p pre) = 0) fsempre then
      List.map
        (fun p -> if (xxpredicate_compare p pre) = 0 then pre else p) fsempre
    else
      pre :: fsempre in
  {fsem with fsem_pre = newpre}


let add_function_sideeffect
         (fsem: function_semantics_t) (se: xxpredicate_t): function_semantics_t =
  let fsemse = fsem.fsem_sideeffects in
  let newse =
    if List.exists (fun p -> (xxpredicate_compare p se) = 0) fsemse then
      List.map
        (fun p -> if (xxpredicate_compare p se) = 0 then se else p) fsemse
    else
      se :: fsemse in
  {fsem with fsem_sideeffects = newse}


let add_function_postrequest
      (fsem: function_semantics_t) (pr: xxpredicate_t): function_semantics_t =
  let fsempr = fsem.fsem_postrequests in
  let newpr =
    if List.exists (fun p -> (xxpredicate_compare p pr) = 0) fsempr then
      List.map
        (fun p -> if (xxpredicate_compare p pr) = 0 then pr else p) fsempr
    else
      pr :: fsempr in
  {fsem with fsem_postrequests = newpr}


let join_semantics
      (sem:function_semantics_t) (optsem:function_semantics_t option) =
  match optsem with
  | Some s -> {
    fsem_pre = sem.fsem_pre @ s.fsem_pre;
    fsem_post = sem.fsem_post @ s.fsem_post;
    fsem_errorpost = sem.fsem_errorpost @ s.fsem_errorpost;
    fsem_sideeffects = sem.fsem_sideeffects @ s.fsem_sideeffects;
    fsem_postrequests = sem.fsem_postrequests @ s.fsem_postrequests;
    fsem_io_actions = sem.fsem_io_actions @ s.fsem_io_actions;
    fsem_throws = sem.fsem_throws @ s.fsem_throws;
    fsem_desc = sem.fsem_desc ^ "; " ^ s.fsem_desc
    }
  | _ -> sem


let default_function_semantics = {
    fsem_pre = [];
    fsem_post = [];
    fsem_errorpost = [];
    fsem_sideeffects = [];
    fsem_postrequests = [];
    fsem_io_actions = [];
    fsem_throws = [];
    fsem_desc = ""
}
