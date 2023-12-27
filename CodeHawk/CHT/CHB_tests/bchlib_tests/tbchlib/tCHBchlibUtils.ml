(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2023  Aarno Labs LLC

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
open CHLanguage
open CHPretty

(* chutil *)
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHBCTypes
open BCHLibTypes

(* tbchlib *)
open TCHBchlibAssertion


let extract_chif_cfg_assignments
      ?(start=0)
      ?(len=0)
      (proc: procedure_int): (variable_t * numerical_exp_t) list =
  match proc#getBody#getCmdAt 0 with
  | CFG (_, cfg) ->
     let states = cfg#getStates in
     let state = List.hd (List.tl states) in
     let state = cfg#getState state in
     let cmd = state#getCode#getCmdAt 0 in
     (match cmd with
      | TRANSACTION (_, trcode, _) ->
         let trlen = trcode#length in
         if start < 0 || start > trlen then
           []
         else
           let len =
             if len <= 0 then
               (trlen - start) + len
             else
               len in
           if start + len > trlen then
             []
           else
             let assigns = ref [] in
             let len = if len = 0 then trlen else len in
             begin
               for i = start to (start + len) - 1 do
                 let trcmd = trcode#getCmdAt i in
                 (match trcmd with
                  | ASSIGN_NUM (v, e) -> assigns := (v, e) :: !assigns
                  | _ -> ())
               done;
               List.rev !assigns
             end
      | _ -> [])
  | _ -> []


type input_parameter_location_t = string * btype_t * string

type input_fts_parameter_t =
  int * string * btype_t * int * (string * btype_t * string) list


let convert_parameter_location_input
      (loc: input_parameter_location_t): x_fts_loc_t =
  let (kind, lty, ldata) = loc in
  match kind with
  | "s" ->
     { xftsl_kind = kind;
       xftsl_type = lty;
       xftsl_offset = ldata;
       xftsl_reg = "none"}
  | "r" ->
     { xftsl_kind = kind;
       xftsl_type = lty;
       xftsl_offset = "-1";
       xftsl_reg = ldata}
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "convert_fts_parameter: location kind: ";
               STR kind;
               STR " not recognized"]))


let input_parameter_location_to_parameter_location
      (arch: string)
      (p: input_parameter_location_t): parameter_location_t =
  let (kind, lty, ldata) = p in
  let pld = {pld_type = lty; pld_size = 4; pld_extract = None} in
  match kind with
  | "s" -> StackParameter (int_of_string ldata, pld)
  | "r" ->
     (match arch with
      | "mips" ->
         RegisterParameter
           (MIPSRegister (mipsreg_from_string ldata), pld)
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [STR "Not yet implemented"])))
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Not recognized"]))

let convert_fts_parameter_input (p: input_fts_parameter_t): x_fts_param_t =
 let (index, name, ty, size, pl) = p in
     { xfts_index = index;
       xfts_name = name;
       xfts_type = ty;
       xfts_size = size;
       xfts_locations =
         List.map convert_parameter_location_input pl
     }


let get_so_xml_summary_string_node
      (fname: string) (xstring: string): xml_element_int =
  try
    let doc = readXmlDocumentString xstring in
    let root = doc#getRoot in
    if root#hasOneTaggedChild "libfun" then
      root#getTaggedChild "libfun"
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Unable to read function summary string for ";
                STR fname]))
  with
  | XmlParseError (line, col, p)
    | XmlReaderError (line, col, p)
    | XmlDocumentError (line, col, p) ->
     let msg = LBLOCK [STR "Error in file: "; STR fname; STR ": "; p] in
     raise (XmlDocumentError (line, col, msg))
