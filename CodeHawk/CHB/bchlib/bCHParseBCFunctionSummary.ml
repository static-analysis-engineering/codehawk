(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchcil *)
open BCHCBasicTypes
open BCHBCFiles
open BCHParseCilFile

(* bchlib *)
open BCHBasicTypes
open BCHFtsParameter
open BCHFunctionData
open BCHFunctionInterface
open BCHFunctionSemantics
open BCHFunctionSummary
open BCHLibTypes
open BCHPreFileIO


let save_function_summary_file (fsl: function_summary_int list) =
  let xsum = xmlElement "function-summaries" in
  begin
    xsum#appendChildren
      (List.fold_left (fun acc fs ->
           let name = fs#get_name in
           match functions_data#has_function_by_name name with
           | Some faddr ->
              let fsnode = xmlElement "fs" in
              begin
                fs#write_xml fsnode;
                fsnode#setAttribute "name" name;
                fsnode#setAttribute "faddr" faddr#to_hex_string;
                fsnode :: acc
              end
           | _ ->
              begin
                chlog#add "cil function summary: no address" (STR name);
                acc
              end
         ) [] fsl);
    save_userdata_function_summaries_file xsum;
    chlog#add
      "cil function summaries"
      (LBLOCK [INT (List.length fsl); STR " summaries"])
  end


let bfargs_to_parameters (fargs: bfunarg_t list option) =
  match fargs with
  | Some funargs ->
     List.mapi
       (fun i (name, btype, _) -> mk_stack_parameter ~btype ~name i) funargs
  | _ -> []

let bvarinfo_to_function_interface (v: bvarinfo_t) =
  let vname = v.bvname in
  let vtype = v.bvtype in
  match vtype with
  | TFun (returntype, fargs, _, _) ->
     let params = bfargs_to_parameters fargs in
     default_function_interface ~returntype vname params
  | _ ->
     raise
       (BCH_failure (LBLOCK [STR "Unexpected type in "; STR vname]))


(* pre/post conditions and sideeffects not yet implemented *)
let bfunction_body_to_function_semantics fintf (bsbody: bblock_t) =
  let preconditions = [] in
  let sideeffects = [] in
  { fsem_pre = preconditions;
    fsem_post = [];
    fsem_errorpost = [];
    fsem_sideeffects = sideeffects;
    fsem_io_actions = [];
    fsem_throws = [];
    fsem_desc = ""
  }


let bcfun_to_function_summary (f: bcfundec_t) =
  let fdoc = default_function_documentation in
  let fintf = bvarinfo_to_function_interface f.bsvar in
  let fsem = bfunction_body_to_function_semantics fintf f.bsbody in
  make_function_summary ~fintf:fintf ~sem:fsem ~doc:fdoc


let parse_bc_function_summary (fname: string) =
  if bcfiles#has_gfun fname then
    let bcfunction = bcfiles#get_gfun fname in
    bcfun_to_function_summary bcfunction
  else
    raise
      (BCH_failure
         (LBLOCK [STR "No bc function found with name "; STR fname]))
