(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2025  Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypePretty
open BCHBCTypeUtil
open BCHFtsParameter
open BCHFunctionInterface
open BCHLibTypes


let convert_b_attributes_to_function_conditions
      (name: string)
      (fintf: function_interface_t)
      (attrs: b_attributes_t):
      (xxpredicate_t list * xxpredicate_t list * xxpredicate_t list) =
  let parameters = get_fts_parameters fintf in
  let get_par (n: int) =
    try
      List.find (fun p ->
          match p.apar_index with Some ix -> ix = n | _ -> false) parameters
    with
    | Not_found ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "No parameter with index ";
                 INT n;
                 pretty_print_list (List.map (fun p -> p.apar_name) parameters)
                   (fun s -> STR s) "[" "," "]"])) in
  let get_derefty (par: fts_parameter_t): btype_t =
    if is_pointer par.apar_type then
      ptr_deref par.apar_type
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "parameter is not a pointer type: ";
                fts_parameter_to_pretty par])) in
  List.fold_left (fun ((xpre, xside, xpost) as acc) attr ->
      match attr with
      | Attr (("access" | "chk_access"), params) ->
         let (pre, side) =
           (match params with
            | [ACons ("read_only", []); AInt refindex] ->
               let par = get_par refindex in
               let ty = get_derefty par in
               ([XXBuffer (ty, ArgValue par, RunTimeValue)], [])

            | [ACons ("read_only", []); AInt refindex; AInt sizeindex] ->
               let rpar = get_par refindex in
               let spar = get_par sizeindex in
               let ty = get_derefty rpar in
               ([XXBuffer (ty, ArgValue rpar, ArgValue spar)], [])

            | [ACons (("write_only" | "read_write"), []); AInt refindex] ->
               let par = get_par refindex in
               let ty = get_derefty par in
               ([XXBuffer (ty, ArgValue par, RunTimeValue)],
                [XXBlockWrite (ty, ArgValue par, RunTimeValue)])

            | [ACons (("write_only" | "read_write"), []);
               AInt refindex; AInt sizeindex] ->
               let rpar = get_par refindex in
               let spar = get_par sizeindex in
               let ty = get_derefty rpar in
               ([XXBuffer (ty, ArgValue rpar, ArgValue spar)],
                [XXBlockWrite (ty, ArgValue rpar, ArgValue spar)])

            | _ ->
               begin
                 log_error_result
                   ~msg:("attribute conversion for " ^ name ^ ": "
                         ^ "attribute parameters "
                         ^ (String.concat
                              ", " (List.map b_attrparam_to_string params)))
                   ~tag:"attribute conversion"
                   __FILE__ __LINE__ [];
                 ([], [])
               end) in
         (pre @ xpre, side @ xside, xpost)
      | _ ->
         acc) ([], [], []) attrs
