(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* cchlib *)
open CCHBasicTypes

(* cchpre *)
open CCHPreTypes


let ad = CCHAssignDictionary.assigndictionary


let set_global_value (vinfo:varinfo) =
  let assignments = ad#get_assignments in
  match (vinfo.vstorage, vinfo.vaddrof) with
  | (Static, false) ->
     let initexp =
       List.fold_left (fun acc a ->
           match acc with
           | Some _ -> acc
           | _ ->
              match a with
              | InitAssignment (_,vid,SingleInit e) when vinfo.vid = vid ->
                 Some e
              | _ -> acc) None assignments in
     let exps =
       List.fold_left (fun acc a ->
           match a with
           | StaticAssignment (_,_,vid,d) when vinfo.vid = vid ->
              d.asg_rhs :: acc
           | _ -> acc)[] assignments in
     ignore
       (ad#index_global_value
          (GlobalValue (vinfo.vname, vinfo.vid, initexp, exps)))
  | _ -> ()


let get_global_value (vinfo:varinfo) =
  let globalvalues = ad#get_global_values in
  List.fold_left (fun acc gv ->
      match acc with
      | Some _ -> acc
      | _ ->
         match gv with
         | GlobalValue (_, vid, Some e, []) when vinfo.vid = vid -> Some e
         | _ -> acc) None globalvalues
