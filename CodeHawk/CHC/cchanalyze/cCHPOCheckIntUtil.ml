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
open CHNumerical

(* xprlib *)
open XprTypes

(* cchlib  *)
open CCHBasicTypes
open CCHLibTypes
   
(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

let nonneg (x:xpr_t) =
  match x with
  | XConst (IntConst n) -> n#geq numerical_zero
  | _ -> false    

let nonpos (x:xpr_t) =
  match x with
  | XConst (IntConst n) -> n#leq numerical_zero
  | _ -> false

let positive (x:xpr_t) =
  match x with
  | XConst (IntConst n) -> n#gt numerical_zero
  | _ -> false

let xpr_existential_min_values
      (poq:po_query_int)
      (invindex:int)
      (xpr:xpr_t) =
  match xpr with
  | XConst (IntConst n) ->
     let deps = DLocal ( [ invindex ]) in
     let msg = "constant value: " ^ n#toString in
     [ (n,deps,msg) ]
  | XVar v when poq#env#is_tainted_value v ->
     begin
       match poq#env#get_tainted_value_bounds v with
       | (Some (XConst (IntConst n)),_) ->
          let (s,callee,pc) = poq#get_tainted_value_origin v in
          let deps = DEnvC ([ invindex ],[PostAssumption (callee.vid,pc) ]) in
          let msg = s ^ " choose max value: " ^ n#toString in
          [ (n,deps,msg) ]
       | _ -> []
     end
  | _ -> []
     
let get_existential_min_values
      (poq:po_query_int)
      (inv:invariant_int) =
  match inv#expr with
  | Some x -> xpr_existential_min_values poq inv#index x
  | _ ->
     match inv#lower_bound_xpr_alternatives with
     | Some l ->
        List.concat
          (List.map (xpr_existential_min_values poq inv#index) l)
     | _ -> []

let xpr_existential_max_values
      (poq:po_query_int)
      (invindex:int)
      (xpr:xpr_t) =
  match xpr with
  | XConst (IntConst n) ->
     let deps = DLocal ( [ invindex ]) in
     let msg = "constant value: " ^ n#toString in
     [ (n,deps,msg) ]
  | XVar v when poq#env#is_tainted_value v ->
     begin
       match poq#env#get_tainted_value_bounds v with
       | (_, Some (XConst (IntConst n))) ->
          let (s,callee,pc) = poq#get_tainted_value_origin v in
          let deps = DEnvC ([ invindex ],[PostAssumption (callee.vid,pc) ]) in
          let msg = s ^ " choose max value: " ^ n#toString in
          [ (n,deps,msg) ]
       | _ -> []
     end
  | _ -> []
     
let get_existential_max_values
      (poq:po_query_int)
      (inv:invariant_int) =
  match inv#expr with
  | Some x -> xpr_existential_max_values poq inv#index x
  | _ ->
     match inv#upper_bound_xpr_alternatives with
     | Some l ->
        List.concat
          (List.map (xpr_existential_max_values poq inv#index) l)
     | _ -> []
    
