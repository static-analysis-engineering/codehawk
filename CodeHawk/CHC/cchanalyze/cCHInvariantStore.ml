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
open CHAtlas
open CHLanguage
open CHPretty
open CHStack

(* cchanalyze *)
open CCHAnalysisTypes

module H = Hashtbl

class c_invariants_t:c_invariants_int =
object
  val invariants = H.create 3
  val mutable return_invariants = []
    
  method reset = H.clear invariants
    
  method add_invariant (opname:string) (domain:string) (inv:atlas_t) =
    if (String.sub opname 0 4) = "inv_" then
      let optable = if H.mem invariants opname then
	  H.find invariants opname 
	else
	  let table = H.create 1 in
	  begin H.add invariants opname table ; table end in
      H.replace optable domain inv

  method get_invariants = invariants

end
  
let c_invariants = new c_invariants_t

let invariant_semantics domain name invariant =
  c_invariants#add_invariant name domain invariant

let default_opsemantics domain =
  let is_invariant s = ((String.length s) > 4) && (String.sub s 0 4) = "inv_" in
  fun ~invariant ~stable ~fwd_direction ~context ~operation ->
  if is_invariant operation.op_name#getBaseName then
    let _ =
      if stable then 
	invariant_semantics domain operation.op_name#getBaseName invariant in
    invariant
  else
    invariant
  
  
