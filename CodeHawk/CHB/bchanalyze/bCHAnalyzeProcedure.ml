(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHSymbolicSetsDomainNoArrays

(* chutil *)
open CHAnalysisSetup

(* bchanalyze *)
open BCHAnalysisTypes

module H = Hashtbl


class bb_invariants_t:bb_invariants_int =
object
  val invariants = H.create 3
    
  method reset = H.clear invariants
    
  method add_invariant (opname:string) (domain:string) (inv:atlas_t) =
    let optable = if H.mem invariants opname then
	H.find invariants opname 
      else
	let table = H.create 1 in
	begin H.add invariants opname table ; table end in
    H.replace optable domain inv
      
  method get_invariants = invariants

  method toPretty =
    let result = ref [] in
    begin
      H.iter (fun iaddr varinvs ->
          H.iter (fun var inv ->
              let p =
                LBLOCK [
                    STR iaddr; STR ": "; STR var; STR ": "; inv#toPretty; NL] in
              result := p :: !result) varinvs) invariants;
      LBLOCK (List.rev !result)
    end
    
end

let bb_invariants = new bb_invariants_t

let default_opsemantics domain = 
  fun ~invariant ~stable ~fwd_direction ~context ~operation ->
    let _ = if stable then 
	if operation.op_name#getBaseName = "invariant" then
	  bb_invariants#add_invariant (List.hd (operation.op_name#getAttributes)) domain invariant in
    invariant

let analyze_procedure_with_linear_equalities (proc:procedure_int) (system:system_int) =
  let analysis_setup = mk_analysis_setup () in
  begin
    analysis_setup#addLinearEqualities ;
    analysis_setup#setOpSemantics (default_opsemantics "karr") ;
    analysis_setup#analyze_procedure system proc 
  end

let analyze_procedure_with_intervals (proc:procedure_int) (system:system_int) =
  let analysis_setup = mk_analysis_setup () in
  begin
    analysis_setup#addIntervals ;
    analysis_setup#setOpSemantics (default_opsemantics "intervals") ;
    analysis_setup#analyze_procedure system proc 
  end
    
let analyze_procedure_with_valuesets (proc:procedure_int) (system:system_int) =
  let analysis_setup = mk_analysis_setup  () in
  begin
    analysis_setup#addValueSets ;
    analysis_setup#setOpSemantics (default_opsemantics "valuesets") ;
    analysis_setup#analyze_procedure system proc
  end


let analyze_procedure_with_symbolic_sets (proc: procedure_int) (system: system_int) =
  let analysis_setup = mk_analysis_setup () in
  begin
    analysis_setup#addDomain "symbolicsets" (new symbolic_sets_domain_no_arrays_t);
    analysis_setup#setOpSemantics (default_opsemantics "symbolicsets");
    analysis_setup#analyze_procedure system proc
  end
