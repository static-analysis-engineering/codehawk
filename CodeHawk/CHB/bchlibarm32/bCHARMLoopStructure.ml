(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs LLC

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
open CHLanguage
open CHSCC
open CHIterator

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHLocation

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMCHIFSystem
open BCHARMTypes

module H = Hashtbl


let loop_levels = H.create 53


let add_loop_levels (address:ctxt_iaddress_t) (levels:ctxt_iaddress_t list) =
  H.replace loop_levels address levels


let get_arm_loop_levels (address:ctxt_iaddress_t) =
  try H.find loop_levels address with Not_found -> []


let get_cfg (proc:procedure_int) =
  match proc#getBody#getCmdAt 0 with
  | CFG (_, cfg) -> cfg
  | _ ->
     let msg =
       LBLOCK [STR "Procedure ";
               symbol_to_pretty proc#getName;
               STR " does not have a CFG"] in
     begin 
       ch_error_log#add "invocation error" msg ;
       raise (BCH_failure msg)
     end


let get_strongly_connected_components (proc:procedure_int) =
  let cfg = get_cfg proc in
  let engine = new wto_engine_t (new fwd_graph_t cfg) in
  engine#computeWTO


let record_arm_loop_levels (faddr:doubleword_int) =
  let table = H.create 53 in
  let get_ctxt_string (s:symbol_t) = symbol_to_ctxt_string s in
  let f = get_arm_assembly_function faddr in
  let proc = arm_chif_system#get_arm_procedure faddr in
  let rec get_wto_head wto =
    match wto with
    | [] ->
       let msg =
         LBLOCK [STR "Encountered empty wto in record_loops in function: ";
                 faddr#toPretty] in
	begin
	  ch_error_log#add "loops" msg;
          raise (BCH_failure msg)
	end
    | hd::_ -> get_wto_component_head hd 
  and get_wto_component_head wtoComponent =
    match wtoComponent with
    | VERTEX s -> get_ctxt_string s
    | SCC scc -> get_wto_head scc in
  let rec record_wto wto levels =
    List.iter (fun wtoComponent -> record_wto_component wtoComponent levels) wto
  and record_wto_component wtoComponent levels =
    match wtoComponent with
    | VERTEX s -> H.add table (get_ctxt_string s) levels
    | SCC scc -> record_wto scc ((get_wto_head scc) :: levels) in 
  let sccs = get_strongly_connected_components proc in
  begin
    (match sccs with [] -> () | _ -> record_wto sccs []) ;
    f#itera (fun baddr block ->
      if H.mem table baddr then
	let levels = H.find table baddr in
	add_loop_levels baddr (List.rev levels))
  end


let get_arm_loop_count_from_table (f:arm_assembly_function_int) =
  let table =  H.create 3 in
  let _ =
    f#itera (fun baddr _ ->
        List.iter
          (fun a ->
            if H.mem table a then
              ()
            else
              H.add table a true)
          (get_arm_loop_levels baddr)) in
  H.length table


let get_arm_loop_depth_from_table (f:arm_assembly_function_int) =
  let maxdepth = ref 0 in
  let _ =
    f#itera (fun baddr _ ->
        let d = List.length (get_arm_loop_levels baddr) in
        if d > !maxdepth then maxdepth := d) in
  !maxdepth
                    
