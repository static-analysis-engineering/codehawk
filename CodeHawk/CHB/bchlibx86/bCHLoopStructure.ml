(* =============================================================================
   CodeHawk Binary Analyzer 
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

(* bchlibx86 *)
open BCHAssemblyBlock
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHIFSystem
open BCHLibx86Types

module H = Hashtbl

let loop_levels = H.create 53

let add_loop_levels (address:ctxt_iaddress_t) (levels:ctxt_iaddress_t list) =
  H.add loop_levels address levels

let get_loop_levels (address:ctxt_iaddress_t) =
  try H.find loop_levels address with Not_found -> []

let get_cfg (proc:procedure_int) =
  match proc#getBody#getCmdAt 0 with
  | CFG (_, cfg) -> cfg
  | _ ->
     let msg = LBLOCK [ STR "Procedure " ;
                        symbol_to_pretty proc#getName ; STR " does not have a CFG" ] in
     begin 
       ch_error_log#add "invocation error" msg ;
       raise (BCH_failure msg)
     end
    
let get_strongly_connected_components (proc:procedure_int) =
  let cfg = get_cfg proc in
  let engine = new wto_engine_t (new fwd_graph_t cfg) in
  engine#computeWTO


let record_loop_levels (faddr:doubleword_int) =
  let table = H.create 53 in
  (* let get_index (s:symbol_t) = (symbol_to_doubleword s)#index in *)
  let get_ctxt_string (s:symbol_t) = symbol_to_ctxt_string s in
  let f = get_assembly_function faddr in
  let proc = chif_system#get_procedure_by_address faddr in
  let rec get_wto_head wto =
    match wto with
    | [] -> 
	begin
	  ch_error_log#add "invalid argument" (STR "Encountered empty wto in record_loops") ;
	  raise (Invalid_argument "record_loops")
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

let get_loop_count_from_table (f:assembly_function_int) =
  let table =  H.create 3 in
  let _ =
    f#itera (fun baddr _ ->
        List.iter
          (fun a ->
            if H.mem table a then
              ()
            else
              H.add table a true)
          (get_loop_levels baddr)) in
  H.length table

let get_loop_depth_from_table (f:assembly_function_int) =
  let maxdepth = ref 0 in
  let _ =
    f#itera (fun baddr _ ->
        let d = List.length (get_loop_levels baddr) in
        if d > !maxdepth then maxdepth := d) in
  !maxdepth
    
let get_cfg_loop_complexity_from_table (f:assembly_function_int) =
  let rec m l = match l with
    | 0 -> 1 | 1 -> 2 | 2 -> 4 | 3 -> 8 | 4 -> 16 | 5 -> 32 
    | _ when l > 0 -> 2 * (m (l-1))
    | _ -> 1 in
  let result = ref 0 in
  let _ = f#itera (fun baddr block ->
    result := !result + m (List.length (get_loop_levels baddr))) in
  !result
  

let get_cfg_loop_complexity (f:assembly_function_int) =
  let faddr = f#get_address in
  let rec m l = match l with
    | 0 -> 1 | 1 -> 2 | 2 -> 4 | 3 -> 8 | 4 -> 16 | 5 -> 32 
    | _ when l > 0 -> 2 * (m (l-1))
    | _ -> 1 in
  let result = ref 0 in
  let _ = record_loop_levels faddr in
  let _ = f#itera (fun baddr block ->
    result := !result + m (List.length (get_loop_levels baddr))) in
  !result
      
let get_vc_complexity (f:assembly_function_int) (env:function_environment_int) =
  let instrs = (float_of_int f#get_instruction_count) in
  let bblocks = (float_of_int f#get_block_count) in
  let loopComplexity = (float_of_int (get_cfg_loop_complexity f)) in
  let vars = (float_of_int env#get_var_count) in
  let scale = 0.001 in
  let exponent = 1.4 in
  instrs *. (vars ** exponent) *. loopComplexity *. scale /. bblocks
    
