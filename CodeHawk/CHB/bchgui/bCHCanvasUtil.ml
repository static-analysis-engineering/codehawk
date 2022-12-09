(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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
open CHLogger
open CHPrettyUtil

(* chgui *)
open CHCanvasBase

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFunctionInfo
open BCHFloc
open BCHLibTypes
open BCHLocation

(* bchlibx86 *)
open BCHAssemblyFunctions
open BCHLibx86Types
open BCHLoopStructure

module H = Hashtbl

let graph_indices = H.create 5
                  
let add_graph_index (name:string) (index:dw_index_t) =
  H.add graph_indices name index
  
let has_graph_index (name:string) = H.mem graph_indices name

let get_floca faddr iaddr =
  let loc = ctxt_string_to_location faddr iaddr in
  get_floc loc

                                  
let get_graph_index (name:string) = 
  try
    Hashtbl.find graph_indices name
  with
    Not_found ->
      begin
	ch_error_log#add "invocation error" (STR "BCHCanvasBase.get_graph_index") ;
	raise (Invocation_error "BCHCanvasBase.get_graph_index")
      end

let graph_nodes = Hashtbl.create 5
let get_graph_nodes (graphName:string) =
  try
    Hashtbl.find graph_nodes graphName 
  with
      Not_found -> []

let get_address_from_ctxt_iaddr (nodeName:string) = nodeName
                                                  
let get_address (nodeName:string) =
  index_to_doubleword (int_of_string (string_suffix nodeName 1))

let color_nodes (graphName:string) f  =
  let nodes = get_graph_nodes graphName in
  List.iter (fun nodeItem ->
    match f (get_address_from_ctxt_iaddr nodeItem#get_name) with
	Some iColor -> 
	  nodeItem#set_color iColor
      | _ -> ()) nodes

let show_loops graphName _ = 
  color_nodes graphName
    (fun address -> 
      let nesting_level =
        List.length (BCHLoopStructure.get_loop_levels address) in
      match nesting_level with
	  0 -> None
	| 1 -> Some 0xFFAAAAFF
	| 2 -> Some 0xFF7777FF
	| 3 -> Some 0xFF3333FF
	| _ -> Some 0xFF0000FF)

let unresolved_jumps = H.create 13
let nonreturning = H.create 13

let record_cfg_dead_ends (faddr:doubleword_int) =
  let f = get_assembly_function faddr in
  f#itera (fun baddr block ->
    block#itera (fun iaddr instr ->
      match instr#get_opcode with
      | IndirectJmp _ ->
	let finfo = get_function_info faddr in
	begin
	  (if finfo#has_call_target iaddr then () 
	   else if finfo#has_jump_target iaddr then 
	     let floc = get_floca faddr iaddr in
	     match floc#get_jump_successors with
	     | [] -> 
	       begin
		 H.add unresolved_jumps baddr "norange" ;
		 pr_debug [ faddr#toPretty ;
                            STR ": add no range info " ; STR baddr ; NL ] 
	       end
	     | _ -> ()
	   else
	      begin
		H.add unresolved_jumps baddr "unresolved" ;
		pr_debug [ faddr#toPretty ;
                           STR "; add unresolved " ; STR baddr ; NL ]
	      end) ;
	  (if (finfo#get_call_target iaddr)#is_nonreturning then
	      begin
		H.add nonreturning baddr true ;
		pr_debug [ faddr#toPretty ;
                           STR "; add nonreturning " ; STR baddr ; NL ]
	      end)
	end
      | DirectCall _ | IndirectCall _ ->
	let finfo = get_function_info faddr in
	if (finfo#get_call_target iaddr)#is_nonreturning then 
	  begin
	    H.add nonreturning baddr true ;
	    pr_debug [ faddr#toPretty ;
                       STR ": add nonreturning " ; STR baddr ; NL ]
	  end
      | _ -> ()))
      
let record_cfg_info (faddr:doubleword_int) =
  begin
    record_cfg_dead_ends faddr;
    record_loop_levels faddr
  end

let show_unresolved_jumps graphName _ = 
  color_nodes graphName
    (fun address -> if H.mem unresolved_jumps address then 
	match H.find unresolved_jumps address with
	| "unresolved" -> Some 0x0000FFFF 
	| "norange" -> Some 0xAAAAFFFF
	| _ -> None
      else None)

let show_nonreturning_blocks graphName _ = 
  color_nodes graphName 
    (fun address -> if H.mem nonreturning address then Some 0x00FF00FF else None)

(*
let show_error_code graphName _ =
  if has_graph_index graphName then
    let functionIndex = get_graph_index graphName in
    let functionAddress = index_to_doubleword functionIndex in
    let proc = chif_system#get_procedure_by_index functionIndex in
    let _ = analyze_procedure ~mode:error_mode proc chif_system#get_system in
    color_nodes graphName
      (fun address ->
	let loc = make_location functionAddress address in
	let inv = invariants#get_invariant ~mode:"error_mode" loc in
	if inv#is_bottom then Some 0x99999999 else None )
  else
    color_nodes graphName (fun _ -> None)
*)  

class type bch_canvas_int =
object
  method initialize: unit
  method reset: unit
  method orphan_code_to_dot: unit
  method call_graph_to_dot : unit
  method sub_call_graph_to_dot: dw_index_t -> unit
  method sub_rv_call_graph_to_dot: dw_index_t -> unit
  method control_flow_graph_to_dot: dw_index_t -> unit
  method annotated_control_flow_graph_to_dot: dw_index_t -> unit
  method trace_graph_to_dot: dw_index_t -> int -> unit
  method trace_rv_graph_to_dot: dw_index_t -> variable_t -> unit
  method trace_se_graph_to_dot: dw_index_t -> floc_int -> variable_t -> unit
end

class bch_canvas_t:bch_canvas_int =
object

  val canvas = CHCanvasBase.make_canvas_base () 

  method initialize = 
    begin
      canvas#add_labeled_button "show\nloops" show_loops ;
      canvas#add_labeled_button "show\nunresolved\njumps" show_unresolved_jumps ; 
      canvas#add_labeled_button "show\nnonreturning\ncalls" show_nonreturning_blocks ;
      (* canvas#add_labeled_button "show\nerror code" show_error_code ; *)
    end

  method reset = 
    begin
      Hashtbl.clear graph_nodes ;
      Hashtbl.clear graph_indices
    end

  method orphan_code_to_dot = BCHOrphanCode.orphan_code#to_dot canvas

  method trace_graph_to_dot (index:dw_index_t) (op:int) =
    BCHCanvasCallgraph.canvas_call_graph#trace_graph_to_dot index op canvas

  method trace_rv_graph_to_dot (index:dw_index_t) (v:variable_t) =
    BCHCanvasCallgraph.canvas_call_graph#trace_rv_to_dot index v canvas

  method trace_se_graph_to_dot (index:dw_index_t) (floc:floc_int) (v:variable_t) =
    BCHCanvasCallgraph.canvas_call_graph#trace_se_to_dot index floc v canvas

  method call_graph_to_dot = 
    BCHCanvasCallgraph.canvas_call_graph#system_call_graph_to_dot canvas

  method sub_call_graph_to_dot (index:dw_index_t) = 
    BCHCanvasCallgraph.canvas_call_graph#sub_call_graph_to_dot index canvas

  method sub_rv_call_graph_to_dot (index:dw_index_t) =
    BCHCanvasCallgraph.canvas_call_graph#sub_rv_call_graph_to_dot index canvas

  method control_flow_graph_to_dot (index:dw_index_t) = 
    let (graphName,graphNodes) = BCHControlFlowGraph.control_flow_graph#to_dot index canvas in
    begin
      Hashtbl.add graph_nodes graphName graphNodes ;
      add_graph_index graphName index
    end

  method annotated_control_flow_graph_to_dot (index:dw_index_t) = 
    let (graphName,graphNodes) = BCHControlFlowGraph.control_flow_graph#to_annotated_dot index canvas in
    begin
      Hashtbl.add graph_nodes graphName graphNodes ;
      add_graph_index graphName index
    end

end

let canvas = let c = new bch_canvas_t in begin c#initialize ; c end
