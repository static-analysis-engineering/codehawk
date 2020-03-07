(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* jchlib *)
open JCHBasicTypes

(* jchgui *)
open JCHCostValues
open JCHBCFunctions
open JCHControlFlowGraph

module H = Hashtbl

let graph_indices = Hashtbl.create 5
let add_graph_index (name:string) (index:int) =
  H.add graph_indices name index
let has_graph_index (name:string) = H.mem graph_indices name
let get_graph_index (name:string) = 
  try
    H.find graph_indices name
  with
    Not_found ->
      begin
	ch_error_log#add
          "invocation error" (STR "JCHCanvasBase.get_graph_index") ;
	raise (JCH_failure (STR "JCHCanvasBase.get_graph_index"))
      end

let graph_nodes = H.create 5
let get_graph_nodes (graphName:string) =
  try
    H.find graph_nodes graphName 
  with
      Not_found -> []

let color_nodes (graphName:string) f  =
  let nodes = get_graph_nodes graphName in
  List.iter (fun nodeItem ->
    match f nodeItem#get_name with
	Some iColor -> 
	  nodeItem#set_color iColor
      | _ -> ()) nodes

let set_node_text (graphName:string) f =
  let nodes = get_graph_nodes graphName in
  List.iter (fun nodeItem ->
    match f nodeItem#get_name with
    | Some t -> nodeItem#set_text t
    | _ -> ()) nodes

let set_pixel_width (graphName:string) f =
  let nodes = get_graph_nodes graphName in
  List.iter (fun nodeItem ->
    match f nodeItem#get_name with
    | Some i -> nodeItem#set_pixel_width i
    | _ -> ()) nodes

let show_loops graphName _ = 
  let bcfunction = bcfunctions#get_bc_function_by_name graphName in
  color_nodes graphName
    (fun name -> 
      let name = string_suffix name 3 in
      let pc = int_of_string name in
      let nesting_level =  List.length (bcfunction#get_loop_levels pc) in
      match nesting_level with
      | 0 -> None
      | 1 -> Some 0xFFAAAAFF
      | 2 -> Some 0xFF7777FF
      | 3 -> Some 0xFF3333FF
      | _ -> Some 0xFF0000FF)


let show_tainted_loops graphName _ = 
  let bcfunction = bcfunctions#get_bc_function_by_name graphName in
  color_nodes graphName 
    (fun name ->
      let name = string_suffix name 3 in
      let pc = int_of_string name in
      let looptaint = bcfunction#get_loop_taint pc in
      match looptaint with
      | 0 -> None
      | 1 -> Some light_yellow
      | 2 -> Some yellow
      | 3 -> Some cyan
      | _ -> Some orange)

let show_call_nodes mname graphName _ =
  let bcfunction = bcfunctions#get_bc_function_by_name graphName in
    color_nodes graphName
      (fun name ->
	let name = string_suffix name 3 in
	let pc = int_of_string name in
	if bcfunction#has_method_call mname pc then Some light_blue else None)

let show_class_call_nodes cname graphName _ =
  let bcfunction = bcfunctions#get_bc_function_by_name graphName in
    color_nodes graphName
      (fun name ->
	let name = string_suffix name 3 in
	let pc = int_of_string name in
	if bcfunction#has_class_call cname pc then Some light_blue else None)
  

let show_cost_nodes graphName _ =
  let cms = (nsplit '_' graphName) in
  let cms = int_of_string (List.hd cms) in
  begin
    set_pixel_width graphName (fun name -> None) ;
    set_node_text
      graphName
      (fun name -> 
        let pc = int_of_string (string_suffix name 3) in
        match (costvalues#get_block_cost_string cms pc) with
        | Some s ->
	   Some ("cost: " ^ s ^ "\npc=" ^ (string_of_int pc))
        | _ -> None )
  end

class type jch_canvas_int =
object
  method initialize: unit
  method cfg_to_dot: int -> unit
  method annotated_cfg_to_dot: int -> bool -> unit
  method callgraph_to_dot: bool -> unit
  method sub_callgraph_to_dot: int -> ?show_cost:bool -> bool -> unit
  method sub_rv_callgraph_to_dot: int ->unit
end

class jch_canvas_t:jch_canvas_int =
object

  val canvas = CHCanvasBase.make_canvas_base ()

  method initialize =
    begin
      canvas#add_labeled_button "show\nloops" show_loops ;
      canvas#add_labeled_button "show\nappend" (show_call_nodes "append") ;
      canvas#add_labeled_button "show\npush" (show_call_nodes "push") ;
      canvas#add_labeled_button "show\npop" (show_call_nodes "pop") ;
      canvas#add_labeled_button "show\nsleep" (show_call_nodes "sleep") ;
      canvas#add_labeled_button
        "show\nBigDecimal" (show_class_call_nodes "java.math.BigDecimal") ;
    end

  method callgraph_to_dot (show_libcalls:bool) =
    JCHCanvasCallgraph.canvas_callgraph#system_callgraph_to_dot
      canvas show_libcalls

  method sub_callgraph_to_dot
           (cmsId:int) ?(show_cost=false) (show_libcalls:bool) =
    JCHCanvasCallgraph.canvas_callgraph#sub_callgraph_to_dot
      cmsId canvas ~show_cost show_libcalls

  method sub_rv_callgraph_to_dot (cmsId:int) =
    JCHCanvasCallgraph.canvas_callgraph#sub_rv_callgraph_to_dot cmsId canvas

  method cfg_to_dot (index:int) =
    let (graphName,graphNodes) = control_flow_graph#to_dot index canvas in
    begin
      H.add graph_nodes graphName graphNodes ;
      add_graph_index graphName index
    end

  method annotated_cfg_to_dot (index:int) (has_costs:bool) =
    let (graphName,graphNodes) =
      control_flow_graph#to_annotated_dot index canvas has_costs in
    begin
      H.add graph_nodes graphName graphNodes ;
      add_graph_index graphName index
    end

end

let canvas = let c = new jch_canvas_t in begin c#initialize ; c end
