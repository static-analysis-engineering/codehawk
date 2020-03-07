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
open CHPretty
open CHUtils

(* chgui *)
open CHCanvasBase

(* chutil *)
open CHLogger
open CHDot
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHIFSystem
open JCHPreAPI

(* jchstacgui *)
open JCHBCFunctions

    

class type control_flow_graph_int =
object
  method to_dot: int -> canvas_window_int ->
    (string * CHCanvasBase.canvas_node_item_int list)
  method to_annotated_dot: int -> canvas_window_int -> bool ->
    (string * CHCanvasBase.canvas_node_item_int list)
end

class control_flow_graph_t:control_flow_graph_int =
object

  method to_dot (index:int) (window:canvas_window_int) =
    let cms = retrieve_cms index in
    let mInfo = app#get_method cms in
    let (fname,bcfunction) = bcfunctions#get_bc_function mInfo in
    let graph = bcfunction#get_cfg_dot in
    let _ = graph#setRankdir "TB" in
    let (graphNodes,_) = window#show_graph graph fname in
    (fname,graphNodes)

  method to_annotated_dot (index:int) (window:canvas_window_int) (has_costs:bool) =
    let cms = retrieve_cms index in
    let mInfo = app#get_method cms in
    let (fname,bcfunction) = bcfunctions#get_bc_function mInfo in
    let graph = bcfunction#get_annotated_cfg_dot has_costs in
    let _ = graph#setRankdir "TB" in
    let (graphNodes,_) = window#show_graph graph fname in
    (fname,graphNodes)

end

let control_flow_graph = new control_flow_graph_t
