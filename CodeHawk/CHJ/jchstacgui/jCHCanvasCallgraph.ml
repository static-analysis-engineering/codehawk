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

(* chutil *)
open CHDot
open CHUtil
open CHXmlDocument
open CHXmlReader
   

(* chgui *)
open CHCanvasBase

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI
open JCHPreFileIO

(* jchstacgui *)
open JCHBCFunctions
open JCHCostValues
open JCHSystemDisplay

let replace_lst = [ ('"',"") ; ('%', "pct") ; ('<',"__") ; ('>',"__") ]

let sanitize s =
  let result =
    List.fold_left (fun sa (c,r) -> string_replace c r sa) s replace_lst in
  begin
    result
  end

let mk_nodename ?(include_package=false) (cms:class_method_signature_int) =
  let cn = cms#class_name in
  let packageinit =
    String.concat "" (List.map (fun s -> String.sub s 0 1) cn#package) in
  let name = 
    cn#simple_name ^ "." ^ cms#name ^ "_" ^ (string_of_int cms#index) in
  let name =
    if include_package then
      packageinit ^ "." ^ name
    else
      name in
  sanitize name

let mk_nodelabel ?(show_cost=false) (cms:class_method_signature_int) =
  let name = mk_nodename cms in
  let coststr =
    if show_cost then
      match costvalues#get_method_cost_string cms#index with
      | Some s ->  ": " ^ s
      | _ -> ""
    else
      "" in
  name ^ coststr

class type canvas_callgraph_int =
  object
    method reset: unit
    method sub_callgraph_to_dot:
             int -> canvas_window_int -> ?show_cost:bool -> bool -> unit
    method sub_rv_callgraph_to_dot:  int -> canvas_window_int -> unit
    method system_callgraph_to_dot:
             canvas_window_int -> ?show_cost:bool -> bool -> unit
  end

class canvas_callgraph_t:canvas_callgraph_int =
object(self)

  val mutable opt_system_callgraph = None
  val mutable opt_min_system_callgraph = None
  val excludedmethods = read_excluded_methods ()

  method reset = opt_system_callgraph <- None

  method private color_nodes nodes stubNodes nativeNodes loopingNodes =
    List.iter (fun node ->
      let nodeName = node#get_name in
      if List.mem nodeName stubNodes then
	node#set_color CHCanvasBase.green
      else if List.mem nodeName nativeNodes then
	node#set_color CHCanvasBase.yellow
      else if List.exists (fun (n,_) -> n = nodeName) loopingNodes then
	let (_,depth) = List.find (fun (n,_) -> n = nodeName) loopingNodes in
	match depth with
	| 0 -> ()
	| 1 -> node#set_color 0xFFAAAAFF
	| 2 -> node#set_color 0xFF7777FF
	| 3 -> node#set_color 0xFF3333FF
	| _ -> node#set_color 0xFF0000FF) nodes

  method sub_callgraph_to_dot
           (cmsId:int)
           (window:canvas_window_int)
           ?(show_cost=false)
           (show_libcalls:bool) =
    let cms = retrieve_cms cmsId in
    if self#method_is_excluded cms then
      write_message_pp (LBLOCK [ STR "Method " ; cms#toPretty ; 
			      STR " has been excluded from the call graph" ])
    else
      let graphName = "method_" ^ (string_of_int cmsId) ^ "_cg" ^
	(if show_libcalls then "" else "_nolib") in
      let (graph,stubNodes,nativeNodes,loopingNodes) = 
	if show_libcalls then
	  match opt_system_callgraph with
	  | Some g -> g
	  | _ -> self#system_callgraph_to_dot_aux ~show_cost true
	else
	  match opt_min_system_callgraph with
	  | Some g -> g
	  | _ -> self#system_callgraph_to_dot_aux ~show_cost false in
      let subgraph = graph#subgraph (mk_nodename cms) graphName in
      let (nodes,_) = window#show_graph subgraph graphName in
      let _ = self#color_nodes nodes stubNodes nativeNodes loopingNodes in
      write_message_pp
        (LBLOCK [ STR "Created descendant callgraph for " ; cms#toPretty ])

  method sub_rv_callgraph_to_dot (cmsId:int) (window:canvas_window_int) =
    let cms = retrieve_cms cmsId in
    if self#method_is_excluded cms then
      write_message_pp (LBLOCK [ STR "Method " ; cms#toPretty ; 
			      STR " has been excluded from the call graph" ])
    else
      let cms = retrieve_cms cmsId in
      let graphName = "method_" ^ (string_of_int cmsId) ^ "_rvcg" in
      let (graph,stubNodes,nativeNodes,loopingNodes) =
	match opt_system_callgraph with
	| Some g -> g
	| _ -> self#system_callgraph_to_dot_aux true in
      let subgraph = graph#revsubgraph (mk_nodename cms) graphName in
      let _ = subgraph#setRankdir "TB" in
      let _ = pr_debug [ STR "Show graph ... " ; NL ] in
      let (nodes,_) = window#show_graph subgraph graphName in
      let _ = pr_debug [ STR " Color nodes ... " ; NL ] in
      let _ = self#color_nodes nodes stubNodes nativeNodes loopingNodes in
      write_message_pp (LBLOCK [ STR "Created ascendant callgraph for " ; cms#toPretty ])

  method system_callgraph_to_dot
           (window:canvas_window_int)
           ?(show_cost=false)
           (show_libcalls:bool) =
    let (graph,stubNodes,nativeNodes,loopingNodes) =
      if show_libcalls then 
	match opt_system_callgraph with
	| Some g -> g
	| _ -> self#system_callgraph_to_dot_aux ~show_cost true
      else
	match opt_min_system_callgraph with
	| Some g -> g
	| _ -> self#system_callgraph_to_dot_aux ~show_cost false in
    let (nodes,_) = window#show_graph graph "system-call-graph" in
    let _ = self#color_nodes nodes stubNodes nativeNodes loopingNodes in
    ()

  method private method_is_excluded (cms:class_method_signature_int) =
    List.exists (fun ix -> ix = cms#index) excludedmethods

  method private system_callgraph_to_dot_aux
                   ?(show_cost=false) (show_libcalls:bool) =
    let name = "system-call-graph" in
    let graph = mk_dot_graph name in
    let stubNodes = ref [] in
    let nativeNodes = ref [] in
    let loopingNodes = ref [] in
    let addStubNode (name:string) =
      if List.mem name !stubNodes then
        ()
      else
        stubNodes := name :: !stubNodes in
    let addNativeNode (name:string) =
      if List.mem name !nativeNodes then
        ()
      else
        nativeNodes := name :: !nativeNodes in
    let addLoopingNode (name:string) (depth:int) =
      if List.exists (fun (n,_) -> n = name) !loopingNodes then
        ()
      else 
	loopingNodes := (name,depth) :: !loopingNodes in
    let checkLoopingNode (mInfo:method_info_int) (name:string) =
      try
	if mInfo#has_bytecode then
	  let (_,bcfunction) = bcfunctions#get_bc_function mInfo in
	  let maxloopdepth = bcfunction#get_max_loop_depth in
          if maxloopdepth > 0 then addLoopingNode name maxloopdepth
      with 
      | JCH_failure p -> 
        pr_debug [ STR "Error in call graph for " ; 
	           mInfo#get_class_method_signature#toPretty ;
                   STR ": " ; p ; NL ]
      | XmlDocumentError (line,col,p) 
      | XmlParseError (line,col,p) ->
	pr_debug [ STR "Xml error in retrieving loops for " ;
	           mInfo#get_class_method_signature#toPretty ; STR " at (" ;
	           INT line ; STR "," ; INT col ; STR "): " ; p ; NL ] in
    let addTgtNode
          (nodename:string)
          (nodelabel:string)
          (cms:class_method_signature_int) =
      let mInfo = app#get_method cms in
      let tgtname = mk_nodename cms in
      let tgtlabel = mk_nodelabel ~show_cost cms in
      begin
	graph#addNode ~label:nodelabel nodename ;
	graph#addNode ~label:tgtlabel  tgtname ;
	graph#addEdge nodename tgtname ;
	if mInfo#is_stubbed then addStubNode tgtname ;
	if mInfo#is_native then addNativeNode tgtname ;
	checkLoopingNode mInfo tgtname
      end in
    begin
      List.iter (fun mInfo ->
	let cms = mInfo#get_class_method_signature in
	if self#method_is_excluded cms then () else
	  let nodename = mk_nodename cms in
          let nodelabel = mk_nodelabel ~show_cost cms in
	  let _ = graph#addNode ~label:nodelabel nodename in
	  let _ = checkLoopingNode mInfo nodename in
	  if show_libcalls then
	    List.iter (fun tgtcms -> 
	      if self#method_is_excluded tgtcms then () else
		addTgtNode nodename nodelabel tgtcms) mInfo#get_callees
	  else
            List.iter (fun tgtcms -> 
	      let tgtinfo = app#get_method tgtcms in
	      if mInfo#is_stubbed
                 || tgtinfo#is_stubbed
                 || (self#method_is_excluded tgtcms)
              then () 
              else addTgtNode nodename nodelabel tgtcms) mInfo#get_callees)
	app#get_methods ;
      List.iter (fun stub ->
          graph#addNode ~label:stub stub) !stubNodes;
      List.iter (fun native ->
          graph#addNode ~label:native native) !nativeNodes ;
      List.iter (fun (llnode,_) ->
          graph#addNode ~label:llnode llnode) !loopingNodes ;
      (if show_libcalls then
	  opt_system_callgraph <- 
	    Some (graph, !stubNodes, !nativeNodes, !loopingNodes)
       else
	  opt_min_system_callgraph <- 
	    Some (graph, !stubNodes, !nativeNodes, !loopingNodes)) ;
      (graph, !stubNodes, !nativeNodes, !loopingNodes)
    end
end

let canvas_callgraph = new canvas_callgraph_t


 
