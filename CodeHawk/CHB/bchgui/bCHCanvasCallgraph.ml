(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHDot
open CHPrettyUtil
open CHUtil

(* xprlib *)
open Xprt
open XprToPretty

(* chgui *)
open CHCanvasBase

(* bchlib *)
open BCHDoubleword
open BCHFloc
open BCHFunctionInfo
open BCHFunctionData
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo

(* bchlibx86 *)
open BCHX86Opcodes
open BCHAssemblyBlock
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHAssemblyInstruction
open BCHAssemblyInstructionAnnotations

(* bchanalyze *)
open BCHTrace

module H = Hashtbl

let string_printer = CHPrettyUtil.string_printer

let replace_lst = [ ('"', "") ; ('%', "pct") ]

let sanitize (s:string) =
  let result =
    List.fold_left (fun sa (c,r) -> string_replace c r sa) s replace_lst in
  begin
    pr_debug [ STR "Sanitize " ; STR s ; STR " into " ; STR result ; NL ] ;
    result
  end

let make_va_node_name (va:doubleword_int) = "n" ^ (dw_index_to_string va#index)
                                          
let make_index_node_name (index:dw_index_t) = "n" ^ (dw_index_to_string index)
                                            
let get_address (nodeName:string) = 
  index_to_doubleword (string_to_dw_index (string_suffix nodeName 1))
  
let get_fname faddr =
  if functions_data#has_function_name faddr then
    (functions_data#get_function faddr)#get_function_name
  else
    faddr#to_hex_string

let print_argument (floc:floc_int) invio par =
  let args = floc#get_call_args in
  try
    let (_,arg) =
      List.find (fun (p,_) ->
          match p.apar_location with
          | StackParameter i -> i = par | _ -> false) args in
    xpr_formatter#pr_expr arg
  with
    Not_found -> STR ("?" ^ (string_of_int par) ^ "?")
	
let trace_forward_arg (graph:dot_graph_int) faddress op_n =
  let make_sig_node faddr op = "n" ^ faddr#to_hex_string ^ (string_of_int op) in
  let make_call_node faddr iaddr par = 
    "n" ^ faddr#to_hex_string ^ iaddr#to_hex_string ^ (string_of_int par) in
  let make_dll_node name par = "n" ^ name ^ (string_of_int par) in
  let make_jni_node fintf par = "n" ^ fintf.fintf_name ^ (string_of_int par) in
  let make_sig_label faddr op =
    (get_fname faddr) ^ "(" ^ (string_of_int op) ^ ")" in
  let make_call_label floc invio par =
    string_printer#print (print_argument floc invio par) in
  let make_dll_label dll name par = 
    if function_summary_library#has_dll_function dll name then
      let fsum = function_summary_library#get_dll_function dll name in
      let pars = fsum#get_parameters in
      let pname = 
	try
	  let par = List.find (fun p -> match p.apar_location with
	    | StackParameter i -> i = par | _ -> false) pars in
	  "," ^ par.apar_name
	with
	  Not_found -> "" in
      name ^ "(" ^ (string_of_int par) ^ pname ^ ")" 
    else 
      name ^ "(" ^ (string_of_int par) ^ ")" in
  let make_jni_label fintf par =
    let fts = fintf.fintf_type_signature in
    let pars = fts.fts_parameters in
      let pname = 
	try
	  let par = List.find (fun p -> match p.apar_location with
	    | StackParameter i -> i = par | _ -> false) pars in
	  "," ^ par.apar_name
	with
	  Not_found -> "" in
      fintf.fintf_name ^ "(" ^ (string_of_int par) ^ pname ^ ")" in
  let table = H.create 5 in
  let dllNodes = ref [] in
  let add_dll_node n =
    if List.mem n !dllNodes then () else dllNodes := n :: !dllNodes in
  let jniNodes = ref [] in
  let add_jni_node n =
    if List.mem n !jniNodes then () else jniNodes := n :: !jniNodes in
  let rec aux faddr op =
    (* let fname = get_fname faddr in *)
    (* let finfo = load_function_info faddr in *)
    let callees = get_callees faddr in
    let _ =
      graph#addNode
        ~label:(make_sig_label faddr op) (make_sig_node faddr op) in
    let _ = H.add table (make_sig_label faddr op) 1 in
    List.iter (fun callee ->
        if callee#has_call_target then
          let ctinfo = callee#get_call_target in
	  let call_args = callee#get_call_args in
	  List.iter (fun (p,e) ->
	      match p.apar_location with
	      | StackParameter par ->
	         let argIndices = [] in  (* get_xarg_indices finfo e in *)
	         if List.mem op argIndices then
	           let label = make_call_label callee callee par in
	           let callNode = make_call_node faddr callee#l#i par in
	           let srcSigNode = make_sig_node faddr op in
	           let tgtSigNode tgt = make_sig_node tgt par in
	           begin
		     graph#addNode ~label callNode;
		     graph#addEdge srcSigNode callNode ;
		     if ctinfo#is_app_call then
		       let target = ctinfo#get_application_target in
		       begin
		         graph#addEdge callNode (tgtSigNode target) ;
		         if H.mem table (make_sig_label target par) then () else 
		           begin
			     H.add table (make_sig_label target par) 1;
			     aux target par
		           end
		       end
		     else if ctinfo#is_dll_call then
		       let (dll,target) = ctinfo#get_dll_target in
		       let label = make_dll_label dll target par in
		       let dllNode = make_dll_node target par in
		       begin
		         graph#addNode ~label dllNode ;
		         graph#addEdge callNode dllNode ;
		         add_dll_node dllNode
		       end
		     else if ctinfo#is_jni_call then
		       let jniIndex = ctinfo#get_jni_index in
		       if function_summary_library#has_jni_function jniIndex then
		         let fintf =
                           (function_summary_library#get_jni_function jniIndex)#get_function_interface in
		         let label = make_jni_label fintf par in
		         let jniNode = make_jni_node fintf par in
		         begin
		           graph#addNode ~label jniNode ;
		           graph#addEdge callNode jniNode ;
		           add_jni_node jniNode
		         end
	           end
	      | _ -> ()) call_args
        else
	  ()) callees in
  begin
    aux faddress op_n ;
    (make_sig_node faddress op_n,!dllNodes,!jniNodes)
  end


let trace_fwd_returnval (graph:dot_graph_int) faddr v =
  let finfo = load_function_info faddr in
  let callees = get_callees faddr in
  let _ = graph#addNode ~label:v#getName#getBaseName "root" in
  List.iter (fun callee ->
    if callee#has_call_target then
      let call_args = callee#get_call_args in
      List.iter (fun (p,x) ->
	if var_is_referenced finfo x v then
	  match p.apar_location with
	  | StackParameter i -> 
	     if callee#has_call_target then
               let ctinfo = callee#get_call_target in
               if ctinfo#is_app_call then
	         let target = ctinfo#get_application_target in
	         let (node,_,_) = trace_forward_arg graph target i in
	         let _ = graph#addEdge "root" node in
	         ()
	       else if ctinfo#is_dll_call then
	         let (_,target) = ctinfo#get_dll_target in
	         let _ = graph#addNode ~label:(target ^ "(" ^ (string_of_int i) ^ ")")
		                       ("n_" ^ target ^ (string_of_int i)) in
	         let _ = graph#addEdge "root" ("n_" ^ target ^ (string_of_int i)) in
	         ()
               else
                 ()
	     else
	       ()
	  | _ -> ()) call_args ) callees
		
  
let trace_fwd_sideeffect (graph:dot_graph_int) faddr floc v =
  let finfo = get_function_info faddr in
  let callees = get_callees faddr in
  let _ = graph#addNode ~label:v#getName#getBaseName "root" in
  List.iter (fun callee ->
      let call_args = callee#get_call_args in
      let ctinfo = callee#get_call_target in
      List.iter (fun (p,x) ->
	if se_address_is_referenced finfo floc x v then
	  match p.apar_location with
	  | StackParameter i -> 
	    if ctinfo#is_app_call then
	      let target = ctinfo#get_application_target in
	      let (node,_,_) = trace_forward_arg graph target i in
	      let _ = graph#addEdge "root" node in
	      ()
	    else if ctinfo#is_dll_call then
	      let (_,target) = ctinfo#get_dll_target in
	      let _ = graph#addNode ~label:(target ^ "(" ^ (string_of_int i) ^ ")")
		("n_" ^ target ^ (string_of_int i)) in
	      let _ = graph#addEdge "root" ("n_" ^ target ^ (string_of_int i)) in
	      ()
	    else
	      ()
	  | _ -> ()) call_args ) callees

 
class type canvas_call_graph_int =
object
  method reset: unit
  method system_call_graph_to_dot: canvas_window_int -> unit
  method sub_call_graph_to_dot: dw_index_t -> canvas_window_int -> unit
  method sub_rv_call_graph_to_dot: dw_index_t -> canvas_window_int -> unit
  method trace_graph_to_dot: dw_index_t -> int -> canvas_window_int -> unit
  method trace_rv_to_dot: dw_index_t -> variable_t -> canvas_window_int -> unit
  method trace_se_to_dot:
           dw_index_t -> floc_int -> variable_t -> canvas_window_int -> unit
end

class canvas_call_graph_t :canvas_call_graph_int =
object (self)

  val mutable opt_system_call_graph = None

  method reset = opt_system_call_graph <- None

  method private color_nodes nodes dllNodes jniNodes =
    List.iter (fun node ->
      let nodeName = node#get_name in
      if List.mem nodeName dllNodes then
	node#set_color CHCanvasBase.green
      else if List.mem nodeName jniNodes then
	node#set_color CHCanvasBase.yellow) nodes

  method sub_call_graph_to_dot 
    (function_index:dw_index_t) (canvas_window:canvas_window_int) =
    let nodeName = make_index_node_name function_index in
    let functionAddress = index_to_doubleword function_index in
    let graphName = if functions_data#has_function_name functionAddress then
	(functions_data#get_function functionAddress)#get_function_name
      else
	functionAddress#to_hex_string in
    let (graph,dllNodes,jniNodes) = 
      match opt_system_call_graph with 
      | Some g -> g 
      | _ -> self#system_call_graph_to_dot_aux "LR" in
    let subgraph = graph#subgraph nodeName graphName in
    let (nodes,_) = canvas_window#show_graph subgraph graphName in
    let _ = self#color_nodes nodes dllNodes jniNodes in
    ()    
 
  method sub_rv_call_graph_to_dot 
    (function_index:dw_index_t) (canvas_window:canvas_window_int) =
    let nodeName = make_index_node_name function_index in
    let functionAddress = index_to_doubleword function_index in
    let graphName = if functions_data#has_function_name functionAddress then
	(functions_data#get_function functionAddress)#get_function_name
      else
	functionAddress#to_hex_string in
    let (graph,_,_) = 
      match opt_system_call_graph with 
      | Some g -> g 
      | _ -> self#system_call_graph_to_dot_aux "TB" in
    let subgraph = graph#revsubgraph nodeName graphName in
    let _ = canvas_window#show_graph subgraph graphName in
    ()    
   
  method system_call_graph_to_dot (canvas_window:canvas_window_int) =
    let name = "system-call-graph" in
    let (graph,dllNodes,jniNodes) = 
      match opt_system_call_graph with 
      | Some g -> g
      | _ -> self#system_call_graph_to_dot_aux "LR" in
    let (nodes,_) = canvas_window#show_graph graph name in
    let _ = self#color_nodes nodes dllNodes jniNodes in
    ()

  method trace_graph_to_dot
           (findex:dw_index_t) (op:int) (canvas_window:canvas_window_int) =
    let faddr = index_to_doubleword findex in
    let graph = mk_dot_graph "trace-graph" in
    let (_,dllNodes,jniNodes) = trace_forward_arg graph faddr op in
    let (nodes,_) = canvas_window#show_graph graph "trace-graph" in
    let _ = self#color_nodes nodes dllNodes jniNodes in
    ()

  method trace_rv_to_dot 
    (findex:dw_index_t) (v:variable_t) (canvas_window:canvas_window_int) =
    let faddr = index_to_doubleword findex in
    let graph = mk_dot_graph "rv-graph" in
    let _ = trace_fwd_returnval graph faddr v in
    let _ = canvas_window#show_graph graph "rv-graph" in
    ()

  method trace_se_to_dot
           (findex:dw_index_t)
           (floc:floc_int)
           (v:variable_t)
           (canvas_window:canvas_window_int) =
    let faddr = index_to_doubleword findex in
    let graph = mk_dot_graph "rv-graph" in
    let _ = trace_fwd_sideeffect graph faddr floc v in
    let _ = canvas_window#show_graph graph "rv-graph" in
    ()
    
    
  method private system_call_graph_to_dot_aux rankdir =
    let name = "system-call-graph" in
    let graph = mk_dot_graph name in
    let _ = graph#setRankdir rankdir in
    let dllNodes = ref [] in
    let jniNodes = ref [] in
    let add_dll_node (name:string)  = 
      if List.mem name !dllNodes then () else dllNodes := name :: !dllNodes in
    let add_jni_node (name:string) =
      if List.mem name !jniNodes then () else jniNodes := name :: !jniNodes in
    let add_tgt_node (nodename:string) (tgt:call_target_t) =
      match tgt with 
      | StubTarget (DllFunction (_,dllfn)) -> 
	begin
	  add_dll_node dllfn ;
	  graph#addEdge nodename dllfn
	end
      | AppTarget a -> graph#addEdge nodename (make_va_node_name a)
      | _ -> () in
    let _ = assembly_functions#itera
      (fun faddr f ->
	let nodename = make_va_node_name faddr in
	let label = get_fname faddr in
	begin
	  graph#addNode ~label nodename ;
	  f#iter_calls (fun _ floc ->
              if floc#has_call_target then
                let ctinfo = floc#get_call_target in
	        if ctinfo#is_dll_call then
	          let (_,dllfn) = ctinfo#get_dll_target in
	          begin add_dll_node dllfn ; graph#addEdge nodename dllfn end
	        else if ctinfo#is_app_call then
	          graph#addEdge
                    nodename (make_va_node_name ctinfo#get_application_target)
	        else if ctinfo#is_indirect_call then
	          let tgts = [] (* floc#get_indirect_target *) in
	          List.iter (add_tgt_node nodename) tgts
	        else if ctinfo#is_jni_call then
	          let jniIndex = ctinfo#get_jni_index in
	          if function_summary_library#has_jni_function jniIndex then
		    let fsum = function_summary_library#get_jni_function jniIndex in
		    let fintf = fsum#get_function_interface in
		    begin 
		      add_jni_node fintf.fintf_name  ;
		      graph#addEdge nodename fintf.fintf_name
		    end
                  else
                    ()
	        else ())
	end) in
    let _ = List.iter (fun dllfn -> graph#addNode ~label:dllfn dllfn) !dllNodes in
    let _ = List.iter (fun jnifn -> graph#addNode ~label:jnifn jnifn) !jniNodes in
    begin
      opt_system_call_graph <- Some (graph, !dllNodes, !jniNodes) ;
      (graph, !dllNodes, !jniNodes)
    end

end

let canvas_call_graph = new canvas_call_graph_t						     
	    
