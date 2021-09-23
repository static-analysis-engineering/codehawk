(* =============================================================================
   CodeHawk Java Analyzer
   Author: Andrew McGraw and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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
open CHSCC
open CHUtils

(* chgui *)
open CHCanvasBase

(* chutil *)
open CHLogger
open CHDot
open CHPrettyUtil
open CHUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHAnalysisResults
open JCHAnnotationsPre   
open JCHApplication
open JCHBCFunction
open JCHIFSystem
open JCHPreAPI

(* jchstacgui *)
open JCHCostValues

module H = Hashtbl


let reflectiveops = [
  ("java.lang.Class", "forName") ;
  ("java.lang.Class", "newInstance") ]

let is_reflective_op cname mname =
  List.exists (fun (c,m) -> c = cname && m = mname) reflectiveops

let reflectivepackages = [ "java.lang.reflect" ]

let condition_substitution s =
  if s = "randomNumberGeneratorInstance.nextDouble()" then
    "p"
  else
    s


let is_reflective_call (cn:class_name_int) (ms:method_signature_int) =
  List.mem cn#package_name  reflectivepackages ||
    is_reflective_op cn#name ms#name

class type bc_function_int =
  object
    method get_blocks: bc_block_int list
    method get_cfg_dot: dot_graph_int
    method get_annotated_cfg_dot: bool -> dot_graph_int
    method get_max_loop_depth: int
    method get_conditions: (int * string) list
    method get_reflective_calls: (int * opcode_t * pretty_t) list
    method get_pushpop_calls: (int * opcode_t * pretty_t) list
    method get_thread_calls: (int * opcode_t * pretty_t) list
    method get_append_calls: (int * opcode_t * pretty_t) list
    method get_loop_taint: int -> int
    method get_cost: int -> int
    method get_total_cost: int
    method get_loop_levels: int -> symbol_t list

    method has_method_call: string -> int -> bool
    method has_class_call: string -> int -> bool
  end
    
class bc_function_t 
        (mInfo:method_info_int)
        (blocks:bc_block_int list)
        (succ:(int * int) list):bc_function_int =
object (self)

  val mutable looplevels = None

  method get_blocks = blocks

  method get_cfg_dot =
    let g = mk_dot_graph "cfg" in
    let name i = "pc=" ^ (string_of_int i) in
    begin
      List.iter (fun b ->
    let label = name b#get_firstpc in
    begin
      g#addNode ~label label ;
      List.iter
        (fun s -> g#addEdge label (name s))
        b#get_successors
    end) blocks ;
      g
    end

  method get_max_loop_depth = 
    let cfglooplevels = get_cfg_loop_levels mInfo blocks succ in
    H.fold
      (fun _ v m ->
        let len = List.length v in if len > m then len else m) cfglooplevels 0

  method get_conditions =
    let result = ref [] in
    begin
      List.iter (fun b ->
	let lastpc = b#get_lastpc in
	if is_conditional_jump mInfo lastpc then
	  let anntrue = fst (get_cfg_tf_annotations mInfo lastpc) in
	  result := (lastpc, anntrue) :: !result) blocks ;
      !result
    end

  method get_reflective_calls =
    let result = ref [] in
    begin
      List.iter (fun b ->
	b#iter (fun pc opc ->
	  match opc with
	  | OpInvokeVirtual (TClass cn, ms) 
	  | OpInvokeStatic (cn,ms) when is_reflective_call cn ms ->
	    let ann = opcode_annotation mInfo pc opc in
	    result := (pc,opc,ann) :: !result
	  | _ -> ())) blocks ;
      List.sort (fun (pc1,_,_) (pc2,_,_) -> Stdlib.compare pc1 pc2) !result
    end

  method get_pushpop_calls =
    let result = ref [] in
    begin
      List.iter (fun b ->
	b#iter (fun pc opc ->
	  match opc with
	  | OpInvokeVirtual (_, ms) when ms#name = "push" || ms#name = "pop" ->
	    let ann = opcode_annotation mInfo pc opc in
	    result := (pc,opc,ann) :: !result
	  | _ -> ())) blocks ;
      List.sort (fun (pc1,_,_) (pc2,_,_) -> Stdlib.compare pc1 pc2) !result
    end

  method get_thread_calls =
    let result = ref [] in
    begin
      List.iter (fun b ->
	b#iter (fun pc opc ->
	  match opc with
	  | OpInvokeStatic (_,ms) when ms#name = "sleep" ->
	    let ann = opcode_annotation mInfo pc opc in
	    result := (pc,opc,ann) :: !result
	  | OpInvokeStatic (cn,_)
	  | OpInvokeVirtual (TClass cn,_) when cn#name = "java.lang.Thread" ->
	    let ann = opcode_annotation mInfo pc opc in
	    result := (pc,opc,ann) :: !result
	  | _ -> ())) blocks ;
      List.sort (fun (pc1,_,_) (pc2,_,_) -> Stdlib.compare pc1 pc2) !result
    end

  method get_append_calls =
    let result = ref [] in
    begin
      List.iter (fun b ->
	b#iter (fun pc opc ->
	  match opc with
	  | OpInvokeVirtual (_,ms) when ms#name = "append" ->
	    let ann = opcode_annotation mInfo pc opc in
	    result := (pc,opc,ann) :: !result
	  | _ -> ())) blocks ;
      List.sort (fun (pc1,_,_) (pc2,_,_) -> Stdlib.compare pc1 pc2) !result
    end

	

  method get_annotated_cfg_dot (has_costs:bool) =
    let g = mk_dot_graph "acfg" in
    let mk_nodename pc = "pc=" ^ (string_of_int pc) in
    let mk_nodelabel pc = 
      let cms = mInfo#get_class_method_signature#index in
      let coststr =
        if has_costs then
          match costvalues#get_block_cost_string cms pc with
          | Some s -> ": " ^ s
          | _ -> ""
        else
          "" in
	  let loopcoststr = 
		if has_costs then
		  match costvalues#get_loop_cost_string cms pc with
		  | Some s -> ",L[" ^ s
		  | _ -> ""
		else
		  "" in
	  let loopiterstr =
		if has_costs then
		  match costvalues#get_loop_iter_string cms pc with
		  | Some s -> "," ^ s ^ "]"
		  | _ -> ""
		else
		  "" in
      (mk_nodename pc) ^ coststr ^ loopcoststr ^ loopiterstr in
    begin
      List.iter (fun b ->
	  let nodelabel = mk_nodelabel b#get_firstpc in
          let nodename = mk_nodename b#get_firstpc in
	  let _ = g#addNode ~label:nodelabel nodename in
	  let edgeLabeling =
	    let lastpc = b#get_lastpc in
	    if is_conditional_jump mInfo lastpc then
	      let (anntrue,annfalse) =
                get_cfg_tf_annotations ~subst:condition_substitution mInfo lastpc in
	      let offset = get_offset mInfo lastpc in
	      let fsucc = mInfo#get_next_bytecode_offset lastpc in
	      let tsucc = lastpc + offset in
	      let fblock = List.find (fun b -> b = fsucc) b#get_successors in
	      let tblock = List.find (fun b -> b = tsucc) b#get_successors in
	      Some ([ (fblock,annfalse) ; (tblock,anntrue) ])
	    else
	      match mInfo#get_opcode lastpc with
	      | OpTableSwitch(def,_,_,table) ->
	         let tblocks =
                   Array.to_list
                     (Array.mapi (fun i v -> 
		          let succ =
                            List.find (fun b -> b = (lastpc + v)) b#get_successors in
		          (succ, string_of_int (i+1))) table) in
	         let defblock =
                   List.find (fun b -> b = (lastpc + def)) b#get_successors in
	         let tblocks = (defblock, "default") :: tblocks in
	         Some tblocks
	      | _ -> None in
	  match edgeLabeling with
	  | None ->
	     List.iter (fun s ->
                 g#addEdge nodename (mk_nodename s)) b#get_successors
	  | Some ablocks ->
	     List.iter (fun (s,txt) ->
                 g#addEdge ~label:txt nodename (mk_nodename s)) ablocks) blocks;
      g
    end
      
  method get_loop_taint (pc:int) =
    let cmsId = mInfo#get_index in
    (application_analysis_results#get_taints cmsId)#get_loopcounter_taint_level pc

  method has_method_call (name:string) (pc:int) =
    try
      let block = List.find (fun b -> b#get_firstpc = pc) blocks in
      let result = ref false in
      begin
	block#iter (fun pc opc ->
	  match opc with
	  | OpInvokeVirtual (_,ms) 
	  | OpInvokeStatic (_,ms) when ms#name = name -> result := true
	  | _ -> ()) ;
	!result
      end
    with
    | JCH_failure p ->
      begin pr_debug [ STR "Error in has_method_call: " ; p ] ; false end

  method has_class_call (classname:string) (pc:int) =
    try
      let block = List.find (fun b -> b#get_firstpc = pc) blocks in
      let result = ref false in
      begin
	block#iter (fun pc opc ->
	  match opc with
	  | OpInvokeVirtual (TClass cn,_) 
	  | OpInvokeStatic (cn,_) when cn#name = classname -> result := true
	  | _ -> ()) ;
	!result
      end
    with
    | JCH_failure p ->
      begin pr_debug [ STR "Error in has_class_call: " ; p ] ; false end

  method get_cost (pc:int) =
    let block = List.find (fun b -> b#get_firstpc = pc) blocks in
    block#get_cost

  method get_total_cost =
    List.fold_left (fun acc b -> acc + b#get_cost) 0 blocks

  method get_loop_levels (pc:int) =
    let retrieve () = match looplevels with
      | Some t -> if H.mem t pc then H.find t pc else []
      | _ -> [] in
    match looplevels with
    | Some _ -> retrieve ()
    | _ -> 
      let _ = looplevels <- Some (get_cfg_loop_levels mInfo blocks succ) in
      retrieve ()
	
end


let get_bc_function (mInfo:method_info_int) =
  let (blocks,successors) = get_bc_function_basic_blocks mInfo in
  new bc_function_t mInfo blocks successors

class type bc_functions_int =
  object
    method get_bc_function: method_info_int -> string  * bc_function_int
    method get_bc_function_by_name: string -> bc_function_int
  end

class bc_functions_t:bc_functions_int =
object

  val table = H.create 11
  val indices = H.create 11

  method get_bc_function (mInfo:method_info_int):(string * bc_function_int) =
    if H.mem table mInfo#get_index then H.find table mInfo#get_index else
      let bcf = get_bc_function mInfo in
      let cms = mInfo#get_class_method_signature in
      let mname = cms#method_name_string in
      let mname =
        if mname = "<init>" then
	  "__constructor__"
	else
          if mname = "<clinit>" then
	    " __classconstructor__"
          else
            if (String.length mname) > 6 && String.sub mname 0 6 = "lambda" then
              string_replace '$' "__" mname
            else if (String.length mname) > 20
                    && String.sub mname 0 19 = "$deserializeLambda$" then
              string_replace '$' "__" mname
	else mname in
      let name = mname ^ "_" ^ (string_of_int cms#index) in
      begin 
	H.add table mInfo#get_index (name,bcf) ; 
	H.add indices name mInfo#get_index ;
	(name,bcf)
      end

  method get_bc_function_by_name (name:string) =
    if H.mem indices name then
      let (_,f) = H.find table (H.find indices name) in f
    else
      raise
        (JCH_failure
           (LBLOCK [ STR "No function found for name " ; STR name ]))


end

let bcfunctions = new bc_functions_t
