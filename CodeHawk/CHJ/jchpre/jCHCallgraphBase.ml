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
open CHUtils

(* chutil *)
open CHLogger
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHFile

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHCGDictionary
open JCHClassInfo
open JCHFunctionSummaryLibrary
open JCHFunctionSummaryXmlDecoder
open JCHMethodImplementations
open JCHPreAPI
open JCHSystemSettings
open JCHUserData
open JCHXmlUtil

module H = Hashtbl
module P = Pervasives

let ms_implementers_init = {
  mscn_classes =  [] ;
  mscn_stubs = [] ;
  mscn_native = []
}

let create_ordering 
    (functions:int list) 
    (calls:(int * int) list)  =
  let get_pivot_node cs fnIndices =
    let counts = Hashtbl.create 10 in
    let add dw = if Hashtbl.mem counts dw then 
	Hashtbl.replace counts dw ((Hashtbl.find counts dw) + 1)
      else
	Hashtbl.add counts dw 1 in
    let maxCount = ref (fst (List.hd cs),-1) in
    let _ = List.iter (fun (_,callee) -> add callee) cs in
    let _ = Hashtbl.iter (fun k v -> 
      if v > (snd !maxCount) && List.mem k fnIndices then maxCount := (k,v)) counts in
    (fst !maxCount,snd !maxCount) in
  let rec aux fns cs result stats cycle =
    match fns with 
      [] -> (result,stats,cycle)
    | _ ->
      let (leaves,nonleaves) = 
	List.fold_left (fun (l,n) (f:int) ->
	  if (List.exists (fun ((caller,_):(int * int)) -> 
	    caller = f) cs) then 
	    (l,f::n) 
	  else 
	    (f::l,n)) ([],[]) fns in
      try
	match leaves with
	  [] ->  (* there is a cycle; find the node with the largest number of incoming 
		    edges and remove one of the	outgoing edges from that node
		    pass list of functions to avoid pivoting on a non-existing function *)
	    let fnIndices = fns in
	    let (pivotNode,incoming) = get_pivot_node cs fnIndices in  
	    let edge = 
	      try
		List.find (fun (c,_) -> c = pivotNode) cs
	      with
		Not_found ->
		  begin
		    ch_error_log#add "pivot node not found"
		      (LBLOCK [ INT pivotNode ]) ;
		    raise Not_found
		  end in
	    let newCalls = List.filter 
	      (fun (e1,e2) -> 
		(not (e1 = (fst edge))) || (not (e2 = (snd edge)))) cs in  	    
	    let _ = chlog#add "break cycle" 
	      (LBLOCK [ STR "remove " ; STR "(" ; 
			INT (fst edge) ; STR "," ; INT (snd edge) ;
			STR ") with " ; INT incoming ; STR " edges (size of cycle: " ;
			INT (List.length fns) ; STR ")" ]) in
	    aux nonleaves newCalls result ((-1)::stats) true
	| _ ->
	  let newCalls = 
	    List.filter (fun (_,callee) -> 
	      List.for_all (fun f -> not (callee = f)) leaves) cs in
	  aux nonleaves newCalls (result@leaves) ((List.length leaves)::stats) cycle 
      with 
	Not_found ->
	  begin
	    ch_error_log#add "error in find cycle" 
	      (LBLOCK [ STR "calls: " ; pretty_print_list cs 
		(fun (a1,a2) ->
		  LBLOCK [ STR "(" ; INT a1 ; STR "," ; INT a2 ; STR ")" ]) 
		" [" ", " "]" ]) ;
	    (result,stats,cycle)
	  end
  in
  aux functions calls [] [] false

let summary_classpath = ref None

let get_summary_classpath () =
  match !summary_classpath with
  | None ->
    let cp = system_settings#get_summary_classpath in
    begin summary_classpath := Some cp ; cp end	
  | Some cp -> cp

let get_class_summary_codependents (c:class_summary_int) =
  let result = c#get_interfaces in
  if c#has_super_class then c#get_super_class :: result else result

let non_virtual_target_type_to_string t =
  match t with
  | PrivateMethod -> "p"
  | StaticMethod -> "s"
  | FinalClass -> "fc"
  | FinalMethod -> "fm"
  | LocalAnalysis -> "la"

let non_virtual_target_type_from_string s =
  match s with
  | "p" -> PrivateMethod
  | "s" -> StaticMethod
  | "fc" -> FinalClass
  | "fm" -> FinalMethod
  | "la" -> LocalAnalysis
  | _ -> raise (JCH_failure (LBLOCK [ STR "non-virtual-target-type " ; STR s ;
				      STR " not recognized" ]))


let write_xml_target (node:xml_element_int) (tgt:call_targets_t) =
  cgdictionary#write_xml_target node tgt
  
let read_xml_target (node:xml_element_int):call_targets_t =
  cgdictionary#read_xml_target node
  
class callgraph_base_t:callgraph_base_int =
object (self)

  val table = H.create 3
  val back_edges = new IntCollections.set_t
  val mutable callgraph_order = None

  method private add cms pc ms tgt = H.add table (cms#index,pc,ms#index) tgt

  method private add_virtual_tgt cms pc tgtCn tgtMs is_interface l =
    let tgt = match l with 
      | [] -> EmptyTarget (is_interface,tgtCn,tgtMs) 
      | _ -> VirtualTargets l in
    self#add cms pc tgtMs tgt

  method private get_instruction_target (mInfo:method_info_int) (pc:int) =
    let loc = get_bytecode_location mInfo#get_index pc in
    if app#has_instruction loc then
      let iInfo = app#get_instruction loc in
      if iInfo#has_method_target then
        let mtgt = iInfo#get_method_target () in
        if mtgt#is_top then
          None
        else
          let tgts = mtgt#get_all_targets in
          let tgts = List.map (fun minfo -> minfo#get_class_name#index) tgts in
          Some (ConstrainedVirtualTargets ("iinfo",tgts))
      else
        None
    else
      None

  method private add_forward_edges (mInfo:method_info_int) =
    let cms = mInfo#get_class_method_signature in
    if mInfo#has_bytecode then
      mInfo#bytecode_iteri (fun pc opc ->
	match opc with
	| OpInvokeStatic (cn,ms) ->
	  self#add cms pc ms (NonVirtualTarget (StaticMethod,cn#index))
	| OpInvokeSpecial (cn,ms) ->
	  self#add cms pc ms (NonVirtualTarget (PrivateMethod,cn#index))
	| OpInvokeVirtual (TClass cn,ms) when 
	       app#has_class cn && (app#get_class cn)#is_final
               && (app#has_method (make_cms cn ms)) ->
           let cn = (app#get_method (make_cms cn ms))#get_class_name in
	   self#add cms pc ms (NonVirtualTarget (FinalClass,cn#index))
	| OpInvokeVirtual (TClass cn,ms) when
	    (let tgtCms = make_cms cn ms in
	     app#has_method tgtCms && (app#get_method tgtCms)#is_final) ->
           let cn = (app#get_method (make_cms cn ms))#get_class_name in
	  self#add cms pc ms (NonVirtualTarget (FinalMethod,cn#index))
	| OpInvokeVirtual (obj,ms) ->
           begin
             match userdata#get_callees cms#index pc with
             | [] ->
                begin
                  match self#get_instruction_target mInfo pc with
                  | Some tgt -> self#add cms pc ms tgt
                  | _ ->
	             let cn = match obj with TClass cn -> cn | _ -> make_cn "java.lang.Object" in
	             let targets = 
	               List.map (fun cn -> cn#index)
	                        (method_signature_implementations#get_implementations ms) in
	             self#add_virtual_tgt cms pc cn ms false targets
                end
             | l ->
                let tgts = List.map (fun cms -> cms#class_name#index) l in
                self#add cms pc ms (ConstrainedVirtualTargets ("user",tgts))
           end
	| OpInvokeInterface (cn,ms) ->
           if userdata#has_interface_target cms#index cn#index then
             let cntgt = userdata#get_interface_target cms#index cn#index in
             let targets = ConstrainedVirtualTargets ("user",[ cntgt#index ]) in
             self#add cms pc ms targets
           else
             begin
               match userdata#get_callees cms#index pc with
               | [] -> 
                  begin
                    match self#get_instruction_target mInfo pc with
                    | Some tgt -> self#add cms pc ms tgt
                    | _ ->
                       if app#has_class cn then
	                 let cInfo = app#get_class cn in
	                 let defaultImpls = cInfo#get_default_implementations in
	                 let targets = List.map (fun cn -> cn#index) defaultImpls in
	                 self#add_virtual_tgt cms pc cn ms true targets
                       else
                         begin
                           ch_error_log#add "callgraph: missing interface" cn#toPretty ;
                           ()
                         end
                  end
               | l ->
                  let tgts = List.map (fun cms -> cms#class_name#index) l in
                  self#add cms pc ms (ConstrainedVirtualTargets ("user",tgts))
             end
	| _ -> ())
    else
      ()

  method private add_back_edge (mInfo:method_info_int) =
    let cms = mInfo#get_class_method_signature in
    let ms = cms#method_signature in
    let cn = cms#class_name in
    if ms#name = "<init>" || ms#name = "<clinit>" || 
      mInfo#is_private || mInfo#is_static then ()
    else
      let is_jdk_class cn = not (app#is_application_class cn) in
      let defines_method ms cn = app#has_class cn && (app#get_class cn)#defines_method ms in
      if app#has_class cn then
	let cInfo = app#get_class cn in
	let interfaces = List.filter is_jdk_class cInfo#get_interfaces in
	let ancestors = List.filter is_jdk_class (app#get_ancestors cn) in
	if (List.exists (defines_method ms) interfaces) ||
	  (List.exists (defines_method ms) ancestors) then
	  back_edges#add cms#index

  method build_graph =
    app#iter_methods (fun mInfo ->
      begin
	self#add_forward_edges mInfo ;
	self#add_back_edge mInfo
      end)

  method get_callees (index:int) =
    let result = ref [] in
    let _ = H.iter (fun (edgeIx,pc,msIx) tgt -> 
      if userdata#has_run_method index pc then
	let _ = chlog#add "connect start to run in callgraph"
	  (LBLOCK [ (retrieve_cms index)#toPretty ; STR " (" ; INT index ; STR ")" ;
		    STR " at pc = " ; INT pc ]) in
	let runcallee = userdata#get_run_method index pc in
	result := runcallee :: !result
      else if edgeIx = index then
	let ms = retrieve_ms msIx in
	let cnTgts = match tgt with
	  | NonVirtualTarget (_,t) -> [ t ]
	  | ConstrainedVirtualTargets (_,l) -> l
	  | VirtualTargets l -> l 
	  | _ -> [] in
	let cnTgts = List.map retrieve_cn cnTgts in
	let cmsTgts = List.map (fun cn -> make_cms cn ms) cnTgts in
	result := cmsTgts @ !result) table in
    !result

  method get_pc_callees (cmsix:int) (pc:int) =
    if userdata#has_run_method cmsix pc then
      let _ = chlog#add "connect start to run in callgraph"
	(LBLOCK [ (retrieve_cms cmsix)#toPretty ; STR " (" ; INT cmsix ; STR ")" ;
		  STR " at pc = " ; INT pc ]) in
      [ userdata#get_run_method cmsix pc ]
    else
      let result = ref [] in
      let _ = H.iter (fun (edgeIx,edgePc,msIx) tgt -> 
	          if cmsix  = edgeIx && pc = edgePc then
                    let ms = retrieve_ms msIx in
                    if userdata#has_edge (cmsix,pc) then
                      let cn = userdata#get_edge (cmsix,pc) in
                      result := [ make_cms cn ms ]
                    else
	              let cnTgts = match tgt with
	                | NonVirtualTarget (_,t) -> [ t ]
	                | ConstrainedVirtualTargets (_,l) -> l
	                | VirtualTargets l -> l
	                | _ -> [] in
	              let cnTgts = List.map retrieve_cn cnTgts in
	              let cmsTgts = List.map (fun cn -> make_cms cn ms) cnTgts in
	              result := cmsTgts @ !result) table in
      !result
      

  method private get_final_method_targets =
    H.fold (fun _ v acc ->
      match v with NonVirtualTarget (FinalMethod, _) -> acc + 1 | _ -> acc) table 0

  method private get_final_class_targets =
    H.fold (fun _ v acc ->
      match v with NonVirtualTarget (FinalClass, _) -> acc + 1 | _ -> acc) table 0

  method private get_private_targets =
    H.fold (fun _ v acc ->
      match v with NonVirtualTarget (PrivateMethod, _) -> acc + 1 | _ -> acc) table 0

  method private get_static_targets =
    H.fold (fun _ v acc ->
      match v with NonVirtualTarget (StaticMethod, _) -> acc + 1 | _ -> acc) table 0

  method private get_empty_targets =
    H.fold (fun _ v acc -> match v with EmptyTarget _ -> acc + 1 | _ -> acc) table 0

  method private get_single_virtual_targets =
    H.fold (fun _ v acc -> match v with VirtualTargets [ i ] -> acc + 1 | _ -> acc) table 0

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      cgdictionary#read_xml (getc "dictionary") ;
      List.iter self#read_xml_edge ((getc "edges")#getTaggedChildren "edge") ;
      List.iter self#read_xml_backedge ((getc "callback-edges")#getTaggedChildren "cb-edge") ;
      pr_debug [ STR "Callgraph edges: " ; INT (H.length table) ; NL ]
    end

  method private get_bottomup_function_list =
    match callgraph_order with
    | Some l -> l
    | _ ->
       let methods = List.filter (fun m -> m#has_bytecode) app#get_methods in
       let _ = pr_debug [ STR "methods: " ; INT (List.length methods) ; NL ] in
       let cmss = List.map (fun m -> m#get_class_method_signature) methods in
       let fnindices = List.map (fun cms -> cms#index) cmss in
       let fnpairs =
         List.concat
           (List.map (fun cms ->
	        let callees = self#get_callees cms#index in
	        List.fold_left (fun acc callee ->
	            if (app#has_method callee) && (app#get_method callee)#has_bytecode then
	              (cms#index,callee#index) :: acc
	            else
	              acc) [] callees) cmss) in
       let (orderedList,stats,cycle) = create_ordering fnindices fnpairs in
       let _ = chlog#add "callgraph order"
	                 (LBLOCK [ pretty_print_list stats (fun s -> INT s) "[" "; " "]" ;
	                           (if cycle then STR " (cycle)" else STR "") ]) in
       let _ = callgraph_order <- Some orderedList in
       let _ = pr_debug [ STR "Call graph order: " ; INT (List.length orderedList) ; NL ] in
       orderedList

  method bottomup_iter (f:method_info_int -> unit) =
    let orderedList = self#get_bottomup_function_list in
    let orderedFunctions = List.map app#get_method_by_index orderedList in
    List.iter f orderedFunctions      
      

  method private read_xml_edge (node:xml_element_int) =
    let geti = node#getIntAttribute in
    let tgt = read_xml_target node in
    let cms = geti "ix" in
    let pc = geti "pc" in
    let ms = geti "ms-ix" in
    H.add table (cms,pc,ms) tgt

  method private read_xml_backedge (node:xml_element_int) =
    back_edges#add (node#getIntAttribute "ix")

  method write_xml (node:xml_element_int) =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) table in
    let eeNode = xmlElement "edges" in
    let cbNode = xmlElement "callback-edges" in
    let dnode = xmlElement "dictionary" in
    let append = node#appendChildren in
    let seti key i = if i > 0 then eeNode#setIntAttribute key i in
    let staticTgts = self#get_static_targets in
    let privateTgts = self#get_private_targets in
    let backEdges = List.sort P.compare back_edges#toList in
    begin
      eeNode#appendChildren (List.map (fun ((cms,pc,ms),tgt) ->
	let eNode = xmlElement "edge" in
	let seti = eNode#setIntAttribute in
	begin
	  seti "ix" cms ;
	  seti "pc" pc ;
	  seti "ms-ix" ms ;
	  write_xml_target eNode tgt ;
	  eNode
	end) !l) ;
      cbNode#appendChildren (List.map (fun i ->
	let eNode = xmlElement "cb-edge" in
	let seti = eNode#setIntAttribute in
	begin seti "ix" i ; eNode end) backEdges) ;
      cgdictionary#write_xml dnode ;
      append [ dnode ; eeNode ; cbNode ] ;
      cbNode#setIntAttribute "size" back_edges#size ;
      seti "size" (List.length !l) ;
      seti "final-method" self#get_final_method_targets ;
      seti "final-class" self#get_final_class_targets ;
      seti "private" privateTgts ;
      seti "static" staticTgts ;
      seti "single-virtual" self#get_single_virtual_targets ;
      seti "resolved" (privateTgts + staticTgts) ;
      seti "empty" self#get_empty_targets
    end
    

end

let callgraph_base = new callgraph_base_t

let get_app_callgraph () =
  let make_procname i = new symbol_t ~seqnr:i "procname" in
  let methods = List.filter (fun m -> m#has_bytecode) app#get_methods in
  let cmss = List.map (fun m -> m#get_class_method_signature) methods in
  List.concat (List.map (fun cms ->
    let callerProc = make_procname cms#index in
    let callees = callgraph_base#get_callees cms#index in
    List.fold_left (fun acc callee ->
      if (app#has_method callee) && (app#get_method callee)#has_bytecode then
	let calleeProc = make_procname callee#index in
	(callerProc,calleeProc) :: acc
      else
	acc) [] callees) cmss)
