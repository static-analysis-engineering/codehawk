(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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
open CHUtils
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHJTerm

(* jchpre *)
open JCHApplication
open JCHPreAPI

open JCHGlobals
open JCHTNode
open JCHTGraph
open JCHPrintUtils

let lib_stub_table = new SymbolCollections.table_t
let dbg = ref false 

let mk_lib_stub stub_name cms:JCHTGraph.taint_graph_t =

  let fsum = function_summary_library#get_method_summary cms in

  let ms = cms#class_method_signature_data#method_signature in
  let msd = ms#descriptor in

  let return_node_opt = ref None in

  let types = 
    if fsum#is_static then
      msd#arguments 
    else
      TBasic Object :: msd#arguments in

  let get_var_type t = 
    match t with 
    | TObject _ 
    | TBasic Object -> SYM_VAR_TYPE
    | _ -> NUM_VAR_TYPE in

  let arg_offset = ref 1 in
  let get_nodes () = 
    let nodes = ref [mk_var_node_pc 0 stub_name exception_var] in
    (match msd#return_value with 
    | Some t -> 
	incr arg_offset ;
	let node =
          mk_var_node_pc
            0
            stub_name
            (make_variable "return" (get_var_type t)) in
        begin
	  return_node_opt := Some node;
	  nodes := node :: !nodes
        end
    | _ -> ()) ;
    let number = ref 0 in
    let rec add_arg arg_types = 
      match arg_types with 
      | t :: rest_arg_types -> 
	  let name = "arg"^(string_of_int !number) in
	  let node =
            mk_var_node_pc 0 stub_name (make_variable name (get_var_type t)) in
          begin
	    nodes := node :: !nodes ;
	    incr number ;
	    add_arg rest_arg_types
          end
      | [] -> () in
    add_arg types ;
    List.rev !nodes in
  
  let nodes = get_nodes () in 
  let sources = new TaintNodeCollections.set_t in

  let add_edges fsum = 
    let fedges = new TaintNodeCollections.table_t in
    let bedges = new TaintNodeCollections.table_t in
    let return_has_taint = ref false in
    let get_node t = 
      match t with
      |	JLocalVar (-1) ->
         begin
	   return_has_taint := true ;
	   Option.get !return_node_opt
         end
      | JLocalVar i -> 
	  (try
	    List.nth nodes (i + !arg_offset) 
	   with _ ->
             begin
               pr__debug [STR "mkLibStub "; stub_name#toPretty; STR " ";
                          cms#toPretty; STR " List.nth failed for "; INT i; NL; 
			  fsum#toPretty; NL] ;
	       raise (JCH_failure (STR "List.nth"))
             end)
      | JObjectFieldValue (cmsix,varindex,cnix,fieldname) ->
         let cn = retrieve_cn cnix in
         let cInfo =
           try
             app#get_class cn
           with
           | JCH_failure p ->
              begin
                ch_error_log#add
                  "class missing from summary"
                  (LBLOCK [ cms#toPretty ; STR ": " ; cn#toPretty ]) ;
                raise
                  (JCH_failure
                     (LBLOCK [ STR "mk_lib_stubs:add_edges: " ; p ]))
              end in
         let fs =
           try
             cInfo#get_field_signature fieldname
           with
           | JCH_failure p ->
              let cms = retrieve_cms cmsix in
              raise (JCH_failure
                       (LBLOCK [ STR "TGraphStubs:mk_lib_stub:add_edges:JObjectFieldValue: " ;
                                 cms#toPretty ; STR ": " ; p ])) in
         let cfs = make_cfs cn fs in
         let _ = pr__debug [ STR "Library field taint: " ; cfs#toPretty ;
                             STR " (using variable only now)" ; NL ] in
         (try
            List.nth nodes (varindex + !arg_offset)
	  with _ ->
            begin
              pr__debug [STR "mkLibStub "; stub_name#toPretty; STR " ";
                         cms#toPretty; STR " List.nth failed for ";
                         INT varindex; NL; 
		         fsum#toPretty; STR " (field value " ; STR fieldname ;
                         STR ")" ; NL] ;
	      raise (JCHBasicTypes.JCH_failure (STR "List.nth: mk_lib_stub"))
            end)
      | JStaticFieldValue (cnix,fieldname) ->
         let cn = retrieve_cn cnix in
         let cInfo =
           try
             app#get_class cn
           with
           | JCH_failure p ->
              begin
                ch_error_log#add
                  "class missing from summary"
                  (LBLOCK [ cms#toPretty ; STR ": " ; cn#toPretty ]) ;
                raise (JCH_failure (LBLOCK [ STR "mk_lib_stubs:add_edges: " ; p ]))
              end in             
         let fs =
           try
             cInfo#get_field_signature fieldname
           with
           | JCH_failure p ->
              raise (JCH_failure
                       (LBLOCK [ STR "TGraphStubs:mk_lib_stub:add_edges:JStaticFieldValue: " ;
                                 p ])) in
         let cfs = make_cfs cn fs in
         let _ =
           pr__debug [ STR "mkLibStub: "; stub_name#toPretty ; STR " " ;
                       cms#toPretty ;  STR ": Static field not yet handled: " ;
                       cfs#toPretty ; NL ] in
         raise (JCH_failure (LBLOCK [ STR "mk_lib_stub: static field not yet handled" ]))
      | JSize t ->
         let _ =
           pr__debug [ STR "mkLibStub: " ; stub_name#toPretty ; STR " " ;
                       cms#toPretty ; STR ": Size term not yet handled: " ;
                       jterm_to_pretty t ; NL ] in
         raise
           (JCH_failure
              (LBLOCK [ STR "mk_lib_stub: size term not yet handled" ]))
      | _ -> 
	 pr__debug [STR "mkLibStub "; stub_name#toPretty; STR " "; cms#toPretty;
                    STR " jterm not found "; NL; fsum#toPretty; NL] ;
	  raise (JCH_failure (STR "node not found")) in
    let add_edge taint_el = 
      match taint_el with 
      |	TTransfer (t1, t2) -> 
	  let nd1 = get_node t1 in
	  let nd2 = get_node t2 in
	  let addE table n1 n2 = 
	    match table#get n1 with 
	    | Some set -> set#add n2 
	    | None -> 
		let set = TaintNodeCollections.set_of_list [n2] in
		table#set n1 set in
          begin
	    addE fedges nd1 nd2 ;
	    addE bedges nd2 nd1
          end
      | TRefEqual (t1,t2) ->
         let _ = pr__debug [ STR "Temporary code for TRefEqual " ; NL ] in
	 let nd1 = get_node t1 in
	 let nd2 = get_node t2 in
	 let addE table n1 n2 = 
	   match table#get n1 with 
	   | Some set -> set#add n2 
	   | None -> 
	      let set = TaintNodeCollections.set_of_list [n2] in
	      table#set n1 set in
	 let refeqnode = mk_ref_equal_node () in
         begin
	   addE fedges nd1 refeqnode ;
	   addE fedges nd2 refeqnode ;
	   addE bedges refeqnode nd1 ;
	   addE bedges refeqnode nd2
         end
      |	TDefPut t -> 
	  let nd = get_node t in
	  sources#add nd;
	  let name =
            new symbol_t ~seqnr:cms#index (cms#name ^ (string_of_int cms#index)) in
	  nd#set_stub_untrusted name;
      |	TRemove t -> () in
    List.iter add_edge fsum#get_taint_elements ;
    (fedges, bedges) in
  let (fedges, bedges) = add_edges fsum in
  let empty_taint_set = new TaintNodeCollections.set_t in

  new taint_graph_t stub_name nodes
    empty_taint_set empty_taint_set empty_taint_set empty_taint_set
    fedges bedges sources

let get_lib_stub stub_name cmsig = 
  match lib_stub_table#get stub_name with 
  | Some stub -> stub
  | None -> 
     let stub = mk_lib_stub stub_name cmsig in
     
     (if !dbg then
        pr__debug [STR "mk_lib_stub "; stub_name#toPretty; STR " ";
                   cmsig#toPretty; NL; stub#toPretty ; NL]);
     
     lib_stub_table#set stub_name stub ;
     stub

let tgraph_to_taint_elements
      (proc_name:symbol_t) (tgraph:taint_graph_t):JCHPreAPI.taint_int =
  let edges = tgraph#get_edges in
  let mk_jterm (cmsix, v, _) =
    let pname = make_procname cmsix in
    if pname#getIndex <> proc_name#getIndex then
      None
    else 
      let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
      let info = jproc_info#get_jvar_info v in
      if JCHSystemUtils.is_return v then Some (JLocalVar (-1)) 
      else 
	match info#get_param_index with 
	| Some i -> Some (JLocalVar i)
	| _ -> None in
  let not_translated = ref false in
  let add_taint_element (node1: taint_node_int) ls (node2: taint_node_int) = 
    match (node2#get_node_type, node1#get_node_type) with 
    | (TN_VAR v2, TN_VAR v1) -> 
	begin
	  try 
	    match (mk_jterm v1, mk_jterm v2) with 
	    | (Some t1, Some t2) -> (TTransfer (t1, t2)) :: ls
	    | _ -> not_translated := true ; ls
	  with _ -> ls (* In case the variable is exception_var *)
	end
    | (TN_VAR v2, TN_FIELD _) -> 
	begin
	  try 
	    not_translated := true ; 
	    match mk_jterm v2 with 
	    | Some t2 ->  (TDefPut t2) :: ls
	    | _ -> ls
	  with _ -> ls
	end
    | (_, _) -> 
	not_translated := true ;
	ls in
  let add_taint_elements ls node1 = 
    let set = Option.get (edges#get node1) in
    List.fold_left (add_taint_element node1) ls set#toList in
  let add_other_taint ls (node : taint_node_int) = 
    match node#get_node_type with 
    | TN_VAR v -> 
	begin
	  try 
	    match mk_jterm v with 
	    | Some t ->  
		let nd =
		  if node#get_untrusted_origins#get_origins = [] then
                    TRemove t
		  else
                    TDefPut t in 
		nd :: ls
	    | _ -> not_translated := true ; ls
	  with _ -> ls 
	end 
    | _ -> ls in
  if !not_translated then 
    pr__debug [STR "tgraph_to_taint_elements could lose precision for ";
               proc_name_pp proc_name; NL] ;

  let nodes = edges#listOfKeys in
  let taint_els = List.fold_left add_taint_elements [] nodes in
  let taint_els = List.fold_left add_other_taint taint_els nodes in
  JCHFunctionSummary.make_taint taint_els 

let get_all_stubs () = lib_stub_table#listOfValues
