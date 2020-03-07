(* =============================================================================
   CodeHawk Java Analyzer
   Author: Cody Schuffelen and Anca Browne and Henny Sipma
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
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI
open JCHAnalysisResults
open JCHTaintOrigin

(* jchstacgui *)
open JCHBCFunctions
open JCHCanvasUtil
open JCHMethodsDisplay
open JCHSystemDisplay

module H = Hashtbl
module P = Pervasives

let pp_str p = string_printer#print p

let quit_analyzer () = JCHSystemDisplay.destroy ()

let delete_event ev = false

let methods_page =
  let label = GMisc.label ~text:"           APPLICATION METHODS               " () in
  let _ = JCHMethodsDisplay.methods_display#initialize window in
  main_notebook#append_page
    ~tab_label:label#coerce
    (JCHMethodsDisplay.methods_display#get_display)#coerce

let about_codehawk () =
  let dialog = 
    GWindow.about_dialog 
      ~show:true
      ~name:"CodeHawk Java Analyzer" 
      ~copyright:"Copyright: Kestrel Technology LLC"
      ~version:"0.8"
      ~comments:("Created on Jan 25, 2020")
      ()
  in
  let _ = dialog#connect#response ~callback:(fun _ -> dialog#destroy ()) in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  ()

let view_log () =
  begin
    write_message "Retrieving log ......." ;
    write_to_system_display_pp "CHLog" CHLogger.chlog#toPretty ;
    write_message "Displayed log" ;
    goto_system_page ()
  end

let view_error_log () =
  begin
    write_message "Retrieving error log ......." ;
    write_to_system_display_pp "CHErrorLog" CHLogger.ch_error_log#toPretty ;
    write_message "Displayed error log" ;
    goto_system_page ()
  end

let show_system_callgraph () =
  begin
    write_message "Constructing system call graph ... " ;
    canvas#callgraph_to_dot true;
    write_message "Displayed system callgraph on canvas"
  end

let show_min_system_callgraph () =
  begin
    write_message "Constructing system call graph without library calls ... " ;
    canvas#callgraph_to_dot false;
    write_message "Displayed system call graph without library calls on canvas"
  end

let get_tainted_loop_info mInfo = "?"

let get_cost_info mInfo =
  let (_,bcf) = bcfunctions#get_bc_function mInfo in
  let cost = bcf#get_total_cost in
  if cost > 0 then
    LBLOCK [ fixed_length_pretty ~alignment:StrRight (INT cost) 5 ; STR "  " ]
  else
    STR "       "

let initial_display_to_pretty () =
  let version_info = "CodeHawk Java Analyzer (STAC): version 0.7 (Feb 6, 2018)" in
  let methods = List.filter (fun m -> m#has_bytecode) app#get_methods in
  let table = Hashtbl.create 13 in
  let _ = List.iter (fun m -> 
    Hashtbl.add table m#get_class_method_signature#class_name#index m) methods in
  let get_methods_analyzed cnI = Hashtbl.find_all table cnI in
  let pp = ref [] in
  let _ = List.iter (fun cInfo ->
    let mInfos = get_methods_analyzed cInfo#get_index in
    match mInfos with
    | [] -> ()
    | _ ->
      begin
	pp := (LBLOCK [ NL ; cInfo#get_class_name#toPretty ; NL ]) :: !pp ;
	List.iter (fun mInfo ->
	  let pTaint = STR (get_tainted_loop_info mInfo) in
	  let pCost = get_cost_info mInfo in
	  pp :=
            (INDENT
               (3, LBLOCK [ pTaint ; pCost ;
			    mInfo#get_class_method_signature#toPretty ; NL ])) :: !pp)
	  mInfos
      end) app#get_classes in
  
  let usagemsg =   
    "\n" ^ (string_repeat "-~" 40) ^
      "\n" ^ version_info ^ 
      "\n" ^ (string_repeat "-~" 40) ^
      "\n\n === CFG option requires graphviz (dot) to be installed === " ^
      "\n\n\n Method details available under the APPLICATION METHODS tab" in
  LBLOCK [ STR usagemsg ; NL ; NL ; LBLOCK (List.rev !pp) ]

let view_initial_display () =
  begin
    write_to_system_display_pp "initial_display" (initial_display_to_pretty ()) ;
    goto_system_page ()
  end

let view_taint_sources () = ()
                          
let view_class_package_names () =
  let classnames = list_class_names () in
  let table = H.create 3 in
  let _ = List.iter (fun cn ->
    let pname = cn#package_name in
    let apname = cn#abbreviated_package_name in
    if H.mem table apname then
      let pnames = H.find table apname in
      if List.mem pname pnames then () else H.replace table apname (pname :: pnames)
    else
      H.add table apname [ pname ]) classnames in
  let lst = ref [] in
  let _ = H.iter (fun apn pns -> lst := (apn,pns) :: !lst) table in
  let lst = List.sort (fun (p1,_) (p2,_) -> P.compare p1 p2) !lst in
  let maxlen = List.fold_left (fun m (apn,_) -> 
    let len = String.length apn in if len > m then len else m) 15 lst in
  let pp = List.map (fun (apn,pns) ->
    LBLOCK [ fixed_length_pretty (STR apn) maxlen ; 
	     pretty_print_list pns (fun n -> STR n) "[ "  ", " " ]" ; NL ]) lst in
  let pp =
    LBLOCK [ fixed_length_pretty (STR "Abbreviation") maxlen ; STR "Packages" ; NL ;
		    LBLOCK pp ] in
  begin
    write_to_system_display_pp "full package names" pp ;
    goto_system_page ()
  end
		    
let view_jump_conditions () =
  let minfos = app#get_methods in
  let table = H.create 3 in
  let _ = List.iter (fun minfo ->
    if minfo#has_bytecode then
      try
	let (_,bcfunction) = bcfunctions#get_bc_function minfo in 
	let conditions = bcfunction#get_conditions in
	List.iter (fun (pc,c) ->
	  if H.mem table c then
	    H.replace table c ((minfo#get_index,pc) :: (H.find table c))
	  else
	    H.add table c [ (minfo#get_index,pc) ]) conditions
      with _ -> ()) minfos in
  let lst = ref [] in
  let _ = H.iter (fun c d -> lst := (c,d) :: !lst) table in
  let _ = pr_debug [ STR "Found " ; INT (List.length !lst) ; STR " conditions" ; NL ] in
  let maxlen = List.fold_left (fun m (c,_) ->
    let len = String.length c in if len > m then len else m) 0 !lst in
  let lst = List.sort (fun (c1,_) (c2,_) -> P.compare c1 c2) !lst in
  let _ = pr_debug [ STR "Found " ; INT (List.length lst) ; STR " conditions" ; NL ] in
  let pp = LBLOCK (List.map (fun (c,sites) ->
    let pSites = 
      if List.length sites < 4 then
	pretty_print_list sites (fun (cmsId,pc) ->
	  let cms = retrieve_cms cmsId in
	  let name = cms#class_name#abbreviated_name ^ "." ^ cms#name in
	  LBLOCK [ STR name ; STR " @ " ; INT pc ]) "[" "; " "]" 
      else
	LBLOCK [ INT (List.length sites) ; STR "x" ] in
    LBLOCK [ fixed_length_pretty (STR c) maxlen ; STR "  " ; pSites ; NL ]) lst) in
  begin
    write_to_system_display_pp "jump conditions" pp ;
    goto_system_page ()
  end

let call_to_pretty (pc,opc,ann) =
  LBLOCK [ INT pc ; STR "  " ; opcode_to_pretty opc ;
           STR " (" ;  ann ; STR ")" ; NL ]

let view_reflective_calls () =
  let minfos = app#get_methods in
  let table = H.create 3 in
  let _ = List.iter (fun minfo ->
    if minfo#has_bytecode then
      try
	let (_,bcfunction) = bcfunctions#get_bc_function minfo in
	let reflectivecalls = bcfunction#get_reflective_calls in
	if List.length reflectivecalls > 0 then
	  let cms = minfo#get_class_method_signature in
	  H.add table (pp_str cms#toPretty) reflectivecalls
      with _ -> ()) minfos in
  let lst = ref [] in
  let _ = H.iter (fun s l -> lst := (s,l) :: !lst) table in
  let lst = List.sort (fun (s1,_) (s2,_) -> P.compare s1 s2) !lst in
  let pp =
    LBLOCK [
        STR "Reflective calls " ; NL ; NL ;
	LBLOCK
          (List.map (fun (cms,calls) ->
	       LBLOCK
                 [ STR cms ; NL ;
		   INDENT
                     (3, LBLOCK (List.map call_to_pretty calls)) ; 
	           NL ]) lst) ] in
  begin
    write_to_system_display_pp "reflective calls" pp ;
    goto_system_page ()
  end

let view_pushpop_calls () =
  let minfos = app#get_methods in
  let table = H.create 3 in
  let _ = List.iter (fun minfo ->
    if minfo#has_bytecode then
      try
	let (_,bcfunction) = bcfunctions#get_bc_function minfo in
	let ppcalls = bcfunction#get_pushpop_calls in
	if List.length ppcalls > 0 then
	  let cms = minfo#get_class_method_signature in
	  H.add table (pp_str cms#toPretty) ppcalls
      with _ -> ()) minfos in
  let lst = ref [] in
  let _ = H.iter (fun s l -> lst := (s,l) :: !lst) table in
  let lst = List.sort (fun (s1,_) (s2,_) -> P.compare s1 s2) !lst in
  let pp =
    LBLOCK [ STR "Calls to push and pop methods " ; NL ; NL ;
	     LBLOCK ( List.map (fun (cms,calls) ->
		          LBLOCK [ STR cms ; NL ;
			           INDENT
                                     (3,
                                      LBLOCK
                                        (List.map call_to_pretty calls)) ; 
	                           NL ]) lst) ] in
  begin
    write_to_system_display_pp "pushpop calls" pp ;
    goto_system_page ()
  end
  
let view_thread_calls () =
  let minfos = app#get_methods in
  let table = H.create 3 in
  let _ = List.iter (fun minfo ->
    if minfo#has_bytecode then
      try
	let (_,bcfunction) = bcfunctions#get_bc_function minfo in
	let ttcalls = bcfunction#get_thread_calls in
	if List.length ttcalls > 0 then
	  let cms = minfo#get_class_method_signature in
	  H.add table (pp_str cms#toPretty) ttcalls
      with _ -> ()) minfos in
  let lst = ref [] in
  let _ = H.iter (fun s l -> lst := (s,l) :: !lst) table in
  let lst = List.sort (fun (s1,_) (s2,_) -> P.compare s1 s2) !lst in
  let pp = LBLOCK [ STR "Calls to thread methods " ; NL ; NL ;
		    LBLOCK ( List.map (fun (cms,calls) ->
		      LBLOCK [ STR cms ; NL ;
			       INDENT (3,
                                       LBLOCK
                                         (List.map call_to_pretty calls)) ;
	     NL ]) lst) ] in
  begin
    write_to_system_display_pp "thread calls" pp ;
    goto_system_page ()
  end

let view_append_calls () =
  let minfos = app#get_methods in
  let table = H.create 3 in
  let _ = List.iter (fun minfo ->
    if minfo#has_bytecode then
      try
	let (_,bcfunction) = bcfunctions#get_bc_function minfo in
	let ppcalls = bcfunction#get_append_calls in
	if List.length ppcalls > 0 then
	  let cms = minfo#get_class_method_signature in
	  H.add table (pp_str cms#toPretty) ppcalls
      with _ -> ()) minfos in
  let lst = ref [] in
  let _ = H.iter (fun s l -> lst := (s,l) :: !lst) table in
  let lst = List.sort (fun (s1,_) (s2,_) -> P.compare s1 s2) !lst in
  let pp = LBLOCK [ STR "Calls to thread methods " ; NL ; NL ;
		    LBLOCK ( List.map (fun (cms,calls) ->
		      LBLOCK [ STR cms ; NL ;
			       INDENT (3, LBLOCK (List.map call_to_pretty calls)) ; 
	     NL ]) lst) ] in
  begin
    write_to_system_display_pp "thread calls" pp ;
    goto_system_page ()
  end

				 
let set_menu () =
  let create_menu label =
    let item = GMenu.menu_item ~label:label ~packing:menubar#append () in
    GMenu.menu ~packing:item#set_submenu () in
  let codehawk_menu = create_menu "CodeHawk" in
  let view_menu = create_menu "View" in
  let graph_menu = create_menu "Graph" in

  let codehawk_entries = [
    `I ("About", about_codehawk) ;
    `I ("Quit", quit_analyzer)
  ] in
  let _ = GToolbox.build_menu codehawk_menu ~entries:codehawk_entries in

  let view_entries = [
    `I ("Initial display", view_initial_display) ;
    `S ;
    `I ("Taint sources", view_taint_sources) ;
    `I ("Package names", view_class_package_names) ;
    `I ("Jump conditions", view_jump_conditions) ;
    `I ("Reflective calls", view_reflective_calls) ;
    `I ("Push/pop calls", view_pushpop_calls) ;
    `I ("Thread calls", view_thread_calls) ;
    `I ("Append calls", view_append_calls) ;
    `S ;
    `I ("Log", view_log) ;
    `I ("Error log", view_error_log)
  ] in
  let _ = GToolbox.build_menu view_menu ~entries:view_entries in  

  let graph_entries = [
    `I ("System callgraph", show_system_callgraph) ;
    `I ("System callgraph - no libcalls", show_min_system_callgraph)
  ] in
  let _ = GToolbox.build_menu graph_menu ~entries:graph_entries in
  ()

let run_gui () =
  let _ = window#event#connect#delete ~callback:delete_event in
  let _ = window#connect#destroy ~callback:destroy in
  begin
    set_menu () ;
    methods_display#set_model ;
    window#show () ;
    write_to_system_display_pp "initial_display" (initial_display_to_pretty ()) ;
    GMain.Main.main ()
  end
