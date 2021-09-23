(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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

(* gtk *)
open Gobject.Data

(* chlib *)
open CHPretty
open CHBounds
open CHIntervals

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHLibTypes
open BCHLocationInvariant
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo

(* bchlibx86 *)
open BCHAssemblyInstructionAnnotations
open BCHAssemblyBlock
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHDisassemble
open BCHFunctionInfo
open BCHLibx86Types
open BCHLoopStructure
open BCHIFSystem
open BCHTranslateToCHIF

(* bchanalyze *)
open BCHFileIO

(* bchgui *)
open BCHSystemDisplay
open BCHDllFunctionsDisplay
open BCHCanvasUtil
open BCHStateDialogs
open BCHStackFrame


let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p

let get_floca faddr iaddr =
  let loc = ctxt_string_to_location faddr iaddr in
  get_floc loc


class type functions_display_int =
object
  method initialize: GWindow.window -> unit
  method reset: unit
  method set_model: assembly_function_int list -> unit

  method get_display: GPack.table
end

let createCfg (index:dw_index_t) () = canvas#control_flow_graph_to_dot index

let get_function_name (address:doubleword_int) =
  if functions_data#has_function_name address then
    (functions_data#get_function address)#get_function_name
  else
    address#to_fixed_length_hex_string

let show_info_dialog (title:string) (pp:pretty_t) (parent:GWindow.window) =
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:true
      ~show:true
      ~width:400
      ~height:340 () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let view = GText.view () in
  let _ = view#set_pixels_above_lines 5 in
  let _ = view#set_left_margin 10 in
  let buffer = view#buffer in
  let iter = buffer#get_iter `START in
  let _ = buffer#insert ~iter (pp_str pp) in
  let _ = window#add view#coerce in
  let _ = dialog#add_button_stock `OK `OK in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let get_assignments_info () =  STR "TBD"   (* FIX *)
(*
  let numRegisterAssignments = assignment#count_register_assigns in
  let numMemoryAssignments = assignment#count_memory_assigns in
  let numUnknownMemoryAssignments = assignment#count_unknown_memory_assigns in
  let numUnknownBaseAssignments = assignment#count_unknown_base_memory_assigns in
  let numUnknownOffsetAssignments = assignment#count_unknown_offset_memory_assigns in
  let unknownMemoryAssigns = assignment#get_unknown_memory_assigns in
  let unknownMemoryAssignsPP =
    List.fold_left (fun functionsAcc (functionAddress, assigns) ->
      let functionTmpAssignsPP = 
	List.fold_left (fun functionAcc (loc,operand) ->
	  LBLOCK [ functionAcc ; NL ; INDENT (3, LBLOCK [ loc#i#toPretty ; STR "  " ; operand#toPretty ]) ])
	  (functionAddress#toPretty) assigns in
      LBLOCK [ functionsAcc ; NL ; functionTmpAssignsPP ]) (STR "") unknownMemoryAssigns in
  LBLOCK [
    STR "Unknown writes       : " ; INT numUnknownMemoryAssignments ; 
    STR " (out of " ; INT numMemoryAssignments ;  STR " memory assignments)" ; NL ; 
    STR "Unknown base writes  : " ; INT numUnknownBaseAssignments ; NL ;
    STR "Unknown offset writes: " ; INT numUnknownOffsetAssignments ; NL ; NL ;
    STR "Register assignments: " ; INT numRegisterAssignments ; NL ; NL ; unknownMemoryAssignsPP ]
*)

class functions_display_t:functions_display_int =
object (self)

  (* (display, (store, indexColumn, nameColumn, blockSizeColumn, instrSizeColumn), view)  *)
  val mutable display_data =  None 

  val mutable function_view_contents = None
  val mutable opt_dll_functions_page_activation = None
  val mutable opt_parent = None
  val mutable current_function = wordzero#index
  val mutable analysis_repeats = 5
  val mutable history = [] 
  val mutable future = []
  val iters = Hashtbl.create 13

  method reset =
    begin
      self#set_model [] ;
      current_function <- wordzero#index ;
      Hashtbl.clear iters ;
      (match function_view_contents with Some w -> self#get_display#remove w | _ -> () ) ;
      function_view_contents <- None ;
    end

  method private goback () =
    match history with
    | [] -> ()
    | h :: tl ->
      begin
	history <- tl ;
	future <- current_function :: future ;
	self#show_function h
      end

  method private gofwd () =
    match future with
    | [] -> ()
    | h :: tl ->
      begin
	history <- current_function :: history ;
	future <- tl ;
	self#show_function h
      end

  method get_display = match display_data with Some (display,_,_) -> display | _->
    raise (BCH_failure (STR "get_display: functions_display has not been initialized"))

  method private get_view = match display_data with Some (_,_,view) -> view | _ ->
    raise (BCH_failure (STR "get_view: functions_display has not been initialized"))

  method private get_parent = match opt_parent with Some parent -> parent | _ ->
    raise (BCH_failure (STR "get_parent: functions_display has not been initialized"))

  method private get_model = match display_data with Some (_,model,_) -> model | _ ->
    raise (BCH_failure (STR "get_model: functions_display has not been initialized"))

  method private check_current_function =
    if (index_to_doubleword current_function)#equal wordzero  then 
      begin
	write_message "No function selected. Please select a function" ;
	false
      end
    else
      true

  method private get_current_function_name =
    let faddr = (assembly_functions#get_function current_function)#get_address in
    get_function_name faddr

  method private get_dll_functions_page_activation =
    match opt_dll_functions_page_activation with Some n -> n | _ ->
      raise (BCH_failure (STR "get_main_notebook: functions_display has not been initialize"))

  method private get_iter (index:int) = Hashtbl.find iters index

  method private createCfg () = 
    if self#check_current_function then
      begin
	write_message ("Creating control flow graph for " ^ self#get_current_function_name ^ " .......") ;
	canvas#control_flow_graph_to_dot current_function ;
	write_message ("Created control flow graph for " ^ self#get_current_function_name)
      end

  method private createAnnotatedCfg () =
    if self#check_current_function then 
      begin
	write_message ("Creating decorated control flow graph for " ^ 
			  self#get_current_function_name ^ " .......") ;
	canvas#annotated_control_flow_graph_to_dot current_function ;
	write_message ("Created decorated control flow graph for " ^  
			  self#get_current_function_name) ;
    end

  method private create_sub_call_graph () = 
    if self#check_current_function then
      begin
	write_message ("Creating descendant call graph for " ^ 
			  self#get_current_function_name ^ " .......") ;
	canvas#sub_call_graph_to_dot current_function ;
	write_message ("Created descendant call graph for " ^ 
			  self#get_current_function_name)      
      end

  method private create_rv_sub_call_graph () =
    if self#check_current_function then
      try
	begin
	  write_message ("Creating ascendant call graph for " ^
			    self#get_current_function_name ^ " .......") ;
	  canvas#sub_rv_call_graph_to_dot current_function ;
	  write_message ("Created ascendant call graph for " ^ 
			    self#get_current_function_name)
	end
      with CHCommon.CHFailure p ->
	pr_debug [ STR "Unable to show reverse call graph: "  ; p ; NL ]
	
  method private show_chif () = 
    if self#check_current_function then show_chif_dialog current_function self#get_parent

  method private load_more_functions (faddrs:doubleword_int list) =
    let loads = List.fold_left (fun acc faddr ->
      if add_function_listed faddr#to_hex_string then faddr :: acc else acc) [] faddrs in
    match loads with
    | [] -> ()
    | _ ->
      begin
	List.iter (fun faddr ->
	  begin
	    translate_assembly_function_by_address faddr ;
	    record_cfg_info faddr
	  end) loads ;
	self#set_model
	  (List.map (fun a -> 
	    assembly_functions#get_function_by_address (string_to_doubleword a))
	     (get_functions_listed ())) 
      end


  method private show_callers () = 
    if self#check_current_function then 
      show_callers_dialog current_function self#load_more_functions self#get_parent

  method private show_callees () = 
    try
      if self#check_current_function then 
	show_callees_dialog current_function self#load_more_functions self#get_parent
    with
      BCH_failure p ->
	pr_debug [ STR "Failure in show_callees call: " ; p ; NL ]

  method private show_dll_calls () =
    try
      if self#check_current_function then 
	show_dll_calls_dialog current_function self#get_parent
    with
      BCH_failure p ->
	pr_debug [ STR "Failure in show_dll_calls: " ; p ; NL ]

  method private show_types () =
    try
      if self#check_current_function then
	show_types_dialog current_function self#get_parent
    with
      BCH_failure p ->
	pr_debug [ STR "Failure in show types: " ; p ; NL ]

  method private show_gvars () =
    if self#check_current_function then show_gvars_dialog current_function self#get_parent
	
  method private generate_valuesets () = ()

  method private generate_linear_equalities () = ()

  method private translate_and_analyze (n:int) () = 
    if self#check_current_function then self#show_function current_function
(*    let _ = interrupt_handler#reset in
    try
      if self#check_current_function then
	begin
	  for i = 1 to n do
	    try
	      let _ = if check_interrupt () then raise RequestInterrupt in
	      let _ = if check_skip () then raise RequestSkip in
	      let f = assembly_functions#get_function current_function in
	      let function_address = f#get_address in
	      let proc = chif_system#get_procedure_by_address function_address in
	      begin
		write_message ("Translating " ^ (get_function_name function_address) ^ 
				  " (" ^ (string_of_int i) ^ ") .......") ;
		BCHTranslateToCHIF.translate_assembly_function_by_address f#get_address ;
		function_translation_status#record_translation function_address ; 
		write_message ("Analyzing " ^ (get_function_name function_address) ^ 
				  " (" ^ (string_of_int i) ^ ") .......") ;
		analyze_procedure proc chif_system#get_system ;
		function_translation_status#record_analysis function_address ;
		reset_stack_frame function_address ;
		(* FIX
			BCHDisassemble.resolve_indirect_jumps f ;
			BCHDisassemble.resolve_indirect_calls f ;
		*)
		set_progress_bar i n
	      end
	    with
	      RequestSkip ->
		let address = (assembly_functions#get_function current_function)#get_address in
		begin
		  chlog#add "skip" (LBLOCK [ STR "Function translation/analysis was interrupted: " ; 
					     address#toPretty ]) ;
		  interrupt_handler#clear_skip
		end			 
	  done;
	  annotation_table#reset ;
	  write_message ("Analyzed " ^ self#get_current_function_name) ;
	  self#show_function current_function ;
	  reset_progress_bar ()
	end
    with
      RequestInterrupt | RequestSkip ->
	let address = (assembly_functions#get_function current_function)#get_address in
	begin
	  chlog#add "skip" (LBLOCK [ STR "Function translation/analysis was interrupted: " ; address#toPretty ]) ;
	  interrupt_handler#reset ;
	  reset_progress_bar ()
	end
*)
  method private show_function_metrics () =
    if self#check_current_function then 
      show_function_metrics_dialog current_function self#get_parent

  method private show_register_state_dialog () = 
    if self#check_current_function then 
      show_register_state_dialog current_function self#get_parent

  method private show_summary_dialog () =
    if self#check_current_function then
      show_summary_dialog current_function self#get_parent

  method private show_stack_state_dialog () =
    if self#check_current_function then 
      show_stack_state_dialog current_function self#get_parent

  method private show_reg_stack_state_dialog () = 
    if self#check_current_function then 
      show_reg_stack_state_dialog current_function self#get_parent 

  method private show_reg_stack_type_dialog () = ()

  method private show_stack_frame_dialog () = ()
  (*
    if self#check_current_function then 
      let stack_frame = get_stack_frame current_function in
      stack_frame#display self#get_parent
   *)
  method initialize (parent:GWindow.window) =
    (* let _ = opt_dll_functions_page_activation <- Some dll_functions_page_activation in *)
    let _ = opt_parent <- Some parent in
    let display = GPack.table ~row_spacings:5 ~col_spacings:5 ~columns:2 ~rows:2 () in
    let scroll = GBin.scrolled_window ~width:200
      ~packing:(display#attach ~left:0 ~top:1 ~expand:`Y)
      ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC () in
    let buttonBox = 
      let vbox = GPack.vbox ~homogeneous:false 
	~packing:(display#attach ~left:0 ~right:2 ~top:0 ~expand:`X) () in
      GPack.button_box `HORIZONTAL ~layout:`START ~height:50 ~packing:vbox#pack () in

    let backButton = GButton.button ~packing:buttonBox#add () in
    let _ = GMisc.image ~stock:`GO_BACK ~icon_size:`BUTTON ~packing:backButton#add () in
    let _ = backButton#connect#clicked ~callback:self#goback in
    let _ = backButton#misc#set_tooltip_text "go back" in

    let fwdButton = GButton.button ~packing:buttonBox#add () in
    let _ = GMisc.image ~stock:`GO_FORWARD ~icon_size:`BUTTON ~packing:fwdButton#add () in
    let _ = fwdButton#connect#clicked ~callback:self#gofwd in
    let _ = fwdButton#misc#set_tooltip_text "go forward" in

    let cfgButton = GButton.button ~label:"CFG" ~packing:buttonBox#add () in
    let _ = cfgButton#connect#clicked ~callback:self#createCfg in
    let _ = cfgButton#misc#set_tooltip_text "show control flow graph (on canvas)" in

    let annotatedCfgButton = GButton.button ~label:"CFG+" ~packing:buttonBox#add () in
    let _ = annotatedCfgButton#connect#clicked ~callback:self#createAnnotatedCfg in
    let _ = annotatedCfgButton#misc#set_tooltip_text 
      "show control flow graph annotated with branch conditions (on canvas)" in

    let callGraphButton = GButton.button ~label:"CG->" ~packing:buttonBox#add () in
    let _ = callGraphButton#connect#clicked ~callback:self#create_sub_call_graph in
    let _ = callGraphButton#misc#set_tooltip_text 
      "show call graph starting from current function (on canvas)" in

    let rvcallGraphButton = GButton.button ~label:"<-CG" ~packing:buttonBox#add () in
    let _ = rvcallGraphButton#connect#clicked ~callback:self#create_rv_sub_call_graph in
    let _  = callGraphButton#misc#set_tooltip_text
      "show reverse call graph starting from current function (on canvas)" in

    let chifButton = GButton.button ~label:"CHIF" ~packing:buttonBox#add () in
    let _ = chifButton#connect#clicked ~callback:self#show_chif in
    let _ = chifButton#misc#set_tooltip_text "show CHIF code" in 
 
    let callersButton = GButton.button ~label:"callers" ~packing:buttonBox#add () in
    let _ = callersButton#connect#clicked ~callback:self#show_callers in
    let _ = callersButton#misc#set_tooltip_text "list functions that call the current function" in
    let calleesButton = GButton.button ~label:"callees" ~packing:buttonBox#add () in
    let _ = calleesButton#connect#clicked ~callback:self#show_callees in
    let _ = calleesButton#misc#set_tooltip_text 
      "list functions that are called by the current function" in
(*
    let dllCallsButton = GButton.button ~label:"dll\ncalls" ~packing:buttonBox#add () in
    let _ = dllCallsButton#connect#clicked ~callback:self#show_dll_calls in
    let _ = dllCallsButton#misc#set_tooltip_text
      "list dll calls with option to do fwd/bwd propation on arguments and return value" in
*)
    let typesButton = GButton.button ~label:"types" ~packing:buttonBox#add () in
    let _ = typesButton#connect#clicked ~callback:self#show_types in
    let _ = typesButton#misc#set_tooltip_text "show variable types" in
(*
    let gvarsButton = GButton.button ~label:"global\nvars" ~packing:buttonBox#add () in
    let _ = gvarsButton#connect#clicked ~callback:self#show_gvars in
    let _ = gvarsButton#misc#set_tooltip_text 
      "show reading of and writing to global variables" in
*)
(*    let analyzeButton = GButton.button ~packing:buttonBox#add () in
    let _ = GMisc.image ~stock:`MEDIA_PLAY ~icon_size:`BUTTON ~packing:analyzeButton#add () in
    let _ = analyzeButton#connect#clicked ~callback:(self#translate_and_analyze 1) in
    let _ = analyzeButton#misc#set_tooltip_text 
      "translate and analyze the current function once" in
    let analyzeNButton = GButton.button ~packing:buttonBox#add () in
    let _ = GMisc.image ~stock:`MEDIA_FORWARD ~icon_size:`BUTTON ~packing:analyzeNButton#add () in
    let _ = analyzeNButton#connect#clicked 
      ~callback:(self#translate_and_analyze analysis_repeats) in
    let _ = analyzeNButton#misc#set_tooltip_text
      ("translate and analyze the current function " ^ (string_of_int analysis_repeats) ^
	  " times") in *)
    let infoButton = GButton.button ~packing:buttonBox#add () in
    let _ = GMisc.image ~stock:`INFO ~icon_size:`BUTTON ~packing:infoButton#add () in
    let _ = infoButton#connect#clicked ~callback:self#show_function_metrics in
    let _ = infoButton#misc#set_tooltip_text "show translation and analysis information" in

    let summaryButton = GButton.button ~label:"summary" ~packing:buttonBox#add () in
    let _ = summaryButton#connect#clicked ~callback:self#show_summary_dialog in
    let _ = summaryButton#misc#set_tooltip_text "show function summary" in

    let stackFrameButton = GButton.button ~label:"stack\nframe" ~packing:buttonBox#add () in
    let _ = stackFrameButton#connect#clicked ~callback:self#show_stack_frame_dialog in
    let _ = stackFrameButton#misc#set_tooltip_text "show the layout of the stack frame" in

    let registerStateButton = GButton.button ~label:"register\nvalues" 
      ~packing:buttonBox#add () in
    let _ = registerStateButton#connect#clicked ~callback:self#show_register_state_dialog in
    let _ = registerStateButton#misc#set_tooltip_text 
      "show the values of the registers at each location in the function" in

    let stackStateButton = GButton.button ~label:"stack\nvalues" 
      ~packing:buttonBox#add () in
    let _ = stackStateButton#connect#clicked ~callback:self#show_stack_state_dialog in
    let _ = stackStateButton#misc#set_tooltip_text
      "show the values of stack variables at each location in the function" in

    (* -------------------------------------------------------------- model *)
    let columns = new GTree.column_list in
    let indexColumn = columns#add int in
    let nameColumn = columns#add string in
    let blockSizeColumn = columns#add int in
    let instrSizeColumn = columns#add int in
    let store = GTree.list_store columns in
    (* --------------------------------------------------------------- view *)
    let view = GTree.view ~model:store () in
    let selection_changed (model:#GTree.model) selection () =
      match selection#get_selected_rows with
	  [ path ] ->
	    let row = model#get_iter path in
	    let index = model#get ~row ~column:indexColumn in
	    begin
	      (if current_function = (-1) then () else 
		  history <- current_function :: history) ;
	      future <- [] ;
	      self#show_function (int_to_dw_index index)
	    end
	| _ -> () in

    let _ = view#append_column
      (GTree.view_column ~title:"B"
	 ~renderer:(GTree.cell_renderer_text [`XALIGN 1.0 ] , 
		    ["text", blockSizeColumn ]) ()) in
    let _ = view#append_column
      (GTree.view_column ~title:"I"
	 ~renderer:(GTree.cell_renderer_text [`XALIGN 1.0 ] , 
		    ["text", instrSizeColumn ]) ()) in
   let _ = view#append_column
      (GTree.view_column ~title:"function"
	 ~renderer:(GTree.cell_renderer_text [] , ["text", nameColumn ])  () ) in
    let _ = view#selection#connect#changed 
      ~callback:(selection_changed store view#selection) in 
    let viewport = GBin.viewport ~packing:scroll#add () in
    let _ = viewport#add view#coerce  in
    display_data <- Some (display, (store,indexColumn,nameColumn,blockSizeColumn,
				    instrSizeColumn), view) 

  method set_model (functions:assembly_function_int list) =
    let functions = List.sort (fun f1 f2 -> 
      Stdlib.compare f1#get_address#index f2#get_address#index) functions in
    let (store, indexColumn, nameColumn,blockSizeColumn,instrSizeColumn) =
      self#get_model in
    let view = self#get_view in
    let _ = view#set_model None in
    let _ = store#clear () in
    let fill (index,name,blockSize, instrSize) =
      let iter = store#append () in
      begin 
	Hashtbl.add iters index iter ;
	store#set ~row:iter ~column:indexColumn index ;
	store#set ~row:iter ~column:nameColumn name ;
	store#set ~row:iter ~column:blockSizeColumn blockSize ;
	store#set ~row:iter ~column:instrSizeColumn instrSize
      end in
    let _ = List.iter fill (List.map (fun f -> 
      let faddr = f#get_address in
      let index = dw_index_to_int faddr#index in
      let name = if functions_data#has_function_name faddr then
	  (functions_data#get_function faddr)#get_function_name
	else
	  faddr#to_hex_string in
      let blockCount = f#get_block_count in
      let instrCount = f#get_instruction_count in
      (index,name,blockCount,instrCount)) functions) in
    let _ = view#set_model (Some store#coerce) in
    ()

  method private show_function (index:dw_index_t) =
    try
      let _ = current_function <- index in
      let display = self#get_display in
      let _ = match function_view_contents with Some w -> display#remove w | _ -> () in
      let assemblyWindow = GBin.scrolled_window ~width:1100
	~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:(display#attach ~left:1 ~top:1) () in
      let assemblyVBox = GPack.vbox ~packing:assemblyWindow#add_with_viewport () in
      let f = assembly_functions#get_function index in
      let _ = resolve_indirect_calls f in
      let faddr = f#get_address in
      let fname = get_function_name faddr in
      let _ = if BCHIFSystem.chif_system#has_procedure_by_address faddr then () else
	  BCHTranslateToCHIF.translate_assembly_function f in
      let blocks = f#get_blocks in
      let _ = write_message ("Preparing function " ^ fname ^ " .......") in
      let _ = List.iter (fun b -> self#show_block faddr b assemblyVBox) blocks in
      let _ = write_message ("Displaying function " ^ fname) in
      function_view_contents <- Some assemblyWindow#coerce
    with
      BCH_failure p ->
	pr_debug [ STR "Failure in show_function: " ; p ; NL ]

  method private show_block
                   (faddr:doubleword_int) (block:assembly_block_int) (vbox:GPack.box) = ()
  (*
    try
      let make_esp_label (level:int) (offset:interval_t) =
	let offsetStr =
	  if offset#isTop then "?" else
	    match offset#singleton with
	      Some n -> n#toString
	    | _ -> 
	      let lbStr = match offset#getMin#getBound with 
		  MINUS_INF -> "-oo"
		| PLUS_INF  -> "oo"
		| NUMBER n  -> n#toString in
	      let ubStr = match offset#getMax#getBound with
		  MINUS_INF -> "-oo"
		| PLUS_INF  -> "oo"
		| NUMBER n  -> n#toString in
	      lbStr ^ ";" ^ ubStr in
	if level = 0 then 
	  "[" ^ offsetStr ^ "]" 
	else if level = 1 then
	  "[[" ^ offsetStr ^ "]]"
	else
	  "[-[" ^ offsetStr ^ "]-]" in    
      let instructionCount = block#get_instruction_count in
      let assemblyTable = GPack.table 
	~row_spacings:0 ~col_spacings:20 ~columns:4 ~rows:instructionCount () in
      let _ = vbox#pack ~expand:false ~fill:false ~padding:10 assemblyTable#coerce in
      let row = ref 0 in
      
      let _ = block#itera (fun iaddr instr ->
      (match !dwarfLineNumbers with None -> ()
	      | Some dwarfLineNumbers ->
	      let sourceLines = dwarfLineNumbers#get_source_info va in
	      List.iter (fun (file, line) ->
	      (GMisc.label ~xalign:0.1 ~text:(file ^ ": " ^ (string_of_int line)) ~packing:(assemblyTable#attach ~top:(!row) ~left:0 ~right:4) ());
	      row := !row + 1) sourceLines);
	let loc = ctxt_string_to_location faddr iaddr in
	let floc = get_floca faddr iaddr in
	let _ = write_message 
	  (iaddr ^ ": " ^ (string_of_int floc#inv#get_count) ^ " invariants\n") in
	let annotation = create_annotation floc in
	let (level,espOffset) = floc#get_esp_offset in
	let address = GButton.button ~relief:`NONE ~label:iaddr#to_hex_string
	  ~packing:(assemblyTable#attach ~top:(!row) ~left:0) () in
	let _ = address#event#connect#button_press 
	  ~callback:(fun event -> show_invariant_dialog loc self#get_parent; true) in 
	let _ = GMisc.label ~xalign:0.5 ~text:(make_esp_label level espOffset)
	  ~packing:(assemblyTable#attach ~top:(!row) ~left:1) () in
	let _ = GMisc.label ~xalign:0.0 ~text:instr#toString
	  ~packing:(assemblyTable#attach ~top:(!row) ~left:2) () in
	let annotation = GMisc.label ~xalign:0.0 ~text:(pp_str annotation#toPretty) 
	  ~packing:(assemblyTable#attach ~top:(!row) ~left:3) () in
        let _ = annotationButton#set_xalign 0.0 in
	     let _ = annotationButton#event#connect#button_press
	     ~callback:(fun event -> self#activate_annotation annotation; true) in
	row := !row + 1) in
      let separator = GMisc.separator `HORIZONTAL () in
      let _ = vbox#pack ~expand:false ~fill:false ~padding:0 separator#coerce in
      ()
    with
      BCH_failure p ->
	pr_debug [ STR "Failure in show block: " ; p ; NL ]
   *)	
  method private activate_annotation (annotation:assembly_instruction_annotation_int) =
    match annotation#get_annotation_type with
      LibraryCall functionName -> 
	begin
	  self#get_dll_functions_page_activation () ;
	  dll_functions_display#select functionName 
	end
    | ApplicationCall functionAddress ->
      let assemblyFunction = assembly_functions#get_function_by_address functionAddress in
      begin
	let view = self#get_view in
	view#selection#select_iter (self#get_iter (dw_index_to_int assemblyFunction#get_address#index))
      end
    | _ -> ()
      
end
  
let functions_display = new functions_display_t

let opt_statically_linked_functions_display = ref None

let make_statically_linked_functions_display (dll_functions_activation:unit -> unit)
    (statically_linked_functions:assembly_function_int list) (parent:GWindow.window) =
  let display = new functions_display_t in
  begin
    display#initialize parent;
    display#set_model statically_linked_functions ;
    opt_statically_linked_functions_display := Some display ;
    display
  end
