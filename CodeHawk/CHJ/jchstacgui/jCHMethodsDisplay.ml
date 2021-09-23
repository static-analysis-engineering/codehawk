(* =============================================================================
   CodeHawk Java Analyzer
   Author: Cody Schuffelen and Anca Browne and Henny Sipma
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

(* gtk *)
open Gobject.Data

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBcDictionary
open JCHBytecode
open JCHDictionary

(* jchpre *)
open JCHAnnotationsPre
open JCHApplication
open JCHPreAPI
open JCHPreFileIO
open JCHAnalysisResults

(* jchstacgui *)
open JCHBCFunctions
open JCHCanvasUtil
open JCHDialogWindow
open JCHSystemDisplay

module H = Hashtbl


let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p

class type methods_display_int =
object
  method initialize: GWindow.window -> unit
  method reset: unit
  method set_model: unit

  method get_display: GPack.table
end

let get_class_detail (cnId:int) =
  try
    let cn = retrieve_cn cnId in
    let cInfo = app#get_class cn in
    let pSubclasses = 
      match app#get_subclasses cn with
      | [] -> STR ""
      | l -> LBLOCK [ STR "Subclasses: " ; NL ;
		      LBLOCK (List.map (fun cn ->
			LBLOCK [ INDENT (3, cn#toPretty) ; NL ]) l) ] in
    let pMethods = 
      match cInfo#get_methods_defined with
      | [] -> STR ""
      | l ->
         LBLOCK
           [ STR "Methods defined: " ; NL ;
	     LBLOCK
               (List.map (fun m -> 
		    let cms = make_cms cInfo#get_class_name m in
		    let mInfo = app#get_method cms in
		    let isstatic = if mInfo#is_static then " (static)" else "" in
		    let isprivate = if mInfo#is_private then " (private)" else "" in
		    let issynchronized =
                      if mInfo#is_synchronized then 
			" (synchronized)" else "" in
		    let isfinal = if mInfo#is_final then " (final)" else "" in
		    LBLOCK [ INDENT(3, m#toPretty) ; STR isstatic ; STR isprivate ; 
			     STR issynchronized ; STR isfinal ; NL ]) l)] in
    let pFields =
      match cInfo#get_fields_defined with
      | [] -> STR ""
      | l ->
         LBLOCK
           [ STR "Fields defined" ; NL ;
	     LBLOCK (List.map (fun fs ->
			 let cfs = make_cfs cn fs in
			 if app#has_field cfs then
			   let field = app#get_field cfs in
			   let pAccess =
                             fixed_length_pretty 
			       (access_to_pretty field#get_visibility) 10 in
			   let pValue =
                             if field#has_value then
			       LBLOCK [ STR ", value=" ;
				        constant_value_to_pretty field#get_value ]
			     else
			       STR "" in
			   let pStatic =
                             if field#is_static then STR " (static)"
                             else
                               STR "" in
			   let pFinal =
                             if field#is_final then STR " (final)"
                             else
                               STR "" in
			   let pInitialized =
                             if field#is_initialized then
			       STR " (initialized)"
                             else
                               STR "" in
			   LBLOCK [ INDENT(3, LBLOCK [ pAccess ; fs#toPretty ; 
						       pValue ; pStatic ; pFinal ;
						       pInitialized ] ) ; NL ]
			 else
			   LBLOCK [ INDENT (3, LBLOCK [ fs#toPretty ]) ; NL ] ) l) ] in
    let pNative =
      match cInfo#get_native_methods_defined with
      | [] -> STR ""
      | l -> LBLOCK [ STR "Native methods declared" ; NL ;
		      LBLOCK (List.map (fun m ->
			LBLOCK [ INDENT (3, m#toPretty) ; NL ]) l) ] in
    LBLOCK [ cInfo#toPretty ; NL ; pSubclasses ; NL ; NL ; 
	     pFields ; NL ; pMethods ;NL ; pNative ]
  with
    JCH_failure p ->
	LBLOCK [ NL ; STR "An error ocurred: " ; p ; NL ]

class methods_display_t:methods_display_int =
object (self)

  (* display, (store, nameColumn), view *)
  val mutable display_data = None

  val mutable method_view_contents = None
  val mutable opt_parent = None
  val mutable current_method = -1
  val mutable current_class = 0
  val mutable history = []       (* list of cms-id for back button *)
  val mutable future = []        (* list of cms-id for fwd button *)
  val iters = H.create 13

  method reset =
    begin
      opt_parent <- None ;
      current_method <- -1 ;
      H.clear iters ;
      (match method_view_contents with
       | Some w -> self#get_display#remove w | _ -> () ) ;
      method_view_contents <- None ;
    end

  method get_display = match display_data with
    | Some (display,_,_) -> display
    | _ ->
       raise
         (JCH_failure (STR "get_display: methods_display has not been initialized"))

  method private get_view =
    match display_data with
    | Some (_,_,view) -> view
    | _ ->
       raise
         (JCH_failure (STR "get_view: methods_display has not been initialized"))

  method private get_parent =
    match opt_parent with
    | Some parent -> parent
    | _ ->
       raise
         (JCH_failure (STR "get_parent: methods_display has not been initialized"))

  method private get_model =
    match display_data with
    | Some (_,model,_) -> model
    | _ ->
       raise
         (JCH_failure (STR "get_model: methods_display has not been initialized"))

  method private check_current_method =
    if current_method = -1 then
      begin
        write_message "No method selected. Please select a method" ;
        false
      end
    else
      true

  method private get_iter (index:int) = H.find iters index

  method private get_current_method_name = 
    (retrieve_cms current_method)#class_method_signature_string

  method private create_cfg () = 
    if self#check_current_method then
      begin
        write_message
          ("Creating control flow graph for " ^ self#get_current_method_name) ;
        canvas#cfg_to_dot current_method ;
        write_message
          ("Created control flow graph for "
           ^ self#get_current_method_name
           ^ " on canvas") ;
      end

  method private create_annotated_cfg () = 
    if self#check_current_method then
      begin
        write_message
          ("Creating annotated control flow graph for "
           ^ self#get_current_method_name) ;
        canvas#annotated_cfg_to_dot current_method false;
        write_message
          ("Created control flow graph for "
           ^ self#get_current_method_name
           ^ " on canvas") ;
      end

  method private create_cost_cfg () = 
    if self#check_current_method then
      begin
        write_message
          ("Creating control flow graph with costs for "
           ^ self#get_current_method_name) ;
        canvas#annotated_cfg_to_dot current_method true ;
        write_message
          ("Created control flow graph with costs for "
           ^ self#get_current_method_name
           ^ " on canvas") ;
      end

  method private create_call_graph () = 
    if self#check_current_method then
      begin
	write_message
          ("Creating descendant callgraph for " ^
             self#get_current_method_name ^ " ...") ;
	canvas#sub_callgraph_to_dot current_method true ;
	write_message
          ("Created descendant callgraph for " ^
	     self#get_current_method_name)
      end

  method private create_rv_call_graph () =
    if self#check_current_method then
      begin
	write_message
          ("Creating ascendant callgraph for " ^
	     self#get_current_method_name ^ " ...") ;
	canvas#sub_rv_callgraph_to_dot current_method;
      end

  method private create_min_call_graph () = 
    if self#check_current_method then
      begin
	write_message
          ("Creating descendant callgraph without library calls for "
           ^ self#get_current_method_name ^ " ...") ;
	canvas#sub_callgraph_to_dot current_method false ;
      end

  method private create_min_cost_call_graph () =
    if self#check_current_method then
      begin
	write_message
          ("Creating descendant callgraph with cost without library calls for "
           ^ self#get_current_method_name ^ " ...") ;
	canvas#sub_callgraph_to_dot current_method ~show_cost:true false ;
      end
    
  method private show_chif () =
    if self#check_current_method then
      show_chif_dialog current_method self#get_parent

  method private show_callers () =
    try
      if self#check_current_method then
	show_callers_dialog current_method self#get_parent
    with
      JCH_failure p ->
	pr_debug [ STR "Failure in show_callers call: " ; p ; NL ]


  method private show_callees () = 
    try
      if self#check_current_method then
	show_callees_dialog current_method self#get_parent
    with
      JCH_failure p ->
	pr_debug [ STR "Failure in show_callees call: " ; p ; NL ]

  method private show_conditions () =
    try 
      if self#check_current_method then
	show_conditions_dialog current_method self#get_parent
    with
      JCH_failure p ->
	pr_debug [ STR "Failure in show_conditions call: " ; p ; NL ]

  method private show_handlers () =
    if self#check_current_method then 
      show_handlers_dialog current_method self#get_parent

  method private show_variable_table () =
    if self#check_current_method then
      show_variable_table_dialog current_method self#get_parent

      
  method private show_method_info () = ()

  method private show_exceptions excns pc () = ()

  method private show_invariant method_index pc () = 
    show_invariant_dialog method_index pc self#get_parent

  method private goback () =
    match history with
    | [] -> ()
    | h::tl ->
      begin
	history <- tl ;
	future <- current_method :: future ;
	self#show_method_data h
      end

  method private gofwd () =
    match future with
    | [] -> ()
    | h::tl ->
      begin
	history <- current_method :: history ;
	future <- tl ;
	self#show_method_data h
      end

  method private get_history_list =         (* needs to be assigned dynamically *)
    match history with
    | [] -> "no history"
    | l -> String.concat "\n" (List.map (fun id ->
      (retrieve_cms id)#class_method_signature_string) l)

  method private get_future_list =         (* needs to be assigned dynamically *)
    match future with
    | [] -> "no forward items"
    | l -> String.concat "\n" (List.map (fun id ->
      (retrieve_cms id)#class_method_signature_string) l)

  method initialize (parent:GWindow.window) =
    let _ = opt_parent <- Some parent in
    let display =
      GPack.table
        ~row_spacings:5
        ~col_spacings:5
        ~columns:2
        ~rows:2
        () in
    let scroll =
      GBin.scrolled_window
        ~width:200
        ~packing:(display#attach ~left:0 ~top:1 ~expand:`Y)
        ~vpolicy:`AUTOMATIC
        ~hpolicy:`AUTOMATIC
        () in
    let buttonBox =
      let vbox =
        GPack.vbox
          ~homogeneous:false
          ~packing:(display#attach ~left:0 ~right:2 ~top:0 ~expand:`X)
          () in
      GPack.button_box
        `HORIZONTAL
        ~layout:`START
        ~height:50
        ~packing:vbox#pack
        () in
    (* -------------------------------------------------------------- buttons *)

    let backButton = GButton.button ~packing:buttonBox#add () in
    let _ =
      GMisc.image
        ~stock:`GO_BACK
        ~icon_size:`BUTTON
        ~packing:backButton#add
        () in
    let _ = backButton#connect#clicked ~callback:self#goback in
    let _ = backButton#misc#set_tooltip_text "go back" in

    let fwdButton = GButton.button ~packing:buttonBox#add () in
    let _ =
      GMisc.image
        ~stock:`GO_FORWARD
        ~icon_size:`BUTTON
        ~packing:fwdButton#add
        () in
    let _ = fwdButton#connect#clicked ~callback:self#gofwd in
    let _ = fwdButton#misc#set_tooltip_text "go forward" in

    let cfgButton =
      GButton.button ~label:"CFG" ~packing:buttonBox#add () in
    let _ = cfgButton#connect#clicked ~callback:self#create_cfg in
    let _ =
      cfgButton#misc#set_tooltip_text "show control flow graph (on canvas)" in

    let acfgButton =
      GButton.button ~label:"CFG+" ~packing:buttonBox#add () in
    let _ = acfgButton#connect#clicked ~callback:self#create_annotated_cfg in
    let _ =
      acfgButton#misc#set_tooltip_text
        "show annotated control flow graph (on canvas)" in

    let cfgCostButton =
      GButton.button ~label:"CFG+cost" ~packing:buttonBox#add () in
    let _ = cfgCostButton#connect#clicked ~callback:self#create_cost_cfg in
    let _ =
      cfgCostButton#misc#set_tooltip_text
        "show control flow graph with costs (on canvas)" in

    let rvcallGraphButton =
      GButton.button ~label:"<-CG" ~packing:buttonBox#add () in
    let _ =
      rvcallGraphButton#connect#clicked ~callback:(self#create_rv_call_graph) in
    let _ = rvcallGraphButton#misc#set_tooltip_text
      "show reverse call graph starting from the current method (on canvas)" in

    let callGraphButton =
      GButton.button ~label:"CG->" ~packing:buttonBox#add () in
    let _ = callGraphButton#connect#clicked ~callback:(self#create_call_graph) in
    let _ = callGraphButton#misc#set_tooltip_text 
      "show call graph starting from the current method (on canvas)" in

    let callGraphMinButton =
      GButton.button ~label:"minCG->" ~packing:buttonBox#add () in
    let _ =
      callGraphMinButton#connect#clicked ~callback:(self#create_min_call_graph) in
    let _ = callGraphMinButton#misc#set_tooltip_text
      "show call graph without libcalls starting from the current method (on canvas)" in

    let callGraphMinButton =
      GButton.button ~label:"mCG->\n  cost" ~packing:buttonBox#add () in
    let _ =
      callGraphMinButton#connect#clicked ~callback:(self#create_min_cost_call_graph) in
    let _ = callGraphMinButton#misc#set_tooltip_text
      "show call graph with cost without libcalls starting from the current method (on canvas)" in

    let chifButton =
      GButton.button ~label:"CHIF" ~packing:buttonBox#add () in
    let _ = chifButton#connect#clicked ~callback:self#show_chif  in
    let _ = chifButton#misc#set_tooltip_text "show CHIF code" in

    let callersButton =
      GButton.button ~label:"Callers" ~packing:buttonBox#add () in
    let _ = callersButton#connect#clicked ~callback:self#show_callers  in
    let _ = callersButton#misc#set_tooltip_text 
      "list functions that may call the current function" in

    let calleesButton =
      GButton.button ~label:"Callees" ~packing:buttonBox#add () in
    let _ = calleesButton#connect#clicked ~callback:self#show_callees  in
    let _ = calleesButton#misc#set_tooltip_text 
      "list function that may be called by the current function" in

    let conditionsButton =
      GButton.button ~label:"Conds" ~packing:buttonBox#add () in
    let _ = conditionsButton#connect#clicked ~callback:self#show_conditions in
    let _ = conditionsButton#misc#set_tooltip_text "list conditional jump conditions" in

    let handlersButton =
      GButton.button ~label:"Handlers" ~packing:buttonBox#add () in
    let _ = handlersButton#connect#clicked ~callback:self#show_handlers in
    let _ = handlersButton#misc#set_tooltip_text 
      "show exception handlers and their catch" in

    let vartableButton =
      GButton.button ~label:" Var\ntable" ~packing:buttonBox#add () in
    let _ = vartableButton#connect#clicked ~callback:self#show_variable_table in
    let _ = vartableButton#misc#set_tooltip_text "show variable table" in

    (* ------------------------------------------------------------------ model *)
    let columns = new GTree.column_list in
    let nameColumn = columns#add string in
    let indexColumn = columns#add int in
    let store = GTree.tree_store columns in
    (* ------------------------------------------------------------------- view *)
    let view = GTree.view ~model:store () in
    let selection_changed (model:#GTree.model) selection () =
      let change_display path =
        if GTree.Path.get_depth path = 1 then
          let class_index =
            model#get ~row:(model#get_iter path) ~column:indexColumn in
          self#show_class_data class_index
        else if GTree.Path.get_depth path = 2 then
          let method_index =
            model#get ~row:(model#get_iter path) ~column:indexColumn in
          try
	    begin
	      (if current_method = (-1) then
                 ()
               else
                 history <- current_method :: history);
	      future <- [] ;
              self#show_method_data method_index
	    end
          with
          | JCH_failure p ->
             pr_debug [ STR "Error in show method data: " ; p ; NL ] in
      List.iter change_display selection#get_selected_rows in
    let _ =
      view#append_column
        (GTree.view_column
           ~title:"classes"
           ~renderer:(GTree.cell_renderer_text [] , [ "text", nameColumn ])
           () ) in
    let _ =
      view#selection#connect#changed
        ~callback:(selection_changed store view#selection) in
    let viewport = GBin.viewport ~packing:scroll#add () in
    let _ = viewport#add view#coerce in
    display_data <- Some (display, (store,indexColumn,nameColumn), view)

  method set_model  =
    let (store, indexColumn, nameColumn) = self#get_model in
    let view = self#get_view in
    let _ = view#set_model None in
    let _ = store#clear () in
    let methods = List.filter (fun m -> m#has_bytecode) app#get_methods in
    let class_table = H.create 13 in
    let _ =
      List.iter (fun m ->
          H.add class_table m#get_class_method_signature#class_name#index m)
                methods in
    let get_methods_analyzed class_index = H.find_all class_table class_index in
    let fill_method classIter (m:method_info_int) =
      let methodIter = store#append ~parent:classIter () in
      let cms = m#get_class_method_signature in
      let cmsd = cms#class_method_signature_data in
      let descr = cmsd#method_signature#method_signature_data#descriptor in
      let (_,args) = 
	List.fold_left (fun (fst,acc) a -> 
	  if fst then 
	    (false,"(" ^ acc ^ (value_type_to_string a)) 
	  else 
	    (fst,acc ^ "," ^ (value_type_to_string a))) (true,"") descr#arguments in
      let args = match descr#arguments with [] -> args ^ "()" | _ -> args ^ ")" in
      let name =
        cmsd#name ^ args ^
	  (match descr#return_value with
           |Some vt -> ":" ^ (value_type_to_string vt) | _ -> "") in
      begin
        store#set ~row:methodIter ~column:indexColumn m#get_index ;
        store#set ~row:methodIter ~column:nameColumn name;
        H.add iters m#get_index methodIter
      end in
    let fill_class (c:class_info_int) =
      let methods = get_methods_analyzed  c#get_index in
      let methods = List.sort (fun m1 m2 -> 
	Stdlib.compare m1#get_class_method_signature#name 
	  m2#get_class_method_signature#name) methods in
      match methods with
        [] -> ()
      | l ->
        let classIter = store#append () in
        begin
          store#set ~row:classIter ~column:nameColumn c#get_class_name#name ;
          store#set ~row:classIter ~column:indexColumn c#get_index ;
          List.iter (fun m -> fill_method classIter m) l
        end in
    let classes =
      List.sort (fun c1 c2 -> 
          Stdlib.compare
            c1#get_class_name#name c2#get_class_name#name) app#get_classes in
    let _ = List.iter fill_class classes in
    let _ = view#set_model (Some store#coerce) in
    ()

  method private show_class_data class_index = 
    let _ = current_method <- -1 in
    let display = self#get_display in
    let _ = match method_view_contents with
      | Some w -> display#remove w | _ -> () in
    let classWindow =
      GBin.scrolled_window 
        ~width:1100
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:(display#attach ~left:1 ~top:1)
        () in
    let textView =
      GText.view
        ~packing:classWindow#add_with_viewport
        () in
    let _ = textView#set_pixels_above_lines 5 in
    let _ = textView#set_left_margin 10 in
    let _ = textView#misc#modify_font_by_name "Monospace 12" in
    let buffer = textView#buffer in
    let iter = buffer#get_iter `START in
    let _ = buffer#insert ~iter:iter (pp_str (get_class_detail class_index)) in
    method_view_contents <- Some classWindow#coerce
      
  method private show_method_data cmsId =
    let _ = current_method <- cmsId in
    let cms = retrieve_cms cmsId in
    let mInfo = app#get_method cms in
    let (_,bcfunction) = bcfunctions#get_bc_function mInfo in
    let _ =
      if mInfo#has_method_stack_layout_loaded then () else
	try
          let cn = cms#class_name in
          let appdir = get_stac_analysis_app_dir () in
          let cnode = load_class_xml_file appdir cn () in
          match cnode with
          | Some cnode ->
             let d = mk_bcdictionary () in
             let _ = d#read_xml (cnode#getTaggedChild "bcdictionary") in
	     let _ = pr_debug [ STR "Load method bc file " ; NL ] in
	     let bcnode = load_method_xml_file cms "bc" in
	     (match bcnode with
	     | Some node -> mInfo#set_saved_method_stack_layout d node 
	     | _ ->
	        pr_debug [ STR "No method file found for " ; cms#toPretty ; NL ] )
          | _ ->
             pr_debug [ STR "No class file found for " ; cn#toPretty ; NL ]
	with
	| XmlDocumentError (line,col,p)
	| XmlParseError (line,col,p) ->
	   let msg =
             LBLOCK [ STR "Xml error in " ; cms#toPretty ; STR " at " ;
		      STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
	  begin
	    pr_debug [ msg ; NL ] ;
	    raise (JCH_failure msg)
	  end
	| JCH_failure p ->
	  begin
	    pr_debug [ STR "Error: " ; p ; NL ] ;
	    raise (JCH_failure p)
	  end
    in	  
    let _ = write_message_pp mInfo#get_class_method_signature#toPretty in
    let display = self#get_display in
    let _ = match method_view_contents with Some w -> display#remove w | _ -> () in
    let haslines = mInfo#has_line_number_table in
    let getline pc =
      if mInfo#has_line_number pc then
        mInfo#get_line_number pc
      else
        -1 in
    let s = if haslines then 1 else 0 in
    let methodWindow =
      GBin.scrolled_window 
        ~width:1100
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:(display#attach ~left:1 ~top:1)
        () in
    let bytecodeCount = mInfo#get_byte_count in
    let table =
      GPack.table 
        ~row_spacings:0
        ~col_spacings:20
        ~columns:5
        ~rows:(bytecodeCount+1)
        ~packing:methodWindow#add_with_viewport
        () in
    let row = ref 1 in
    let _ =
      if haslines then
        ignore (GMisc.label
                  ~xalign:0.0
                  ~text:"line no" 
	          ~packing:(table#attach ~top:0 ~left:0)
                  ()) in
    let _ =
      GMisc.label
        ~xalign:0.0
        ~text:"offset"
        ~packing:(table#attach ~top:0 ~left:s)
        () in
    let _ =
      GMisc.label
        ~xalign:0.0
        ~text:"loops"
        ~packing:(table#attach ~top:0 ~left:(s+1))
        () in
    let _ =
      GMisc.label
        ~xalign:0.0
        ~text:"instruction"
        ~packing:(table#attach ~top:0 ~left:(s+2))
        () in
    let _ =
      GMisc.label
        ~xalign:0.0
        ~text:"description"
        ~packing:(table#attach ~top:0 ~left:(s+3))
        () in
    let _ =
      try
        List.iter (fun b ->
            let firstpc = b#get_firstpc in
            let lctaint = 0 (* bcfunction#get_loop_taint firstpc *) in
            let looplevels = List.length (bcfunction#get_loop_levels firstpc) in
            let _ =
              b#iter (fun pc opcode ->
	          let _ =
              if haslines then 
	        ignore (GMisc.label
                          ~xalign:0.0 ~text:(string_of_int (getline pc))
		          ~packing:(table#attach ~top:(!row) ~left:0)
                          ()) in
	          let bcIndex =
                    GButton.button
                      ~relief:`NONE
                      ~label:(string_of_int pc)
                      ~packing:(table#attach ~top:(!row) ~left:s)
                      () in
	          let _ =
                    bcIndex#connect#clicked
                      ~callback:(self#show_invariant cmsId pc) in
	          let _ =
                    GMisc.label
                      ~xalign:0.0
                      ~text:(pp_str (opcode_to_pretty opcode))
                      ~packing:(table#attach ~top:(!row) ~left:(s+2))
                      () in
	          let _ =
                    GMisc.label
                      ~xalign:0.0
                      ~text:(pp_str (opcode_annotation mInfo pc opcode))
	              ~packing:(table#attach ~top:(!row) ~left:(s+3))
                      () in
	          let _ =
                    if lctaint > 0 then 
	              let _ =
                        GMisc.label
                          ~xalign:0.0
                          ~text:("TL(" ^ (string_of_int lctaint) ^ ")")
	                  ~packing:(table#attach ~top:(!row) ~left:(s+1))
                          () in
	              () 
	            else 
	              if looplevels > 0 then
	                let _ =
                          GMisc.label
                            ~xalign:0.0
                            ~text:("L(" ^ (string_of_int looplevels) ^ ")")
		            ~packing:(table#attach ~top:(!row) ~left:(s+1))
                            () in
	                () in     
	          row := !row + 1 ) in
            row := !row + 1) bcfunction#get_blocks
      with
      | JCH_failure p ->
         begin
           pr_debug [ STR "Error in iterating over blocks: " ; p ; NL ] ;
           raise (JCH_failure p)
         end in
    method_view_contents <- Some methodWindow#coerce
    
end

let methods_display = new methods_display_t
