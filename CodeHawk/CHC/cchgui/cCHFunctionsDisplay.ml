(* =============================================================================
   CodeHawk C Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHUtils

(* cchlib *)
open CCHBasicTypes
open CCHFileEnvironment
open CCHUtilities
open CCHSettings

(* cchpre *)
open CCHInvariantFact
open CCHPreFileIO
open CCHProofScaffolding

(* cchgui *)
open CCHApiDialog
open CCHPpoDialog
open CCHSystemDisplay
open CCHGuiUtils
open CCHGuiStats

module H = Hashtbl

let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p
let linesPerPage = 40.0

class type functions_display_int =
object
  method initialize: GWindow.window -> unit
  method reset: unit
  method set_model: ((string * (int * int)) * (string * int * (int * int)) list) list -> unit
  method get_display: GPack.table
end

class functions_display_t:functions_display_int =
object (self)

  (* (display, (store, nameColumn, totalColumn, percentColumn), view) *)
  val mutable display_data = None
  val mutable opt_parent = None
  val mutable current_file = ""
  val mutable current_function = ""
  val iters = Hashtbl.create 13
  val mutable filefunctions = H.create 13

  val mutable function_view_contents = None
  val mutable file_scrolled_window = None

  val source_table = H.create 13
  val mutable file_table = H.create 13
  val mutable lineno_table = H.create 13

  method reset = ()

  method private check_current_file =
    if current_file = "" then
      begin
	write_message "No file selected. Please select a file first" ;
	false
      end
    else
      true

  method private check_current_function =
    if current_function = "" then
      begin
	write_message "No function selected. Please select a function first" ;
	false
      end
    else
      true

  method private get_functions =
    if H.mem filefunctions current_file then H.find filefunctions current_file else []

  method get_display =
    match display_data with
    | Some (display,_,_) -> display
    | _ ->
       raise (CCHFailure
                (STR "get_display: functions_display has not been initialized"))

  method private get_model =
    match display_data with
    | Some (_,model,_) -> model
    | _ ->
       raise (CCHFailure
                (STR "get_model: functions_display has not been initialized"))

  method private get_view =
    match display_data with
    | Some (_,_,view) -> view
    | _ ->
       raise (CCHFailure
                (STR "get_view: functions_display has not been initialized"))

  method private get_parent =
    match opt_parent with
    | Some parent -> parent
    | _ ->
       raise (CCHFailure
                (STR "get_parent: functions_display has not been initialized"))

  method private add_functions 
    (fileList: ((string * (int * int)) * (string * int * (int * int)) list) list) =
    List.iter (fun ((filename,_), fnames) -> 
      H.add file_table filename (List.map (fun f (a,_,_) -> a) fnames)) fileList

  method private show_invariants () = ()
                                    
  method private show_file_precondition_requests () =
    if self#check_current_file then
      show_file_precondition_request_dialog current_file self#get_parent

  method private show_file_postcondition_requests () =
    if self#check_current_file then
      show_file_postcondition_request_dialog current_file self#get_parent

  method private show_global_variables () =
    if self#check_current_file then
      show_global_variables_dialog current_file self#get_parent

  method private show_ppos () =
    if self#check_current_function then 
      show_ppo_dialog source_table current_file current_function self#get_parent

  method private show_ppo_lines () =
    if self#check_current_function then 
      show_ppo_line_dialog source_table current_file current_function self#get_parent

  method private show_ppo_groups () =
    if self#check_current_function then
      show_ppo_group_dialog source_table current_file current_function self#get_parent

  method private show_spos () =
    if self#check_current_function then 
      show_spo_post_dialog current_file current_function self#get_parent

  method private show_spo_lines  () =
    if self#check_current_function then
      show_ppo_line_dialog source_table current_file current_function self#get_parent

  method private show_spo_groups () =
    if self#check_current_function then
      show_ppo_group_dialog source_table current_file current_function self#get_parent

  method private show_function_assumptions () =
    if self#check_current_function then
      show_function_assumptions_dialog current_file current_function self#get_parent

  method private show_function_guarantees () =
    if self#check_current_function then
      show_function_guarantees_dialog current_file current_function self#get_parent

  method private show_function_requests () =
    if self#check_current_function then
      show_function_requests_dialog current_file current_function self#get_parent

  method private show_callers () = ()

  method private show_callees () =
    if self#check_current_function then
      show_callees_dialog current_file current_function self#get_parent

  method private show_variables () =
    if self#check_current_function then
      show_function_variables_dialog current_file current_function self#get_parent

  method initialize (parent:GWindow.window) =
    let _ = opt_parent <- Some parent in
    let cpx = callback_print_exn in
    let display = GPack.table ~row_spacings:5 ~col_spacings:5 ~columns:2 ~rows:2 () in
    let scroll = GBin.scrolled_window ~width:400
      ~packing:(display#attach ~left:0 ~top:1 ~expand:`Y)
      ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC () in
    (* ----------------------------------------------------- button box *)
    let (fileBox,fnBox) =
      let hbox =
        GPack.hbox
          ~homogeneous:false
	  ~packing:(display#attach ~left:0 ~right:2 ~top:0 ~expand:`X)
          () in
      let fileFrame =
        GBin.frame
          ~label:"File"
          ~label_xalign:0.0 
	  ~shadow_type:`ETCHED_OUT
          ~packing:hbox#add
          () in
      let fnFrame =
        GBin.frame
          ~label:"Function"
          ~label_xalign:0.0
	  ~shadow_type:`ETCHED_OUT
          ~packing:hbox#add () in
      (GPack.button_box
         `HORIZONTAL
         ~layout:`START
         ~height:50
         ~packing:fileFrame#add
         (),
       GPack.button_box
         `HORIZONTAL
         ~layout:`START
         ~height:50
         ~packing:fnFrame#add
         ()) in
    (* ----------------------------------------------------- file buttons *)
    let _ =  (* precondition requests *)
      let button =
        GButton.button
          ~label:"precondition\nrequests"
          ~packing:fileBox#add
          () in
      let _ =
        button#connect#clicked
          ~callback:(cpx self#show_file_precondition_requests) in
      () in
    let _ =  (* postcondition requests *)
      let button =
        GButton.button
          ~label:"postcondition\nrequests"
          ~packing:fileBox#add
          () in
      let _ =
        button#connect#clicked
          ~callback:(cpx self#show_file_postcondition_requests) in
      () in
    let _ =  (* global variables *)
      let button =
        GButton.button
          ~label:" global\nvariables"
          ~packing:fileBox#add
          () in
      let _ =
        button#connect#clicked
          ~callback:(cpx self#show_global_variables) in
      () in
    (* ------------------------------------------------------ function buttons *)
    let _ =  (* ppo's *)
      let button =
        GButton.button
          ~label:"PPOs"
          ~packing:fnBox#add
          () in
      let _ = button#connect#clicked ~callback:(cpx self#show_ppos) in
      let _ =
        button#misc#set_tooltip_text
          "show primary proof obligations and their status for the current function" in
      () in
    let _ =  (* ppo's by line *)
      let button =
        GButton.button
          ~label:" PPOs\nby line"
          ~packing:fnBox#add () in
      let _ = button#connect#clicked ~callback:(cpx self#show_ppo_lines) in
      () in
    let _ =  (*  ppo's by predicate *)   
      let button =
        GButton.button
          ~label:"    PPOs\nby predicate"
          ~packing:fnBox#add
          () in
      let _ = button#connect#clicked ~callback:(cpx self#show_ppo_groups) in
      () in
    let _ =  (* spo's *)
      let button =
        GButton.button
          ~label:"SPOs"
          ~packing:fnBox#add
          () in
      let _ = button#connect#clicked ~callback:(cpx self#show_spos) in
      () in
    let _ =  (* assumptions *)
      let button =
        GButton.button
          ~label:"assumptions"
          ~packing:fnBox#add
          () in
      let _ =
        button#connect#clicked
          ~callback:(cpx self#show_function_assumptions) in
      () in
    let _ =  (* guarantees *)
      let button =
        GButton.button
          ~label:"guarantees"
          ~packing:fnBox#add
          () in
      let _ =
        button#connect#clicked
          ~callback:(cpx self#show_function_guarantees) in
      () in
    let _ =  (* requests *)
      let button =
        GButton.button
          ~label:"requests"
          ~packing:fnBox#add
          () in
      let _ =
        button#connect#clicked
          ~callback:(cpx self#show_function_requests) in
      () in
    let _ =  (* callees *)
      let button =
        GButton.button
          ~label:"callees"
          ~packing:fnBox#add
          () in
      let _ = button#connect#clicked ~callback:(cpx self#show_callees) in
      () in
    let _ =  (* variables *)
      let button =
        GButton.button
          ~label:"variables"
          ~packing:fnBox#add
          () in
      let _ = button#connect#clicked ~callback:(cpx self#show_variables) in
      () in
    (* ----------------------------------------------------- model *)
    let columns = new GTree.column_list in
    let nameColumn = columns#add string in
    let totalColumn = columns#add int in
    let percentColumn = columns#add string in
    let store = GTree.tree_store columns in
    (* ------------------------------------------------------ view *)
    let view = GTree.view ~model:store () in
    let selection_changed (model:#GTree.model) selection () =
      let change_display path = 
	if  GTree.Path.get_depth path = 1 then
	  let fileName =
            model#get
              ~row:(model#get_iter path)
              ~column:nameColumn in
	  self#show_file fileName
	else if GTree.Path.get_depth path = 2 then
	  let iter = model#get_iter path in
	  let functionName = model#get ~row:iter ~column:nameColumn in
	  let fileName =
            model#get
              ~row:(Option.get (model#iter_parent iter))
              ~column:nameColumn in
	  self#show_function fileName functionName in
      List.iter change_display selection#get_selected_rows in
    let _ =
      view#append_column
        (GTree.view_column
           ~title:"%Proven"
	   ~renderer:(GTree.cell_renderer_text [] , [ "text", percentColumn ])
           ()) in
    let _ =
      view#append_column
        (GTree.view_column
           ~title:"Ppos"
	   ~renderer:(GTree.cell_renderer_text [`XALIGN 1.0] , [ "text", totalColumn ])
           ()) in
    let _ =
      view#append_column
        (GTree.view_column
           ~title:"Name"
	   ~renderer:(GTree.cell_renderer_text [`XALIGN 0.0] , [ "text", nameColumn ])
           ()) in
    let _ =
      view#selection#connect#changed
        ~callback:(callback_print_exn (selection_changed store view#selection)) in
    let viewport = GBin.viewport ~packing:scroll#add () in
    let _ = viewport#add view#coerce in
    display_data <-
      Some (display,
	    (store, nameColumn, totalColumn, percentColumn),
	    view)

  method set_model
           (fileList:((string * (int * int)) * 
			(string * int * (int * int)) list) list) =
    let _ = self#add_functions fileList in
    let (store, nameColumn,totalColumn,percentColumn) = self#get_model in
    let view = self#get_view in
    let _ = view#set_model None in
    let _ = store#clear () in
    let fill_function fileIter (fData:string * int * (int * int)) =
      let (fName,floc,(fTotal,fProven)) = fData in
      let fPerc = percent_to_string fProven fTotal in
      let fnIter = store#append ~parent:fileIter () in
      begin
    H.add lineno_table fName [] ;
	store#set ~row:fnIter ~column:nameColumn fName ;
	store#set ~row:fnIter ~column:totalColumn fTotal ;
	store#set ~row:fnIter ~column:percentColumn fPerc ;
	H.add iters fName fnIter
      end in
    let fill_file
          (fileData:((string * (int * int)) * (string * int * (int * int)) list)) =
      let ((fileName,(fileTotal,fileProven)),functions) = fileData in
      let filePerc = percent_to_string fileProven fileTotal in
      let fileIter = store#append () in
      let temp = List.map (fun (fname, floc, _) -> (fname, floc)) functions in
      let _ = H.add lineno_table fileName temp in
      begin
	store#set ~row:fileIter ~column:nameColumn fileName ;
	store#set ~row:fileIter ~column:totalColumn fileTotal ;
	store#set ~row:fileIter ~column:percentColumn filePerc ;
	List.iter (fill_function fileIter) functions
      end in
    let _ = List.iter fill_file fileList in
    let _ = List.iter (fun ((filename,_),l) ->
      H.add filefunctions filename (List.map (fun (fname,_,_) -> fname) l)) fileList in
    let _ = view#set_model (Some store#coerce) in
    ()

  method private update_model (cfilename:string) =
    let (store, nameColumn, totalColumn, percentColumn) = self#get_model in
    let view = self#get_view in
    let first_iter = match store#get_iter_first with
      | Some tree_iter -> tree_iter 
      | None -> raise (CCHFailure (LBLOCK [ STR "No root found" ; NL ])) in
    let get_name tree_iter = (store#get ~row:tree_iter ~column:nameColumn) in
    let get_total tree_iter = (store#get ~row:tree_iter ~column:totalColumn) in
    let has_next tree_iter = store#iter_next tree_iter in
    let rec find_node_with_name tree_iter name =
      let node_name = get_name tree_iter in
      if String.equal name node_name 
      then tree_iter 
      else 
        (if has_next tree_iter
        then find_node_with_name tree_iter name
        else 
          raise (CCHFailure (LBLOCK [ STR "Could not find file with name" ; STR name ; NL ]))) in
    let get_first_child tree_iter =
      (if store#iter_has_child tree_iter
      then
        let first_child = store#iter_children (Some tree_iter) in first_child
      else
        raise (CCHFailure (LBLOCK [ STR "Node has no children" ; NL ]))) in 
    let fill_function fnIter =
      let fName = get_name fnIter in
      let (fTotal, fProven) = read_primary_proof_stats fName in
      let fPerc = percent_to_string fProven fTotal in
      let _ = begin
        store#set ~row:fnIter ~column:totalColumn fTotal ;
        store#set ~row:fnIter ~column:percentColumn fPerc
        (* H.replace iters fName fnIter *)
      end in
      (fTotal, fProven) in
    let rec fill_functions fnIter =
      let (total, proven) = fill_function fnIter in
      if has_next fnIter 
      then (let (acc_total, acc_proven) = fill_functions fnIter in
        (acc_total + total, acc_proven + proven))
      else
        (total, proven) in    
    let fill_file (cfilename:string) =
      let fileIter = find_node_with_name first_iter cfilename in
      let prevTotal = get_total fileIter in
      if prevTotal == 0 
      then (
        let fnIter = get_first_child fileIter in
        let (fileTotal, fileProven) = fill_functions fnIter in
        let filePerc = percent_to_string fileProven fileTotal in
        begin
          store#set ~row:fileIter ~column:totalColumn fileTotal ;
          store#set ~row:fileIter ~column:percentColumn filePerc
        end ) 
       in
    let _ = fill_file cfilename in
    let _ = view#set_model (Some store#coerce) in
    ()

  method private show_function (cfilename:string) (fname:string) =
    let _ = if current_file = cfilename then () else self#show_file cfilename in
    let function_list = H.find lineno_table cfilename in
    let (_, lineNo) = List.find (fun (x, l) -> String.equal fname x) function_list in
    let _ = system_settings#set_cfilename cfilename in
    let _ = current_function <- fname in
    let pageOffset = (float_of_int lineNo) /. linesPerPage in
    let fileWindow = Option.get file_scrolled_window in
    let _ = fileWindow#vadjustment#set_value (fileWindow#vadjustment#page_size *. pageOffset) in
    ()
    
  method private show_file (name:string) = 
    let _ = current_file <- name in
    let _ = pr_debug [ STR "Load file " ;  STR name ; NL ] in
    let _ = current_function <- "" in
    let _ = system_settings#set_cfilename name in
    let _ = proof_scaffolding#reset in
    let _ = H.clear source_table in
    let _ = read_cfile_dictionary () in
    let cfile = read_cfile () in
    let _ = CCHFileEnvironment.file_environment#initialize cfile in
    let _ = read_cfile_context () in
    let _ = read_cfile_predicate_dictionary () in
    let _ = read_cfile_interface_dictionary () in
    let _ = read_cfile_assignment_dictionary () in
    let _ = read_cfile_contract () in
    let _ =
      List.iter (fun fn ->
          let fname = fn.vname in
          let fundec = read_function_semantics fname in
          let fdecls = fundec.sdecls in
          begin
            read_proof_files fname fdecls ;
            read_api fname fdecls
          end) file_environment#get_application_functions  in
    let (sourceLines,sourceString) = read_source name in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    let language =
      match language_manager#language "c" with
      | Some l -> l
      | _ -> raise (CCHFailure (LBLOCK [ STR "Not a valid language name" ])) in
    let sourceBuffer =
      GSourceView2.source_buffer
        ~language
        ~text:sourceString () in
    let display = self#get_display in
    let  _ =
      match function_view_contents with
      | Some w -> display#remove w
      | _ -> () in
    let fileWindow =
      GBin.scrolled_window
        ~width:1100
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:(display#attach ~left:1 ~top:1)
        () in
    let _ = file_scrolled_window <- Some fileWindow in
    let _ =
      GSourceView2.source_view
        ~show:true
        ~show_line_numbers:true
        ~source_buffer:sourceBuffer
        ~packing:(fileWindow#add_with_viewport)
        () in
    let row = ref 1 in
    let _ = List.iter (fun line ->
      let _ = H.add source_table !row line in
	row := !row + 1) sourceLines in
    let _ = self#update_model name in
    let _ = write_message ("Viewing analysis results for file " ^ name) in
    function_view_contents <- Some fileWindow#coerce

end

let functions_display = new functions_display_t
