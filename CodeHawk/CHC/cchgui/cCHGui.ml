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

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* cchlib *)
open CCHBasicTypes
open CCHFileEnvironment
open CCHSettings

(* cchpre *)
open CCHPreFileIO

(* cchgui *)
open CCHFunctionsDisplay
open CCHGuiStats
open CCHGuiUtils
open CCHSystemDisplay
open CCHGuiRequests

let flush_x () = while Glib.Main.iteration false do () done
let delete_event ev = false
let destroy () = GMain.Main.quit ()

let single_target = ref ""

(* ----------------------------------------~--------------------- menu action -- *)

let all_files () = GFile.filter ~name:"All" ~patterns:["*"] ()
let xml_filter () = GFile.filter ~name:"xml files" ~patterns:["*.xml"] ()

let functions_page =
  let label = GMisc.label ~text:"   APPLICATION FUNCTIONS   " () in
  let _ = functions_display#initialize window in
  main_notebook#append_page ~tab_label:label#coerce
    (CCHFunctionsDisplay.functions_display#get_display)#coerce

let read_link_file ():unit =
  let target_files = 
    if !single_target <> "" then [ 0, !single_target ]
    else read_target_files () in
  let fileFunctions = 
  List.map (fun (_,cfileName) ->
    let cfile = get_xml_cfile cfileName in
    let functions = List.fold_left
      (fun acc g -> match g with
        | GFun (vinfo, loc) -> (vinfo.vname , loc.line)::acc
        | _ -> acc) []
    cfile.globals in
    let (total, proven, functions) = 
      List.fold_left (fun (accT, accP, accF) (f, l) ->
        let (fT, fP) = (0, 0) in
        (accT+fT, accP+fP, (f, l, (fT, fP))::accF))
      (0, 0, []) functions in
    ((cfileName, (total, proven)), functions)
  ) target_files in
  let nFiles = List.length fileFunctions in
  let nFunctions =
    List.fold_left (fun acc (_,l) -> acc + (List.length l)) 0 fileFunctions in
  begin
    log_message "reading files and functions ..." ;
    functions_display#set_model fileFunctions ;
    write_to_system_display
      "target-files"
      ("listed " ^ (string_of_int nFiles) ^ " files with "
       ^ (string_of_int nFunctions) ^ " functions" )
  end

let open_file_dialog () =
  let dialog =
    GWindow.file_chooser_dialog
      ~action:`OPEN
      ~title:"Open File"
      ~parent:window
      () in
  begin
    dialog#add_button_stock `CANCEL `CANCEL ;
    dialog#add_select_button_stock `OPEN `OPEN ;
    dialog#add_filter (all_files ()) ;
    dialog#add_filter (xml_filter ()) ;
    (match dialog#run () with
    | `OPEN -> 
	begin
	  match dialog#filename with
	    Some name -> 
	      begin
		filename := name ;
		write_message ("Selected file " ^ name)
	      end
	  | _ -> write_message "No file selected"
	end
    | `CANCEL 
    | `DELETE_EVENT -> write_message "No file selected") ;
    dialog#destroy () ;
    if !filename = "" then ()
    else
      begin
	    ignore (read_link_file ())
      end
  end

let quit_analyzer () = destroy ()

let show_summary_stats () =
  write_to_system_display "summary_stats" (get_app_summary_stats())

let show_return_value_assumptions () =
  write_to_system_display "rv_assumptions" (get_rv_assumptions_stats ())

let show_global_assumptions () =
  write_to_system_display "global-assumptions" (get_global_assumptions_stats ())

let show_global_assignments () =
  write_to_system_display "global-assignments" (get_global_assignment_stats ())

let show_field_assignments () =
  write_to_system_display "field_assignments" (get_field_assignment_stats ())

let view_activity_log () =
  begin
    write_message "Retrieving activity log ...... " ;
    write_to_system_display_pp "ActivityLog" guilog#toPretty ;
    write_message "Displayed activity log" ;
    goto_system_page ()
  end

let view_analyzer_log () =
  begin
    write_message "Retrieving analyzer log ...... " ;
    write_to_system_display_pp "CHLog" chlog#toPretty ;
    write_message "Displayed analyzer log" ;
    goto_system_page ()
  end

let view_error_log () =
  begin
    write_message "Retrieving error log ...... " ;
    write_to_system_display_pp "ErrorLog" ch_error_log#toPretty ;
    write_message "Displayed error log" ;
    goto_system_page ()
  end

let show_missing_summaries () = display_missing_summaries ()

(* ----------------------------------------~------------------- main menu bar -- *)
let set_menu () =
  let create_menu label =
    let item = GMenu.menu_item ~label:label ~packing:menubar#append () in
    GMenu.menu ~packing:item#set_submenu () in
  let file_menu = create_menu "File" in
  let file_entries = [
    `I ("Open", open_file_dialog) ;
    `I ("Save system display", save_system_display_contents) ;
    `S ;
    `I ("Quit", quit_analyzer)
  ] in
  let _ = GToolbox.build_menu file_menu ~entries:file_entries in

  let view_menu = create_menu "View" in
  let view_entries = [
      `I ("Missing summaries", show_missing_summaries) ;
      `I ("Postcondition requests", display_postcondition_requests) ;
      `I ("Diagnostic reports", display_diagnostic_reports) ;
      `I ("Investigations",display_investigations) ;
      `S ;
      `I ("Activity log", view_activity_log) ;
      `I ("Analyzer log", view_analyzer_log) ;
      `I ("Error log", view_error_log)
    ] in
  let _ = GToolbox.build_menu view_menu ~entries:view_entries in

  let stat_menu = create_menu "Statistics" in
  let stat_entries = [
    `I ("Application", (callback_print_exn show_summary_stats)) ;
    `S ;
    `I ("Return value assumptions", (callback_print_exn show_return_value_assumptions)) ;
    `I ("Global variable assumptions", (callback_print_exn show_global_assumptions)) ;
    `I ("Global assignments", (callback_print_exn show_global_assignments)) ;
    `I ("Field assignments", (callback_print_exn show_field_assignments)) 
  ] in
  let _ = GToolbox.build_menu stat_menu ~entries:stat_entries in
  ()

let string_printer = CHPrettyUtil.string_printer

let run_gui analysisdir singlefile =
  let _ = single_target := singlefile in
  let linkFile = get_target_files_name () in
  let _ = read_link_file () in 
  let _ = window#event#connect#delete ~callback:delete_event in
  let _ = window#connect#destroy ~callback:destroy in
  begin 
    set_menu () ; 
    window#show () ;
    write_to_system_display "summary_stats" (get_app_summary_stats()) ; 
    (if linkFile = "" then write_message "Please load a file using Open"
    else
      log_message ("Analysis directory: " ^ analysisdir)) ;
    GMain.Main.main () 
  end
  
