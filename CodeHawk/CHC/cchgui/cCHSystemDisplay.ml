(* =============================================================================
   CodeHawk C Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
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

open GMain
open Unix

(* chlib *)
open CHPretty

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil

(* cchlib *)
open CCHBasicTypes
open CCHUtilities
open CCHSettings

(* cchpre *)
open CCHPreFileIO

(* cchgui *)
open CCHInterrupt

module H = Hashtbl


let filename = ref ""
let source_directory = ref ""
let sate_reports = ref []
let xpm_path = ref ""

let flush_x () = while Glib.Main.iteration false do () done
let delete_event ev = false
let destroy () = GMain.Main.quit ()

let string_printer = CHPrettyUtil.string_printer
let p2s = string_printer#print

let guilog = mk_logger ()

let set_xpm_path s = xpm_path := s
let get_xpm_path () = !xpm_path

let window = 
  GWindow.window ~title:"CodeHawk C Analyzer" ~border_width:5
    ~width:1400 ~height:900 ()

let root_table = 
  GPack.table
    ~row_spacings:5 ~col_spacings:5 ~columns:1 ~rows:4 ~packing:window#add ()

let menubar =
  GMenu.menu_bar ~packing:(root_table#attach ~top:0 ~left:0 ~expand:`NONE) ()

(* -------------------------------------------------------- message area -- *)
let message_area =
  GBin.scrolled_window ~height:60
    ~packing:(root_table#attach ~left:0 ~top:1 ~expand:`X) ()

let message_viewport = GBin.viewport ~packing:message_area#add ()
let message_contents:GObj.widget option ref = ref None


let add_message_viewport w =
  let _ =
    match !message_contents with
    | Some m -> message_viewport#remove m
    | _ -> () in
  begin
    message_contents := Some w#coerce;
    message_viewport#add w
  end


let message_box =
  GMisc.label ~text:"message" ~justify:`LEFT ~packing:add_message_viewport ()


let write_message (msg:string) =
  begin
    message_box#set_text msg;
    print_endline (msg ^ "\n");
    flush_x ();
    flush Stdlib.stdout
  end


let write_message_pp (msg:pretty_t) =
  write_message (string_printer#print msg)

(* -------------------------------------------------------- progress bar -- *)

let progress_box =
  GPack.hbox
    ~border_width:10
    ~homogeneous:false
    ~packing:(root_table#attach ~left:0 ~top:2 ~expand:`X ~shrink:`X)
    ()

let skip_button =
  GButton.button ~stock:`GO_FORWARD ~packing:progress_box#pack ()

let progress_bar =
  GRange.progress_bar ~packing:progress_box#add ()

let interrupt_button =
  GButton.button ~stock:`STOP  ~packing:progress_box#pack ()


let reset_progress_bar () = progress_bar#set_fraction 0.0


let set_progress_bar (finished:int) (total:int) =
  let fraction = (float finished) /. (float total) in
  begin
    progress_bar#set_fraction fraction ;
    flush_x () 
  end


let _ = reset_progress_bar ()


let reset_interrupt () = interrupt_handler#reset
  
let reset_skip () = interrupt_handler#clear_skip
  
let check_interrupt () =
  begin flush_x () ; interrupt_handler#is_interrupt_requested end
  
let check_skip () =
  begin flush_x () ; interrupt_handler#is_skip_requested end

let set_interrupt_requested () = interrupt_handler#request_interrupt

let set_skip_requested () = interrupt_handler#request_skip

let _ = skip_button#connect#clicked ~callback:set_skip_requested

let _ = interrupt_button#connect#clicked ~callback:set_interrupt_requested

(* --------------------------------------------------------- main area -- *)
let main_notebook = GPack.notebook ~tab_pos:`TOP 
    ~packing:(root_table#attach ~top:3 ~left:0 ~expand:`BOTH) ()

(* ---------------------------------------------------- system display -- *)

let system_table =
  GPack.table
    ~row_spacings:5
    ~col_spacings:5
    ~columns:1
    ~rows:2
    ()
  
let system_display =
  GBin.scrolled_window
    ~hpolicy:`AUTOMATIC
    ~vpolicy:`AUTOMATIC 
    ~packing:(system_table#attach
                ~left:0
                ~top:0
                ~expand:`BOTH)
    ()
  
let system_contents:GObj.widget option ref = ref None
                                           
let system_contents_string = ref None
                           
let system_contents_name = ref "none"

(* -------------------------------------------------------- search bar -- *)
let search_bar =
  GPack.table
    ~row_spacings:5
    ~col_spacings:5
    ~columns:2
    ~rows:1
    ~packing:(system_table#attach
                 ~left:0
                 ~top:3
                 ~expand:`X)
    ()
  
let search_label =
  GMisc.label
    ~text:"search: "
    ~justify:`LEFT 
    ~packing:(search_bar#attach ~left:0 ~top:0)
    ()
  
let search_entry =
  GEdit.entry
    ~editable:true
    ~visibility:true
    ~show:true
    ~height:30
    ~packing:(search_bar#attach ~left:1 ~top:0)
    ()

(* ------------------------------------------------------ message area -- *)

let log_message_area =
  GBin.scrolled_window
    ~height:100
    ~packing:(root_table#attach ~left:0 ~top:4 ~expand:`X)
    ()

let log_message_viewport = GBin.viewport ~packing:log_message_area#add ()
                         
let log_text_view = GText.view ~packing:log_message_viewport#add ()

let log_message s =
  let buffer = log_text_view#buffer in
  let _ = buffer#insert (s ^ "\n") in
  ()

let log_message_pp (p:pretty_t) = log_message (p2s p)

let _ = log_message "Welcome to KT Advance"
let _ = log_message "---------------------"


(* name: identification of the information being written, used as a suffix in the
         filename when the system display contents are saved to file
   str: string to be displayed
*)
let write_to_system_display (name:string) (str:string) =
  let _ =
    match !system_contents with
    | Some s -> system_display#remove s
    | _ -> () in
  let view = GText.view  () in
  let _ = view#set_pixels_above_lines 5 in
  let _ = view#set_left_margin 10 in
  let _ = view#misc#modify_font_by_name "Monospace 12" in
  let buffer = view#buffer in
  let _ =
    buffer#create_tag
      ~name:"heading" 
      [`WEIGHT `BOLD; `SIZE (15*Pango.scale)] in
  let _ =
    buffer#create_tag
      ~name:"italic"
      [`STYLE `ITALIC] in
  let _ =
    buffer#create_tag
      ~name:"yellow_background"
      [`BACKGROUND "yellow"] in
  let iter = buffer#get_iter `START in
  let _ = buffer#insert ~iter str in
  let contents = view#coerce in
  let tagged_iters = ref [] in
  let add_tag s e = tagged_iters := (s,e) :: !tagged_iters in
  let remove_tags () =
    begin
      List.iter (fun (s,e) ->
          buffer#remove_tag_by_name "yellow_background" s e) !tagged_iters;
      tagged_iters := []
    end in
  let last_search = ref None in
  let _ = search_entry#connect#activate (fun () ->
    let text = search_entry#text in
    let _ = match !last_search with 
      Some (last_text,_) when not (last_text = text) -> remove_tags ()
    | _ -> () in
    let start = match !last_search with
      Some (last_text,last_end) when last_text = text -> last_end
    | _ -> buffer#start_iter in
    match start#forward_search text with
	Some (found_begin, found_end) ->
	  let _ = last_search := Some (text,found_end) in
	  let _ =
            buffer#apply_tag_by_name "yellow_background" found_begin found_end in
	  let _ = add_tag found_begin found_end in
	  let _ = view#scroll_to_iter ~yalign:(0.5) ~use_align:true found_begin in
	  ()
      | _ -> ()) in
  begin 
    system_contents := Some contents ; 
    system_contents_string := Some str ;
    system_contents_name := name ;
    system_display#add contents 
  end

let get_time_string () =
  let t = Unix.gettimeofday () in
  let tm = Unix.localtime t in
  let yr = tm.tm_year + 1900 in
  let mo = tm.tm_mon + 1 in
  let day = tm.tm_mday in
  let hr = tm.tm_hour in
  let min = tm.tm_min in
  (string_of_int yr)
  ^ "_"
  ^ (string_of_int mo)
  ^ "_"
  ^ (string_of_int day)
  ^ "_" ^ (string_of_int hr)
  ^ "_" ^ (string_of_int min)


let output_path = ref ""
let application_name = ref ""

let set_output_path s = output_path := s
let set_application_name s = application_name := s


let save_system_display_contents ():unit =
  match !system_contents_string with 
  | Some s -> 
    (try
       let timeStr = get_time_string () in
       let filename =
         !application_name ^ "_" ^ !system_contents_name
         ^ "_" ^ timeStr ^ ".txt" in
       let filename =
         if !output_path = ""  then
           filename
         else
           !output_path ^  "/" ^ filename in
       begin
	 file_output#saveStringToFile filename s ;
	 write_message ("Saved system display contents to " ^ filename)
       end
     with
       CHIOFailure s ->
	 write_message ("Unable to save system display contents: " ^ s))
  | _ ->
    write_message ("No data to be saved")


let write_to_system_display_pp (name:string) (p:pretty_t) = 
  write_to_system_display name (string_printer#print p)


let system_page = 
  let label = GMisc.label ~text:"               SYSTEM               " () in
  main_notebook#append_page ~tab_label:label#coerce system_table#coerce


let goto_system_page ():unit = main_notebook#goto_page system_page


let read_source filename =
  let sourcefile =
    if (Filename.is_relative filename)
    then (Filename.concat (get_src_directory ()) filename)
    else filename in
  let lines = ref [] in
  let chan = open_in sourcefile in
  let cleanup () =
    let sourcelines = List.rev (!lines) in
    let sourcestring = String.concat "\n" sourcelines in
    begin
      close_in chan ;
      (sourcelines,sourcestring)
    end in
  try
    while (true) do
      lines := (input_line chan) :: !lines
    done ;
    cleanup ()
  with
    End_of_file -> cleanup ()
