(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Cody Schuffelen and Henny Sipma
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

open GMain

(* chlib *)
open CHPretty
open CHUtils

(* chutil *)
open CHFileIO

(* bchlib *)
open BCHSystemInfo

(* bchanalyze *)
open BCHInterrupt

let flush_x () = while Glib.Main.iteration false do () done
let delete_event ev = false
let destroy () = GMain.Main.quit ()

let string_printer = CHPrettyUtil.string_printer

let functions_listed = new StringCollections.set_t

let set_functions_listed l = functions_listed#addList l

let get_functions_listed () = functions_listed#toList

let has_function_listed = functions_listed#has

let clear_functions_listed () =
  functions_listed#removeList functions_listed#toList

let add_function_listed s = 
  if functions_listed#has s then
    false
  else
    begin functions_listed#add s ; true end


let window = 
  GWindow.window
    ~title:"CodeHawk x86 Binary Analyzer"
    ~border_width:5
    ~width:1200
    ~height:700
    ()

let root_table = 
  GPack.table
    ~row_spacings:5
    ~col_spacings:5
    ~columns:1
    ~rows:4
    ~packing:window#add
    ()


let menubar =
  GMenu.menu_bar ~packing:(root_table#attach ~top:0 ~left:0 ~expand:`NONE) ()

(* ------------------------------------------------------- message area -- *)
let message_area =
  GBin.scrolled_window ~height:60
    ~packing:(root_table#attach ~left:0 ~top:1 ~expand:`X) ()

let message_viewport = GBin.viewport ~packing:message_area#add ()
let message_contents:GObj.widget option ref = ref None

let add_message_viewport w =
  let _ = match !message_contents with
    |Some m -> message_viewport#remove m
    | _ -> () in
  begin message_contents := Some w#coerce ; message_viewport#add w end

let message_box =
  GMisc.label ~text:"message" ~justify:`LEFT ~packing:add_message_viewport ()

let write_message (msg:string) =
  begin
    message_box#set_text msg ;
    print_endline (msg ^ "\n") ;
    flush_x () ;
    flush stdout
  end

let write_message_pp (msg:pretty_t) =
  write_message (string_printer#print msg)

(* ---------------------------------------------------------- progress bar -- *)




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

let reset_progress_bar () =
  begin progress_bar#set_fraction 0.0 ; flush_x () end

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

(* let ptimer = Timeout.add ~ms:50 ~callback:(fun () -> progress_bar#pulse(); true) *)

(*
let adjustment = GData.adjustment ~lower:0. ~upper:100. ~step_incr:1. ~page_incr:10. () 

let set_scale_bound (max_num:int) =  adjustment#set_bounds ~step_incr:((float max_num)/100.) () in

let scale_bar = GRange.scale `HORIZONTAL ~adjustment ~draw_value:true
    ~packing:(root_table#attach ~left:0 ~top:2 ~expand:`X ~shrink:`BOTH) ()

*)

(* -------------------------------------------------------------~~-- main area -- *)
let main_notebook = GPack.notebook ~tab_pos:`TOP 
    ~packing:(root_table#attach ~top:3 ~left:0 ~expand:`BOTH) ()

(* ----------------------------------------------------------- system display -- *)

let system_table =
  GPack.table ~row_spacings:5 ~col_spacings:5 ~columns:1 ~rows:2 ()
let system_display = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
  ~packing:(system_table#attach ~left:0 ~top:0 ~expand:`BOTH) () 
(* let system_viewport = GBin.viewport ~packing:system_display#add ()  *)
let system_contents:GObj.widget option ref = ref None
let system_contents_string = ref None
let system_contents_name = ref "none"

(* ------------------------------------------------------------~~-- search bar -- *)
let search_bar = GPack.table ~row_spacings:5 ~col_spacings:5 ~columns:2 ~rows:1 
  ~packing:(system_table#attach ~left:0 ~top:3 ~expand:`X) ()
let search_label = GMisc.label ~text:"search: " ~justify:`LEFT 
  ~packing:(search_bar#attach ~left:0 ~top:0) ()
let search_entry = GEdit.entry ~editable:true ~visibility:true ~show:true ~height:30
  ~packing:(search_bar#attach ~left:1 ~top:0) ()

(* name: identification of the information being written, used as a suffix in the
         filename when the system display contents are saved to file
   str: string to be displayed
*)
let write_to_system_display (name:string) (str:string) =
  let _ = match !system_contents with
    | Some s -> system_display#remove s | _ -> () in 
  let view = GText.view ~editable:false () in
  let _ = view#set_pixels_above_lines 5 in
  let _ = view#set_left_margin 10 in
  let _ = view#misc#modify_font_by_name "Monospace 12" in
  let buffer = view#buffer in
  let _ = buffer#create_tag ~name:"heading" 
    [`WEIGHT `BOLD; `SIZE (15*Pango.scale)] in
  let _ = buffer#create_tag ~name:"italic" [`STYLE `ITALIC] in
  let _ = buffer#create_tag ~name:"yellow_background" [`BACKGROUND "yellow"] in
  let iter = buffer#get_iter `START in
  let _ = buffer#insert ~iter str in
  let contents = view#coerce in
  let tagged_iters = ref [] in
  let add_tag s e = tagged_iters := (s,e) :: !tagged_iters in
  let remove_tags () =
    begin
      List.iter (fun (s,e) -> buffer#remove_tag_by_name "yellow_background" s e)
                !tagged_iters;
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
	  let _ =
            view#scroll_to_iter ~yalign:(0.5) ~use_align:true found_begin in
	  ()
      | _ -> ()) in
  begin 
    system_contents := Some contents ; 
    system_contents_string := Some str ;
    system_contents_name := name ;
    system_display#add contents 
  end

let save_system_display_contents ():unit =
  let filename = system_info#get_filename in
  match !system_contents_string with 
    Some s -> 
      (try
	let output_filename = filename ^ "_" ^ !system_contents_name ^ ".txt" in
	begin
	  file_output#saveStringToFile output_filename s ;
	  write_message ("Saved system display contents to " ^ output_filename)
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
