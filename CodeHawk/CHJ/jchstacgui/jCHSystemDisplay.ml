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

(* open Graphics *)
open GMain

(* chlib *)
open CHPretty

let flush_x () = while Glib.Main.iteration false do () done
let delete_event ev = false
let destroy () = GMain.Main.quit ()

let string_printer = CHPrettyUtil.string_printer

let window =
  GWindow.window
    ~title:"CodeHawk Java Analyzer"
    ~border_width:5
    ~width:800
    ~height:600
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
  GMenu.menu_bar
    ~packing:(root_table#attach ~top:0 ~left:0 ~expand:`NONE)
    ()

(* ------------------------------------------------------------- message area -- *)
let message_area =
  GBin.scrolled_window
    ~height:60
    ~packing:(root_table#attach ~left:0 ~top:1 ~expand:`X)
    ()

let message_viewport = GBin.viewport ~packing:message_area#add ()
let message_contents:GObj.widget option ref = ref None

let add_message_viewport w =
  let _ = match !message_contents with 
    | Some m -> message_viewport#remove m | _ -> () in
  begin message_contents := Some w#coerce ; message_viewport#add w end

let message_box = 
  GMisc.label
    ~text:"system display initialized"
    ~justify:`LEFT
    ~packing:add_message_viewport
    ()

let write_message (msg:string) =
  begin 
    message_box#set_text msg ; 
    print_endline (msg ^ "\n") ; 
    flush_x () ; 
    flush stdout 
  end

let write_message_pp (msg:pretty_t) =
  write_message (string_printer#print msg)


(* --------------------------------------------------------- system display --- *)

let main_notebook =
  GPack.notebook
    ~tab_pos:`TOP
    ~packing:(root_table#attach ~top:3 ~left:0 ~expand:`BOTH)
    ()

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
    ~packing:(system_table#attach ~left:0 ~top:0 ~expand:`BOTH)
    ()

let system_contents:GObj.widget option ref = ref None
                                           
let system_contents_string = ref None
                           
let system_contents_name = ref "none"

let search_bar =
  GPack.table
    ~row_spacings:5
    ~col_spacings:5
    ~columns:2
    ~rows:1
    ~packing:(system_table#attach ~left:0 ~top:3 ~expand:`X)
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
    ~show:true ~height:30
    ~packing:(search_bar#attach ~left:1 ~top:0)
    ()

let write_to_system_display (name:string) (str:string) =
  let _ = match !system_contents with
    | Some s -> system_display#remove s | _ -> () in 
  let view = GText.view  () in
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

let write_to_system_display_pp (name:string) (p:pretty_t) = 
  write_to_system_display name (string_printer#print p)

let system_page = 
  let label = GMisc.label ~text:"               SYSTEM               " () in
  main_notebook#append_page ~tab_label:label#coerce system_table#coerce

let goto_system_page ():unit = main_notebook#goto_page system_page
