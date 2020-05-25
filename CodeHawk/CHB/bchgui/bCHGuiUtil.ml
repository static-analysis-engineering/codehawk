(* =============================================================================
   CodeHawk Binary Analyzer 
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

open Gobject.Data

let data_entry_dialog
      ~(title:string)
      ~(label_1:string)
      ~(label_2:string)
      ~(action:string -> string -> string option)
      ~parent =
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:true
      ~show:true
      ~width:400
      ~height:230
      () in
  let table =
    GPack.table
      ~row_spacings:5
      ~col_spacings:10
      ~columns:2
      ~rows:2
      ~border_width:5
      ~show:true
      ~packing:dialog#vbox#add
      () in
  let _ = GMisc.label ~text:label_1 ~packing:(table#attach ~left:0 ~top:0) () in
  let _ = GMisc.label ~text:label_2 ~packing:(table#attach ~left:0 ~top:1) () in
  let entry1 =
    GEdit.entry
      ~editable:true
      ~visibility:true
      ~show:true
      ~height:30
      ~packing:(table#attach ~left:1 ~top:0)
      () in
  let entry2
    = GEdit.entry
        ~editable:true
        ~visibility:true
        ~show:true
        ~height:30
        ~packing:(table#attach ~left:1 ~top:1)
        () in
  let _ = dialog#add_button_stock `CANCEL `CANCEL in
  let _ = dialog#add_button_stock `OK `OK in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp ->
    match resp with
    | `OK -> 
	begin
	  match action entry1#text entry2#text with
	    None -> dialog#destroy ()
	  | Some failure_message ->
	      let error_box = GPack.hbox ~packing:dialog#vbox#add () in
	      let _ = GMisc.label ~text:failure_message ~packing:error_box#add () in
	      ()
	end
    | _ -> dialog#destroy ()) in
  ()

let data1_entry_dialog
      ~(height:int)
      ~(width:int)
      ~(title:string)
      ~(label:string)
      ~(action:string -> string option)
      ~parent =
  let dialog =
    GWindow.dialog ~title ~parent ~modal:true ~show:true ~width ~height () in
  let table =
    GPack.table
      ~row_spacings:5
      ~col_spacings:10
      ~columns:2
      ~rows:2
      ~border_width:5
      ~show:true
      ~packing:dialog#vbox#add
      () in
  let _ = GMisc.label ~text:label ~packing:(table#attach ~left:0 ~top:0) () in
  let entry1 =
    GEdit.entry
      ~editable:true
      ~visibility:true
      ~show:true
      ~height:30
      ~packing:(table#attach ~left:1 ~top:0)
      () in
  let _ = dialog#add_button_stock `CANCEL `CANCEL in
  let _ = dialog#add_button_stock `OK `OK in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp ->
    match resp with
    | `OK -> 
	begin
	  match action entry1#text with
	    None -> dialog#destroy ()
	  | Some failure_message ->
	      let error_box = GPack.hbox ~packing:dialog#vbox#add () in
	      let _ =
                GMisc.label ~text:failure_message ~packing:error_box#add () in
	      ()
	end
    | _ -> dialog#destroy ()) in
  ()

let confirmation_dialog
      ~(title:string)
      ~(label:string)
      ~(yes_action:unit -> unit) 
      ~(no_action:unit->unit)
      ~parent =
  let dialog =
    GWindow.dialog ~title ~parent ~modal:true ~show:true ~width:400 ~height:200 () in
  let _ = GMisc.label ~text:label ~packing:dialog#vbox#add () in
  let _ = dialog#add_button_stock `NO `NO in
  let _ = dialog#add_button_stock `YES `YES in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp ->
    match resp with
    | `YES -> begin yes_action () ; dialog#destroy () end
    | `NO  -> begin no_action  () ; dialog#destroy () end
    | _ -> dialog#destroy ()) in
  ()

let select_section_dialog
      ~window_title ~data ~label_text ~parent_window ~select_action =
  let dialog =
    GWindow.dialog
      ~title:window_title
      ~parent:parent_window
      ~modal:true
      ~show:true
      ~width:600
      ~height:400
      () in
  let _ = GMisc.label ~text:label_text ~packing:dialog#vbox#add () in
  let columns = new GTree.column_list in
  let indexColumn = columns#add int in
  let nameColumn = columns#add string in
  let offsetColumn = columns#add string in
  let sizeColumn = columns#add string in

  let create_model () =
    let store = GTree.list_store columns in
    let fill (index,name,offset,size) =
      let iter = store#append () in
      begin
	store#set ~row:iter ~column:indexColumn index ;
	store#set ~row:iter ~column:nameColumn name ;
	store#set ~row:iter ~column:offsetColumn offset ;
	store#set ~row:iter ~column:sizeColumn size
      end in
    List.iter fill data ;
    store in

  let on_row_activated (view:GTree.view) path column =
    let model = view#model in
    let row = model#get_iter path in
    let index = model#get ~row ~column:indexColumn in
    begin dialog#destroy () ; select_action index end in

  let create_view ~model () =
    let view = GTree.view ~model:model () in
    let _ =
      view#append_column 
        (GTree.view_column
           ~title:"name"
	   ~renderer:(GTree.cell_renderer_text [], [ "text" , nameColumn ])
           () ) in
    let _ =
      view#append_column
        (GTree.view_column
           ~title:"offset"
	   ~renderer:(GTree.cell_renderer_text [], [ "text" , offsetColumn ])
           () ) in
    let _ =
      view#append_column
        (GTree.view_column
           ~title:"size"
	   ~renderer:(GTree.cell_renderer_text [], [ "text" , sizeColumn ])
           () ) in
    let _ = view#connect#row_activated ~callback:(on_row_activated view) in
    view in
  let model = create_model () in
  let display = GBin.scrolled_window ~border_width:25 
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let viewport = GBin.viewport ~packing:display#add () in
  let view = create_view ~model:model () in
  let widget = view#coerce in
  let _ = viewport#add widget in
  let _ = dialog#add_button_stock `CANCEL `CANCEL in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()


let make_colored_label
      ?(fg_color:GDraw.color option)
      (color:GDraw.color)
      (text:string) 
      (packing:GObj.widget->unit)
      () =
  let box = GBin.viewport ~packing () in
  let label = GMisc.label ~text ~packing:box#add () in
  let colorList c =
    List.map (fun t -> (t,c))
             [`ACTIVE ; `INSENSITIVE ; `NORMAL ; `PRELIGHT ; `SELECTED ] in
  let _ = box#misc#modify_bg (colorList color) in
  let _ =
    match fg_color with Some c -> label#misc#modify_fg (colorList c) | _ -> () in
  ()
