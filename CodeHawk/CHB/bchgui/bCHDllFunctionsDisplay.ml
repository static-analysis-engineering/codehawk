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

(* gtk *)
open Gobject.Data

(* chlib *)
open CHPretty

(* bchlibpe *)
open BCHPESections   

(* bchlibx86 *)
open BCHBasicTypes
open BCHFunctionSummaryLibrary


let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p

class type dll_functions_display_int =
object
  method initialize: unit
  method reset: unit
  method set_model : (string * string list) list -> unit
  method get_display: GPack.table
  method select: string -> unit
end

class dll_functions_display_t:dll_functions_display_int =
object (self)

  (* (display, (store, nameColumn), view) *)
  val mutable display_data = None
  val mutable view_contents = None
  val iters = Hashtbl.create 13

  method reset =
    begin
      self#set_model [] ;
      view_contents <- None ;
      Hashtbl.clear iters
    end

  method get_display = match display_data with Some (display,_,_) -> display | _ ->
    raise (BCH_failure (STR "get_display: dll_functions_display has not been initialized"))

  method private get_view = match display_data with Some (_,_,view) -> view | _ ->
    raise (BCH_failure (STR "get_view: dll_functions_display has not been initialized"))

  method private get_model = match display_data with Some (_,model,_) -> model | _ ->
    raise (BCH_failure (STR "get_model: dll_functions_display has not been initialized"))

  method private get_iter (name:string) = Hashtbl.find iters name

  method select (functionName:string) =
    let view = self#get_view in
    let iter = self#get_iter functionName in
    view#selection#select_iter iter

  method initialize =
    let display = GPack.table ~row_spacings:5 ~col_spacings:5 ~columns:2 ~rows:2 () in
    let scroll = GBin.scrolled_window ~width:200
      ~packing:(display#attach ~left:0 ~top:1 ~expand:`Y)
      ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC () in
(*    let buttonBox =
      let vbox = GPack.vbox ~homogeneous:false
	~packing:(display#attach ~left:0 ~right:1 ~top:0 ~expand:`X) () in
      GPack.button_box `HORIZONTAL ~layout:`START ~height:40 ~packing:vbox#pack () in  *)
    (* -------------------------------------------------------------- model *)
    let columns = new GTree.column_list in
    let nameColumn = columns#add string in
    let store = GTree.tree_store columns in
    (* --------------------------------------------------------------- view *)
    let view = GTree.view ~model:store () in
    let selection_changed (model:#GTree.model) selection () =
      let change_display path =
	if GTree.Path.get_depth path = 1 then
	  let dllName =
            model#get ~row:(model#get_iter path) ~column:nameColumn in
	  self#show_dll dllName
	else if GTree.Path.get_depth path = 2 then
	  let dllName =
            model#get ~row:(model#get_iter path) ~column:nameColumn in
	  let functionName =
            model#get ~row:(model#get_iter path) ~column:nameColumn in
	  self#show_function dllName functionName
      in
      List.iter change_display selection#get_selected_rows in
    let _ =
      view#append_column
        (GTree.view_column
           ~title:"dll function"
	   ~renderer:(GTree.cell_renderer_text [] , [ "text", nameColumn ])
           () ) in
    let _ =
      view#selection#connect#changed
        ~callback:(selection_changed store view#selection) in
    let viewport = GBin.viewport ~packing:scroll#add () in
    let _ = viewport#add view#coerce in
    display_data <- Some (display, (store, nameColumn), view)

  method set_model (dllFunctions: (string * string list) list) =
    let (store, nameColumn) = self#get_model in
    let view = self#get_view in
    let _ = view#set_model None in
    let _ = store#clear in
    let fill_function dllIter (functionName:string) =
      let functionIter = store#append ~parent:dllIter () in
      begin
	store#set ~row:functionIter ~column:nameColumn functionName;
	Hashtbl.add iters functionName functionIter
      end in
    let fill_dll (dllList:(string * string list)) =
      let dllIter = store#append () in
      begin
	store#set ~row:dllIter ~column:nameColumn (fst dllList) ;
	List.iter (fill_function dllIter) (snd dllList)
      end in
    let _ = List.iter fill_dll dllFunctions in
    let _ = view#set_model (Some store#coerce) in
    ()

  method private show_dll (dllName:string) =
    let display = self#get_display in
    let dllListing =
      pp_str (pe_sections#import_directory_entry_to_pretty dllName) in
    let _ = match view_contents with Some w -> display#remove w | _ -> () in
    let docWindow =
      GBin.scrolled_window
        ~width:1100
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:(display#attach ~left:1 ~top:1)
        () in
    let textView = GText.view ~packing:docWindow#add_with_viewport () in
    let _ = textView#set_pixels_above_lines 5 in
    let _ = textView#set_left_margin 10 in
    let _ = textView#misc#modify_font_by_name "Monospace 12" in
    let buffer = textView#buffer in
    let iter = buffer#get_iter `START in
    let _ = buffer#insert ~iter:iter dllListing in
    view_contents <- Some docWindow#coerce

  method private show_function (dll:string) (functionName:string) =
    let display = self#get_display in
    let functionDocumentation = 
      if function_summary_library#has_dll_function dll functionName then
	pp_str (function_summary_library#get_dll_function dll functionName)#toPretty
      else
	"no documentation available for " ^ functionName in
    let _ = match view_contents with Some w -> display#remove w | _ -> () in
    let docWindow =
      GBin.scrolled_window
        ~width:1100
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:(display#attach ~left:1 ~top:1)
        () in
    let textView = GText.view ~packing:docWindow#add_with_viewport () in
    let _ = textView#set_pixels_above_lines 5 in
    let _ = textView#set_left_margin 10 in
    (* let _ = textView#misc#modify_font_by_name "Monospace 12" in *)
    let buffer = textView#buffer in
    let iter = buffer#get_iter `START in
    let _ = buffer#insert ~iter:iter functionDocumentation in
    view_contents <- Some docWindow#coerce

end

let dll_functions_display = new dll_functions_display_t
