(* =============================================================================
   CodeHawk Graphical User Interface Basis
   Author: A. Cody Schuffelen
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

open CHPretty
open CHUtils
open CHDot

let red = 0xFF0000FF 
let light_red = 0xFFAAAAFF
let green = 0x00FF00FF 
let light_green = 0xAAFFAAFF
let blue = 0x0000FFFF 
let light_blue = 0xAAAAFFFF
let yellow = 0xFFFF00FF
let light_yellow = 0xFFFFAAFF
let orange = 0xFF8800FF
let light_orange = 0xFFCCAAFF
let cyan = 0x00FFFFFF
let light_cyan = 0xAAFFFFFF
let magenta = 0xFF00FF 
let light_magenta = 0xFFAAFF

let linesplit str =
  try
    if str = "" then [] else
      let n = ref 0 in
      let lis: string list ref = ref [] in
      let current = ref "" in
      let _ = while !n < String.length str do
	  let c = str.[!n] in
	  let _ = (if c = '\"' then
	      let _ = n := !n + 1 in
	      while str.[!n] != '\"' do
		let _ = (current := !current ^ (String.sub str !n 1)) in
		n := !n + 1
	      done
	    else if c = ' ' then
	      let _ = lis := !current :: !lis in
	      current := ""
	    else
	      current := !current ^ (String.sub str !n 1)) in
	  n := !n + 1
	done in
      let _ = lis := !current :: !lis in
      List.rev !lis
  with Invalid_argument s ->
    begin
      pr_debug [ STR "Error in linesplit " ; STR str ; STR ": " ; STR s ; NL ] ;
      []
    end

exception Invalid_file
  
module StringMap = Map.Make (String)
  
type graphLine = { 
  graphScale:float;
  graphWidth:float;
  graphHeight:float;
}
type nodeLine = { 
  nodeName:string;
  nodeX:float;
  nodeY:float;
  nodeWidth:float;
  nodeHeight:float;
  nodeLabel:string;
  nodeStyle:string;
  nodeShape:string;
  nodeColor:string;
  nodeFillColor:string;
}
type gpoint = { pointX:float; pointY:float; }
type glabel = { labelText:string; labelX:float; labelY:float; }
type edgeLine = { 
  edgeTail:string;
  edgeHead:string;
  edgeN:int;
  edgePoints: gpoint list ;
  edgeLabel: glabel option;
  edgeStyle:string;
  edgeColor:string;
}
type dotfile = {
  dotfileDesc: graphLine;
  dotfileNodes: nodeLine list;
  dotfileEdges: edgeLine list;
  dotfileNodeMap : nodeLine StringMap.t;
}
type dotLine = GraphLine of graphLine | NodeLine of nodeLine | EdgeLine of edgeLine | StopLine;;
(*
  All lines are of format:
  graph scale width height
  node name x y width height label style shape color fillcolor
  edge tail head n x1 y1 .. xn yn [label xl yl] style color
  stop
*)
let makeGraphLine split_str =
  let nth = List.nth split_str in
  GraphLine {
    graphScale = float_of_string (nth 0);
    graphWidth = float_of_string (nth 1);
    graphHeight = float_of_string (nth 2);
  }
    
let makeNodeLine split_str =
  let nth = List.nth split_str in
  NodeLine {
    nodeName = nth 0;
    nodeX = float_of_string (nth 1);
    nodeY = float_of_string (nth 2);
    nodeWidth = float_of_string (nth 3);
    nodeHeight = float_of_string (nth 4);
    nodeLabel = nth 5;
    nodeStyle = nth 6;
    nodeShape = nth 7;
    nodeColor = nth 8;
    nodeFillColor = nth 9;
  }
    
let rec buildPoints start finish split_str =
  let nth = List.nth split_str in
  if(start >= finish) then [] else
    let point = {pointX = float_of_string (nth start); pointY = float_of_string (nth (start+1));} in
    point :: buildPoints (start+2) finish split_str;;


let makeEdgeLine split_str = 
  let nth = List.nth split_str in
  let n = int_of_string(nth 2) in
  let hasLabel = (List.length split_str) > (6 + 2*n) in
  EdgeLine {
    edgeTail = nth 0;
    edgeHead = nth 1;
    edgeN = n;
    edgePoints = buildPoints 3 (3+2*n) split_str;
    edgeLabel = if hasLabel then 
	Some {labelText = nth (3+2*n); 
	      labelX = float_of_string (nth (4+2*n)); labelY = float_of_string (nth (5+2*n))} 
      else 
	None;
    edgeStyle = nth (List.length split_str - 2);
    edgeColor = nth (List.length split_str - 1);
  }
    
let makeLine str = 
  (* let split_str = nsplit str " " in *)
  let split_str = linesplit str in
  (*let _ = List.iter (Printf.printf "%s/") split_str in
    let _ = print_endline "" in*)
  match List.hd split_str with
    | "graph" -> makeGraphLine (List.tl split_str)
    | "node" -> makeNodeLine (List.tl split_str)
    | "edge" -> makeEdgeLine (List.tl split_str)
    | "stop" -> StopLine
    | _ -> raise Invalid_file

let read_graph_line chan =
  let str = ref (input_line chan) in
  let len = ref (String.length !str) in
  begin
    while !str.[(!len - 1) ] = '\\' do
      begin
	str := (String.sub !str 0 (!len - 1)) ^ (input_line chan) ;
	len := String.length !str
      end
    done;
    !str
  end
      


let buildGraph filename = 
  let lines = ref [] in
  let chan = open_in filename in
  let map = ref (StringMap.empty) in
  let _ = (try
	     while true; do
	       let line = makeLine(read_graph_line chan) in
	       let _ = (match line with
		 |	NodeLine (k) -> map := StringMap.add k.nodeName k !map ; ()
		 |	_ -> ()
	       ) in
	       lines := line :: !lines
	     done;
    with End_of_file -> close_in chan) in
  (* let _ = List.rev !lines in *)
  let ret = {
    dotfileDesc = 
      (match List.hd (List.filter (fun (r) -> match r with GraphLine(g) -> true | _ -> false) !lines) with 
	  GraphLine(g) -> g 
	| _ -> raise Invalid_file);
    dotfileNodes = 
      List.map (fun (m) -> match m with NodeLine(l) -> l | _ -> raise Invalid_file) 
	(List.filter (fun (r) -> match r with NodeLine(n) -> true | _ -> false) !lines);
    dotfileEdges = 
      List.map (fun (m) -> match m with EdgeLine(l) -> l | _ -> raise Invalid_file) 
	(List.filter (fun (r) -> match r with EdgeLine(e) -> true | _ -> false) !lines);
    dotfileNodeMap = !map;
  } in
  ret

let delete_event window ev = window#misc#hide () ; true
let destroy () = GMain.Main.quit ()
let tooltips = GData.tooltips ()

let rec factorial n =
  if n < 2.0 then 1.0 else (n *. (factorial (n -. 1.0)))
    
let rec range i j =
  if i > j then [] else i :: (range (i+1) j)
    
let choose a b =
  if a < b then 0.0 else ((factorial a) /. ((factorial b) *. (factorial (a -. b))))

let makeFancyTabLabel (notebook: GPack.notebook) (pane) text () =
  let hbox = GPack.hbox () in
  let _ = GMisc.label ~text:text ~packing:(hbox#add) () in
  let button = GButton.button ~packing:(hbox#add) () in
  let _ = GMisc.image ~stock:`CLOSE ~width:5 ~height:5 ~packing:(button#add) () in
  let _ = button#connect#clicked (fun () -> notebook#remove_page(notebook#page_num (pane#coerce))) in
  hbox

class type canvas_node_menu_item_int =
object
  method get_label: string
  method get_callback_function: (string -> unit -> unit) 
end

class canvas_node_menu_item_t (label:string) (callback_function:string -> unit -> unit):canvas_node_menu_item_int =
object
  method get_label = label
  method get_callback_function = callback_function
end

let make_node_menu_item (label:string) (callback_function:string -> unit -> unit) =
  new canvas_node_menu_item_t label callback_function

class type canvas_node_item_int =
object
  method set_color: int -> unit
  method set_text : string -> unit
  method set_pixel_width : int -> unit
  method get_name: string
end

class type canvas_edge_item_int =
object
end

class canvas_node_item_t (menu_options:canvas_node_menu_item_int list)
  (name:string) (nodeLabel:GnoCanvas.text) (nodeBox:GnoCanvas.rect) =
object

  initializer
    match menu_options with
      [] -> ()
    | l ->
      let nodeMenu = GMenu.menu ~show:true () in
      let _ = List.iter
	(fun menuOption ->
	  let menuItem = GMenu.menu_item ~label:menuOption#get_label ~packing:nodeMenu#append () in
	  let _ = menuItem#connect#activate 
	    ~callback:(fun () -> menuOption#get_callback_function name ()) in
	  ()) l in
      let clicked = (fun event ->
	match event with
	  `BUTTON_RELEASE (k) -> nodeMenu#popup ~button:1 ~time:(GdkEvent.get_time k) ; true
	| _ -> false) in
      let _ = nodeLabel#connect#event clicked in
      let _ = nodeBox#connect#event clicked in
      () 

  method set_color (color:int)  =
    let int32_color = Int32.of_int color in
    begin
      nodeBox#set [`FILL_COLOR_RGBA int32_color ] ;
    end

  method set_text (s:string) = nodeLabel#set [`TEXT s]

  method set_pixel_width (w:int) = nodeBox#set [`WIDTH_PIXELS w ]

  method get_name = name
end

class canvas_edge_item_t (source:string) (target:string) (line:GnoCanvas.line) =
object
end

    
let canvasTable : (string, GnoCanvas.canvas) Hashtbl.t = Hashtbl.create 10

let showFile (menu_options:canvas_node_menu_item_int list) 
    window (notebook: GPack.notebook) filename () =
  let graph = buildGraph (filename ^ ".plain") in
  let gheight x = graph.dotfileDesc.graphHeight -. x in
	
  let _ = begin
    print_float graph.dotfileDesc.graphWidth;
    print_endline "";
    print_float graph.dotfileDesc.graphHeight;
    print_endline "";
  end in
  
  (* Create a new window and sets the border width of the window. *)
  let scroll = GBin.scrolled_window () in
  let label = makeFancyTabLabel notebook scroll filename () in
  let newgraph = notebook#append_page ~tab_label:(label#coerce) scroll#coerce in
  let canvas = GnoCanvas.canvas ~packing:scroll#add () in
  let _ = Hashtbl.add canvasTable filename canvas in
  let _ = canvas#set_scroll_region 0.0 0.0 (graph.dotfileDesc.graphWidth) (graph.dotfileDesc.graphHeight) in
  let _ = canvas#set_center_scroll_region true in
  let pixelsPerUnit = ref (700.0 /. (max graph.dotfileDesc.graphWidth graph.dotfileDesc.graphHeight)) in
  let _ = canvas#set_pixels_per_unit !pixelsPerUnit in
  
  let nodes = List.map ( fun (elem) ->
    let x1 = elem.nodeX -. (elem.nodeWidth /. 2.0) in
    let y1 = graph.dotfileDesc.graphHeight -. (elem.nodeY -. (elem.nodeHeight /. 2.0)) in
    let x2 = elem.nodeX +. (elem.nodeWidth /. 2.0) in
    let y2 = graph.dotfileDesc.graphHeight -. (elem.nodeY +. (elem.nodeHeight /. 2.0)) in
    let rect = GnoCanvas.rect 
      ~x1:x1 ~y1:y1 ~x2:x2 ~y2:y2 ~fill_color:"white" 
      ~props:[`OUTLINE_COLOR (elem.nodeColor);`WIDTH_PIXELS (1)] canvas#root in
    let text = GnoCanvas.text ~x:(elem.nodeX) ~y:(gheight elem.nodeY) ~text:(elem.nodeLabel) canvas#root in
    let nodeItem = new canvas_node_item_t menu_options elem.nodeName text rect in
    nodeItem
  ) graph.dotfileNodes in
  
  let edges = List.map ( fun (elem) ->
    let _ = print_char '.' in
    let beginNode = (StringMap.find elem.edgeTail) graph.dotfileNodeMap in
    let beginPoint = {
        pointX = beginNode.nodeX;
        pointY = (graph.dotfileDesc.graphHeight -. beginNode.nodeY) } in
    let endNode = (StringMap.find elem.edgeHead) graph.dotfileNodeMap in
    let endPoint = {
        pointX = endNode.nodeX;
        pointY = (graph.dotfileDesc.graphHeight -. endNode.nodeY) } in
    let points_first =
      List.map (fun (pt) ->
          { pointX = (pt.pointX);
            pointY = (graph.dotfileDesc.graphHeight -. pt.pointY) }) elem.edgePoints in
    
    let firstInPoints = List.hd points_first in
    let lastInPoints = List.nth points_first (List.length points_first - 1) in
    let inBeginXRange =
      abs_float(beginPoint.pointX -. firstInPoints.pointX) > ((beginNode.nodeWidth /. 2.0) +. 0.05) in
    let inBeginYRange =
      abs_float(beginPoint.pointY -. firstInPoints.pointY) > ((beginNode.nodeHeight /. 2.0) +. 0.05) in
    let inEndXRange =
      abs_float(endPoint.pointX -. lastInPoints.pointX) > endNode.nodeWidth /. 2.0 in
    let inEndYRange =
      abs_float(endPoint.pointY -. lastInPoints.pointY) > endNode.nodeHeight /. 2.0 in
    
    let needsBeginArrow = inBeginXRange || inBeginYRange in
    let needsEndArrow = inEndXRange || inEndYRange in
    
    let points = (if needsBeginArrow then 
	[beginPoint] else []) @ points_first @ (if needsEndArrow then [endPoint] else []) in
    
    let n = List.length points - 1 in
    let n_f = float_of_int n in
    let bezierpoints = ref [ ] in
    let _ = for t = 200 downto 0 do
	let t_f = (float_of_int t) /. 200.0 in
	let sumX = ref 0.0 in
	let sumY = ref 0.0 in
	let _ = for i = 0 to n do
	    let i_f = float_of_int i in
	    let _ = sumX := !sumX
                            +. ((choose n_f i_f)
                                *. ((1.0 -. t_f) ** (n_f -. i_f))
                                *. (t_f ** i_f) *. (List.nth points i).pointX) in
	    sumY := !sumY
                    +. ((choose n_f i_f)
                        *. ((1.0 -. t_f) ** (n_f -. i_f))
                        *. (t_f ** i_f) *. (List.nth points i).pointY)
	  done in
	let inBeginXRange = 
	  abs_float(beginPoint.pointX -. !sumX) < beginNode.nodeWidth /. 2.0 in
	let inBeginYRange = 
	  abs_float(beginPoint.pointY -. !sumY) < beginNode.nodeHeight /. 2.0 in
	let inEndXRange =
          abs_float(endPoint.pointX -. !sumX) < endNode.nodeWidth /. 2.0 in
	let inEndYRange =
          abs_float(endPoint.pointY -. !sumY) < endNode.nodeHeight /. 2.0 in
	if not ((inBeginXRange && inBeginYRange) || (inEndXRange && inEndYRange)) then 
	  bezierpoints := { pointX = !sumX; pointY = !sumY } :: !bezierpoints 
	else ()
      done in
    let pointarray = Array.of_list 
      (List.flatten (List.map (fun (pt) -> pt.pointX :: pt.pointY :: []) !bezierpoints)) in
    let props = 
      [ `SMOOTH(true); 
	`LAST_ARROWHEAD(needsEndArrow); 
	`FIRST_ARROWHEAD(needsBeginArrow); 
	`ARROW_SHAPE_A(0.1); 
	`ARROW_SHAPE_B(0.1); 
	`ARROW_SHAPE_C(0.05) ] in
    let edge = GnoCanvas.line ~props:props ~points:pointarray 
      ~fill_color:(elem.edgeColor) canvas#root in
    let _ = (match (!bezierpoints,elem.edgeLabel) with
      | (_,None) -> ()
      | ([],_) -> ()
      | (_,Some label) -> 
	let pt = List.nth !bezierpoints (List.length !bezierpoints / 2) in
	let _ = GnoCanvas.text ~anchor:`WEST ~x:pt.pointX ~y:pt.pointY 
	  ~text:(label.labelText) canvas#root in
	()
    ) in
    let edgeItem = new canvas_edge_item_t elem.edgeTail elem.edgeHead edge in
    edgeItem) graph.dotfileEdges in
  let _ = print_endline "." in
  let _ = notebook#goto_page newgraph in
  let _ = window#show () in
  (nodes,edges)

let get_current_canvas (notebook: GPack.notebook) () =
  if (List.length notebook#children = 0) then None else
    let label = notebook#get_tab_label (notebook#get_nth_page (notebook#current_page)) in
    let obj = GtkPack.Box.cast label#as_widget in
    let hbox_of_widget widget = new GPack.box obj in
    let children = (hbox_of_widget ())#children in
    let labelWidget = List.nth children 0 in
    let textobj = GtkMisc.Label.cast labelWidget#as_widget in
    let textlabel = new GMisc.label textobj in
    let name = textlabel#label in
    let canvas:GnoCanvas.canvas = Hashtbl.find canvasTable name in
    Some (name, canvas)

class type canvas_window_int =
object
  method initialize: unit
  method get_window: GWindow.window
  method show: unit
  method add_labeled_button: string -> (string -> GnoCanvas.canvas -> unit) -> unit
  method show_graph:
           ?node_menu_options:canvas_node_menu_item_int list
           -> dot_graph_int -> string
           -> canvas_node_item_int list * canvas_edge_item_int list
end

class canvas_window_t:canvas_window_int =
object (self)

  val windows =
    let w = GWindow.window ~width:800 ~height:600 () in
    let _ = w#event#connect#delete ~callback:(delete_event w) in
    let _ = w#connect#destroy ~callback:destroy in
    let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in
    let b = GPack.button_box `HORIZONTAL ~layout:`START ~height:40 ~packing:vbox#pack () in
    let n = GPack.notebook ~tab_pos:`LEFT ~show_tabs:true ~packing:(vbox#pack ~expand:true) () in
    (w,b,n)

  val graphs = new StringCollections.table_t

  method get_window = let (w,_,_) = windows in w

  method show = 
    let (window,_,notebook) = windows in 
    begin 
      window#show () ; window#misc#grab_focus () ; window#misc#set_state `ACTIVE ; 
      ignore (window#activate_focus ())
    end

  method show_graph ?(node_menu_options=[]) (g:dot_graph_int) (name:string) =
    let (window, buttonbox, notebook) = windows in
    let _ = graphs#set name g in
    let dot_filename = name ^ ".dot" in
    let plain_filename = name ^ ".plain" in
    begin
      CHFileIO.file_output#saveFile dot_filename g#toPretty ;
      ignore (Sys.command ("dot -Tplain -o " ^ plain_filename ^ " " ^ dot_filename)) ;
      showFile node_menu_options window notebook name ()
    end

  method initialize =
    let (window,buttonbox,notebook) = windows in

    let zoomInButton = GButton.button ~packing:buttonbox#add () in
    let _ = tooltips #set_tip zoomInButton#coerce ~text:"Zoom in" in
    let _ = GMisc.image ~stock:`ZOOM_IN ~packing:zoomInButton#add () in
    let _ = zoomInButton#connect#clicked (fun () ->
      if List.length notebook#children = 0 then () else
	let canvas_opt = get_current_canvas notebook () in
	match canvas_opt with
	  | Some (_,canvas) ->
	    let x,y = canvas#w2c_d 1.0 1.0 in
	    canvas#set_pixels_per_unit (x +. 20.0)
	  | None -> ()) in

    let zoomOutButton = GButton.button ~packing:buttonbox#add () in
    let _ = tooltips #set_tip zoomOutButton#coerce ~text:"Zoom out" in
    let _ = GMisc.image ~stock:`ZOOM_OUT ~packing:zoomOutButton#add () in
    let _ = zoomOutButton#connect#clicked (fun () ->
      if List.length notebook#children = 0 then () else
	let canvas_opt = get_current_canvas notebook () in
	match canvas_opt with
	  | Some (_,canvas) ->
	    let x,y = canvas#w2c_d 1.0 1.0 in
	    canvas#set_pixels_per_unit (x -. 20.0)
	  | None -> ()) in
    ()

  method add_labeled_button label action =
    let (window, buttonbox, notebook) = windows in
    let button = GButton.button ~packing:buttonbox#add ~label:label () in
    let _ = button#connect#clicked (fun () ->
      if List.length notebook#children = 0 then () else
	let canvas_opt = get_current_canvas notebook () in
	match canvas_opt with
	  | Some (name, canvas) -> action name canvas
	  | None -> ()) in
    ()

end

let make_canvas_base () = 
  let canvas = new canvas_window_t in begin canvas#initialize ; canvas end
