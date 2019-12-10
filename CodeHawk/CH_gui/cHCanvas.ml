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

open CHUtils
open CHDot

type dot_xreference_t = {
  get_color: string -> string ;
  get_alternate_text: string -> string list ;
  get_predicate: string -> string -> bool ;
  get_history : (string * int) list ;
  get_loops : (string * int) list ;
}

let red = 0xFF0000FF 
let light_red = 0xFFAAAAFF
let green = 0x00FF00FF 
let light_green = 0xAAFFAAFF
let blue = 0x0000FFFF 
let light_blue = 0xBBBBFFFF
let yellow = 0xFFFF00FF
let light_yellow = 0xFFFFAAFF
let orange = 0xFF8800FF
let light_orange = 0xFFCCAAFF
let cyan = 0x00FFFFFF
let light_cyan = 0xAAFFFFFF
let magenta = 0xFF00FF 
let light_magenta = 0xFFAAFF

let get_alternate_text (xref_opt:dot_xreference_t option) (node:string) (current_text:string) =
  match xref_opt with
      None -> current_text
    | Some xref ->
      match xref.get_alternate_text node with
	  [] -> current_text
	| alternates ->
	  if List.mem current_text alternates then
	    let rec pos l p v = match l with [] -> -1 | h::tl -> if h=v then p else pos tl (p+1) v in
	    let s_pos = pos alternates 0 current_text in
	    let new_pos = (s_pos + 1) mod (List.length alternates) in
	    List.nth alternates new_pos 
	  else
	    current_text

open CHPretty

let canvas_nodes = Hashtbl.create 53

let add_node filename node =
  if Hashtbl.mem canvas_nodes filename then
    let nodes = Hashtbl.find canvas_nodes filename in
    Hashtbl.replace canvas_nodes filename (node :: nodes)
  else
    Hashtbl.add canvas_nodes filename [ node ]

let xref_table = Hashtbl.create 53

let add_xref filename xref = Hashtbl.add xref_table filename xref

let linesplit str =
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
  dotfileXref : dot_xreference_t option
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
;;

let buildGraph xref filename = 
  let lines = ref [] in
  let chan = open_in filename in
  let map = ref (StringMap.empty) in
  let _ = (try
	     while true; do
	       let line = makeLine(input_line chan) in
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
    dotfileXref = xref
  } in
  ret

let delete_event window ev =
  window#misc#hide ();
  (* Change [true] to [false] and the main window will be destroyed with
   * a "delete event" *)
  true

let tooltips = GData.tooltips ()
    
let destroy () = GMain.Main.quit ()
     
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
  let _ = GMisc.image ~stock:`CLOSE ~packing:(button#add) () in
  let _ = button#connect#clicked (fun () -> notebook#remove_page(notebook#page_num (pane#coerce))) in
  hbox
    
let canvasTable : (string, GnoCanvas.canvas) Hashtbl.t = Hashtbl.create 10;;

let getCurrentCanvas (notebook: GPack.notebook) () = 
  if(List.length (notebook#children) = 0) then None else
    let label = notebook#get_tab_label (notebook#get_nth_page (notebook#current_page)) in
    let obj = GtkPack.Box.cast label#as_widget in (* Using lablgtk downcast functionality to get around ocaml's lack of downcasting *)
    let hbox_of_widget widget = new GPack.box obj in
    let children = (hbox_of_widget ())#children in
    let labelWidget = List.nth children 0 in
    let textobj = GtkMisc.Label.cast labelWidget#as_widget in
    let textLabel = new GMisc.label textobj in
    let name = textLabel#label in
    let _ = pr_debug [ STR "Notebook label: "  ; STR name ; NL ] in
    let ret : GnoCanvas.canvas = Hashtbl.find canvasTable name in
    Some (name,ret)
      
let settingsCallback canvas firstCheckbox firstTextEntry () =
  let _ = print_endline ("firstCheckbox: " ^ (if firstCheckbox then "true" else "false")) in
  let _ = print_endline ("firstTextEntry: " ^ firstTextEntry) in
  ()

let color_outline_nodes name canvas pred color =
  let nodes = Hashtbl.find canvas_nodes name in
  let xref = Hashtbl.find xref_table name in
  match xref with
      Some xref ->
	List.iter (fun (label,item) ->
	  let is_chosen = (xref.get_predicate pred) label in
	  if is_chosen then item#set [`OUTLINE_COLOR color ; `WIDTH_PIXELS 5 ] else ()) nodes
    | _ -> ()

let color_nodes name canvas pred (color: int) =   
  let int32_color = Int32.of_int color in
  let nodes = Hashtbl.find canvas_nodes name in
  let xref = Hashtbl.find xref_table name in
  match xref with
      Some xref ->
	List.iter (fun (label,item) ->
	  let is_chosen = (xref.get_predicate pred) label in
	  if is_chosen then item#set [`FILL_COLOR_RGBA int32_color] else ()) nodes
    | _ -> ()

let color_stubs name canvas =
  color_nodes name canvas "is_stub" light_green

let color_native_nodes name canvas =

  color_nodes name canvas "is_native" light_blue

let color_variables name canvas = 
  color_nodes name canvas "is_variable" light_blue

let color_fields name canvas = 
  color_nodes name canvas "is_field" light_cyan

let color_calls name canvas = 
  color_nodes name canvas "is_call" light_magenta

let color_not_tainted name canvas = 
  color_nodes name canvas "is_not_tainted" light_green

let color_tainted name canvas = 
  color_nodes name canvas "is_tainted" light_yellow ;
  color_nodes name canvas "is_def_tainted" light_red

let color_def_tainted name canvas = 
  color_nodes name canvas "is_def_tainted" light_red

let current_name = ref "" 
let rest_history = ref []

let color_taint_sources name canvas = 
  color_nodes name canvas "is_taint_source" light_yellow ;
  color_nodes name canvas "is_def_taint_source" light_red

let color_loops name canvas = 
  let xref_opt = Hashtbl.find xref_table name in
  match xref_opt with 
  | Some xref -> 
      let nodes = Hashtbl.find canvas_nodes name in 
      let color (label, color) = 
	try 
	  let (label, item) = List.find (fun (l, i) -> l = label) nodes in
	  let _ = pr_debug [STR "found item for "; STR label; NL] in 
	  let int32_color = Int32.of_int color in
	  item#set [`FILL_COLOR_RGBA int32_color] 
	with _ -> () in  (* These good be unreachable states *)
      List.iter color xref.get_loops
  | _ -> () 

let start_history name canvas = 
  let xref_opt = Hashtbl.find xref_table name in
  match xref_opt with 
  | Some xref -> rest_history := xref.get_history
  | _ -> () 

let step_history name canvas = 
  if name = !current_name then ()
  else (
    current_name := name ;
    start_history name canvas ) ;
  let nodes = Hashtbl.find canvas_nodes name in 
  let rec color_one history = 
    match history with 
    | (label, color) :: future -> (
	try 
	  let (label, item) = List.find (fun (l, i) -> l = label) nodes in
	  let _ = pr_debug [STR "found item for "; STR label; NL] in 
	  let int32_color = Int32.of_int color in
	  item#set [`FILL_COLOR_RGBA int32_color] ;
	  rest_history := future
	with _ -> 
	  begin
	    pr_debug [STR "did not find item for "; STR label; NL] ; 
	    color_one future
	  end )
    | _ -> () in
  color_one !rest_history
	
let reset name canvas = 
  let nodes = Hashtbl.find canvas_nodes name in
  let set_white (label, item) = item#set [`FILL_COLOR "white"] in
  List.iter set_white nodes ;
  start_history name canvas 

let initialize () =
  let window = GWindow.window ~width:800 ~height:600 () in
  let _ = window#event#connect#delete ~callback:(delete_event window) in
  let _ = window#connect#destroy ~callback:destroy in
  let vbox = GPack.vbox ~homogeneous:false ~packing:window#add () in
  let buttonbox = GPack.button_box `HORIZONTAL ~layout:`START ~height:40 ~packing:vbox#pack () in
  let notebook = GPack.notebook ~tab_pos:`LEFT ~show_tabs:true ~packing:(vbox#pack ~expand:true) () in
  let zoomInButton = GButton.button ~packing:buttonbox#add () in
  let _ = tooltips #set_tip zoomInButton#coerce ~text:"Zoom in" in
  let _ = GMisc.image ~stock:`ZOOM_IN ~packing:zoomInButton#add () in
  let zoomOutButton = GButton.button ~packing:buttonbox#add () in
  let _ = tooltips #set_tip zoomOutButton#coerce ~text:"Zoom out" in
  let _ = GMisc.image ~stock:`ZOOM_OUT ~packing:zoomOutButton#add () in
  let _ = zoomInButton#connect#clicked (fun () ->
    if List.length notebook#children = 0 then () else
      let canvasOption = getCurrentCanvas notebook () in
      match canvasOption with
	| Some (_,canvas) -> 
	  let x,y = canvas#w2c_d 1.0 1.0 in
	  canvas#set_pixels_per_unit (x +. 20.0)
	| None -> ()
  ) in
  let _ = zoomOutButton#connect#clicked (fun () ->
    if List.length notebook#children = 0 then () else
      let canvasOption = getCurrentCanvas notebook () in
      match canvasOption with
	| Some (_,canvas) -> 
	  let x,y = canvas#w2c_d 1.0 1.0 in
	  canvas#set_pixels_per_unit (x -. 20.0)
	| None -> ()
  ) in
  let add_button label change = 
    let button = GButton.button ~packing:buttonbox#add ~label:label () in
    let do_on_click () = 
      match getCurrentCanvas notebook () with
      | None -> ()
      | Some (name, canvas) -> change name canvas in
    let _ = button#connect#clicked do_on_click in
    () in
  add_button "Show \nstubs" color_stubs ;
  add_button "Show native\nmethods" color_native_nodes ;
  add_button "Show \nvariables" color_variables ;
  add_button "Show \nfields" color_fields ;
  add_button "Show \ncalls" color_calls ;
  add_button "Show not\ntainted" color_not_tainted ;
  add_button "Show \ntainted" color_tainted ;
  add_button "Show def.\n tainted" color_def_tainted ;
  add_button "Step through\nhistory" step_history ;
  add_button "Reset" reset ;
  window, notebook
    
let showFile xref window (notebook: GPack.notebook) filename () =
  let graph = buildGraph xref (filename ^ ".plain") in
  let gheight x = graph.dotfileDesc.graphHeight -. x in
  let _ = add_xref filename xref in
	
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
  
  let _ = List.iter ( fun (elem) ->
    let x1 = elem.nodeX -. (elem.nodeWidth /. 2.0) in
    let y1 = graph.dotfileDesc.graphHeight -. (elem.nodeY -. (elem.nodeHeight /. 2.0)) in
    let x2 = elem.nodeX +. (elem.nodeWidth /. 2.0) in
    let y2 = graph.dotfileDesc.graphHeight -. (elem.nodeY +. (elem.nodeHeight /. 2.0)) in
    let rect = GnoCanvas.rect 
      ~x1:x1 ~y1:y1 ~x2:x2 ~y2:y2 ~fill_color:"white" 
      ~props:[`OUTLINE_COLOR (elem.nodeColor);`WIDTH_PIXELS (1)] canvas#root in
    let text = GnoCanvas.text ~x:(elem.nodeX) ~y:(gheight elem.nodeY) ~text:(elem.nodeLabel) canvas#root in
    let nameMenu = GMenu.menu ~show:true () in
    let _ = GMenu.menu_item ~show:true ~label:(get_alternate_text xref elem.nodeName elem.nodeLabel)
      ~packing:nameMenu#append () in
    let clicked =  (fun (event) ->
      match event with
	| `BUTTON_RELEASE (k) -> nameMenu#popup ~button:1 ~time:(GdkEvent.get_time k) ; true
	|	_ -> false 
    ) in
    let _ = rect#connect#event clicked in
    let _ = text#connect#event clicked in
    let _ = add_node filename (elem.nodeName, rect) in
    ()
  ) graph.dotfileNodes in
  
  let _ = List.iter ( fun (elem) ->
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
      List.map (fun (pt) -> {
                    pointX = (pt.pointX);
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
    
    let points =
      (if needsBeginArrow then
         [beginPoint]
       else
         []) @ points_first @ (if needsEndArrow then [endPoint] else []) in
    
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
	let inBeginXRange = abs_float(beginPoint.pointX -. !sumX) < beginNode.nodeWidth /. 2.0 in
	let inBeginYRange = abs_float(beginPoint.pointY -. !sumY) < beginNode.nodeHeight /. 2.0 in
	let inEndXRange = abs_float(endPoint.pointX -. !sumX) < endNode.nodeWidth /. 2.0 in
	let inEndYRange = abs_float(endPoint.pointY -. !sumY) < endNode.nodeHeight /. 2.0 in
	if not ((inBeginXRange && inBeginYRange) || (inEndXRange && inEndYRange)) then
          bezierpoints := { pointX = !sumX; pointY = !sumY } :: !bezierpoints
        else
          ()
      done in
    let pointarray =
      Array.of_list (List.flatten (List.map (fun (pt) -> pt.pointX :: pt.pointY :: []) !bezierpoints)) in
    let props = [ `SMOOTH(true);
                  `LAST_ARROWHEAD(needsEndArrow);
                  `FIRST_ARROWHEAD(needsBeginArrow);
                  `ARROW_SHAPE_A(0.1);
                  `ARROW_SHAPE_B(0.1);
                  `ARROW_SHAPE_C(0.05) ] in
    let _ = GnoCanvas.line ~props:props ~points:pointarray ~fill_color:(elem.edgeColor) canvas#root in
    let _ = (match elem.edgeLabel with
      | None -> ()
      | Some label -> 
	let pt = List.nth !bezierpoints (List.length !bezierpoints / 2) in
	let _ =
          GnoCanvas.text
            ~anchor:`WEST
            ~x:pt.pointX
            ~y:pt.pointY
            ~text:(label.labelText) canvas#root in
	()
    ) in
    ()
        
  ) graph.dotfileEdges in
  let _ = print_endline "." in
  let _ = notebook#goto_page newgraph in
  let _ = window#show () in
  ()
    

class type canvas_int =
object
  method newGraph: ?enable_bidirectional_edges:bool -> string -> CHDot.dot_graph_int
  method showGraph: ?xref:dot_xreference_t option -> string -> unit
  method showSubGraph: ?xref:dot_xreference_t option -> string -> string -> unit
  method initializeForJava: unit
  method initializeForBinary: unit
end

class canvas_t:canvas_int =
object (self)

  val windows =
    let w = GWindow.window ~width:1024 ~height:768 () in
    let _ = w#event#connect#delete ~callback:(delete_event w) in
    let _ = w#connect#destroy ~callback:destroy in
    let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in
    let b = GPack.button_box `HORIZONTAL ~layout:`START ~height:40 ~packing:vbox#pack () in
    let n = GPack.notebook ~tab_pos:`LEFT ~show_tabs:true ~packing:(vbox#pack ~expand:true) () in
    (w,b,n)

  val graphs = new StringCollections.table_t

  method newGraph ?(enable_bidirectional_edges=false) (name:string) = 
    let g = CHDot.mk_dot_graph ~enable_bidirectional_edges:enable_bidirectional_edges name in
    begin
      graphs#set name g ;
      g
    end

  method showGraph ?(xref=None) (name:string) = 
    let (window,buttonbox,notebook) = windows in
    match graphs#get name with
	Some g ->
	  let dot_filename = name ^ ".dot" in
	  let plain_filename = name ^ ".plain" in
	  begin
	    CHFileIO.file_output#saveFile dot_filename g#toPretty ;
	    ignore (Sys.command ("dot -Tplain -o " ^ plain_filename ^ " " ^ dot_filename)) ;
	    showFile xref window notebook name ()
	  end
      | _ ->
	pr_debug [ STR "CHCanvas: No graph found with name " ; STR name ; NL ]

  method showSubGraph ?(xref=None) (name:string) (node:string) =
    match graphs#get name with
	Some g ->
	  let subname = name ^ "_" ^ node in
	  let subgraph = g#subgraph node subname in
	  begin 
	    graphs#set subname subgraph ;
	    self#showGraph ~xref:xref subname
	  end
      | _ ->
	pr_debug [ STR "CHCanvas: No graph found with name " ; STR name ; NL ]
    
  method private initialize =
    let (window,buttonbox,notebook) = windows in
    let zoomInButton = GButton.button ~packing:buttonbox#add () in
    let _ = tooltips #set_tip zoomInButton#coerce ~text:"Zoom in" in
    let _ = GMisc.image ~stock:`ZOOM_IN ~packing:zoomInButton#add () in
    let zoomOutButton = GButton.button ~packing:buttonbox#add () in
    let _ = tooltips #set_tip zoomOutButton#coerce ~text:"Zoom out" in
    let _ = GMisc.image ~stock:`ZOOM_OUT ~packing:zoomOutButton#add () in
    let _ = zoomInButton#connect#clicked (fun () ->
      if List.length notebook#children = 0 then () else
	let canvasOption = getCurrentCanvas notebook () in
	match canvasOption with
	  | Some (_,canvas) -> 
	    let x,y = canvas#w2c_d 1.0 1.0 in
	    canvas#set_pixels_per_unit (x +. 20.0)
	  | None -> ()
    ) in
    let _ = zoomOutButton#connect#clicked (fun () ->
      if List.length notebook#children = 0 then () else
	let canvasOption = getCurrentCanvas notebook () in
	match canvasOption with
	  | Some (_,canvas) -> 
	    let x,y = canvas#w2c_d 1.0 1.0 in
	    canvas#set_pixels_per_unit (x -. 20.0)
	  | None -> ()
    ) in
    ()

  method private add_button label change = 
    let (_,buttonbox,notebook) = windows in
    let button = GButton.button ~packing:buttonbox#add ~label:label () in
    let do_on_click () = 
      match getCurrentCanvas notebook () with
	| None -> ()
	| Some (name, canvas) -> change name canvas in
    let _ = button#connect#clicked do_on_click in
    () 
	
    method initializeForJava =
      begin
	self#initialize ;
	self#add_button "Show \nstubs" color_stubs ;
	self#add_button "Show native\nmethods" color_native_nodes ;
	self#add_button "Show \nvariables" color_variables ;
	self#add_button "Show \nfields" color_fields ;
	self#add_button "Show \ncalls" color_calls ;
	self#add_button "Show not\ntainted" color_not_tainted ;
	self#add_button "Show \ntainted" color_tainted ;
	self#add_button "Show taint\nsources" color_taint_sources ;
	self#add_button "Step through\nhistory" step_history ;
	self#add_button "Show \nloops" color_loops ;
	self#add_button "Reset" reset ;
      end

    method initializeForBinary =
      begin
	self#initialize
      end
		
end

let canvas = new canvas_t
  
(*
  
let main () =
  let window, notebook = initialize () in
  let _ = showFile window notebook "test4.dot" () in
  let _ = showFile window notebook "test3.dot" () in
  let _ = showFile window notebook "test2.dot" () in
  GMain.Main.main ()
    

let _ = main ()
*)
