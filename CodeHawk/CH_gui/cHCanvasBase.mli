val red : int
val light_red : int
val green : int
val light_green : int
val blue : int
val light_blue : int
val yellow : int
val light_yellow : int
val orange : int
val light_orange : int
val cyan : int
val light_cyan : int
val magenta : int
val light_magenta : int
val linesplit : string -> string list
exception Invalid_file
module StringMap :
  sig
    type key = String.t
    type 'a t = 'a Map.Make(String).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t
  end
type graphLine = {
  graphScale : float;
  graphWidth : float;
  graphHeight : float;
}
type nodeLine = {
  nodeName : string;
  nodeX : float;
  nodeY : float;
  nodeWidth : float;
  nodeHeight : float;
  nodeLabel : string;
  nodeStyle : string;
  nodeShape : string;
  nodeColor : string;
  nodeFillColor : string;
}
type gpoint = { pointX : float; pointY : float; }
type glabel = { labelText : string; labelX : float; labelY : float; }
type edgeLine = {
  edgeTail : string;
  edgeHead : string;
  edgeN : int;
  edgePoints : gpoint list;
  edgeLabel : glabel option;
  edgeStyle : string;
  edgeColor : string;
}
type dotfile = {
  dotfileDesc : graphLine;
  dotfileNodes : nodeLine list;
  dotfileEdges : edgeLine list;
  dotfileNodeMap : nodeLine StringMap.t;
}
type dotLine =
    GraphLine of graphLine
  | NodeLine of nodeLine
  | EdgeLine of edgeLine
  | StopLine
val makeGraphLine : string list -> dotLine
val makeNodeLine : string list -> dotLine
val buildPoints : int -> int -> string list -> gpoint list
val makeEdgeLine : string list -> dotLine
val makeLine : string -> dotLine
val read_graph_line : in_channel -> string
val buildGraph : string -> dotfile
val delete_event : < misc : < hide : unit -> 'a; .. >; .. > -> 'b -> bool
val destroy : unit -> unit
val tooltips : GData.tooltips
val factorial : float -> float
val range : int -> int -> int list
val choose : float -> float -> float
val makeFancyTabLabel :
  GPack.notebook ->
  < coerce : GObj.widget; .. > -> string -> unit -> GPack.box
class type canvas_node_menu_item_int =
  object
    method get_callback_function : string -> unit -> unit
    method get_label : string
  end
class canvas_node_menu_item_t :
  string -> (string -> unit -> unit) -> canvas_node_menu_item_int
val make_node_menu_item :
  string -> (string -> unit -> unit) -> canvas_node_menu_item_t
class type canvas_node_item_int =
  object
    method get_name : string
    method set_color : int -> unit
    method set_pixel_width : int -> unit
    method set_text : string -> unit
  end
class type canvas_edge_item_int = object  end
class canvas_node_item_t :
  canvas_node_menu_item_int list ->
  string ->
  GnoCanvas.text ->
  GnoCanvas.rect ->
  object
    method get_name : string
    method set_color : int -> unit
    method set_pixel_width : int -> unit
    method set_text : string -> unit
  end
class canvas_edge_item_t : string -> string -> GnoCanvas.line -> object  end
val canvasTable : (string, GnoCanvas.canvas) Hashtbl.t
val showFile :
  canvas_node_menu_item_int list ->
  < show : unit -> 'a; .. > ->
  GPack.notebook ->
  string -> unit -> canvas_node_item_t list * canvas_edge_item_t list
val get_current_canvas :
  GPack.notebook -> unit -> (string * GnoCanvas.canvas) option
class type canvas_window_int =
  object
    method add_labeled_button :
      string -> (string -> GnoCanvas.canvas -> unit) -> unit
    method get_window : GWindow.window
    method initialize : unit
    method show : unit
    method show_graph :
      ?node_menu_options:canvas_node_menu_item_int list ->
      CHDot.dot_graph_int ->
      string -> canvas_node_item_int list * canvas_edge_item_int list
  end
class canvas_window_t : canvas_window_int
val make_canvas_base : unit -> canvas_window_t
