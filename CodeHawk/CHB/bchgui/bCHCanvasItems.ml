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

(* chgui *)
open CHCanvasBase


class type canvas_items_int =
object
  method add_node : string -> canvas_node_item_int -> unit
  method add_edge : string -> canvas_edge_item_int -> unit
end


class canvas_items_t:canvas_items_int =
object

  val canvas_nodes = Hashtbl.create 53
  val canvas_edges = Hashtbl.create 53

  method add_node (graphName:string) (nodeItem:canvas_node_item_int) =
    Hashtbl.add canvas_nodes graphName nodeItem

  method add_edge (graphName:string) (edgeItem:canvas_edge_item_int) =
    Hashtbl.add canvas_edges graphName edgeItem 

end

let canvas_items = new canvas_items_t
