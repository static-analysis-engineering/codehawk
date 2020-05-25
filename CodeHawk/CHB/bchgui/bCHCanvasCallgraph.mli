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

(* chlib *)
open CHLanguage

(* chgui *)
open CHCanvasBase

(* bchlib *)
open BCHLibTypes

class type canvas_call_graph_int =
object
  method reset: unit
  method system_call_graph_to_dot: canvas_window_int -> unit
  method sub_call_graph_to_dot: dw_index_t -> canvas_window_int -> unit
  method sub_rv_call_graph_to_dot: dw_index_t -> canvas_window_int -> unit
  method trace_graph_to_dot: dw_index_t -> int -> canvas_window_int -> unit
  method trace_rv_to_dot: dw_index_t -> variable_t -> canvas_window_int -> unit
  method trace_se_to_dot:
           dw_index_t -> floc_int -> variable_t -> canvas_window_int -> unit
end

val canvas_call_graph: canvas_call_graph_int
