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

type dot_xreference_t = {
  get_color: string -> string ;
  get_alternate_text: string -> string list ;
  get_predicate: string -> string -> bool ;
  get_history : (string * int) list ;
  get_loops : (string * int) list ;
}

class type canvas_int =
object
  method newGraph: ?enable_bidirectional_edges:bool -> string -> CHDot.dot_graph_int
  method showGraph: ?xref:dot_xreference_t option -> string -> unit
  method showSubGraph: ?xref:dot_xreference_t option -> string -> string -> unit
  method initializeForJava: unit
  method initializeForBinary: unit
end

val canvas: canvas_int
