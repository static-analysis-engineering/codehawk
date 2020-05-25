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


val data_entry_dialog:
  title:string
  -> label_1:string
  -> label_2:string
  -> action:(string -> string -> string option)
  -> parent:GWindow.window
  -> unit

val data1_entry_dialog:
  height:int
  -> width:int
  -> title:string
  -> label:string
  -> action:(string -> string option)
  -> parent:GWindow.window
  -> unit

val confirmation_dialog:
  title:string
  -> label:string
  -> yes_action:(unit -> unit)
  -> no_action:(unit -> unit)
  -> parent:GWindow.window
  -> unit

val select_section_dialog:
  window_title:string
  -> data:(int * string * string * string) list
  -> label_text:string
  -> parent_window:GWindow.window
  -> select_action:(int -> unit)
  -> unit

val make_colored_label: 
  ?fg_color:GDraw.color
  -> GDraw.color
  -> string
  -> (GObj.widget-> unit)
  -> unit
  -> unit
