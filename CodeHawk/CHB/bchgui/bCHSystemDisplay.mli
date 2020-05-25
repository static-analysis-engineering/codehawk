(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Cody Schuffelen and Henny Sipma
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
open CHPretty

val check_interrupt: unit -> bool
val reset_interrupt: unit -> unit
val check_skip: unit -> bool
val reset_skip: unit -> unit

val set_progress_bar: int -> int -> unit
val reset_progress_bar: unit -> unit

val write_message   : string -> unit
val write_message_pp: pretty_t -> unit

val write_to_system_display   : string -> string -> unit
val write_to_system_display_pp: string -> pretty_t -> unit

val save_system_display_contents: unit -> unit

val window: GWindow.window
val menubar: GMenu.menu_shell

val main_notebook: GPack.notebook
val goto_system_page: unit -> unit

val set_functions_listed: string list -> unit
val get_functions_listed: unit -> string list
val has_function_listed : string -> bool
val add_function_listed : string -> bool         (* returns true if function was added *)
val clear_functions_listed: unit -> unit
