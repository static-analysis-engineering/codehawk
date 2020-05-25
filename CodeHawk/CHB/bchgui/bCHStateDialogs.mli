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

(* bchlib *)
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant

val about_codehawk: unit -> unit
  
val show_register_state_dialog: dw_index_t -> GWindow.window -> unit
  
val show_invariant_dialog: location_int -> GWindow.window -> unit
  
val show_function_metrics_dialog: dw_index_t -> GWindow.window -> unit
  
val show_summary_dialog: dw_index_t -> GWindow.window -> unit
  
val show_types_dialog: dw_index_t -> GWindow.window -> unit
  
val show_stack_state_dialog: dw_index_t -> GWindow.window -> unit
  
val show_reg_stack_state_dialog: dw_index_t -> GWindow.window -> unit
  
(* val show_reg_stack_type_dialog    : dw_index_t -> GWindow.window -> unit *)
  
val show_chif_dialog: dw_index_t -> GWindow.window -> unit
  
val show_callers_dialog:
  dw_index_t -> (doubleword_int list -> unit) -> GWindow.window -> unit
  
val show_callees_dialog:
  dw_index_t -> (doubleword_int list -> unit) -> GWindow.window -> unit
  
val show_dll_calls_dialog: dw_index_t -> GWindow.window -> unit
  
val show_gvars_dialog: dw_index_t -> GWindow.window -> unit
  
val show_lib_callers_dialog:
  string
  -> floc_int list
  -> (doubleword_int list -> unit)
  -> GWindow.window
  -> unit
  
val show_external_inputs_dialog:
  string
  -> (floc_int * (string list)) list
  -> (doubleword_int list -> unit)
  -> GWindow.window
  -> unit
  
val show_external_effects_dialog:
  string
  -> (floc_int * ((string * string) list)) list
  -> (doubleword_int list -> unit)
  -> GWindow.window
  -> unit
