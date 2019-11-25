(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
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

(* chlib *)
open CHAtlas

(* cchlib *)
open CCHLibTypes

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

val set_timeout_value: int -> unit

val extract_external_value_facts:
  c_environment_int
  -> invariant_io_int
  -> (string, (string,atlas_t) Hashtbl.t) Hashtbl.t
  -> unit

val extract_ranges:
  c_environment_int
  -> invariant_io_int
  -> (string, (string,atlas_t) Hashtbl.t) Hashtbl.t
  -> unit

val extract_pepr:
  c_environment_int
  -> invariant_io_int
  -> (string, (string,atlas_t) Hashtbl.t) Hashtbl.t
  -> unit
  
val extract_symbols:
  c_environment_int
  -> invariant_io_int
  -> (string, (string,atlas_t) Hashtbl.t) Hashtbl.t
  -> unit

val extract_states:
  c_environment_int
  -> invariant_io_int
  -> (string, (string,atlas_t) Hashtbl.t) Hashtbl.t
  -> unit

val extract_valuesets:
  c_environment_int
  -> invariant_io_int
  -> (string, (string,atlas_t) Hashtbl.t) Hashtbl.t
  -> unit

val extract_sym_pointersets:
  c_environment_int
  -> invariant_io_int
  -> (string, (string,atlas_t) Hashtbl.t) Hashtbl.t
  -> unit
