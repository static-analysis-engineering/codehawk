(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma and Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

(* jchcost *)
open JCHCostBounds

val dbg : bool ref

val get_timecost_diagnostics : unit -> pretty_t
val save_timecost_diagnostics: unit -> unit

class sidechannelcheck_t : int -> int -> int ->
  object
    method get_cmsix : int
    method get_decision_pc : int
    method get_observation_pc : int
    method get_path_cost : int -> cost_bounds_t
    method get_path_pcs : int list
    method set_path_cost : int -> cost_bounds_t -> unit
    method toPretty : pretty_t
    method write_xml : xml_element_int -> unit
    method write_xml_cost:
             ?tag:string -> xml_element_int -> cost_bounds_t -> unit
  end

class costmodel_t : sidechannelcheck_t list ->
  object
    method add_to_coststore_final : int -> cost_bounds_t -> unit
    method compute_block_cost : int -> int -> int -> cost_bounds_t
    method get_block_cost : int -> int -> cost_bounds_t
    method get_loop_cost : int -> int -> cost_bounds_t
    method get_loopbound : int -> int -> jterm_range_int
    method get_sidechannelspecs : int -> (int * int) list
    method has_loopbound : int -> int -> bool
    method mk_bottom : cost_bounds_t
    method mk_top : cost_bounds_t
    method print_cost_stores : unit -> unit
    method read_xml_cost :
             ?tag:string -> xml_element_int -> cost_bounds_t
    method read_xml_class : class_info_int -> unit
    method save_xml_class : class_info_int -> unit
    method save_xml_atlas_class: class_info_int -> unit
    method set_loop_cost : int -> int -> cost_bounds_t -> unit
    method set_loopstructure :
             int -> CHLoopStructure.loop_structure_int -> unit
    method set_methodcost : int -> cost_bounds_t -> unit
    method set_sidechannelcost :
             int -> int -> int -> int -> cost_bounds_t -> unit
    method write_xml_cost :
             ?tag:string -> xml_element_int -> cost_bounds_t -> unit
  end

val set_symbolic_defaults : bool -> unit
