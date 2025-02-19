(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
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
open CHIntervals
open CHPretty

(* chutil *)
open CHLoopStructure
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

class type sidechannelcheck_int =
  object

    (* setters *)
    method set_path_cost: int -> 'a -> unit

    (* accessors *)
    method get_cmsix         : int
    method get_decision_pc   : int
    method get_observation_pc: int
    method get_path_pcs      : int list
    method get_path_cost     : int -> 'a

    (* xml *)
    method write_xml: xml_element_int -> unit

    (* printing *)
    method cost_to_pretty: 'a -> pretty_t
    method toPretty: pretty_t
  end

class type costmodel_int =
object

  (* utility *)
  method mk_bottom: 'a
  method mk_top   : 'a
  method cost_join: 'a -> 'a -> 'a
  method cost_add : 'a -> 'a -> 'a
  method cost_mult: 'a -> 'a -> 'a

  (* setters *)
  method set_methodcost   : int -> 'a -> unit
  method set_loopstructure: int -> loop_structure_int -> unit

  (* accessors *)
  method get_blockcost : int -> int -> int -> 'a
  method get_loopbound : int -> int -> jterm_range_int

  (* predicates *)
  method has_loopbound : int -> int -> bool

  (* converters *)
  method jterm_range_to_cost: int -> int -> jterm_range_int -> 'a
  method cost_to_interval         : 'a -> interval_t

  (* xml *)
  method write_xml_cost: xml_element_int -> 'a -> unit
  method save_xml_class: class_info_int -> unit
  method save_xml_atlas_class: class_info_int -> unit
  method read_xml_cost: xml_element_int -> unit
  method read_xml_class: class_info_int -> unit


  (* printing *)
  method cost_to_pretty: 'a -> pretty_t

end
