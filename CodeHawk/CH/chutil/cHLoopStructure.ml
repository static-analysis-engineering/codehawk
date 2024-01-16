(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright 9c) 2024      Aarno Labs LLC

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
open CHPretty
open CHSCC
open CHUtils

(* chutil *)
open CHLogger
open CHXmlDocument

module H = Hashtbl


let get_node_name i = new symbol_t ~seqnr:i (string_of_int i)


class bb_graph_t (root:int) (succ:(int * int) list):graph_t =
object

  method getRootNode = get_node_name root

  method getNextNodes (s:symbol_t) =
    let index = s#getSeqNumber in
    let edges = List.filter (fun (s,_) -> s = index) succ in
    List.map (fun (_,t) -> get_node_name t) edges

end


class type loop_structure_int =
object
  method get_loopheads    : int list
  method get_loop         : int -> int list
  method get_pc_loopheads : int -> int list
  method get_nesting_level: int -> int

  method is_loophead      : int -> bool
  method is_inloop        : int -> bool
  method is_inloop_with_loophead: int -> int -> bool

  method write_xml        : xml_element_int -> unit
end

(* -----------------------------------------------------------------------
 * looplevels: pc -> dominating loopheads
 * ----------------------------------------------------------------------- *)
class loop_structure_t (looplevels:(int, int list) H.t) =
object (self)

  method get_loopheads =
    let s = new IntCollections.set_t in
    let _ = H.iter (fun _ v -> s#addList v) looplevels in
    s#toList

  method get_loop (loophead:int) =
    let s = new IntCollections.set_t in
    let _ =
      H.iter (fun k v -> if List.mem loophead v then s#add k) looplevels in
    s#toList

  method get_pc_loopheads (pc:int) =
    if H.mem looplevels pc then H.find looplevels pc else []

  method get_nesting_level (pc:int) = List.length (self#get_pc_loopheads pc)

  method is_loophead (pc:int) = List.mem pc self#get_loopheads

  method is_inloop (pc:int) =
    (H.mem looplevels pc) &&
      (match H.find looplevels pc with [] -> false | _ -> true)

  method is_inloop_with_loophead (pc:int) (loophead:int) =
    (H.mem looplevels pc) &&
      (List.mem loophead (H.find looplevels pc))

  method write_xml (node:xml_element_int) =
    node#appendChildren (List.map (fun lh ->
      let lNode = xmlElement "loop" in
      let loop = self#get_loop lh in
      begin
	lNode#setIntAttribute "lh" lh;
	write_xml_indices lNode loop;
	lNode
      end) self#get_loopheads)

end


let get_loop_structure (root:int) (succ:(int * int) list):loop_structure_int =
  let sccs = (new wto_engine_t (new bb_graph_t root succ))#computeWTO in
  let table = H.create 3 in
  let looplevels = H.create 3 in
  let rec get_wto_head wto =
    match wto with
    | [] ->
      begin
	ch_error_log#add
          "invalid argument"
	  (STR "Encountered empty wto in get_cfg_loop_levels");
	raise (Invalid_argument "record loops")
      end
    | hd::_ -> get_wto_component_head hd
  and get_wto_component_head wtoComponent =
    match wtoComponent with
    | VERTEX s -> s
    | SCC scc -> get_wto_head scc in
  let rec record_wto wto levels =
    List.iter (fun wtoComponent -> record_wto_component wtoComponent levels) wto
  and record_wto_component wtoComponent levels =
    match wtoComponent with
    | VERTEX s -> H.add table s#getSeqNumber levels
    | SCC scc -> record_wto scc ((get_wto_head scc) :: levels) in
  begin
    (match sccs with [] -> () | _ -> record_wto sccs []);
    List.iter (fun (b,_) ->
      if H.mem table b then
	let levels = List.map (fun s -> s#getSeqNumber) (H.find table b) in
	H.add looplevels b (List.rev levels)
      else
	H.add looplevels b []) succ;
    new loop_structure_t looplevels
  end
