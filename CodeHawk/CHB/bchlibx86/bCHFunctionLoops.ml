(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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
open CHLanguage
open CHSCC
open CHIterator

(* chutil *)
open CHLogger

(* bchlib *)
open BCHDoubleword
open BCHLibTypes

module TR = CHTraceResult


class cfg_loops_t (cfg:cfg_int) =
object

  val table =
    let htable = Hashtbl.create 7 in
    let get_index (s:symbol_t) = (TR.tget_ok (symbol_to_doubleword s))#index in
    let rec get_wto_head wto =
      match wto with
      | [] ->
	 begin
	   ch_error_log#add
             "invalid argument" (STR "Encountered empty wto in record_loops");
	   raise (Invalid_argument "record_loops")
	 end
      | hd::_ -> get_wto_component_head hd
    and get_wto_component_head wtoComponent =
      match wtoComponent with
	VERTEX s -> TR.tget_ok (index_to_doubleword (get_index s))
      | SCC scc -> get_wto_head scc in
    let rec record_wto wto levels =
      List.iter (fun wtoComponent -> record_wto_component wtoComponent levels) wto
    and record_wto_component wtoComponent levels =
      match wtoComponent with
	VERTEX s -> Hashtbl.add htable (get_index s) levels
      | SCC scc -> record_wto scc ((get_wto_head scc) :: levels) in
    let engine = new wto_engine_t (new fwd_graph_t cfg) in
    let sccs = engine#computeWTO in
    let _ =
      match sccs with
      | [] -> ()
      | _ -> record_wto sccs [] in
    htable

  method get_loop_levels (ba:doubleword_int) =
    if Hashtbl.mem table ba#index then Hashtbl.find table ba#index else	[]

  method toPretty =
    let pp = ref [] in
    let _ =
      Hashtbl.iter (fun k l ->
          let p =
            LBLOCK [
                (TR.tget_ok (index_to_doubleword k))#toPretty;
                STR ": ";
		pretty_print_list l (fun b -> b#toPretty) "[" ", " "]";
                NL] in
          pp := p :: !pp) table in
    LBLOCK (List.rev !pp)

end


let make_cfg_loops (cfg:cfg_int) = new cfg_loops_t cfg
