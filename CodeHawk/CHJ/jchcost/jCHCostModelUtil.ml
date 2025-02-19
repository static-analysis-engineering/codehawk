(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2025  Henny B. Sipma

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
open CHUtils

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

module Q = Queue

let replace_with_nops (bc:bytecode_int) (l:int list) =
  List.iter (fun pc -> bc#get_code#replace pc OpNop) l

let opcodesq: int Q.t = Q.create ()

let get_basic_blocks (bc:bytecode_int) =
  let code = bc#get_code in
  let blocks = new IntCollections.set_t in
  let bblocks = ref [] in
  let pcsprocessed = new IntCollections.set_t in
  let next_pc pc =
    match code#next pc with
    | Some i -> i
    | _ -> raise (JCH_failure (STR "Inconsistent bytecode #1")) in
  let make_block pc =
    let rec get_lastpc (tpc:int) (prev:int) =
      if blocks#has tpc then
	prev
      else match code#next tpc with
      | Some i -> get_lastpc i tpc
      | _ -> tpc in
    let lastpc =
      match code#next pc with
      | Some i -> get_lastpc i pc
      | _ -> pc in
    let successors =
      match code#at lastpc with
	| OpIfEq offset
	| OpIfNe offset
	| OpIfLt offset
	| OpIfGe offset
	| OpIfGt offset
	| OpIfLe offset
	| OpIfCmpEq offset
	| OpIfCmpNe offset
	| OpIfCmpLt offset
	| OpIfCmpGe offset
	| OpIfCmpGt offset
	| OpIfCmpLe offset
	| OpIfNull offset
	| OpIfNonNull offset
	| OpIfCmpAEq offset
	| OpIfCmpANe offset ->
	  let nextpc = next_pc lastpc in
	  let thenpc = lastpc + offset in
	  [nextpc; thenpc]
	| OpGoto offset -> [lastpc + offset]
	| OpTableSwitch (default, _low, _high, table) ->
	  let s = new IntCollections.set_t in
	  begin
	    Array.iter (fun offset -> s#add (lastpc + offset)) table;
	    s#add (lastpc + default);
	    s#toList
	  end
	| OpLookupSwitch (default, match_pairs) ->
	  let s = new IntCollections.set_t in
	  begin
	    List.iter (fun (_,offset) -> s#add (lastpc + offset)) match_pairs;
	    s#add (lastpc + default);
	    s#toList
	  end
        | OpThrow -> []
	| OpReturn _ -> []
	| _ -> [next_pc lastpc] in
    (pc, lastpc, successors) in
  begin
    Q.clear opcodesq;
    List.iter (fun h -> blocks#add h#handler) bc#get_exception_table;
    List.iter (fun h -> Q.add h#handler opcodesq) bc#get_exception_table;
    blocks#add 0;
    Q.add 0 opcodesq;
    while not (Q.is_empty opcodesq) do
      let pc = Q.take opcodesq in
      if pcsprocessed#has pc then () else
	let opcode = code#at pc in
	let _ = pcsprocessed#add pc in
	match opcode with
	| OpIfEq offset
	| OpIfNe offset
	| OpIfLt offset
	| OpIfGe offset
	| OpIfGt offset
	| OpIfLe offset
	| OpIfCmpEq offset
	| OpIfCmpNe offset
	| OpIfCmpLt offset
	| OpIfCmpGe offset
	| OpIfCmpGt offset
	| OpIfCmpLe offset
	| OpIfNull offset
	| OpIfNonNull offset
	| OpIfCmpAEq offset
	| OpIfCmpANe offset ->
	  let nextpc = next_pc pc in
	  let thenpc = pc + offset in
	  begin
	    Q.add nextpc opcodesq;
	    Q.add thenpc opcodesq;
	    blocks#add nextpc;
	    blocks#add thenpc;
	  end
	| OpGoto offset ->
	  let gotopc = pc + offset in
	  begin
	    Q.add gotopc opcodesq;
	    blocks#add gotopc
	  end
	| OpTableSwitch (default, _low, _high, table) ->
	  begin
	    Array.iter (fun offset ->
	      let tgt = pc + offset in
	      begin Q.add tgt opcodesq; blocks#add tgt end) table;
	    Q.add (pc + default) opcodesq;
	    blocks#add (pc + default)
	  end
	| OpLookupSwitch (default, match_pairs) ->
	  begin
	    List.iter (fun (_,offset) ->
	      let tgt = pc + offset in
	      begin Q.add tgt opcodesq; blocks#add tgt end) match_pairs;
	    Q.add (pc + default) opcodesq;
	    blocks#add (pc + default)
	  end
	| OpThrow | OpReturn _ -> ()
	| _ -> Q.add (next_pc pc) opcodesq
    done;
    blocks#iter (fun pc -> bblocks := (make_block pc) :: !bblocks);
    !bblocks
  end
