(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny Sipma

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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

module H = Hashtbl


let get_stack_top_slot (mInfo: method_info_int) (pc: int) =
  (mInfo#get_method_stack_layout#get_stack_layout pc)#get_top_slot


let get_stack_top_slots (mInfo: method_info_int) (pc: int) (n: int) =
  (mInfo#get_method_stack_layout#get_stack_layout pc)#get_top_slots n


let get_cost_registers (mInfo: method_info_int) =
  let result = ref [] in
  begin
    (mInfo#bytecode_iteri (fun pc opc ->
      match opc with
      | OpStore (Long,r) ->
	begin
	  let slot = get_stack_top_slot mInfo pc in
	  match slot#get_sources with
	  | [opSrc] ->
	    begin
	      match mInfo#get_opcode opSrc with
	      | OpGetStatic (cn,fs)
		  when (cn#simple_name = "SingleCounter") && (fs#name = "value") ->
		result := r :: !result
	      | _ -> ()
	    end
	  | _ -> ()
	end
      | _ -> ()));
    !result
  end


let get_increments (mInfo: method_info_int) registers firstpc lastpc =
  let result = ref [] in
  begin
    (mInfo#bytecode_iteri (fun pc opc ->
      if pc < firstpc || pc > lastpc then () else
	match opc with
	| OpAdd _ ->
	  let slots = get_stack_top_slots mInfo pc 2 in
	  let vslot = List.hd (List.tl slots) in
	  begin
	    match vslot#get_sources with
	    | [opSrc] ->
	      begin
		match mInfo#get_opcode opSrc with
		| OpLoad (Long,r) when List.mem r registers -> ()
(*		  if cslot#has_value then
		    match cslot#get_value with
		    | LongValueRange (Some low,Some high) when Big_int.eq_big_int low high ->
		      result := (Big_int.int_of_big_int low) :: !result
		    | IntValueRange (Some low,Some high) when low = high ->
		      result := low :: !result
		    | _ -> ()
		  else
		    ()   *)
		| _ -> ()
	      end
	    | _ -> ()
	  end
	| _ -> ()));
    !result
  end


class bc_block_t
  (mInfo:method_info_int) (firstpc:int) (lastpc:int) (succ:int list):bc_block_int =
object
  method get_firstpc = firstpc

  method get_lastpc = lastpc

  method get_successors = succ

  method get_cost =
    match get_cost_registers mInfo with
    | [] -> 0
    | l ->
      let incrs = get_increments mInfo l firstpc lastpc in
      List.fold_left (fun acc incr -> acc + incr) 0 incrs

  method iter (f:int -> opcode_t -> unit) =
    let pcs =
      let rec aux pc result =
	if pc = lastpc then
	  pc :: result
	else
	  aux (mInfo#get_next_bytecode_offset pc) (pc :: result) in
      List.rev (aux firstpc []) in
    List.iter (fun pc -> f pc (mInfo#get_opcode pc)) pcs

end

let get_node_name i = "pc=" ^ (string_of_int i)


class bc_graph_t (succ:(int * int) list):bc_graph_int =
object

  method getRootNode = new symbol_t ~seqnr:0 (get_node_name 0)

  method getNextNodes (s:symbol_t) =
    let index = s#getSeqNumber in
    let edges = List.filter (fun (s,_) -> s = index) succ in
    List.map (fun (_,t) -> new symbol_t ~seqnr:t (get_node_name t)) edges

end

let make_bc_graph (succ:(int * int) list) = new bc_graph_t succ


let get_block_succ (code: opcodes_int) (pc: int) =
  let opc = code#at pc in
  match opc with
  | OpGoto off -> [pc + off]
  | OpIfEq off | OpIfNe off | OpIfLt off | OpIfGe off | OpIfGt off | OpIfLe off
  | OpIfNull off | OpIfNonNull off
  | OpIfCmpEq off | OpIfCmpNe off | OpIfCmpLt off | OpIfCmpGe off | OpIfCmpGt off
  | OpIfCmpLe off | OpIfCmpAEq off | OpIfCmpANe off ->
    begin
      match code#next pc with
      | Some nextpc -> [nextpc; pc + off]
      | _ ->
         raise
           (JCH_failure
              (LBLOCK [
                   STR "Missing next instruction for pc = "; INT pc]))
    end
  | OpTableSwitch (default,_,_,a) ->
    (pc + default) :: (Array.fold_left (fun acc i -> (pc + i) :: acc) [] a)
  | OpLookupSwitch (default,l) ->
    (pc + default) :: (List.fold_left (fun acc (_,i) -> (pc + i) :: acc) [] l)
  | OpReturn _ -> []
  | OpThrow -> []
  | _ -> match code#next pc with
    | Some i -> [i]
    | _ -> []

let get_block_entries (code:opcodes_int) =
  let s = new IntCollections.set_t in
  let addnext i = match code#next i with Some j -> s#add j | _ -> () in
  begin
    code#iteri (fun pc opc ->
      match opc with
      | OpGoto off
        | OpIfEq off
        | OpIfNe off
        | OpIfLt off
        | OpIfGe off
        | OpIfGt off
        | OpIfLe off
        | OpIfNull off
        | OpIfNonNull off
        | OpIfCmpEq off
        | OpIfCmpNe off
        | OpIfCmpLt off
        | OpIfCmpGe off
        | OpIfCmpGt off
        | OpIfCmpLe off
        | OpIfCmpAEq off
        | OpIfCmpANe off ->
	 begin
           s#add (pc + off);
           addnext pc
         end
      | OpTableSwitch (default, _, _, a) ->
	 let l =
           (pc + default)
           :: (Array.fold_left (fun acc i -> (pc + i) :: acc) [] a) in
	s#addList l
      | OpLookupSwitch (default, l) ->
	 let l =
           (pc + default)
           :: (List.fold_left (fun acc (_,i) -> (pc + i) :: acc) [] l) in
	s#addList l
      | OpReturn _ -> addnext pc
      | OpThrow -> addnext pc
      | _ -> ());
    s
  end


let get_bc_block
      (mInfo: method_info_int)
      (code: opcodes_int)
      (pc: int)
      (blockentries: IntCollections.set_t) =
  match code#next pc with
  | None ->
     let succ = get_block_succ code pc in
     new bc_block_t mInfo pc pc succ
  | Some nextpc ->
     let rec findlast (currpc:int) (prevpc:int) =
       if blockentries#has currpc then prevpc
       else match code#next currpc with
            | Some i -> findlast i currpc
            | _ -> currpc in
     let lastpc = findlast nextpc pc in
     let succ = get_block_succ code lastpc in
     new bc_block_t mInfo pc lastpc succ


let get_bc_function_basic_blocks (mInfo: method_info_int) =
  let code = mInfo#get_bytecode#get_code in
  let blockentries = get_block_entries code in
  let blocks = ref [] in
  let workset = new IntCollections.set_t in
  let doneset = new IntCollections.set_t in
  let successors = ref [] in
  let addtoworkset pc = if doneset#has pc then () else workset#add pc in
  let rec add_block (pc:int) =
    let block = get_bc_block mInfo code pc blockentries in
    let blocksucc = block#get_successors in
    begin
      workset#remove pc;
      doneset#add pc;
      blocks := block :: !blocks;
      successors := (List.map (fun succ -> (pc,succ)) blocksucc) @ !successors;
      List.iter addtoworkset blocksucc;
      match workset#choose with Some wpc -> add_block wpc | _ -> ()
    end in
  let _ = add_block 0 in
  let handlers =
    List.fold_left (fun acc h ->
        if List.mem h#handler acc then
          acc
        else h#handler :: acc) [] mInfo#get_exception_table in
  let _ = List.iter add_block handlers in
  let blocks =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_firstpc b2#get_firstpc) !blocks in
  (blocks,!successors)


let get_cfg_loop_levels
    (_mInfo: method_info_int) (blocks:bc_block_int list)(succ:(int * int) list) =
  let table = H.create 3 in
  let looplevels = H.create 3 in
  let graph = make_bc_graph succ in
  let sccs = (new wto_engine_t graph)#computeWTO in
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
    List.iter (fun b ->
      if H.mem table b#get_firstpc then
	let levels = H.find table b#get_firstpc in
	H.add looplevels b#get_firstpc (List.rev levels)) blocks;
    looplevels
  end


let get_max_loop_levels (mInfo:method_info_int) =
  let (blocks,succ) = get_bc_function_basic_blocks mInfo in
  let cfglooplevels = get_cfg_loop_levels mInfo blocks succ in
  H.fold
    (fun _ v m -> let len = List.length v in if len > m then len else m)
    cfglooplevels 0
