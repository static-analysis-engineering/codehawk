(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023 Aarno Labs, LLC

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
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHCallgraph
open BCHDataBlock
open BCHDoubleword
open BCHFunctionData
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHMetricsHandler
open BCHSystemInfo
open BCHSystemSettings

(* bchlibelf *)
open BCHELFHeader

(* bchlibpower32 *)
open BCHPowerAssemblyFunction
open BCHPowerAssemblyInstructions
open BCHPowerOpcodeRecords
open BCHPowerTypes

module H = Hashtbl
module TR = CHTraceResult


module IntSet =
  Set.Make
    (struct
      type t = int
      let compare = Stdlib.compare
    end)


let create_ordering 
    (functions: doubleword_int list) 
    (calls: (doubleword_int * doubleword_int) list)  =
  let get_pivot_node cs fnIndices =
    let counts = H.create 10 in
    let add dw = if H.mem counts dw then 
	H.replace counts dw ((H.find counts dw) + 1)
      else
	H.add counts dw 1 in
    let maxCount = ref ((fst (List.hd cs))#index,-1) in
    let _ = List.iter (fun (_, callee) -> add callee#index) cs in
    let _ =
      H.iter (fun k v ->
          if v > (snd !maxCount)
             && List.mem k fnIndices then maxCount := (k, v)) counts in
    (TR.tget_ok (index_to_doubleword (fst !maxCount)), snd !maxCount) in

  let rec aux fns cs result stats cycle =
    match fns with 
    | [] -> (result,stats,cycle)
    | _ ->
      let (leaves,nonleaves) = 
	List.fold_left (fun (l,n) (f:doubleword_int) ->
	  if (List.exists (fun ((caller,_):(doubleword_int * doubleword_int)) -> 
	    caller#equal f) cs) then 
	    (l, f::n)
	  else 
	    (f::l, n)) ([], []) fns in
      try
	match leaves with
	  [] ->
           (* there is a cycle; find the node with the largest number of incoming
	      edges and remove one of the	outgoing edges from that node
	      pass list of functions to avoid pivoting on a non-existing function *)
	    let fnIndices = List.map (fun dw -> dw#index) fns in
	    let (pivotNode, incoming) = get_pivot_node cs fnIndices in  
	    let edge = 
	      try
		List.find (fun (c, _) -> c#equal pivotNode) cs
	      with
		Not_found ->
		  begin
		    ch_error_log#add "pivot node not found"
		      (LBLOCK [ pivotNode#toPretty ]);
		    raise Not_found
		  end in
	    let newCalls = List.filter 
	      (fun (e1,e2) -> 
		(not (e1#equal (fst edge))) || (not (e2#equal (snd edge)))) cs in
	    let _ =
              chlog#add "break cycle"
	        (LBLOCK [
                     STR "remove ";
                     STR "(";
		     (fst edge)#toPretty;
                     STR ",";
                     (snd edge)#toPretty;
		     STR ") with ";
                     INT incoming;
                     STR " edges (size of cycle: ";
		     INT (List.length fns);
                     STR ")"]) in
	    aux nonleaves newCalls result ((-1)::stats) true
	| _ ->
	  let newCalls = 
	    List.filter (fun (_,callee) -> 
	      List.for_all (fun f -> not (callee#equal f)) leaves) cs in
	  aux nonleaves newCalls (result@leaves) ((List.length leaves)::stats) cycle 
      with 
      | Not_found ->
	  begin
	    ch_error_log#add "error in find cycle" 
	      (LBLOCK [
                   STR "calls: ";
                   pretty_print_list cs 
		     (fun (a1,a2) ->
		       LBLOCK [
                           STR "(";
                           a1#toPretty;
                           STR ",";
                           a2#toPretty;
                           STR ")"]) 
		     " [" ", " "]" ]);
	    (result,stats,cycle)
	  end
  in
  aux functions calls [] [] false


class power_assembly_functions_t: power_assembly_functions_int =
object (self)

  val functions = H.create 53

  val mutable callgraphorder = None

  method reset = H.clear functions

  method add_function (f: power_assembly_function_int) =
    H.replace functions f#faddr#index f

  method remove_function (faddr: doubleword_int) =
    H.remove functions faddr#index

  method functions = H.fold (fun _ v a -> v :: a) functions []

  method get_function (index: dw_index_t) =
    if H.mem functions index then
      H.find functions index
    else
      let msg = [
          STR "Unable to find function with index: ";
          dw_index_to_pretty index] in
      begin
        pr_debug (msg @ [NL]);
        raise (BCH_failure (LBLOCK msg))
      end

  method get_function_by_address (faddr: doubleword_int) =
    if H.mem functions faddr#index then
      H.find functions faddr#index
    else
      let msg = [
          STR "Unable to find function with address: ";
          faddr#toPretty] in
      begin
        pr_debug (msg @ [NL]);
        raise (BCH_failure (LBLOCK msg))
      end

  method get_callgraph =
    let callgraph = make_callgraph () in
    let _ = self#itera (fun _ f ->f#populate_callgraph callgraph) in
    callgraph

  method private get_bottomup_function_list =
    match callgraphorder with Some l -> l | _ ->
      let calls = ref [] in
      let _ = self#itera (fun faddr _ ->
	let finfo = get_function_info faddr in
	let appCallees = 
	  List.fold_left (fun acc c -> 
	      if c#is_app_call then
                (c#get_app_address)::acc
              else
                acc) [] finfo#get_callees in
	calls :=
          (List.map (fun callee -> (faddr, callee)) appCallees) @ !calls) in
      let addresses = List.map (fun f -> f#faddr) self#functions in
      let (orderedList,stats,cycle) = create_ordering addresses !calls in
      let _ =
        chlog#add "callgraph order"
	  (LBLOCK [
               pretty_print_list stats (fun s -> INT s) "[" "; " "]";
	       (if cycle then STR " (cycle)" else STR "")]) in
      let _ = callgraphorder <- Some orderedList in
      orderedList

  method bottom_up_itera (f:doubleword_int -> power_assembly_function_int -> unit) =
    let orderedList = self#get_bottomup_function_list in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#faddr afn) orderedFunctions
      
  method top_down_itera (f:doubleword_int -> power_assembly_function_int -> unit) =
    let orderedList = List.rev self#get_bottomup_function_list in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#faddr afn) orderedFunctions
      
  method iter (f: power_assembly_function_int -> unit) =
    List.iter (fun afn -> f afn) self#functions

  method itera (f:doubleword_int -> power_assembly_function_int -> unit) =
    List.iter (fun afn -> f afn#faddr afn) self#functions

  method get_function_coverage =
    let table = H.create 37 in
    let add faddr ctxta =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      if H.mem table a#index then 
	H.replace table a#index ((H.find table a#index) + 1)
      else
	H.add table a#index 1 in
    let add_library_stub_instr (iaddr: doubleword_int) =
      if H.mem table iaddr#index then
        ()
      else
        H.add table iaddr#index 1 in
    let add_library_stub (faddr: doubleword_int) =
      begin
        add_library_stub_instr faddr;
        add_library_stub_instr (faddr#add_int 4);
        add_library_stub_instr (faddr#add_int 8);
      end in
    let _ =
      List.iter (fun f ->
          f#iteri (fun faddr a _ -> add faddr a)) self#functions in
    let _ =
      List.iter add_library_stub functions_data#get_library_stubs in
    let overlap = ref 0 in
    let multiple = ref 0 in
    let _ = 
      H.iter (fun _ v ->
          if v = 1 then
            ()
          else 
	    begin
              overlap := !overlap + 1;
              multiple := !multiple + (v-1)
            end) table in
    (H.length table, !overlap, !multiple)

  method private get_live_instructions =
    let table = H.create 37 in
    let add faddr ctxta =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      if H.mem table a#index then
        H.replace table a#index ((H.find table a#index) + 1)
      else
        H.add table a#index 1 in
    let add_library_stub_instr (iaddr: doubleword_int) =
      if H.mem table iaddr#index then
        ()
      else
        H.add table iaddr#index 1 in
    let add_library_stub (faddr: doubleword_int) =
      begin
        add_library_stub_instr faddr;
        add_library_stub_instr (faddr#add_int 4);
        add_library_stub_instr (faddr#add_int 8)
      end in
    begin
      List.iter (fun f ->
          f#iteri
            (fun faddr a _ -> add faddr a))
        self#functions;
      List.iter add_library_stub functions_data#get_library_stubs;
      table
    end

  method private get_duplicate_instructions =
    let table = H.create 37 in
    let add faddr ctxta =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      let entry =
        if H.mem table a#index then
          H.find table a#index
        else
          [] in
        H.add table a#index (faddr#to_hex_string :: entry) in
    let _ =
      List.iter (fun f ->
          f#iteri (fun faddr a _ -> add faddr a)) self#functions in
    table

  method private get_function_stats =
    let table = H.create self#get_num_functions in
    let _ =
      self#itera (fun faddr fn ->
          H.add
            table
            faddr#to_hex_string
            (fn#get_block_count,
             fn#get_instruction_count,
             fn#get_not_valid_instr_count)) in
    String.concat
      "\n"
      (List.map (fun (faddr, (blocks, instrs, notvalid)) ->
           (fixed_length_string faddr 12)
           ^ "  "
           ^ (fixed_length_string ~alignment:StrRight (string_of_int blocks) 8)
           ^ "  "
           ^ (fixed_length_string ~alignment:StrRight (string_of_int instrs) 8)
           ^ "  "
           ^ (if notvalid = 0 then
                ""
              else
                fixed_length_string ~alignment:StrRight (string_of_int notvalid) 8))
         (List.sort
            (fun (_, (b, i, _)) (_, (b2, i2, _)) -> Stdlib.compare (b, i) (b2, i2))
            (H.fold (fun k v a -> (k, v)::a) table [])))

  method dark_matter_to_string =
    let table = self#get_live_instructions in
    let filter = (fun i -> not (H.mem table i#get_address#index)) in
    let dark = !power_assembly_instructions#toString ~filter () in
    let functionstats = self#get_function_stats in
    dark ^ "\n\n" ^ functionstats

  method duplicates_to_string =
    let table = self#get_duplicate_instructions in
    let lines = ref [] in
    begin
      !power_assembly_instructions#itera
        (fun va instr ->
          if (H.mem table instr#get_address#index
              && (List.length (H.find table instr#get_address#index)) > 1) then
            let _ =
              if functions_data#is_function_entry_point va then
                lines := "" :: !lines in
            let line =
              va#to_hex_string
                ^ " "
                ^ (fixed_length_string instr#toString 32)
                ^ "["
                ^ (String.concat ", " (H.find table instr#get_address#index))
                ^ "]" in
            lines := line :: !lines);
      String.concat "\n" (List.rev !lines)
    end
    
  method get_num_functions = H.length functions
                           
  method has_function_by_address (va:doubleword_int) = H.mem functions va#index

  method includes_instruction_address (va:doubleword_int)=
    H.fold 
      (fun _ f found ->
        if found then
          true
        else
          f#includes_instruction_address va) functions false

end
    

let power_assembly_functions = new power_assembly_functions_t


let get_power_assembly_function (faddr: doubleword_int) =
  power_assembly_functions#get_function_by_address faddr


let get_export_metrics () = exports_metrics_handler#init_value


let get_power_disassembly_metrics () =
  let _ = pverbose [STR "Compute coverage: "; NL] in
  let (coverage, overlap, alloverlap) =
    power_assembly_functions#get_function_coverage in
  let _ = pverbose [STR "Get number of instructions: "; NL] in
  let instrs = !power_assembly_instructions#get_num_instructions in
  let _ = pverbose [STR "Get imports"; NL] in
  let imported_imports = [] in
  let loaded_imports = [] in
  let imports = imported_imports @ loaded_imports in
  let _ = pverbose [STR "Get unknown instructions: "; NL] in
  let numunknown = !power_assembly_instructions#get_num_unknown_instructions in
  let _ = pverbose [STR "Found "; INT numunknown; STR " instructions"; NL] in
  { dm_unknown_instrs = !power_assembly_instructions#get_num_unknown_instructions;
    dm_instrs = instrs;
    dm_functions = power_assembly_functions#get_num_functions;
    dm_coverage = coverage;
    dm_pcoverage = 100.0 *. (float_of_int coverage) /. (float_of_int instrs) ;    
    dm_overlap = overlap;
    dm_alloverlap = alloverlap;
    dm_jumptables = List.length system_info#get_jumptables;
    dm_datablocks = List.length system_info#get_data_blocks;
    dm_imports = imports;
    dm_exports = get_export_metrics()
  }
