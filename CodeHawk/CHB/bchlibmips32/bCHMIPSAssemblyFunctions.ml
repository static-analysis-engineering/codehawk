(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma

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
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHCallgraph
open BCHDoubleword
open BCHFunctionData
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHMetricsHandler
open BCHSystemInfo

(* bchlibmips32 *)
open BCHMIPSAssemblyFunction
open BCHMIPSAssemblyInstructions
open BCHMIPSOpcodeRecords   
open BCHMIPSTypes

module H = Hashtbl
module P = Pervasives

module IntSet = Set.Make
    (struct
      type t = int
      let compare = Pervasives.compare
    end)

let create_ordering 
    (functions:doubleword_int list) 
    (calls:(doubleword_int * doubleword_int) list)  =
  let get_pivot_node cs fnIndices =
    let counts = H.create 10 in
    let add dw = if H.mem counts dw then 
	H.replace counts dw ((H.find counts dw) + 1)
      else
	H.add counts dw 1 in
    let maxCount = ref ((fst (List.hd cs))#index,-1) in
    let _ = List.iter (fun (_,callee) -> add callee#index) cs in
    let _ = H.iter (fun k v -> 
      if v > (snd !maxCount) && List.mem k fnIndices then maxCount := (k,v)) counts in
    (index_to_doubleword (fst !maxCount),snd !maxCount) in
  let rec aux fns cs result stats cycle =
    match fns with 
      [] -> (result,stats,cycle)
    | _ ->
      let (leaves,nonleaves) = 
	List.fold_left (fun (l,n) (f:doubleword_int) ->
	  if (List.exists (fun ((caller,_):(doubleword_int * doubleword_int)) -> 
	    caller#equal f) cs) then 
	    (l,f::n) 
	  else 
	    (f::l,n)) ([],[]) fns in
      try
	match leaves with
	  [] ->  (* there is a cycle; find the node with the largest number of incoming 
		    edges and remove one of the	outgoing edges from that node
		    pass list of functions to avoid pivoting on a non-existing function *)
	    let fnIndices = List.map (fun dw -> dw#index) fns in
	    let (pivotNode,incoming) = get_pivot_node cs fnIndices in  
	    let edge = 
	      try
		List.find (fun (c,_) -> c#equal pivotNode) cs
	      with
		Not_found ->
		  begin
		    ch_error_log#add "pivot node not found"
		      (LBLOCK [ pivotNode#toPretty ]) ;
		    raise Not_found
		  end in
	    let newCalls = List.filter 
	      (fun (e1,e2) -> 
		(not (e1#equal (fst edge))) || (not (e2#equal (snd edge)))) cs in  	    
	    let _ = chlog#add "break cycle" 
	      (LBLOCK [ STR "remove " ; STR "(" ; 
			(fst edge)#toPretty ; STR "," ; (snd edge)#toPretty ;
			STR ") with " ; INT incoming ; STR " edges (size of cycle: " ;
			INT (List.length fns) ; STR ")" ]) in
	    aux nonleaves newCalls result ((-1)::stats) true
	| _ ->
	  let newCalls = 
	    List.filter (fun (_,callee) -> 
	      List.for_all (fun f -> not (callee#equal f)) leaves) cs in
	  aux nonleaves newCalls (result@leaves) ((List.length leaves)::stats) cycle 
      with 
	Not_found ->
	  begin
	    ch_error_log#add "error in find cycle" 
	      (LBLOCK [ STR "calls: " ; pretty_print_list cs 
		(fun (a1,a2) ->
		  LBLOCK [ STR "(" ; a1#toPretty ; STR "," ; a2#toPretty ; STR ")" ]) 
		" [" ", " "]" ]) ;
	    (result,stats,cycle)
	  end
  in
  aux functions calls [] [] false
    

class mips_assembly_functions_t:mips_assembly_functions_int =
object (self)

  val functions = H.create 53
  val mutable callgraphorder = None

  method reset = H.clear functions

  method add_function (f:mips_assembly_function_int) =
    H.add functions f#get_address#index f

  method inline_blocks =
    self#iter
      (fun f ->
        let fdata = functions_data#get_function f#get_address in
        if fdata#has_inlined_blocks then
          begin
            H.replace
              functions
              f#get_address#index
              (inline_blocks_mips_assembly_function
                 fdata#get_inlined_blocks f) ;
            chlog#add
              "mips assembly function:inline blocks" f#get_address#toPretty
          end)

  method get_functions = H.fold (fun _ v a -> v::a) functions []

  method get_function (index:dw_index_t) =
    try
      H.find functions index
    with
    | Not_found ->
       let msg = [ STR "Unable to find function with index: " ;
                   dw_index_to_pretty index ] in
       begin
         pr_debug (msg @ [ NL ]) ;
         raise (BCH_failure (LBLOCK msg))
       end

  method get_function_by_address (faddr:doubleword_int) =
    try
      self#get_function faddr#index
    with
    | BCH_failure _ ->
       let msg = [ STR "Unable to find function with address: " ;
                   faddr#toPretty ] in
       begin
         pr_debug (msg @ [ NL ]) ;
         raise (BCH_failure (LBLOCK msg))
       end

  method get_callgraph =
    let callgraph = make_callgraph () in
    let _ = self#itera (fun _ f -> f#populate_callgraph callgraph) in
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
	calls := (List.map (fun callee -> (faddr, callee)) appCallees) @ !calls) in
      let addresses = List.map (fun f -> f#get_address) self#get_functions in
      let (orderedList,stats,cycle) = create_ordering addresses !calls in
      let _ = chlog#add "callgraph order"
	(LBLOCK [ pretty_print_list stats (fun s -> INT s) "[" "; " "]" ;
		  (if cycle then STR " (cycle)" else STR "" ) ]) in
      let _ = callgraphorder <- Some orderedList in
      orderedList

      
  method bottom_up_itera (f:doubleword_int -> mips_assembly_function_int -> unit) =
    let orderedList = self#get_bottomup_function_list in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#get_address afn) orderedFunctions
      
  method top_down_itera (f:doubleword_int -> mips_assembly_function_int -> unit) =
    let orderedList = List.rev self#get_bottomup_function_list in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#get_address afn) orderedFunctions
      
  method iter (f:mips_assembly_function_int -> unit) =
    List.iter (fun assemblyFunction -> f assemblyFunction) self#get_functions

  method itera (f:doubleword_int -> mips_assembly_function_int -> unit) =
    List.iter (fun assemblyFunction -> 
        f assemblyFunction#get_address assemblyFunction) self#get_functions

  method get_function_coverage =
    let table = H.create 37 in
    let add faddr ctxta =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      if H.mem table a#index then 
	H.replace table a#index ((H.find table a#index) + 1)
      else
	H.add table a#index 1 in
    let _ = List.iter (fun f -> f#iteri (fun faddr a _ -> add faddr a)) self#get_functions in
    let overlap = ref 0 in
    let multiple = ref 0 in
    let _ = 
      H.iter (fun _ v -> if v = 1 then () else 
	  begin overlap := !overlap + 1 ; multiple := !multiple + (v-1) end) table in
    (H.length table, !overlap, !multiple)

  method add_functions_by_preamble =
    let preambles = H.create 3 in
    let preamble_instrs = H.create 3 in
    let _ =    (* collect preambles of regular functions *)
      self#itera (fun faddr f ->
          let instr = f#get_instruction faddr in
          let instrs = instr#get_instruction_bytes in
          let entry =
            if H.mem preambles instrs then
              H.find preambles instrs
            else
              begin
                H.add preambles instrs 0;
                H.add preamble_instrs instrs instr;
                0
              end in
          H.replace preambles instrs (entry + 1)) in
    let _ =    (* log the results *)
      H.iter (fun k v ->
          chlog#add
            "function preambles"
            (LBLOCK [ (H.find preamble_instrs k)#toPretty ; STR " (" ;
                      STR (byte_string_to_printed_string k) ; STR "): ";
                      INT v ])) preambles in
    let maxentry = ref 0 in
    let maxpreamble = ref "" in
    let _ =    (* find the most common preamble *)
      H.iter (fun k v ->
          if v > !maxentry then
            begin
              maxentry := v;
              maxpreamble := k
            end) preambles in
    let commonpreambles =
      H.fold (fun k v a -> if v >= 8 then k :: a else a) preambles [] in
    let is_common_preamble bytes =
      List.fold_left (fun a p -> a || p = bytes) false commonpreambles in
    let fnsAdded = ref [] in
    let _ =     (* check instructions for function entry points *)
      !mips_assembly_instructions#itera (fun a instr ->
          if H.mem functions a#index then
            ()
                                         (* else if instr#get_instruction_bytes = !maxpreamble then *)
          else if is_common_preamble instr#get_instruction_bytes then
            let fndata = functions_data#add_function a in
            begin
              fnsAdded := a :: !fnsAdded;
              fndata#set_by_preamble
            end
          else
            ()) in
    let _ =
      chlog#add
        "initialization"
        (LBLOCK [ STR "Add " ; INT (List.length !fnsAdded) ;
                  STR " functions by preamble" ]) in
    !fnsAdded

  method dark_matter_to_string =
    let table = H.create 37 in
    let add faddr ctxta  =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      if H.mem  table a#index then
        H.replace table a#index ((H.find table a#index) + 1)
      else
        H.add table a#index 1 in
    let _ = List.iter (fun f-> f#iteri (fun faddr a _ -> add faddr a)) self#get_functions in
    let filter = (fun i -> not (H.mem table i#get_address#index)) in
    !mips_assembly_instructions#toString ~filter ()
    
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

let mips_assembly_functions = new mips_assembly_functions_t

let get_mips_assembly_function (faddr:doubleword_int) =
  mips_assembly_functions#get_function_by_address faddr
    
let get_export_metrics () = exports_metrics_handler#init_value

let get_mips_disassembly_metrics () = 
  let (coverage,overlap,alloverlap) = mips_assembly_functions#get_function_coverage in
  let instrs = !mips_assembly_instructions#get_num_instructions in
  let imported_imports = [] in 
  let loaded_imports = [] in
  let imports = imported_imports @ loaded_imports in
  { dm_unknown_instrs = !mips_assembly_instructions#get_num_unknown_instructions ;
    dm_instrs = instrs ;
    dm_functions = mips_assembly_functions#get_num_functions ;
    dm_coverage = coverage ;
    dm_pcoverage = 100.0 *. (float_of_int coverage) /. (float_of_int instrs) ;
    dm_overlap = overlap ;
    dm_alloverlap = alloverlap ;
    dm_jumptables = List.length system_info#get_jumptables ;
    dm_datablocks = List.length system_info#get_data_blocks ;
    dm_imports = imports ;
    dm_exports = get_export_metrics ()
  }
