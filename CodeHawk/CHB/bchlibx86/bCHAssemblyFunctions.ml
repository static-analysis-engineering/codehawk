(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHCallgraph
open BCHDemangler
open BCHDoubleword
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHJavaSignatures
open BCHLibTypes
open BCHLocation
open BCHMetricsHandler
open BCHSystemInfo
open BCHSystemSettings

(* bchlibx86 *)
open BCHAssemblyInstructions
open BCHLibx86Types
open BCHX86OpcodeRecords

module H = Hashtbl
module P = Pervasives
module FFU = BCHFileFormatUtil

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
    
    
class assembly_functions_t:assembly_functions_int =
object (self)
  
  val functions = H.create 53
  val mutable callgraph_order = None    (* cache bottom-up traversal order of call graph *)
    
  method reset = H.clear functions
    
  method add_function (f:assembly_function_int) = 
    H.add functions f#get_address#index f

  method replace_function (f:assembly_function_int) =
    H.replace functions f#get_address#index f

  method get_num_functions = H.length functions

  method get_num_complete_functions = 
    List.length (List.filter (fun f -> f#is_complete) self#get_functions)

  method get_num_basic_blocks =
    List.fold_left (fun a f -> a + f#get_block_count) 0 self#get_functions

  (* returns: number of instructions that depend on a condition-code status flag   *)
  method get_num_conditional_instructions =
    List.fold_left 
      (fun (c,a,t) f ->
	let (cf,af,tf) = f#get_num_conditional_instructions in (c+cf,a+af,t+tf)) 
      (0,0,0) self#get_functions

  method get_num_indirect_calls =
    List.fold_left
      (fun (c,r) f -> 
	let (cf,rf) = f#get_num_indirect_calls in (c+cf,r+rf)) (0,0) self#get_functions

  method get_functions = H.fold (fun _ v a -> v::a) functions []

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
    let table = H.create 37 in
    let add faddr ctxta =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      if H.mem table a#index then 
	H.replace table a#index ((H.find table a#index) + 1)
      else
	H.add table a#index 1 in
    let _ =
      List.iter (fun f ->
          f#iteri (fun faddr a _ -> add faddr a)) self#get_functions in
    let fnsAdded = ref [] in
    let pfaddr = ref wordzero in
    let reset () = pfaddr := wordzero in
    let p1 a = pfaddr := a in
    let p2 () =
      begin
        pverbose [ STR "add function by preamble: " ; !pfaddr#toPretty ; NL ] ;
        ignore (functions_data#add_function !pfaddr) ;
        fnsAdded := !pfaddr :: !fnsAdded ;
        reset ()
      end in
    let _ = !assembly_instructions#itera (fun a instr ->
      if H.mem table a#index then reset () else
	let bytes = (instr#get_instruction_bytes) in
	if !pfaddr#equal wordzero && (String.length bytes) = 1 && 
	  Char.code (String.get bytes 0) = 85 (* 0x55 : push ebp *) then
	  p1 a
	else if wordzero#lt !pfaddr && ((!pfaddr)#add_int 1)#equal a && 
	    (String.length bytes) = 2 && 
	       (let c1 = Char.code (String.get bytes 0) in
		let c2 = Char.code (String.get bytes 1) in
		((c1 = 139 && c2 = 236) (* 8b ec: mov ebp, esp *)
		    || (c1 = 137 && c2 = 229))) then p2 ()    (* 89 e5: mov ebp, esp *)
	else reset () ) in
    begin
      chlog#add "initialization"
	(LBLOCK [ STR "Add " ; INT (List.length !fnsAdded) ; 
		  STR " functions by preamble" ]) ;
      !fnsAdded
    end
      
  method dark_matter_to_string =
    let table = H.create 37 in
    let add faddr ctxta =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      if H.mem table a#index then 
	H.replace table a#index ((H.find table a#index) + 1)
      else
	H.add table a#index 1 in
    let _ = List.iter (fun f -> f#iteri (fun faddr a _ -> add faddr a)) self#get_functions in
    let filter = (fun i -> 
      not ((H.mem table i#get_address#index) || i#is_nop)) in
    !assembly_instructions#toString ~filter ()

  method duplicates_to_string =
    let table = H.create 37 in
    let add faddr ctxta =
      let a = (ctxt_string_to_location faddr ctxta)#i in
      if H.mem table a#index then
        H.replace table a#index ((H.find table a#index) + 1)
      else
        H.add table a#index 1 in
    let _ =
      List.iter (fun f ->
          f#iteri (fun faddr a _ -> add faddr a)) self#get_functions in
    let filter = (fun i ->
        (H.mem table i#get_address#index)
        && ((H.find table i#get_address#index) > 1)) in
    !assembly_instructions#toString ~filter ()

  method get_function_stats =
    let table = H.create 37 in
    let largeentries = ref [] in
    let addentry flen =
      let entry = if H.mem table flen then
                    H.find table flen
                  else 0 in
      H.replace table flen (entry + 1) in
    let add f =
      let flen = f#get_instruction_count in
      if flen <= 10 then
        addentry 10
      else if flen <= 100 then
        addentry 100
      else if flen  <= 1000 then
        addentry  1000
      else
        begin
          largeentries := f :: !largeentries
        end in
    let _ = List.iter add self#get_functions in
    let entries = List.sort P.compare (H.fold (fun k v a -> (k,v)::a) table []) in
    (entries,!largeentries)
    
  method get_application_functions = self#get_functions

  method get_statically_linked_functions = []

  method get_function (index:dw_index_t) =
    try
      H.find functions index
    with
      Not_found ->
	let msg = [ STR "Unable to find function with index " ; 
		    dw_index_to_pretty index ] in
	begin
	  pr_debug (msg @ [ NL ]) ;
	  raise (BCH_failure (LBLOCK msg))
	end

  method get_function_by_address (address:doubleword_int) = 
    self#get_function address#index

  method get_containing_function (va:doubleword_int) =
    let result = H.fold
      (fun index f found ->
	match found with Some _ -> found | _ -> 
	  if f#includes_instruction_address va then 
	    Some index 
	  else None) functions None in
    match result with
	Some index -> index_to_doubleword index
      | _ ->
	raise (BCH_failure 
		 (LBLOCK [ STR "No function found that contains address " ; 
			   va#toPretty ]))

  method get_opcode_stats =
    let stats = H.create 53 in
    let add s = if H.mem stats s then 
	H.replace stats s ((H.find stats s) + 1) 
      else
	H.add stats s 1 in
    begin
      self#iter (fun f ->
	f#iteri (fun _ _ instr -> add (get_opcode_long_name instr#get_opcode))) ;
      H.fold (fun k v a -> (k,v) :: a) stats []
    end

  method get_opcode_group_stats =
    let stats = H.create 53 in
    let add s = if H.mem stats s then 
	H.replace stats s ((H.find stats s) + 1) 
      else
	H.add stats s 1 in
    begin
      self#iter (fun f ->
	f#iteri (fun _ _ instr -> add (get_opcode_group instr#get_opcode))) ;
      H.fold (fun k v a -> (k,v) :: a) stats []
    end


  method get_callgraph =
    let callgraph = make_callgraph () in
    let _ = self#itera (fun _ f -> f#populate_callgraph callgraph) in
    callgraph

  method private get_bottomup_function_list =
    match callgraph_order with Some l -> l | _ ->
      let calls = ref [] in
      let _ = self#itera (fun faddr _ ->
	let finfo = get_function_info faddr in
	let appCallees = 
	  List.fold_left (fun acc c -> 
	    match c with AppTarget a -> a::acc | _ -> acc) [] finfo#get_callees in
	calls := (List.map (fun callee -> (faddr, callee)) appCallees) @ !calls) in
      let addresses = List.map (fun f -> f#get_address) self#get_functions in
      let (orderedList,stats,cycle) = create_ordering addresses !calls in
      let _ = chlog#add "callgraph order"
	(LBLOCK [ pretty_print_list stats (fun s -> INT s) "[" "; " "]" ;
		  (if cycle then STR " (cycle)" else STR "" ) ]) in
      let _ = callgraph_order <- Some orderedList in
      orderedList

      
  method bottom_up_itera (f:doubleword_int -> assembly_function_int -> unit) =
    let orderedList = self#get_bottomup_function_list in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#get_address afn) orderedFunctions
      
  method top_down_itera (f:doubleword_int -> assembly_function_int -> unit) =
    let orderedList = List.rev self#get_bottomup_function_list in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#get_address afn) orderedFunctions
      
  method iter (f:assembly_function_int -> unit) =
    List.iter (fun assemblyFunction -> f assemblyFunction) self#get_functions

  method itera (f:doubleword_int -> assembly_function_int -> unit) =
    List.iter (fun assemblyFunction -> 
      f assemblyFunction#get_address assemblyFunction) self#get_functions

  method has_function_by_address (va:doubleword_int) = H.mem functions va#index

  method includes_instruction_address (va:doubleword_int)=
    H.fold 
      (fun _ f found ->
        if found then true else f#includes_instruction_address va) functions false

end

let assembly_functions = new assembly_functions_t

let get_assembly_function (faddr:doubleword_int) =
  assembly_functions#get_function_by_address faddr



let get_export_metrics () =
  if FFU.has_export_directory_table () then
    let table = FFU.get_export_directory_table () in
    let names = List.map snd table#get_exported_function_names in
    { exm_count = List.length names ;
      exm_cpp = List.length (List.filter has_demangled_name names) ;
      exm_java = List.length (List.filter is_java_native_method_name names)
    }
  else
    exports_metrics_handler#init_value

let get_disassembly_metrics () = 
  let (coverage,overlap,alloverlap) = assembly_functions#get_function_coverage in
  let instrs = !assembly_instructions#get_num_instructions in
  let imported_imports = 
    if FFU.has_import_directory_table () then
      let table = FFU.get_import_directory_table () in
      List.map (fun e -> 
	let dll = e#get_name in
	let summaries = List.fold_left (fun acc f ->
	  if function_summary_library#has_dll_function dll f then acc + 1 else acc)
	  0 e#get_functions in
	(e#get_name,List.length e#get_functions, summaries,false)) table
    else [] in
  let loaded_imports =
    let imports = system_info#get_lib_functions_loaded in
    List.map (fun (dll,fns) ->
      let summaries = List.fold_left (fun acc f ->
	if function_summary_library#has_dll_function dll f then acc + 1 else acc)
	0 fns in
      (dll,List.length fns, summaries, true)) imports in
  let imports = imported_imports @ loaded_imports in
  { dm_unknown_instrs = !assembly_instructions#get_num_unknown_instructions ;
    dm_instrs = instrs ;
    dm_functions = assembly_functions#get_num_functions ;
    dm_coverage = coverage ;
    dm_pcoverage = 100.0 *. (float_of_int coverage) /. (float_of_int instrs) ;
    dm_overlap = overlap ;
    dm_alloverlap = alloverlap ;
    dm_jumptables = List.length system_info#get_jumptables ;
    dm_datablocks = List.length system_info#get_data_blocks ;
    dm_imports = imports ;
    dm_exports = get_export_metrics ()
  }
