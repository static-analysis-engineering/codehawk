(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs, LLC

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
open BCHUtilities

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMAssemblyFunction
open BCHARMAssemblyInstructions
open BCHARMTypes

module H = Hashtbl
module TR = CHTraceResult


module IntSet = Set.Make
    (struct
      type t = int
      let compare = Stdlib.compare
    end)


(* Maximum number of cycles tolerated in the bottom-up ordering *)
let max_cycles = 10


let preamble_exclusions = H.create 3
let _ =
  List.iter (fun (b, t) -> H.add preamble_exclusions b t)
    [("0028",     "CMP          R0, #0");
     ("0029",     "CMP          R1, #0");
     ("002a",     "CMP          R2, #0");
     ("000050e3", "CMP          R0, #0x0");
     ("000051e3", "CMP          R1, #0x0");
     ("000052e3", "CMP          R2, #0x0");
     ("0030d0e5", "LDRB         R3, [R0, #0]");
     ("0010a0e3", "MOV          R1, #0x0");
     ("0110a0e3", "MOV          R1, #0x1");
     ("54110fe3", "MOVW         R1, #0xf154");
     ("24120fe3", "MOVW         R1, #0xf224");
     ("d01b08e3", "MOVW         R1, #0x8bd0");
     ("401b08e3", "MOVW         R1, #0x8b40");
     ("6c160be3", "MOVW         R1, #0xb66c");
     ("a81804e3", "MOVW         R1, #0x48a8");
     ("741b0fe3", "MOVW         R1, #0xfb74");
     ("681305e3", "MOVW         R1, #0x5368");
     ("f41b04e3", "MOVW         R1, #0x4bf4");
    ]


let create_ordering
    (functions: doubleword_int list)
    (calls: (doubleword_int * doubleword_int) list) =
  let fns_included = included_functions () in
  if ((List.length fns_included) > 0) || (List.length functions > 5000) then
    (functions, [], true)
  else
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

    let rec aux fns cs result stats cycle counter =
      if counter > max_cycles then
        begin
          ch_error_log#add
            "too many cycles"
            (LBLOCK [
                 STR "Abandon bottom-up iteration after encountering ";
                 INT max_cycles;
                 STR " cycles. Return original function list"]);
          (functions, stats, true)
        end
      else
        match fns with
        | [] -> (result, stats, cycle)
        | _ ->
           let (leaves, nonleaves) =
	     List.fold_left (fun (l,n) (f:doubleword_int) ->
	         if (List.exists (fun ((caller,_):(doubleword_int * doubleword_int)) ->
	                 caller#equal f) cs) then
	           (l, f::n)
	         else
	           (f::l, n)) ([], []) fns in
           try
	     match leaves with
	     | [] ->
                (* there is a cycle; find the node with the largest number of incoming
	      edges and remove one of the outgoing edges from that node
	      pass list of functions to avoid pivoting on a non-existing function *)
	        let fnIndices = List.map (fun dw -> dw#index) fns in
	        let (pivotNode, incoming) = get_pivot_node cs fnIndices in
	        let edge =
	          try
		    List.find (fun (c, _) -> c#equal pivotNode) cs
	          with
	          | Not_found ->
		     begin
		       ch_error_log#add "pivot node not found"
		         (LBLOCK [ pivotNode#toPretty ]);
		       raise Not_found
		     end in
	        let newCalls =
                  List.filter
	            (fun (e1, e2) ->
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
	        aux nonleaves newCalls result ((-1)::stats) true (counter + 1)
	     | _ ->
	        let newCalls =
	          List.filter (fun (_, callee) ->
	              List.for_all (fun f -> not (callee#equal f)) leaves) cs in
	        aux
                  nonleaves
                  newCalls
                  (result @leaves )
                  ((List.length leaves)::stats)
                  cycle
                  counter
           with
           | Not_found ->
	      begin
	        ch_error_log#add
                  "error in find cycle"
	          (LBLOCK [
                       STR "calls: ";
                       pretty_print_list
                         cs
                         (fun (a1,a2) ->
		           LBLOCK [
                               STR "(";
                               a1#toPretty;
                               STR ",";
                               a2#toPretty;
                               STR ")"])
		         " [" ", " "]" ]) ;
	        (result, stats, cycle)
	      end
    in
    aux functions calls [] [] false 0


class arm_assembly_functions_t:arm_assembly_functions_int =
object (self)

  val functions = H.create 53

  val mutable callgraphorder = None

  method reset = H.clear functions

  method add_function (f:arm_assembly_function_int) =
    H.replace functions f#get_address#index f

  method remove_function (faddr: doubleword_int) =
    H.remove functions faddr#index

  method inline_blocks =
    self#iter (fun f ->
        let fdata = functions_data#get_function f#get_address in
        if fdata#has_inlined_blocks then
          begin
            H.replace
              functions
              f#get_address#index
              (inline_blocks_arm_assembly_function fdata#get_inlined_blocks f);
            chlog#add
              "arm assembly function:inline blocks" f#get_address#toPretty
          end)

  method apply_path_contexts =
    self#iter (fun f ->
        let fdata = functions_data#get_function f#get_address in
        if fdata#has_path_contexts then
          List.iter (fun (startaddr, sentinels) ->
              begin
                H.replace
                  functions
                  f#get_address#index
                  (create_path_contexts startaddr sentinels f);
                chlog#add
                  "arm assembly function: create path contexts"
                  f#get_address#toPretty
              end) fdata#get_path_contexts)

  method get_functions = H.fold (fun _ v a -> v :: a) functions []

  method get_function (index:dw_index_t) =
    try
      H.find functions index
    with
    | Not_found ->
       let msg = [
           STR "Unable to find function with index: ";
           dw_index_to_pretty index] in
       begin
         pr_debug (msg @ [NL]);
         raise (BCH_failure (LBLOCK msg))
       end

  method get_function_by_address (faddr:doubleword_int) =
    try
      self#get_function faddr#index
    with
    | BCH_failure _ ->
       let msg = [
           STR "Unable to find function with address: ";
           faddr#toPretty] in
       begin
         pr_debug (msg @ [NL]);
         pr_debug [STR "Number of functions present: "; INT (H.length functions); NL];
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
	calls :=
          (List.map (fun callee -> (faddr, callee)) appCallees) @ !calls) in
      let addresses = List.map (fun f -> f#get_address) self#get_functions in
      let _ =
        pverbose [STR (timing ()); STR "Create ordering on functions ..."; NL] in
      let (orderedList,stats,cycle) = create_ordering addresses !calls in
      let _ =
        chlog#add "callgraph order"
	  (LBLOCK [
               pretty_print_list stats (fun s -> INT s) "[" "; " "]";
	       (if cycle then STR " (cycle)" else STR "")]) in
      let _ = callgraphorder <- Some orderedList in
      orderedList

  method bottom_up_itera (f:doubleword_int -> arm_assembly_function_int -> unit) =
    let orderedList = self#get_bottomup_function_list in
    let _ =
      pverbose [
          STR (timing ());
          STR "  obtained bottom-up-ordered function list";
          NL] in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#get_address afn) orderedFunctions

  method top_down_itera (f:doubleword_int -> arm_assembly_function_int -> unit) =
    let orderedList = List.rev self#get_bottomup_function_list in
    let orderedFunctions = List.map self#get_function_by_address orderedList in
    List.iter (fun afn -> f afn#get_address afn) orderedFunctions

  method iter (f:arm_assembly_function_int -> unit) =
    List.iter (fun assemblyFunction -> f assemblyFunction) self#get_functions

  method itera (f:doubleword_int -> arm_assembly_function_int -> unit) =
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
    let add_library_stub_instr (iaddr:doubleword_int) =
      if H.mem table iaddr#index then
        ()
      else
        H.add table iaddr#index 1 in
    let add_library_stub (faddr:doubleword_int) =
      begin
        add_library_stub_instr faddr;
        add_library_stub_instr (faddr#add_int 4);
        add_library_stub_instr (faddr#add_int 8);
      end in
    let _ =
      List.iter (fun f ->
          f#iteri (fun faddr a _ -> add faddr a)) self#get_functions in
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
        self#get_functions;
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
          f#iteri (fun faddr a _ -> add faddr a)) self#get_functions in
    table

  method add_functions_by_preamble =
    let instrtable = self#get_live_instructions in
    let preambles = H.create 3 in
    let preamble_instrs = H.create 3 in
    let _ =   (* collect preambles of regular functions *)
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
            (LBLOCK [
                 (H.find preamble_instrs k)#toPretty;
                 STR " (";
                 STR (byte_string_to_printed_string k);
                 STR "): ";
                 INT v])) preambles in
    let maxentry = ref 0  in
    let maxpreamble = ref "" in
    let _ =    (* find the most common preamble *)
      H.iter (fun k v ->
          if v > !maxentry then
            begin
              maxentry := v;
              maxpreamble := k
            end) preambles in
    let commonpreambles =
      let preamble_cutoff_factor = system_info#get_preamble_cutoff in
      let preamble_cutoff_factor =
        if preamble_cutoff_factor > 0 then
          preamble_cutoff_factor
        else
          10 in
      let preamble_cutoff = self#get_num_functions / preamble_cutoff_factor in
      H.fold (fun k v a ->
          if v >= preamble_cutoff then k :: a else a) preambles [] in
    let is_common_preamble bytes =
      List.fold_left (fun a p -> a || p = bytes) false commonpreambles in
    let fnsAdded = ref [] in
    let _ =
      !arm_assembly_instructions#itera
        (fun a instr ->
          if H.mem functions a#index then
            ()
          else if H.mem instrtable instr#get_address#index then
            ()
          else if H.mem
                    preamble_exclusions
                    (byte_string_to_printed_string instr#get_instruction_bytes) then
            ()
          else if (match instr#get_opcode with
                   | LoadRegister _ | Move _ -> true | _ -> false) then
            ()
          else if ((is_common_preamble instr#get_instruction_bytes)
                   || (match instr#get_opcode with
                       | Push (_, _, rlist,_)
                            when List.mem ARLR rlist#get_register_list -> false
                       | _ -> false)) then
            let fndata = functions_data#add_function a in
            begin
              fnsAdded := a :: !fnsAdded;
              fndata#set_by_preamble;
              chlog#add
                "function added by preamble"
                (LBLOCK [
                     STR (byte_string_to_printed_string instr#get_instruction_bytes);
                     STR ": ";
                     a#toPretty])
            end
          else ()) in
    let _ =
      chlog#add
        "initialization"
        (LBLOCK [
             STR "Add ";
             INT (List.length !fnsAdded);
             STR " functions by preamble"]) in
    !fnsAdded

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
    let dark = !arm_assembly_instructions#toString ~filter () in
    let functionstats = self#get_function_stats in
    dark ^ "\n\n" ^ functionstats

  method private collect_data_references =
    let _ = pverbose [STR (timing ()); STR "collect data references ..."; NL] in
    let livetable = self#get_live_instructions in
    let filter = (fun i -> H.mem livetable i#get_address#index) in
    let table = H.create 11 in
    let add (a: doubleword_int) (instr: arm_assembly_instruction_int) =
      let ixa = a#index in
      let entry =
        if H.mem table ixa then
          H.find table ixa
        else
          [] in
      H.replace table ixa (instr::entry) in
    begin
      !arm_assembly_instructions#itera
        (fun va instr ->
          if filter instr then
            match instr#get_opcode with
            | LoadRegister (_, _, _, _, mem, _) when mem#is_pc_relative_address ->
               let pcoffset = if instr#is_arm32 then 8 else 4 in
               let a = mem#get_pc_relative_address va pcoffset in
               if elf_header#is_program_address a then
                 add a instr
               else
                 ch_error_log#add
                   "LDR from non-code-address"
                   (LBLOCK [va#toPretty; STR " refers to "; a#toPretty])
            | LoadRegister (_, _, _, _, mem, _) when mem#is_literal_address ->
               let a = mem#get_literal_address in
               if elf_header#is_program_address a then
                 add a instr
               else
                 ch_error_log#add
                   "LDR (literal) from non-code-address"
                   (LBLOCK [va#toPretty; STR " refers to "; a#toPretty])
            | VLoadRegister (_, vd, _, mem) when mem#is_pc_relative_address ->
               let pcoffset = if instr#is_arm32 then 8 else 4 in
               let a = mem#get_pc_relative_address va pcoffset in
               if elf_header#is_program_address a then
                 begin
                   add a instr;
                   if (vd#get_size = 8) then add (a#add_int 4) instr;
                 end
               else
                 ch_error_log#add
                   "VLDR from non-code-address"
                   (LBLOCK [va#toPretty; STR " refers to "; a#toPretty])
            | _ -> ());
      pverbose [STR (timing ()); STR "  collect data references: done"; NL];
      table
    end

  method get_data_references =
    let datarefs = self#collect_data_references in
    H.fold (fun k v a ->
        let dw = TR.tget_ok (index_to_doubleword k) in
        (dw#to_hex_string, v) :: a) datarefs []

  method identify_dataref_datablocks =
    let datareftable = self#collect_data_references in
    let table = self#get_live_instructions in
    let filter = (fun i ->
        let index = i#get_address#index in
        (index mod 4) = 0
        && (not (H.mem table index))
        && (H.mem datareftable index)) in
    let dbstart = ref wordzero in
    let inBlock = ref false in
    let count = ref 0 in
    let fnremoved = ref 0 in
    begin
      !arm_assembly_instructions#itera
        (fun va instr ->
          match instr#get_opcode with
          | OpInvalid -> ()
          | NotCode _ -> ()
          | _ ->
             try
               if filter instr then
                 begin
                   (if not !inBlock then
                      begin
                        dbstart := va;
                        inBlock := true
                      end);
                   (match instr#get_opcode with
                    | BranchLink (_, op)
                      | BranchLinkExchange (_, op) when op#is_absolute_address ->
                       let tgtaddr = op#get_absolute_address in
                       if functions_data#is_function_entry_point tgtaddr then
                         let fndata = functions_data#get_function tgtaddr in
                         let remaining = fndata#remove_callsite in
                         if remaining = 0 then
                           begin
                             functions_data#remove_function tgtaddr;
                             self#remove_function tgtaddr;
                             fnremoved := !fnremoved + 1;
                             chlog#add
                               "remove function"
                               (LBLOCK [
                                    STR "call: ";
                                    va#toPretty;
                                    STR ": ";
                                    tgtaddr#toPretty])
                           end
                    | _ -> ())
                 end
               else if (instr#get_address#index mod 4) > 0 then
                 ()
               else if !inBlock then
                 let db =
                   TR.tget_ok
                     (make_data_block !dbstart va "inferred-dataref blocks") in
                 let dblen = TR.tget_ok (va#subtract_to_int !dbstart) in
                 let datastring =
                   try
                     elf_header#get_xsubstring !dbstart dblen
                   with
                   | BCH_failure p ->
                      begin
                        ch_error_log#add
                          "datablock: get_xsubstring"
                          (LBLOCK [
                               STR "Datablock: ";
                               !dbstart#toPretty;
                               STR " - ";
                               va#toPretty;
                               STR ": ";
                               p]);
                        raise (BCH_failure p)
                      end in
                 let _ = db#set_data_string datastring in
                 begin
                   chlog#add
                     "add data block"
                     (LBLOCK [
                          db#get_start_address#toPretty;
                          STR " - ";
                          db#get_end_address#toPretty;
                          STR ": ";
                          STR db#get_name]);
                   system_info#add_data_block db;
                   inBlock := false;
                   count := !count + 1;
                   !arm_assembly_instructions#set_not_code [db]
                 end
               else
                 ()
             with
             | BCH_failure p ->
                let msg =
                     LBLOCK [
                         STR "Error in identifying dataref datablocks: ";
                         p] in
                ch_error_log#add "identifying datablocks" msg);
      chlog#add
        "identify data-blocks"
        (LBLOCK [STR "Identified "; INT !count; STR " data-blocks"]);
    end

  method identify_datablocks =
    let inprogress = ref true in
    while !inprogress do
      if self#identify_datablocks_aux = 0 then
        inprogress := false
    done

  method private identify_datablocks_aux =
    let _ = pverbose [STR (timing ()); STR " get_live_instructions ..."; NL] in
    let table = self#get_live_instructions in
    let _ = pverbose [STR (timing ()); STR " collect_data_references ..."; NL] in
    let datareftable = self#collect_data_references in
    let filter = (fun i -> not (H.mem table i#get_address#index)) in
    let dbstart = ref wordzero in
    let inBlock = ref false in
    let notcode = ref false in
    let count = ref 0 in
    let fnremoved = ref 0 in
    begin
      !arm_assembly_instructions#itera
        (fun va instr ->
          try
            if filter instr then
              match instr#get_opcode with
              | OpInvalid -> ()
              | NotCode _ -> ()
              | _ ->
                 begin
                   if not !inBlock then
                     begin
                       dbstart := va;
                       inBlock := true;
                     end;
                   (if H.mem datareftable instr#get_address#index then
                      notcode := true);
                   (match instr#get_opcode with
                    | NotRecognized (itxt, idw) ->
                       begin
                         notcode := true;
                         chlog#add
                           "block out not-recognized"
                           (LBLOCK [
                                va#toPretty;
                                STR ": ";
                                STR itxt;
                                STR " (";
                                idw#toPretty;
                                STR ")"])
                       end
                    | BranchLink (_, op)
                      | BranchLinkExchange (_, op) when op#is_absolute_address ->
                       let tgtaddr = op#get_absolute_address in
                       if functions_data#is_function_entry_point tgtaddr && !notcode then
                         let fndata = functions_data#get_function tgtaddr in
                         let remaining = fndata#remove_callsite in
                         if remaining = 0 then
                           begin
                             functions_data#remove_function tgtaddr;
                             self#remove_function tgtaddr;
                             fnremoved := !fnremoved + 1;
                             chlog#add
                               "remove function"
                               (LBLOCK [
                                    STR "call: ";
                                    va#toPretty;
                                    STR ": ";
                                    tgtaddr#toPretty])
                           end
                    | _ -> ())
                 end
            else
              if !inBlock then
                if !notcode then
                  let db = TR.tget_ok (make_data_block !dbstart va "inferred") in
                  let dblen = TR.tget_ok (va#subtract_to_int !dbstart) in
                  let datastring =
                    try
                      elf_header#get_xsubstring !dbstart dblen
                    with
                    | BCH_failure p ->
                       begin
                         ch_error_log#add
                           "datablock: get_xsubstring"
                           (LBLOCK [
                                STR "Datablock: ";
                                !dbstart#toPretty;
                                STR " - ";
                                va#toPretty;
                                STR ": ";
                                p]);
                         raise (BCH_failure p)
                       end in
                  let _ = db#set_data_string datastring in
                  begin
                    system_info#add_data_block db;
                    inBlock := false;
                    notcode := false;
                    count := !count + 1;
                    !arm_assembly_instructions#set_not_code [db]
                  end
                else
                  inBlock := false
              else
                ()
          with
          | BCH_failure p ->
             let msg =
                  LBLOCK [
                      STR "Error in identifying data blocks: ";
                      va#toPretty;
                      STR ": ";
                      p] in
             ch_error_log#add "identifying datablocks" msg);
      chlog#add
        "identify data-blocks"
        (LBLOCK [STR "Identified "; INT !count; STR " data-blocks"]);
      !fnremoved
    end

  method set_datablocks =
    let table = self#get_live_instructions in
    let filter = (fun i -> not (H.mem table i#get_address#index)) in
    let dbstart = ref wordzero in
    let inBlock = ref false in
    let count = ref 0 in
    begin
      !arm_assembly_instructions#itera
        (fun va instr ->
          try
            if filter instr then
              match instr#get_opcode with
              | OpInvalid -> ()
              | NotCode _ -> ()
              | _ ->
                 if not !inBlock then
                   begin
                     dbstart := va;
                     inBlock := true
                   end
                 else
                   ()
            else
              if !inBlock then
                let db = TR.tget_ok (make_data_block !dbstart va "inferred") in
                begin
                  system_info#add_data_block db;
                  inBlock := false;
                  count := !count + 1
                end
          with
          | BCH_failure p ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Error in instruction: ";
                       va#toPretty;
                       STR ": ";
                       p])));
      chlog#add
        "set data-blocks"
        (LBLOCK [STR "Added "; INT !count; STR " data blocks"])
    end

  method duplicates_to_string =
    let table = self#get_duplicate_instructions in
    let lines = ref [] in
    begin
      !arm_assembly_instructions#itera
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


let arm_assembly_functions = new arm_assembly_functions_t


let get_arm_assembly_function (faddr:doubleword_int) =
  arm_assembly_functions#get_function_by_address faddr


let get_export_metrics () = exports_metrics_handler#init_value


let get_arm_disassembly_metrics () =
  let (coverage, overlap, alloverlap) =
    arm_assembly_functions#get_function_coverage in
  let instrs = !arm_assembly_instructions#get_num_instructions in
  let imported_imports = [] in
  let loaded_imports = [] in
  let imports = imported_imports @ loaded_imports in
  let numunknown = !arm_assembly_instructions#get_num_unknown_instructions in
  { dm_unknown_instrs = numunknown;
    dm_instrs = instrs;
    dm_functions = arm_assembly_functions#get_num_functions;
    dm_coverage = coverage;
    dm_pcoverage = 100.0 *. (float_of_int coverage) /. (float_of_int instrs) ;
    dm_overlap = overlap;
    dm_alloverlap = alloverlap;
    dm_jumptables = List.length system_info#get_jumptables;
    dm_datablocks = List.length system_info#get_data_blocks;
    dm_imports = imports;
    dm_so_imports = system_info#dmso_metrics;
    dm_exports = get_export_metrics()
  }


let get_arm_data_references () = arm_assembly_functions#get_data_references
