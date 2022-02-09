(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHFunctionInfo
open BCHFloc
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation
open BCHSystemInfo
open BCHUtilities

(* bchlibx86 *)
open BCHFunctionLoops
open BCHLibx86Types
open BCHPredefinedCallSemantics
open BCHX86OpcodeRecords

module H = Hashtbl
module FFU = BCHFileFormatUtil


class assembly_function_t 
        (faddr:doubleword_int)                 (* function entry address *)
        (blocks:assembly_block_int list)       (* basic blocks, may be inlined *)
        (successors:(ctxt_iaddress_t * ctxt_iaddress_t) list)
      :assembly_function_int =
object (self)

  val mutable dll_stub = None
  val blocktable =
    let t = H.create 3 in
    let _ = List.iter (fun b -> H.add t b#get_context_string b) blocks in
    t
  val successortable =
    let t = H.create 3 in
    let _ = List.iter (fun (src,tgt) -> H.add t src tgt) successors in
    t

  method get_address = faddr

  method get_blocks = blocks

  method get_block (bctxt:ctxt_iaddress_t) =
    if H.mem blocktable bctxt then
      H.find blocktable bctxt
    else
      begin
	ch_error_log#add
          "invocation error"
	  (LBLOCK [STR "assembly_function#get_block: "; STR bctxt]);
	raise
          (BCH_failure
             (LBLOCK [
                  STR "No assembly block found at ";
                  STR bctxt;
                  STR " in function ";
                  faddr#toPretty]))
      end

  method get_block_count = List.length blocks

  method get_bytes_ashexstring =
    let s = ref "" in
    let _ = self#iter (fun b -> s := !s ^ b#get_bytes_ashexstring) in
    !s

  (* md5 of the hex representation of the function, not of the raw bytes *)
  method get_function_md5 =
    byte_string_to_printed_string (Digest.string self#get_bytes_ashexstring)

  method get_instruction_count = 
    List.fold_left (fun a b -> a + b#get_instruction_count) 0 blocks

  (* a function is a dll stub if the only action it performs is to call a dll
     function and return to the caller 
     Example:
     F B 0x407b02  55                              push ebp
         0x407b03  a1 88 c4 42 00                  mov eax, 0x42c488
         0x407b08  89 e5                           mov ebp, esp
         0x407b0a  c9                              leave
         0x407b0b  ff e0                           jmp* eax
  *)
  method is_dll_stub = match dll_stub with Some _ -> true | _ -> false

  method get_dll_stub =
    match dll_stub with 
    | Some (lib,fname) -> (lib,fname)
    | _ -> raise (BCH_failure (LBLOCK [ self#get_address#toPretty ; 
					STR " is not a dll stub" ]))

  method private check_dll_stub = ()

  method private is_esp_manipulating =
    let result = ref [] in
    let _ =
      self#iteri
        (fun faddr ctxtiaddr instr ->
          let iloc = ctxt_string_to_location faddr ctxtiaddr in
          let floc = get_floc iloc in
          if instr#is_esp_manipulating floc then result := ctxtiaddr :: !result) in
    !result
				 
  method get_stack_adjustment =
    let valid = ref true in
    let adjustments = ref [] in
    let _ =
      self#iteri
        (fun faddr ctxtiaddr instr ->
          let iloc = ctxt_string_to_location faddr ctxtiaddr in
          if iloc#has_context then
            ()
          else
            let iaddr = iloc#i in
            match instr#get_opcode with
            | Ret _ | BndRet _ ->
	       if system_info#is_goto_return iaddr then
                 ()
               else
	         let default () =
	           match instr#get_opcode with
	           | Ret None
                     | BndRet None  -> adjustments := 0 :: !adjustments
	           | Ret (Some n)
                     | BndRet (Some n) -> adjustments := n :: !adjustments
	           | _ -> () in
	         let floc = get_floc iloc in
	         let (level,offset) = floc#get_stackpointer_offset "x86" in
	         if level = 0 then
	           match offset#singleton with
	           | Some n when n#is_zero -> default ()
	           | Some n -> 
	              begin
	                chlog#add
                          "stack adjustment"
		          (LBLOCK [faddr#toPretty; STR ": offset is "; n#toPretty]);
	                valid := false
	              end
	           | _ ->
	              begin
	                match self#is_esp_manipulating with
	                | [] -> default ()
	                | l ->
		           begin
		             chlog#add
                               "stack adjustment"
		               (LBLOCK [
                                    faddr#toPretty;
                                    STR ": esp is manipulated at ";
			            pretty_print_list
                                      l (fun a -> STR a) "[" "," "]"]);
		             valid := false
		           end
	              end
	         else
	           begin
	             chlog#add
                       "stack adjustment"
	               (LBLOCK [faddr#toPretty; STR ": level is "; INT level]) ;
	             valid := false
	           end
            | IndirectJmp _ ->
	       let finfo = get_function_info faddr in
	       if finfo#is_dll_jumptarget ctxtiaddr then
	         let (dll,fname) = finfo#get_dll_jumptarget ctxtiaddr in
	         let _ = self#check_dll_stub in
	         let _ = function_summary_library#load_dll_library_function dll fname in
	         let adj =
                   if function_summary_library#has_dll_function dll fname then
	             (function_summary_library#get_dll_function dll fname)#get_stack_adjustment 
	           else None in
	         match adj with
	         | Some n -> adjustments := n :: !adjustments
	         | _ -> ()
	       else
	         ()
            | _ -> ()) in
    match !adjustments with
      [] -> None
    | h::tl ->
       if !valid then 
	 (if List.for_all (fun t -> h=t) tl then Some h else
	    begin
	      chlog#add
                "disassembly" 
		(LBLOCK [ STR "Inconsistent stack adjustments for " ; 
			  self#get_address#toPretty ; STR ": " ; 
			  pretty_print_list !adjustments (fun i -> INT i) "[" ";" "]" ]) ;
	      None
	    end)
       else
	 None
	     
  method get_num_conditional_instructions = 
    let nJumps = ref 0 in
    let _ = self#iteri 
      (fun _ _ instr -> 
	if is_conditional_instruction instr#get_opcode then nJumps := !nJumps + 1 ) in
    let finfo = get_function_info self#get_address in
    (!nJumps, finfo#get_num_conditions_associated, finfo#get_num_test_expressions)

  method get_num_indirect_calls = 
    let nCalls = ref 0 in
    let nResolved = ref 0 in
    let _ =
      self#iteri
        (fun _ ctxtiaddr instr ->
          let iloc = ctxt_string_to_location faddr ctxtiaddr in
	  match instr#get_opcode with
	    IndirectCall op ->	
	    let floc = get_floc iloc in
	    begin
	      nCalls := !nCalls + 1 ;
	      if floc#has_call_target
                 && floc#get_call_target#is_unknown then
                ()
              else
                nResolved := !nResolved + 1
	    end
	  | _ -> ()) in
    (!nCalls, !nResolved) 
      
  method populate_callgraph (callgraph:callgraph_int) = 
    let finfo = get_function_info faddr in
    self#iteri (fun _ ctxtiaddr instr ->
        let iloc = ctxt_string_to_location faddr ctxtiaddr in
        match instr#get_opcode with
	  DirectCall _ | IndirectCall _ | IndirectJmp _ ->
	  let floc = get_floc iloc in
	  let env = floc#f#env in
	  let argExprs =
            if floc#has_call_target
               && floc#get_call_target#is_signature_valid then
	      let fintf = floc#get_call_target#get_function_interface in
	      let parNames = get_stack_parameter_names fintf in
	      let argExprs =
		List.map (fun (index,name) ->
		  let argvar = env#mk_bridge_value floc#cia index in
		  let argvalue = floc#get_bridge_variable_value index argvar in
		  (index,name,argvalue) ) parNames in
	      argExprs
	    else
	      [] in
	  if finfo#has_call_target ctxtiaddr then
	    let rec add_call_target tgt =
	      match tgt with
              | StubTarget (SOFunction name)
                | StaticStubTarget (_, SOFunction name) ->
                 callgraph#add_so_edge faddr name ctxtiaddr argExprs
              | StubTarget (LinuxSyscallFunction index)
                | StaticStubTarget (_, LinuxSyscallFunction index) ->
                 callgraph#add_so_edge
                   faddr ("syscall-" ^ (string_of_int index)) ctxtiaddr argExprs
	      | StubTarget (DllFunction (_,name))
	        | StaticStubTarget (_, DllFunction(_,name)) -> 
		 callgraph#add_dll_edge faddr name ctxtiaddr argExprs
	      | AppTarget a -> callgraph#add_app_edge faddr a ctxtiaddr argExprs
              | StubTarget (PckFunction(_,pkgs,name)) 
	        | StaticStubTarget (_,PckFunction(_,pkgs,name)) ->
		 callgraph#add_dll_edge
                   faddr ((String.concat "::" pkgs) ^ name) ctxtiaddr argExprs
	      | InlinedAppTarget _ -> ()
	      | WrappedTarget(_,_,tgt,_) -> add_call_target tgt
	      | StubTarget (JniFunction n)
                | StaticStubTarget (_,JniFunction n) ->
                 callgraph#add_jni_edge faddr n ctxtiaddr argExprs
	      | VirtualTarget s ->
                 callgraph#add_virtual_edge faddr s ctxtiaddr argExprs
	      | UnknownTarget ->
                 callgraph#add_unresolved_edge faddr (-1) ctxtiaddr argExprs
              | CallbackTableTarget _ -> (* not implemented yet *) ()
	      | IndirectTarget (_,tgts) -> List.iter add_call_target tgts in
	    add_call_target (finfo#get_call_target ctxtiaddr)#get_target
	  else 
	    begin 
	      match instr#get_opcode with 
		IndirectCall _ ->
                 callgraph#add_unresolved_edge faddr (-1) ctxtiaddr argExprs
	      | _ -> ()
	    end
      | _ -> ())
      
  method iter (f:assembly_block_int -> unit) = 
    List.iter (fun block -> f block) self#get_blocks
    
  method itera (f:ctxt_iaddress_t -> assembly_block_int -> unit) =
    List.iter (fun block -> f block#get_context_string block) self#get_blocks
      
  method iteri
           (f:doubleword_int -> ctxt_iaddress_t -> assembly_instruction_int -> unit) =
    List.iter (fun (block:assembly_block_int) -> 
      block#itera (fun iaddr instr -> f faddr iaddr instr)) self#get_blocks

  method iter_calls (f:ctxt_iaddress_t -> floc_int -> unit) =
    self#iteri (fun _ ctxtiaddr instr ->
        let iloc = ctxt_string_to_location faddr ctxtiaddr in
      match instr#get_opcode with
      | DirectCall _ | IndirectCall _ -> f ctxtiaddr (get_floc iloc)
      | IndirectJmp _ when (get_function_info faddr)#is_dll_jumptarget ctxtiaddr ->
	f ctxtiaddr (get_floc iloc)
      | _ -> ())

  method can_be_inlined =
    if self#is_complete && self#get_block_count  = 1 then
      let result = ref true in
      let _ = self#iteri (fun _ _ instr ->
	if !result then
	  match instr#get_opcode with
	  | DirectCall _ | IndirectCall _ 
	  | DirectJmp _  | IndirectJmp _
	  | Jcc _ -> result := false
	  | _ -> ()) in
      !result
    else
      false

  method private get_unknown_instructions =
    let n = ref 0 in
    begin self#iteri (fun _ _ instr -> if instr#is_unknown then n := !n + 1) ; !n end
      
  method is_complete =
    let finfo = get_function_info self#get_address in
    let hasUnresolvedJumps = finfo#has_unknown_jump_target in
    let unknowns = self#get_unknown_instructions in
    (not hasUnresolvedJumps) &&	unknowns = 0 
      
  method is_nonreturning = List.for_all (fun b -> not b#is_returning) self#get_blocks

  method includes_instruction_address (va:doubleword_int) =
    List.exists (fun b -> b#includes_instruction_address va) blocks
      
  method toPretty = 
    LBLOCK (List.map (fun block -> LBLOCK [ block#toPretty ; NL ]) blocks)

  method to_annotated_pretty =
    LBLOCK [ 
      NL ; NL ; STR (string_repeat "~" 80) ; NL ;
      faddr#toPretty ; 
      (if functions_data#has_function_name faddr then
	 LBLOCK [ STR " (" ; STR (functions_data#get_function faddr)#get_function_name ;
                  STR ")" ]
       else STR "") ; NL ;
      STR (string_repeat "~" 80) ; NL ;
      LBLOCK (List.map (fun block -> LBLOCK [ block#to_annotated_pretty ; NL ]) blocks)
    ]
    
  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let addr = self#get_address in
    let bbNode = xmlElement "blocks" in
    begin
      node#setAttribute "a" addr#to_hex_string ;
      (if functions_data#has_function_name addr then
         let name = (functions_data#get_function addr)#get_function_name in
         let name =
           if has_control_characters name then
             "__xx__" ^ (hex_string name)
           else
             name in
	  node#setAttribute "fn" name) ;
      bbNode#appendChildren (List.map (fun block -> 
	let bNode = xmlElement "block" in
	begin block#write_xml bNode; bNode end) blocks) ;
      append [ bbNode ]
    end
      
  method private cfg_to_xml (cfg:cfg_int) =
    let cfgLoops = make_cfg_loops cfg in
    let node = xmlElement "cfg" in
    begin 
      node#appendChildren 
	(List.map (fun b -> b#to_xml cfgLoops) self#get_blocks) ; node end
      
end
  
let make_assembly_function
      (va:doubleword_int)
      (blocks:assembly_block_int list)
      (successors:(ctxt_iaddress_t * ctxt_iaddress_t) list) =
  let blocks =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string)
    blocks in
  let fn = new assembly_function_t va blocks successors in
  begin
    register_predefined_callsemantics 
      fn#get_bytes_ashexstring 
      fn#get_function_md5 
      fn#get_instruction_count
      fn#get_address ;
    FFU.register_exn_handler fn#get_address fn#get_bytes_ashexstring ;
   fn
  end
    
let get_op_metrics (f:assembly_function_int) (finfo:function_info_int) =
  let faddr = f#get_address in
  let reads = ref 0 in
  let qreads = ref 0 in
  let writes = ref 0 in
  let qwrites = ref 0 in
  let is_memory_op op = 
    match op#get_kind with
    | IndReg _ | ScaledIndReg _ -> true | _ -> false in
  let is_loc_unknown floc (op:operand_int) =
    let (v,_) = op#to_lhs floc in
    v#isTmp || (finfo#env#is_unknown_memory_variable v) in
  let add_read floc (op:operand_int) =
    if is_memory_op op then 
      begin 
	reads := !reads + 1 ; 
	if is_loc_unknown floc op then qreads := !qreads + 1
      end in
  let add_write floc (op:operand_int) =
    if is_memory_op op then
      begin
	writes := !writes + 1 ;
	if is_loc_unknown floc op then qwrites := !qwrites + 1
      end in
  let _ = f#iteri (fun _ ctxtiaddr instr ->
    let ops = get_operands instr#get_opcode in
    match ops with
    | [] -> ()
    | _ ->
       let loc = ctxt_string_to_location faddr ctxtiaddr in
       let floc = get_floc loc in
       List.iter (fun (op:operand_int) ->
	   match op#get_mode with
	   | RD -> add_read floc op 
	   | WR -> add_write floc op
	   | RW -> begin add_read floc op ; add_write floc op end
	   | AD -> ()) ops)  in
  (!reads,!qreads,!writes,!qwrites)

let get_esp_metrics (f:assembly_function_int) (finfo:function_info_int) =
  let faddr = f#get_address in
  let esptop = ref 0 in
  let esprange = ref 0 in
  let _ =
    f#iteri
      (fun _ ctxtiaddr _ ->
        let loc = ctxt_string_to_location faddr ctxtiaddr in
        let floc = get_floc loc in
        let (_,range) = floc#get_stackpointer_offset "x86" in
        if range#isTop then
          esptop := !esptop + 1
        else match range#singleton with 
               Some _ -> () | _ -> esprange := !esprange + 1) in
  (!esptop,!esprange)


let get_memory_access_metrics (f:assembly_function_int) (finfo:function_info_int) =
  let (reads,qreads,writes,qwrites) = get_op_metrics f finfo in
  let (esptop,esprange) = get_esp_metrics f finfo in
  { mmem_reads = reads ;
    mmem_qreads = qreads ;
    mmem_writes = writes ;
    mmem_qwrites = qwrites ;
    mmem_esptop = esptop ;
    mmem_esprange = esprange
  }
