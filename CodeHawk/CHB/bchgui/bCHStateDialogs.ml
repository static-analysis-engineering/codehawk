(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHNumerical
open CHNumericalConstraints
open CHLanguage
open CHIntervals
open CHValueSets
open CHSymbolicSets
open CHUtils

(* chutil *)
open CHPrettyUtil
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHDoubleword
open BCHFloc
open BCHFtsParameter
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHFunctionSummary
open BCHLibTypes
open BCHLocationInvariant
open BCHLocation
open BCHCPURegisters
open BCHMemoryReference
open BCHPreFileIO
open BCHSystemInfo
open BCHVariable
open BCHVariableNames

(* bchlibpe *)
open BCHLibPETypes
open BCHPESections

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHAssemblyBlock
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHAssemblyInstructionAnnotations
open BCHIFSystem
open BCHLibx86Types
open BCHX86Opcodes
open BCHX86OpcodeRecords

(* bchanalyze *)
open BCHFileIO
open BCHInterrupt
open BCHTrace

(* bchgui *)
open BCHCanvasUtil
open BCHSystemDisplay
open BCHGuiUtil

module H = Hashtbl
module TR = CHTraceResult


(*
module BTypeCollections = CHCollections.Make
  (struct
    type t = btype_t * string list
    let compare (t1,lst1) (t2,lst2) = 
      let l1 = btype_compare t1 t2 in if l1 = 0 then Stdlib.compare lst1 lst2 else l1
    let toPretty (t,l) = 
      LBLOCK [ btype_to_pretty t ; 
	       match l with 
	       | [] -> STR ""
	       | h::tl -> LBLOCK [ STR "(" ; STR h ; STR ":" ; 
				   pretty_print_list tl (fun s -> STR s) "" "." "" ] ]
   end)
 *)
         
let pp_str p = string_printer#print p

let get_floca faddr iaddr =
  let loc = ctxt_string_to_location faddr iaddr in
  get_floc loc


let dialog_interrupted = ref false

let about_codehawk () =
  (* let ch = GdkPixbuf.from_file "logo.gif" in *)
  let version_date = get_version () in
  let dialog = 
    GWindow.about_dialog 
      ~show:true
      ~name:"CodeHawk Binary Analyzer" 
      ~copyright:"Copyright: KestrelTechnology LLC"
      ~version:"0.2"
      (* ~logo:ch *)
      ~comments:("Created on " ^ version_date)
      ()
  in
  let _ = dialog#connect#response ~callback:(fun _ -> dialog#destroy ()) in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  ()

let get_function_name (address:doubleword_int) =
  if functions_data#has_function_name address then
    (functions_data#get_function address)#get_function_name
  else
    address#to_fixed_length_hex_string


let base_pointer_to_pretty (finfo:function_info_int) (name:symbol_t) =
  symbol_to_pretty name
(*  let env = finfo#env in
  let baseVariable = env#get_assembly_variable name in
  match baseVariable#get_denotation with
    AuxiliaryVariable (InitialRegisterValue (reg,level)) ->
      begin
	match reg with
	  CPURegister Esp -> 
	    if level = 0 then STR "SF" else STR ("SF" ^ (string_of_int level))
	| _ -> symbol_to_pretty name
      end
  | _ -> symbol_to_pretty name  *)
    
let get_variable_invariant (floc:floc_int) (var:variable_t) =
  if floc#is_constant var then
    (floc#get_constant var)#toPretty
  else if floc#inv#is_base_offset var then
    let (base,offset) = floc#inv#get_base_offset var in
    let pp_offset = match offset#singleton with
	Some i -> i#toPretty
      | _ -> offset#toPretty in
    LBLOCK [ base_pointer_to_pretty floc#f base ; STR ":" ; pp_offset ]
  else
    STR ""

let is_stack_base (floc:floc_int) (name:symbol_t) =
  let env = floc#f#env in
  let baseVariable = env#varmgr#get_variable_by_index name#getSeqNumber in
  match baseVariable#get_denotation with
		AuxiliaryVariable (InitialRegisterValue (CPURegister Esp,0)) -> true
  | _ -> false
		
let is_realigned_stack_base (floc:floc_int) (name:symbol_t) =
  let env = floc#f#env in
  let baseVariable = env#varmgr#get_variable_by_index name#getSeqNumber in
  match baseVariable#get_denotation with
    AuxiliaryVariable (InitialRegisterValue (CPURegister Esp,1)) -> true
  | _ -> false

let is_external_base_var (floc:floc_int) (name:symbol_t) =
  let env = floc#f#env in
  let baseVariable = env#varmgr#get_variable_by_index name#getSeqNumber in
  match baseVariable#get_denotation with
  | MemoryVariable (_, memref, memoffset) ->
     let memref = env#varmgr#memrefmgr#get_memory_reference memref in
      begin
	match memref#get_base with
	| BLocalStackFrame -> true
	| BaseVar baseVar -> env#is_basevar_memory_value baseVar
                           (*
	  let assemblyBaseVar = env#varmgr#get_variable baseVar in
	  if assemblyBaseVar#is_memory_variable then
	    assemblyBaseVar#get_memory_reference#get_offset#is_constant_offset
	  else
	    true *)
	| _ -> false
      end
  | AuxiliaryVariable (InitialRegisterValue (CPURegister reg,0)) ->
    not (reg = Esp)
  | AuxiliaryVariable (FunctionReturnValue _) -> true
  | _ -> false
    
let base_offset_to_address_pretty 
    (finfo:function_info_int) 
    (base:symbol_t) 
    (offset:interval_t)  =
  let env = finfo#env in
  let avar = env#varmgr#get_variable_by_index base#getSeqNumber in
  (* let is_zero_offset = match offset#singleton with 
      Some constant -> constant#is_zero | _ -> false in *)
  let pp_offset = match offset#singleton with
    | Some constant -> constant#toPretty
    | _ -> offset#toPretty in
  match avar#get_denotation with
  | AuxiliaryVariable (InitialRegisterValue (CPURegister Esp,0)) -> 
    LBLOCK [ STR "SF:" ; pp_offset ]
  | AuxiliaryVariable (InitialRegisterValue (CPURegister Esp,1)) -> 
    LBLOCK [ STR "SF1:" ; pp_offset ]
  | MemoryVariable (_, memref, memoffset) ->
     (match memoffset with
      | ConstantOffset (n,_)  when n#equal numerical_zero ->
         (STR base#getBaseName)
      | _ ->
         LBLOCK [ STR base#getBaseName ; STR "[" ; pp_offset ; STR "]" ])
  | _ -> LBLOCK [ STR "base:" ; STR base#getBaseName ; STR "offset: " ; pp_offset]

let base_offset_color (finfo:function_info_int) (base:symbol_t) =
  let env = finfo#env in
  let avar = env#varmgr#get_variable_by_index base#getSeqNumber in
  match avar#get_denotation with
  | AuxiliaryVariable (InitialRegisterValue (CPURegister Esp,0)) -> ("white","green")
  | AuxiliaryVariable (InitialRegisterValue (CPURegister Esp,1)) -> ("white","yellow")
  | _ -> ("white","blue")
      
let base_pointers_to_pretty (finfo:function_info_int) =
  let env = finfo#env in
  let description (name:symbol_t) =
    let baseVariable = env#varmgr#get_variable_by_index name#getSeqNumber in
    match baseVariable#get_denotation with
      AuxiliaryVariable (InitialRegisterValue (reg,level)) ->
	begin 
	  match reg with
	    CPURegister Esp ->
	      if level = 0 then 
		STR "base of local stack frame" 
	      else
		LBLOCK [ STR "base of local stack frame " ; 
			 pp_quantity level "time" "times" ; STR " aligned" ]
	  | CPURegister reg ->
	    LBLOCK [ STR "Caller value of " ; STR (cpureg_to_string reg) ]
	  | _ -> STR " ? "
	end
(*    | AuxiliaryVariable (HeapBase heapRegion) -> 
      LBLOCK [ STR "heap region allocated at " ; heapRegion#get_allocation_site#toPretty ] *)
    | AuxiliaryVariable (FunctionReturnValue address) ->
      LBLOCK [ STR "return value at address " ; STR address ]
    | _ -> STR " ? " in
  let base_pointers = finfo#get_base_pointers in
  let (_,pp) =
    List.fold_left (fun (first,a) basePtr -> 
      (false, LBLOCK [ a ; (if first then STR "" else NL) ; 
		       base_pointer_to_pretty finfo basePtr#getName ; 
		       STR " - " ; description basePtr#getName ]))
      (true,STR "") base_pointers in
  pp
    
let get_stack_variables (finfo:function_info_int) = (0, [])
(*
  let env = finfo#env in
  let sort_vars = (fun v1 v2 ->
      let m1 = env#get_memory_reference v1 in
      let m2 = env#get_memory_reference v2 in
      m2#get_offset#get_constant_offset#compare m1#get_offset#get_constant_offset) in
  let localVars = List.sort sort_vars env#get_local_stack_variables in
  let parentVars = List.sort sort_vars env#get_parent_stack_variables in
  let realignedVars = List.sort sort_vars env#get_realigned_stack_variables in
  let lenR = List.length realignedVars in
  let lenL = List.length localVars in
  let lenP = List.length parentVars in
  let variableCount = lenR + lenL + lenP in
  let add_offset l = 
    List.map (fun v -> 
      (v, (env#get_memory_reference v)#get_offset#get_constant_offset)) l in
  let add_index start l = 
    let (_,l) = List.fold_left (fun (c,a) v -> (c+1,(c,v)::a)) (start,[]) l in l in
  (variableCount, [ (add_index 1 (List.rev (add_offset realignedVars))) ; 
		    (add_index (lenR + 1) (List.rev (add_offset localVars))) ; 
		    (add_index (lenR+lenL+1) (List.rev (add_offset parentVars))) ])
 *)
                                                  
let attach_stack_headings (table:GPack.table) variables col =
  let realignedLength = List.length (List.nth variables 0) in
  let localLength = List.length (List.nth variables 1) in
  let parentLength = List.length (List.nth variables 2) in
  let col1 = col+realignedLength+1 in
  let col2 = col1+localLength in
  let col3 = col2+parentLength in
  let _ = if realignedLength > 0 then
      ignore (GMisc.label ~text:"realigned" ~xalign:0.5	
		~packing:(table#attach ~left:col ~right:col1 ~top:0) ()) in
  let _ = if localLength > 0 then
      ignore (GMisc.label ~text:"local" ~xalign:0.5 
		~packing:(table#attach ~left:col1 ~right:col2 ~top:0) ()) in
  let _ = if parentLength > 0 then
      ignore (GMisc.label ~text:"parent" ~xalign:0.5
		~packing:(table#attach ~left:col2~right:col3 ~top:0) ()) in
  List.iter (fun (index, (var,offset)) ->
    ignore (GMisc.label ~text:(pp_str (fixed_length_pretty 
					 ~alignment:StrCenter offset#toPretty 4))
      ~packing:(table#attach ~left:(col+index) ~top:1) ()) ) (List.concat variables)

let registers = [ (1,Eax) ; (2,Ebx) ; (3,Ecx) ; (4,Edx) ; (5,Esp) ; (6,Ebp) ; 
		  (7,Esi) ; (8,Edi) ] 

let register_variables finfo = 
  List.map (fun (index,reg) -> (index, finfo#get_cpu_register_variable reg)) registers

let attach_register_headings (table:GPack.table) =
  let _ = GMisc.label ~text:"cpu registers" ~xalign:0.5 
    ~packing:(table#attach ~left:1 ~right:8 ~top:0) () in
  List.iter (fun (colIndex,register) -> 
    ignore (GMisc.label ~text:(cpureg_to_string register)
	      ~packing:(table#attach ~left:colIndex ~top:1) ()))
    registers

let attach_address (table:GPack.table) (va:ctxt_iaddress_t) (row:int) =
  ignore (GMisc.label ~text:va ~packing:(table#attach ~left:0 ~top:row) ())

let attach_annotation (table:GPack.table) (loc:location_int) (row:int) (col:int) =
  let floc = get_floc loc in
  let annotation = create_annotation floc in
  ignore
    (GMisc.label
       ~text:(pp_str annotation#toPretty)
       ~xalign:0.0
       ~packing:(table#attach ~left:col ~top:row)
       ())

let variable_value_label
      ~(floc:floc_int) ~(var:variable_t) ~(packing:GObj.widget->unit) =
  let inv = floc#inv in
  let finfo = floc#f in
  let env = finfo#env in
  let image_base = system_info#get_image_base in
  let isprintable num = num#geq (mkNumerical 32) && (mkNumerical 127)#geq num in
  let pp_constant num = 
    if num#gt image_base#to_numerical then 
      STR (TR.tget_ok (numerical_to_hex_string num))
    else if isprintable num then
      STR (String.make 1 (Char.chr num#toInt))
    else
      num#toPretty in
  let pp_offset offset = 
    pp_str (match offset#singleton with
            | Some i -> pp_constant i | _ -> offset#toPretty) in
  if floc#has_initial_value var then
    make_colored_label (`NAME "white") ("") packing ()
  else if inv#is_constant var then 
    let pp = pp_constant (inv#get_constant var) in
    make_colored_label (`NAME "orange") (pp_str pp) packing ()
  else if inv#is_base_offset var then
    let (base,offset) = inv#get_base_offset var in
    let pp_address = pp_str (base_offset_to_address_pretty finfo base offset) in
    let (fgc,bgc) = base_offset_color finfo base in
    make_colored_label ~fg_color:(`NAME fgc) (`NAME bgc) pp_address packing ()
  else if inv#is_interval var then
    make_colored_label (`NAME "orange") (pp_offset (inv#get_interval var)) packing ()
  else
    let xpr = inv#rewrite_expr (XVar var) env#get_variable_comparator in
    match xpr with
    | XVar v ->
       if v#equal var then make_colored_label (`NAME "gray") ("") packing ()
      else if env#is_initial_register_value v then
	make_colored_label (`NAME "white") v#getName#getBaseName packing ()
      else 
	make_colored_label ~fg_color:(`NAME "white") (`NAME "red") 
	  v#getName#getBaseName packing ()
    | _ -> make_colored_label ~fg_color:(`NAME "white") (`NAME "red") 
      (pp_str (xpr_formatter#pr_expr xpr)) packing ()

let attach_register_values (table:GPack.table) (loc:location_int) (row:int) =
  let floc = get_floc loc in
  List.iter (fun (index,reg) ->
    let var = floc#f#env#mk_cpu_register_variable reg in
    ignore (variable_value_label ~floc ~var 
	      ~packing:(table#attach ~left:index ~top:row))) registers

let attach_stack_variable_values 
    (table:GPack.table) 
    (loc:location_int) 
    (row:int) 
    (col:int)  
    (variables:(int * variable_t) list) =
  let floc = get_floc loc in
  List.iter (fun (index,var) ->
    ignore (variable_value_label ~floc ~var 
	      ~packing:(table#attach ~left:(col+index) ~top:row))) variables
	    
let show_register_state_block 
    (faddr:doubleword_int) 
    (finfo:function_info_int) 
    (block:assembly_block_int) 
    (displayBox:GPack.box)  
    (instrCompleted:int) 
    (totalInstrCount:int) = 
  try
    let _ = if check_interrupt () then raise RequestInterrupt in
    let _ = if check_skip () then raise RequestSkip in   
    let count = block#get_instruction_count in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:10
        ~columns:10
        ~rows:(count+1)
        ~border_width:5
        ~show:true
        () in
    let _ = displayBox#pack ~expand:false ~fill:false ~padding:10 table#coerce in
    let _ = attach_register_headings table in
    let row = ref 2 in
    let _ = block#itera (fun va instruction ->
      let loc = ctxt_string_to_location faddr va in
      let _ = attach_address table va !row in
      let _ = attach_annotation table loc !row 9 in
      let _ = attach_register_values table loc !row in
      begin
	set_progress_bar (instrCompleted + (!row-2)) totalInstrCount ;
	row := !row + 1 
      end ) in
    let separator = GMisc.separator `HORIZONTAL () in
    let _ = displayBox#pack ~expand:false ~fill:false ~padding:0 separator#coerce in
    instrCompleted + (!row-2)
  with
    RequestInterrupt | RequestSkip ->
      let msg = LBLOCK [ STR "Skip requested in show register state " ] in
      begin
	chlog#add "skip" msg ;
	pr_debug [ msg ; NL ] ;
	interrupt_handler#clear_skip ;
	dialog_interrupted := true ;
	instrCompleted
      end

let show_stack_state 
    (finfo:function_info_int)
    (block:assembly_block_int) 
    (variableCount:int)
    (variables:(int * (variable_t * numerical_t)) list list) 
    (displayBox:GPack.box) 
    (instrCompleted:int)
    (totalInstrCount:int)  =
  try
    let _ = if check_interrupt () then raise RequestInterrupt in
    let _ = if check_skip () then raise RequestSkip in
    let faddr = finfo#get_address in
    let count = block#get_instruction_count in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:10 
        ~columns:(variableCount+2)
        ~rows:(count+2)
        ~border_width:5
        ~show:true
        () in
    let _ = displayBox#pack ~expand:false ~fill:false ~padding:10 table#coerce in
    let _ = attach_stack_headings table variables 0 in
    let row = ref 2 in
    let _ = block#itera (fun va instruction ->
      let loc = ctxt_string_to_location faddr va in
      let _ = attach_address table va !row in
      let _ = attach_annotation table loc !row (variableCount+1) in
      let _ = attach_stack_variable_values table loc !row 0 
	(List.map (fun (index,(v,_)) -> (index,v)) (List.concat variables)) in 
      begin
	set_progress_bar (instrCompleted + (!row-2)) totalInstrCount ;
	row := !row+1
      end) in
    let separator = GMisc.separator `HORIZONTAL () in
    let _ =
      displayBox#pack ~expand:false ~fill:false ~padding:0 separator#coerce in
    instrCompleted + (!row-2)
  with
    _ ->
      let msg = LBLOCK [ STR "Skip requested in show stack state " ] in
      begin
	chlog#add "skip" msg ;
	pr_debug [ msg ; NL ] ;
	interrupt_handler#clear_skip ;
	dialog_interrupted := true ;
	instrCompleted
      end

let show_reg_stack_state 
    (fnAddress:doubleword_int)
    (block:assembly_block_int) 
    (variableCount:int) 
    (variables:(int * (variable_t * numerical_t)) list list) 
    (displayBox:GPack.box)
    (instrCompleted:int) 
    (totalInstrCount:int) =
  try
    let count = block#get_instruction_count in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:10 
        ~columns:(variableCount + 10)
        ~rows:(count+2)
        ~border_width:5
        ~show:true () in
    let _ =
      displayBox#pack ~expand:false ~fill:false ~padding:10 table#coerce in
    let _ = attach_register_headings table in
    let _ = attach_stack_headings table variables 8 in
    let row = ref 2 in
    let _ = block#itera (fun va instruction ->
      let loc = ctxt_string_to_location fnAddress va in
      let _ = attach_address table va !row in
      let _ = attach_annotation table loc !row (variableCount+9) in
      begin
	set_progress_bar (instrCompleted + (!row-2)) totalInstrCount ;
	row := !row + 1
      end) in
    let separator = GMisc.separator `HORIZONTAL () in
    let _ =
      displayBox#pack ~expand:false ~fill:false ~padding:0 separator#coerce in
    instrCompleted + (!row-2)
  with
    _ ->
      let msg = LBLOCK [ STR "Skip requested in show register/stack state " ] in
      begin
	chlog#add "skip" msg ;
	pr_debug [ msg ; NL ] ;
	(* interrupt_handler#clear_skip ; *)
	dialog_interrupted := true ;
	instrCompleted
      end

   
let show_register_state_dialog (findex:dw_index_t) (parent:GWindow.window) =
  let _ = interrupt_handler#reset in
  let f = assembly_functions#get_function findex in
  let faddr = f#get_address in
  let finfo = get_function_info faddr in
  let instructionCount = f#get_instruction_count in
  let assemblyBlocks = f#get_blocks in
  let fname = get_function_name faddr in
  let title = "Register contents for function " ^ fname in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true 
      ~width:1000
      ~height:670
      () in
  let stateWindow =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC 
      ~packing:dialog#vbox#add
      () in
  let stateBox = GPack.vbox ~packing:stateWindow#add_with_viewport () in
  let _ = write_message_pp 
    (LBLOCK [ STR "Calculating invariants for eight cpu registers at " ; 
	      INT instructionCount ;
	      STR " locations ......." ]) in
  let _ =
    try
      let instrCompleted = List.fold_left
	(fun instrCompleted block ->
	  show_register_state_block faddr finfo block stateBox instrCompleted 
	    instructionCount) 0 assemblyBlocks in
      let _ = write_message_pp 
	(LBLOCK [ STR "Calculated invariants for 8 variables at " ; 
		  INT instrCompleted ; STR " locations" ;
		  (if !dialog_interrupted then
                     STR " (calculation was interrupted)"
                   else 
		      STR "") ]) in
      reset_progress_bar ()
    with
      RequestInterrupt | RequestSkip ->
	let msg = LBLOCK [ STR "Interrupt requested in register state dialog " ] in
	begin
	  chlog#add "interrupt" msg ;
	  pr_debug [ msg ; NL ] ;
	  interrupt_handler#reset ;
	  write_message_pp 
	    (LBLOCK [ STR "Calculation of register invariants was interrupted" ]) ;
	  reset_progress_bar () 
	end in
  let _ = dialog_interrupted := false in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_stack_state_dialog (functionIndex:dw_index_t) (parent:GWindow.window) =
  let _ = interrupt_handler#reset in
  let f = assembly_functions#get_function functionIndex in
  let faddr = f#get_address in
  let finfo = load_function_info faddr in
  let assemblyBlocks = f#get_blocks in
  let instructionCount = f#get_instruction_count in
  let fname = get_function_name faddr in
  let title = "Stack values for function " ^ fname in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:1000
      ~height:670
      () in
  let stateWindow =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let stateBox = GPack.vbox ~packing:stateWindow#add_with_viewport () in
  let (variableCount,variables) = get_stack_variables finfo in
  let _ = write_message_pp 
      (LBLOCK [ STR "Calculating invariants for " ; INT variableCount ; 
		STR " variables at " ; 
		INT instructionCount ; STR " locations ....... "]) in
  let _ = 
    try
      let instrCompleted = List.fold_left 
	(fun instrCompleted block -> 
	  show_stack_state finfo block variableCount variables stateBox instrCompleted
	    instructionCount) 0  assemblyBlocks in
      let _ = write_message_pp 
	(LBLOCK [ STR "Calculated invariants for " ; INT variableCount ; 
		  STR " variables at " ; 
		  INT instrCompleted ; STR " locations" ;
		  (if !dialog_interrupted then
                     STR " (calculation was interrupted)"
                   else 
		      STR "") ]) in
      reset_progress_bar ()
    with
     RequestInterrupt | RequestSkip ->
	let msg = LBLOCK [ STR "Interrupt requested in stack state dialog " ] in
	begin
	  chlog#add "interrupt" msg ;
	  pr_debug [ msg ; NL ] ;
	  interrupt_handler#reset ;
	  write_message_pp 
	    (LBLOCK [ STR "Calculation of stack invariants was interrupted" ]) ;
	  reset_progress_bar ()
	end in
  let _ = dialog_interrupted := false in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_reg_stack_state_dialog (functionIndex:dw_index_t) (parent:GWindow.window) =
  let _ = interrupt_handler#reset in 
  let f = assembly_functions#get_function functionIndex in
  let faddr = f#get_address in
  let finfo = load_function_info faddr in
  let assemblyBlocks = f#get_blocks in
  let instructionCount = f#get_instruction_count in
  let fname = get_function_name faddr in
  let title = "Register and stack values for function " ^ fname in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:1000
      ~height:670
      () in
  let stateWindow =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let stateBox = GPack.vbox ~packing:stateWindow#add_with_viewport () in
  let (variableCount,variables) = get_stack_variables finfo in
  let _ = write_message_pp
            (LBLOCK [ STR "Calculating invariants for " ;
                      INT (variableCount + 8) ;
                      STR " registers and stack variables at " ;
	              INT instructionCount ; STR " locations ....... "]) in
  let _ = 
    try
      let instrCompleted = List.fold_left
	(fun instrCompleted block ->
	  show_reg_stack_state
            faddr
            block
            variableCount
            variables
            stateBox
            instrCompleted
	    instructionCount) 0 assemblyBlocks in
      let _ = write_message_pp
	(LBLOCK [ STR "Calculated invariants for " ; INT (variableCount + 8) ; 
		  STR " registers and stack variables at " ;
		  INT instrCompleted ; STR " locations" ; 
		  (if !dialog_interrupted then
                     STR " (calculation was interrupted)"
                   else
                     STR "") ] ) in
      reset_progress_bar ()
    with
      _  ->
	let msg = LBLOCK [ STR "Interrupt requested in register/stack state dialog " ] in
	begin
	  chlog#add "skip" msg ;
	  pr_debug [ msg ; NL ] ;
	  (* interrupt_handler#reset ; *)
	  write_message_pp (LBLOCK [ STR "Calculation register/stack invariants was interrupted" ]) ;
	  reset_progress_bar ()
	end in
  let _ = dialog_interrupted := false in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
(*

let attach_variable_types (table:GPack.table) (loc:location_int)
    (row:int) (col:int) (variables:(int * variable_t) list) =
  let invariant = invariants#get_invariant loc in
  let varTypes = invariant#get_types (fun v -> not v#isTmp) in
  let typeTable = Hashtbl.create (List.length varTypes) in
  let _ = List.iter (fun (var,s) -> Hashtbl.add typeTable var#getName#getSeqNumber s) varTypes in
  let get_types v = if Hashtbl.mem typeTable v#getName#getSeqNumber then
      Hashtbl.find typeTable v#getName#getSeqNumber 
    else
      topSymbolicSet in
  List.iter (fun (index,var) ->
    let symset = get_types var in
    let packing = table#attach ~left:(col+index) ~top:row in
    match symset#getSymbols with
      TOP -> make_colored_label (`NAME "gray") ("") packing ()
    | BOTTOM -> make_colored_label (`NAME "black") ("") packing ()
    | SET s -> 
      let pp = pretty_print_list s#toList (fun sym -> symbol_to_pretty sym) "" ";" "" in
      make_colored_label (`NAME "green") (pp_str pp) packing ()) variables


let show_reg_stack_types (fnAddress:doubleword_int)
    (block:assembly_block_int) (variableCount:int)
    (variables:(int * (variable_t * numerical_t)) list list) (displayBox:GPack.box)
    (instrCompleted:int) (totalInstrCount:int) =
  try
    let finfo = get_function_info fnAddress in
    let _ = if check_interrupt () then raise RequestInterrupt in
    let _ = if check_skip () then raise RequestSkip in
    let count = block#get_instruction_count in
    let table = GPack.table ~row_spacings:5 ~col_spacings:10 ~columns:(variableCount + 10) ~rows:(count+2)
      ~border_width:5 ~show:true () in
    let _ = displayBox#pack ~expand:false ~fill:false ~padding:10 table#coerce in
    let _ = attach_register_headings table in
    let _ = attach_stack_headings table variables 8 in
    let row = ref 2 in
    let _ = block#itera (fun va instruction ->
      let loc = make_location fnAddress va in
      let _ = attach_address table va !row in
      let _ = attach_annotation table loc !row (variableCount+9) in
      let _ = attach_variable_types table loc !row 0 (register_variables finfo) in
      let _ = attach_variable_types table loc !row 8
	(List.map (fun (index,(v,_)) -> (index,v)) (List.concat variables)) in
      begin
	set_progress_bar (instrCompleted + (!row-2)) totalInstrCount ;
	row := !row + 1
      end) in
    let separator = GMisc.separator `HORIZONTAL () in
    let _ = displayBox#pack ~expand:false ~fill:false ~padding:0 separator#coerce in
    instrCompleted + (!row-2)
  with
    RequestSkip ->
      let msg = LBLOCK [ STR "Skip requested in show stack types " ] in
      begin
	chlog#add "skip" msg ;
	pr_debug [ msg ; NL ] ;
	interrupt_handler#clear_skip ;
	dialog_interrupted := true ;
	instrCompleted ;
      end
    


let show_reg_stack_type_dialog (functionIndex:dw_index_t) (parent:GWindow.window) =
  let _ = interrupt_handler#reset in
  let assemblyFunction = assembly_functions#get_function functionIndex in
  let fnAddress = assemblyFunction#get_address in
  let assemblyBlocks = assemblyFunction#get_blocks in
  let instructionCount = assemblyFunction#get_instruction_count in
  let functionName = get_function_name fnAddress in
  let title = "Register and stack variable types for function " ^ functionName in
  let dialog = GWindow.dialog ~title ~parent ~modal:false ~show:true ~width:1000 ~height:670 () in
  let stateWindow = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let stateBox = GPack.vbox ~packing:stateWindow#add_with_viewport () in
  let (variableCount,variables) = get_stack_variables fnAddress in
  let _ = write_message_pp
    (LBLOCK [ STR "Extracting type invariants for " ; INT (variableCount + 8) ; 
	      STR " registers and stack variables at " ;
	      INT instructionCount ; STR " locations ....... "]) in
  let _ = 
    try
      let instrCompleted = List.fold_left
	(fun instrCompleted block ->
	  show_reg_stack_types fnAddress block variableCount variables stateBox instrCompleted
	    instructionCount) 0 assemblyBlocks in
      let _ = write_message_pp
	(LBLOCK [ STR "Extracted type invariants for " ; INT (variableCount + 8) ; 
		  STR " registers and stack variables at " ;
		  INT instrCompleted ; STR " locations" ; 
		  (if !dialog_interrupted then STR " (calculation was interrupted)" else STR "") ] ) in
      reset_progress_bar ()
    with
      RequestInterrupt | RequestSkip ->
	let msg = LBLOCK [ STR "Interrupt requested in stack types dialog " ] in
	begin
	  chlog#add "skip" msg ;
	  pr_debug [ msg ; NL ] ;
	  interrupt_handler#reset ;
	  write_message_pp (LBLOCK [ STR "Calculation register/stack invariants was interrupted" ]) ;
	  reset_progress_bar ()
	end in
  let _ = dialog_interrupted := false in
  let _ = reset_interrupt () in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  
*)

(*
let valueset_to_pretty (function_address:doubleword_int) (invariant:b_invariant_int) =
  let filter v = not (v#isTmp || (variable_manager#is_special_variable v) || 
			(variable_manager#is_initial_register_value v)) in
  let finfo = get_function_info function_address in
  let valuesets = invariant#get_valuesets filter in
  let pp_offset offset = match offset#singleton with Some i -> i#toPretty | _ -> offset#toPretty in
  let valueset_to_pretty (valueset:valueset_t) =
    if valueset#isTop then STR "T" else
      if valueset#isZeroOffset then 
	match valueset#getZeroOffset#singleton with
	  Some i -> i#toPretty
	| _ -> valueset#getZeroOffset#toPretty
      else if valueset#isSingleBase then
	let (base,offset) = valueset#getSingleBase in
	LBLOCK [ base_pointer_to_pretty base ; STR ":" ; pp_offset offset ]
      else valueset#toPretty in
  List.fold_left (fun a (var,valueset) -> 
    LBLOCK [ a ; NL ; variable_to_pretty var ; STR " : " ; valueset_to_pretty valueset ])
    (LBLOCK [ STR "base-pointers in function " ; STR (get_function_name function_address) ; NL ;
	      INDENT (3,base_pointers_to_pretty finfo) ; NL ]) valuesets
   
let intervals_to_pretty (function_address:doubleword_int) (invariant:b_invariant_int) =
  let filter v = not (v#isTmp || (variable_manager#is_special_variable v)) in
  let intervals = invariant#get_intervals filter in
  let pp_interval interval = match interval#singleton with Some i -> i#toPretty | _ -> interval#toPretty in
  match intervals with
    [] -> STR ""
  | _ ->
      List.fold_left (fun a (var,interval) ->
	LBLOCK [ a ; NL ; INDENT (3, LBLOCK [ variable_to_pretty var ; STR " : " ; pp_interval interval ]) ])
	(LBLOCK [ NL ; NL ; STR "Intervals" ]) intervals

let numerical_constraints_to_pretty (inv:b_invariant_int) =
    let comparator = variable_manager#get_external_variable_comparator in
    let constraint_to_pretty c =
      let constant = c#getConstant in
      let pp_kind = match c#getKind with LINEAR_EQ -> " = " | LINEAR_INEQ -> " <= " in
      let pp_factor (c,f) = 
	if c#equal numerical_one then factor_to_pretty f else LBLOCK [ c#toPretty ; factor_to_pretty f ] in
      let pp_factors l =
	List.fold_left (fun (first,a) (c,f) ->
	  if c#equal numerical_one && first then
	    (false, LBLOCK [ factor_to_pretty f ])
	  else if c#neg#equal numerical_one && first then
	    (false, LBLOCK [ STR "-" ; factor_to_pretty f])
	  else if c#equal numerical_one && not first then
	    (false, LBLOCK [ a ; STR " + " ; factor_to_pretty f ])
	  else if c#neg#equal numerical_one && not first then
	    (false, LBLOCK [ a ; STR " - " ; factor_to_pretty f ])
	  else if first then
	    (false, pp_factor (c,f))
	  else if c#gt numerical_zero then
	    (false, LBLOCK [ a ; STR " + " ; pp_factor (c,f) ])
	  else
	    (false, LBLOCK [ a ; STR " - " ; pp_factor (c#neg,f) ])) (true,STR "") l in
      let pp_constant first constant  = 
	if constant#equal numerical_zero then if first then STR "0" else STR "" 
	else if constant#gt numerical_zero then
	  if first then constant#toPretty else LBLOCK [ STR " + " ; constant#toPretty ] 
	else if first then constant#toPretty else LBLOCK [ STR " - " ; constant#neg#toPretty ] in
      let factors = c#getFactorsList in
      let sortedFactors = List.sort (fun (c1,f1) (c2,f2) -> 
	let unitFactor1 = c1#equal numerical_one || c1#neg#equal numerical_one in
	let unitFactor2 = c2#equal numerical_one || c2#neg#equal numerical_one in
	match (unitFactor1, unitFactor2) with
	  (true, false) -> -1
	| (false, true) -> 1
	| _ -> comparator f2#getVariable f1#getVariable) factors in
      match sortedFactors with
	  [] -> STR ""
	| (c,f)::tl ->
	  let (lhs,rhs,constant) = if c#gt numerical_zero then 
	      ((c,f),List.map (fun (c,f) -> (c#neg,f)) tl,constant) 
	    else
	      ((c#neg,f), tl,constant#neg) in
	  let (_, pp_rhs) = pp_factors rhs in
	  LBLOCK [ pp_factor lhs ; STR pp_kind ; pp_rhs ; pp_constant ((List.length tl) = 0) constant ] in
    let constraints = inv#get_numerical_constraints ~var_filter:(fun v -> not v#isTmp) () in
    pretty_print_list constraints (fun c -> LBLOCK [ constraint_to_pretty c ; NL ]) "" "" ""


let linear_equalities_to_pretty (function_address:doubleword_int) (invariant:b_invariant_int) = 
  try
    let var_filter = (fun v -> not v#isTmp) in
    let constraints = invariant#get_numerical_constraints ~var_filter () in
    match constraints with
	[] -> STR ""
      | _ ->
	LBLOCK [ NL ; NL ; STR "Linear equalities: " ; NL ; 
		 INDENT (3, numerical_constraints_to_pretty invariant) ]
  with
      CHCommon.CHFailure p ->
	begin
	  pr_debug [ STR "CHFailure: " ; p ; NL ] ;
	  STR ""
	end

let types_to_pretty (function_address:doubleword_int) (invariant:b_invariant_int) =
  try
    let filter = (fun v -> true) in
    let type_values = invariant#get_types filter in
    match type_values with
      [] -> STR ""
    | _ ->
      List.fold_left (fun a (var,type_value) ->
	LBLOCK [ a ; NL ; INDENT (3, LBLOCK [ variable_to_pretty var ; STR " : " ; type_value#toPretty] ) ])
	(LBLOCK [ NL ; NL ; STR "Types"]) type_values
  with
    CHCommon.CHFailure p ->
      begin
	ch_error_log#add "invariant failure" (LBLOCK [ STR "types_to_pretty: " ; function_address#toPretty ]) ;
	STR ""
      end
*)	

	      
let show_invariant_dialog (loc:location_int) (parent:GWindow.window) =
  let display_invariant window contents =
    let _ = match contents with Some s -> window#remove s | _ -> () in
    let view = GText.view () in
    let _ = view#set_pixels_above_lines 5 in
    let _ = view#set_left_margin 10 in
    let buffer = view#buffer in
    let iter = buffer#get_iter `START in
    let floc = get_floc loc in
    let inv = floc#inv in
    let extVars = floc#f#env#get_external_memory_variables in
    let modVars = List.filter (fun v -> not (inv#var_has_initial_value v)) extVars in
    let pModVars = match modVars with
      | [] -> STR "   none"
      | _ -> pretty_print_list modVars 
	(fun v -> LBLOCK [ STR "   " ; STR v#getName#getBaseName ; NL ]) "" "" "" in	
    let pModVars =
      LBLOCK [ STR "External memory variables modified: " ; NL ;
	       pModVars ; NL ] in
    let pInvs =
      LBLOCK [ inv#toPrettyVar (Some floc#env#variable_name_to_string) ; 
	       NL ; NL ; pModVars ; NL ;
	       floc#tinv#toPretty ; NL ] in			      
    let _ = buffer#insert ~iter (pp_str pInvs) in
    let newcontents = view#coerce in
    let _ = window#add newcontents in
    Some newcontents in
  let fname = get_function_name loc#f in
  let title = "Invariant for " ^ loc#i#to_hex_string ^ " in function " ^ fname in
  let dialog = GWindow.dialog 
    ~title ~parent ~modal:false ~show:true ~width:800 ~height:480 () in
  let window =
    GBin.scrolled_window 
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let windowcontents = ref (display_invariant window None) in
  let refreshButton =
    GButton.button
      ~stock:`REFRESH
      ~packing:dialog#action_area#add
      () in
  let _ = refreshButton#connect#clicked 
    ~callback:(fun () ->windowcontents := display_invariant window !windowcontents) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let get_esp_stats (f:assembly_function_int) = STR ("To be done")
(*
  let faddr = f#get_address in
  let known = ref 0 in
  let range = ref 0 in 
  let unknown = ref 0 in
  let _ = f#iter 
    (fun block ->block#itera 
      (fun iaddr _ -> 
	let floc = get_floca faddr iaddr in
	let (_,espOffset) = floc#get_esp_offset in
	if espOffset#isTop then 
	  unknown := !unknown + 1
	else
	  match espOffset#singleton with
	    Some _ -> known := !known + 1
	  | _ -> range := !range + 1)
    ) in
  let total = !known + !range + !unknown in
  let known_percentage = (float !known) /. (float total) *. 100.0 in
  let range_percentage = (float !range) /. (float total) *. 100.0 in
  let unknown_percentage = (float !unknown) /. (float total) *. 100.0 in
  let pr_float ft = LBLOCK [ STR ( Printf.sprintf "%.1f" ft ) ; STR "%" ]  in
  LBLOCK [ STR "Esp precision: " ; NL ;
	   INDENT (5, LBLOCK [ STR "known: " ; pr_float known_percentage ;
			       STR "; range: " ; pr_float range_percentage ;
			       STR "; unknown: " ; pr_float unknown_percentage ]) ]
 *)
let show_function_metrics_dialog (findex:dw_index_t) (parent:GWindow.window) = ()
(*
  let faddr = index_to_doubleword findex in
  let results = file_metrics#function_to_pretty faddr#to_hex_string in
  let fname = get_function_name faddr in
  let f = assembly_functions#get_function findex in
  let faddr = f#get_address in
  let fname = get_function_name faddr in
  let finfo = get_function_info faddr in
  let fsum = finfo#get_summary in
  let title = "Function information for " ^ fname in
  let dialog = GWindow.dialog
    ~title ~parent ~modal:true ~show:true ~width:800 ~height:480 () in
  let window = GBin.scrolled_window 
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let view = GText.view () in
  let _ = view#set_pixels_above_lines 5 in
  let _ = view#set_left_margin 10 in
  let buffer = view#buffer in 
  let iter = buffer#get_iter `START in
  let _ = buffer#insert ~iter ("Function " ^ fname ^ "\n\n") in
  let _ = buffer#insert ~iter (pp_str results) in
  let _ = window#add view#coerce in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
 *)
let show_summary_dialog (findex:dw_index_t) (parent:GWindow.window) = ()
(*
  let faddr = index_to_doubleword findex in
  let fname = get_function_name faddr in
  let finfo = get_function_info faddr in
  let psummary = finfo#get_summary#toPretty in
  let parguments = finfo#get_argument_values#toPretty in
  let title = "Function summary for " ^ fname in
  let dialog = GWindow.dialog
    ~title ~parent ~modal:true ~show:true ~width:800 ~height:480 () in
  let window = GBin.scrolled_window
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let view = GText.view () in
  let _ = view#set_pixels_above_lines 5 in
  let _ = view#set_left_margin 10 in
  let buffer = view#buffer in 
  let iter = buffer#get_iter `START in
  let _ = buffer#insert ~iter ("Function summary " ^ fname ^ "\n\n") in
  let _ = buffer#insert ~iter (pp_str psummary) in
  let _ = buffer#insert ~iter ("\nFunction arguments " ^ "\n\n") in
  let _ = buffer#insert ~iter (pp_str parguments) in
  let _ = window#add view#coerce in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
 *)

let show_lib_callers_dialog
    (title:string)
    (flocs:floc_int list)
    (add_fns:doubleword_int list -> unit)
    (parent:GWindow.window) =
  let dialog = GWindow.dialog 
    ~title ~parent ~modal:false ~show:true ~width:800 ~height:400 () in
  let window = GBin.scrolled_window
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let count = List.length flocs in
  let table = GPack.table ~col_spacings:25 ~row_spacings:5 ~columns:3 ~rows:(count+1) () in
  let _ = window#add_with_viewport table#coerce in
  let row = ref 1 in
  let _ = List.iter (fun floc ->
      let loc = floc#l in
      let annotation = create_annotation floc in
      let fname = get_function_name loc#f in
      let _ =
        GMisc.label
          ~text:fname ~xalign:0.0 ~packing:(table#attach ~top:!row ~left:0) () in
      let _ = GMisc.label ~text:loc#i#to_hex_string ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:1) () in
      let _ = GMisc.label ~text:(pp_str annotation#toPretty) ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:2) () in
      row := !row+1) flocs in
  let callers = List.map (fun floc -> floc#l#f) flocs in
  let addButton = GButton.button ~label:"Add to list" ~packing:dialog#action_area#add () in
  let _ = addButton#connect#clicked ~callback:(fun () -> add_fns  callers) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_external_inputs_dialog
    (title:string)
    (floc_sources:(floc_int * (string list)) list)
    (add_fns:doubleword_int list -> unit)
    (parent:GWindow.window) =
  let dialog = GWindow.dialog
    ~title ~parent ~modal:false ~show:true ~width:800 ~height:400 () in
  let dwindow = GBin.scrolled_window
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let vbox = GPack.vbox ~packing:dwindow#add_with_viewport () in
  let bounded v mn mx = if v > mx then mx else if v < mn then mn else v in
  let add_frame label flocs =
    let len = List.length flocs in
    let height = bounded (40 * len) 100 300 in
    let frame = GBin.frame ~label ~border_width:10 ~height () in
    let _ = vbox#pack ~expand:false ~fill:false ~padding:10 frame#coerce in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table ~col_spacings:25 ~row_spacings:5 ~columns:3 ~rows:(len+1) () in
    let _ = window#add_with_viewport table#coerce in
    let row = ref 1 in
    let _ = List.iter (fun floc ->
      let loc = floc#l in
      let annotation = create_annotation floc in
      let fname = get_function_name loc#f in
      let _ =
        GMisc.label
          ~text:fname ~xalign:0.0 ~packing:(table#attach ~top:!row ~left:0) () in
      let _ =
        GMisc.label
          ~text:loc#i#to_hex_string
          ~xalign:0.0
	  ~packing:(table#attach ~top:!row ~left:1)
          () in
      let _ =
        GMisc.label
          ~text:(pp_str annotation#toPretty)
          ~xalign:0.0
	  ~packing:(table#attach ~top:!row ~left:2)
          () in
      row := !row+1) flocs in
    () in
  let sources = new StringCollections.set_t in
  let _ = List.iter (fun (_,srcs) -> sources#addList srcs) floc_sources in
  let _ = pr_debug [ STR "External inputs: " ; NL ] in
  let _ = sources#iter (fun s ->
    let flocs = ref [] in
    let _ = List.iter (fun (f,srcs) -> if List.mem s srcs then flocs := f :: !flocs)
      floc_sources in
    let len = List.length !flocs in
    let _ = pr_debug [ STR s ; STR ": " ; INT len ; NL ] in
    add_frame ("from: " ^ s ^ " (" ^ (string_of_int len) ^ ")") !flocs) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  
let show_external_effects_dialog
    (title:string)
    (floc_targets:(floc_int * ((string * string) list)) list)
    (add_fns:doubleword_int list -> unit)
    (parent:GWindow.window) =
  let dialog =
    GWindow.dialog 
      ~title ~parent ~modal:false ~show:true ~width:800 ~height:400 () in
  let dwindow =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let vbox = GPack.vbox ~packing:dwindow#add_with_viewport () in
  let bounded v mn mx = if v > mx then mx else if v < mn then mn else v in
  let add_frame label flocs =
    let len = List.length flocs in
    let height = bounded (40 * len) 100 300 in
    let frame = GBin.frame ~label ~border_width:10 ~height () in
    let _ = vbox#pack ~expand:false ~fill:false ~padding:10 frame#coerce in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table ~col_spacings:25 ~row_spacings:5 ~columns:4 ~rows:(len+1) () in
    let _ = window#add_with_viewport table#coerce in
    let row = ref 1 in
    let _ = List.iter (fun (floc, xactions) ->
      let loc = floc#l in
      let actionLabel = String.concat "," xactions in
      let annotation = create_annotation floc in
      let fname = get_function_name loc#f in
      let _ = GMisc.label ~text:fname ~xalign:0.0 
	~packing:(table#attach ~top:!row ~left:0) () in
      let _ = GMisc.label ~text:loc#i#to_hex_string ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:1) () in
      let _ = GMisc.label ~text:actionLabel ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:2) () in
      let _ = GMisc.label ~text:(pp_str annotation#toPretty) ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:3) () in
      row := !row+1) flocs in
    () in
  let targets = new StringCollections.set_t in
  let _ = List.iter (fun (_,tgts) -> 
    List.iter (fun (tgt,_) -> targets#add tgt) tgts) floc_targets in
  let _ = pr_debug [ STR "External effects" ; NL ] in
  let _ = targets#iter (fun s ->
    let flocs = ref [] in
    let _ = List.iter (fun (f,tgts) -> 
      let actions = List.fold_left (fun acc (xtgt,a) ->
	if xtgt = s then a::acc else acc) [] tgts in
      match actions with
      | [] -> ()
      | _ -> flocs := (f, actions) :: !flocs) floc_targets in
    let len = List.length !flocs in
    let _ = pr_debug [ STR s ; STR ": " ; INT len ; NL ] in
    add_frame ("target: " ^ s ^ " (" ^ (string_of_int len) ^ ")") !flocs) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

  
let show_callers_dialog 
    (findex:dw_index_t) 
    (add_callers_to_list:(doubleword_int list -> unit))
    (parent:GWindow.window) =
  let faddr = TR.tget_ok (index_to_doubleword findex) in
  let fname = get_function_name faddr in
  let callers = get_callers faddr in
  let count = List.length callers in
  let title = "Calls to " ^ fname ^ " (" ^ (string_of_int count) ^ ")" in
  let dialog =
    GWindow.dialog 
      ~title ~parent ~modal:false ~show:true ~width:800 ~height:480 () in
  let window =
    GBin.scrolled_window 
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add () in
  let table =
    GPack.table ~col_spacings:25 ~row_spacings:5 ~columns:3 ~rows:(count+1) () in
  let _ =
    GMisc.label
      ~text:"Calling function"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~text:"Address"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:1)
      () in
  let _ =
    GMisc.label
      ~text:"Instruction"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:2)
      () in
  let _ = window#add_with_viewport table#coerce in
  let row = ref 1 in
  let _ = List.iter (fun floc ->
      let loc = floc#l in
      let annotation = create_annotation floc in
      let fname = get_function_name loc#f in
      let _ =
        GMisc.label
          ~text:fname
          ~xalign:0.0
          ~packing:(table#attach ~top:!row ~left:0)
          () in
      let _ =
        GMisc.label
          ~text:loc#i#to_hex_string
          ~xalign:0.0
	  ~packing:(table#attach ~top:!row ~left:1)
          () in
      let _ =
        GMisc.label
          ~text:(pp_str annotation#toPretty)
          ~xalign:0.0
	  ~packing:(table#attach ~top:!row ~left:2)
          () in
      row := !row+1) callers in
  let callers = List.map (fun floc -> floc#l#f) callers in
  let addButton =
    GButton.button ~label:"Add to list" ~packing:dialog#action_area#add () in
  let _ =
    addButton#connect#clicked ~callback:(fun () -> add_callers_to_list callers)  in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
    
let show_callees_dialog 
    (findex:dw_index_t) 
    (add_callees_to_list:(doubleword_int list -> unit))
    (parent:GWindow.window) =
  try
    let faddr = TR.tget_ok (index_to_doubleword findex) in
    let fname = get_function_name faddr in
    let title = "Calls made by " ^ fname in
    let dialog = GWindow.dialog 
      ~title ~parent ~modal:false ~show:true ~width:800 ~height:480 () in
    let window = GBin.scrolled_window 
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
    let callees = get_callees faddr in
    let count = List.length callees in
    let table =
      GPack.table
        ~col_spacings:25
        ~row_spacings:5
        ~columns:2
        ~rows:(count+1)
        () in
    let _ = window#add_with_viewport table#coerce in
    let _ = GMisc.label 
      ~text:"Address" ~xalign:0.0 ~packing:(table#attach ~top:0 ~left:0) () in
    let _ = GMisc.label 
      ~text:"Instruction" ~xalign:0.0 ~packing:(table#attach ~top:0 ~left:1) () in
    let row = ref 1 in
    let _ = List.iter
      (fun floc ->
	let loc = floc#l in
	let annotation = create_annotation floc in
	let _ = GMisc.label ~text:loc#i#to_hex_string ~xalign:0.0
	  ~packing:(table#attach ~top:!row ~left:0) () in
	let _ = GMisc.label ~text:(pp_str annotation#toPretty) ~xalign:0.0
	  ~packing:(table#attach ~top:!row ~left:1) () in
	row := !row+1) (List.rev callees) in
    let callees =
      List.fold_left (fun acc floc ->
          if floc#has_call_target && floc#get_call_target#is_app_call then
            let ctinfo = floc#get_call_target in
            ctinfo#get_application_target :: acc
          else
            acc)
      [] callees in
    let addButton =
      GButton.button ~label:"Add to list" ~packing:dialog#action_area#add () in
    let _ =
      addButton#connect#clicked ~callback:(fun () -> add_callees_to_list callees)  in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun () -> ()) in
    let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
    ()
  with
    BCH_failure p ->
      pr_debug [ STR "Failure in show_callees_dialog: " ; p ; NL ]

let get_type_invs_pretty fname finfo = (STR "not supported")
                                     (*
  let tinvs = finfo#ftinv in
  let fInvs = tinvs#get_function_facts in
  let lInvs = tinvs#get_location_facts in
  let facts = fInvs @ (List.concat (List.map snd lInvs)) in
  let ppf = ref [] in
  let ppl = ref [] in
  let ppv = ref [] in
  let table = H.create 3 in
  let add v f = 
    let name = v#getName#getBaseName in
    let entry = 
      if H.mem table name then H.find table name else
	let s = new BTypeCollections.set_t in 
	begin H.add table name s ; s end in
   entry#add f in
  let _ = List.iter (fun f ->
    match f#get_fact with
    | VarTypeFact (v,t,l) when not (finfo#env#is_bridge_value v) -> add v (t,l)
    | _ -> ()) facts in
  let _ = List.iter (fun v ->
    ppf := (LBLOCK [ INDENT (3, v#toPretty) ; NL ]) :: !ppf) fInvs in
  let _ = List.iter (fun (loc,fl) ->
    match fl with
    | [] -> ()
    | _ -> 
      let lpp = List.map (fun f -> LBLOCK [ f#toPretty ; NL ]) fl in
      ppl := (LBLOCK [ STR loc ; NL ; INDENT (3, LBLOCK lpp) ; NL ]) :: !ppl) lInvs in
  let l = ref [] in
  let _ = H.iter (fun k v -> l := (k,v) :: !l) table in
  let l = List.sort Stdlib.compare !l in
  let _ = List.iter (fun (k,v) ->
    let sInfo l = match l with [] -> STR "" | h::tl ->
	  LBLOCK [ STR " (" ; STR h ; STR ":" ; pretty_print_list tl (fun s -> STR s)
	    "" "." "" ; STR ")" ] in
    match v#toList with
    | [] -> ()
    | [ (t,l) ] ->
      ppv := (LBLOCK [ STR "   " ; STR k ; STR ": " ; btype_to_pretty t ; sInfo l ; NL ]) :: !ppv
    | ts ->
      let vpp =  List.map (fun (t,l) -> 
	LBLOCK [ btype_to_pretty t ; sInfo l ; NL ]) ts in
      ppv := (LBLOCK [ STR k ; NL ; INDENT (3, LBLOCK vpp ) ]) :: !ppv) l in
  LBLOCK [ STR "Type invariants for " ; STR fname ; STR " valid for all locations: " ; NL ;
	   LBLOCK !ppf ; NL ; NL ;
	   STR "Variable summary " ; NL ; LBLOCK !ppv ; NL ; NL ;
	   STR "Type invariants per location: " ; NL ; LBLOCK (List.rev !ppl) ; NL ]  *)

let show_types_dialog (findex:dw_index_t) (parent:GWindow.window) =
  let faddr = TR.tget_ok (index_to_doubleword findex) in
  let finfo = get_function_info faddr in
  let fname = get_function_name faddr in
  let ppInvs = get_type_invs_pretty fname finfo in
  let title = "Variable types for " ^ fname in
  let dialog =
    GWindow.dialog
      ~title ~parent ~modal:false ~show:true ~width:800 ~height:480 () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let view = GText.view () in
  let _ = view#set_pixels_above_lines 5 in
  let _ = view#set_left_margin 10 in
  let buffer = view#buffer in 
  let iter = buffer#get_iter `START in
  let _ = buffer#insert ~iter ("Function " ^ fname ^ "\n\n") in
  let _ = buffer#insert ~iter (pp_str ppInvs) in
  let _ = window#add view#coerce in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

  

let show_dll_calls_dialog (findex:dw_index_t) (parent:GWindow.window) = ()
(*
  let faddr = index_to_doubleword findex in
  let finfo = get_function_info faddr in
  let fname = get_function_name faddr in
  let title = "Dll calls made by " ^ fname in
  let dialog = GWindow.dialog
    ~title ~parent ~modal:false ~show:true ~width:800 ~height:480 () in
  let window = GBin.scrolled_window
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let callees = get_callees faddr in
  let callCount = List.length callees in
  let maxArgs = List.fold_left (fun acc callee ->
    if callee#has_call_target_signature then
      let api = callee#get_call_target_signature in
      let nPars = List.length api.fapi_parameters in
       if nPars > acc then nPars else acc
    else acc) 0 callees in  
  let trace_rv_graph rv () = canvas#trace_rv_graph_to_dot findex rv in
  let trace_se_graph floc se () = canvas#trace_se_graph_to_dot findex floc se in
  let table =
    GPack.table 
      ~col_spacings:25
      ~row_spacings:5
      ~columns:(3 + maxArgs)
      ~rows:(callCount + 1)
      () in
  let _ = window#add_with_viewport table#coerce in
  let _ = GMisc.label
    ~text:"Address" ~xalign:0.0 ~packing:(table#attach ~top:0 ~left:0) () in
  let make_arg_access floc par x left top =
    if is_intconst x then () else
      if is_pointer par.apar_type then
	if floc#has_call_target_semantics then
	  let ses = floc#get_call_target_semantics.fsem_sideeffects in
	  if List.exists (fun se ->
	    match se with
	    | BlockWrite (_,ArgValue dest,_) -> 
	      api_parameter_compare dest par = 0
	    | _ -> false) ses then
	    let sev = finfo#env#mk_side_effect_value floc#l#i par.apar_name in
	    let button = GButton.button ~label:par.apar_name 
	      ~packing:(table#attach ~top ~left) () in
	    let _ =
              button#connect#clicked ~callback:(trace_se_graph floc sev) in	
	    () 
	  else
	    ()
      else
	() in
  let make_return_value_access floc top =
    if floc#has_call_target_signature then
      let api = floc#get_call_target_signature in
      if is_void api.fapi_returntype then () else
	let rv = finfo#env#mk_return_value floc#l#i in
	let button = GButton.button ~label:"R" ~packing:(table#attach ~top ~left:1) () in
	let _ = button#connect#clicked ~callback:(trace_rv_graph rv) in
	() 
    else
      () in
  let row = ref 1 in
  let _ = List.iter 
    (fun callee ->
      let args = callee#get_call_args in
      let annotation = create_annotation callee in
      let _ =
        GMisc.label
          ~text:callee#l#i#to_hex_string
          ~packing:(table#attach ~top:!row ~left:0) () in
      let _ = make_return_value_access  callee !row in
      let _ = List.iter (fun (p,x) ->
	match p.apar_location with
	| StackParameter i ->
	  let _ = make_arg_access callee p x (i+1) !row in
	  ()
	| _ -> ()) args in
      let _ = GMisc.label ~text:(pp_str annotation#toPretty) ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:(maxArgs + 2)) () in	
      row := !row + 1) callees in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
 *)
  

let show_accesses title accessList faddr parent () =
  let dialog =
    GWindow.dialog 
      ~title ~parent ~modal:false ~show:true ~width:800 ~height:480 () in
  let window =
    GBin.scrolled_window 
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:dialog#vbox#add () in
  let table =
    GPack.table 
      ~row_spacings:5
      ~col_spacings:10
      ~columns: 4
      ~rows:((List.length accessList)+1)
      ~packing:window#add_with_viewport
      () in
  let _ = GMisc.label ~text:"writers" ~packing:(table#attach ~top:0 ~left:2) () in
  let _ = GMisc.label ~text:"readers" ~packing:(table#attach ~top:0 ~left:3) () in
  let row = ref 1 in
  let is_memory_read acc = false in
(*    match acc with 
    | MARead _ | MAIndexedRead _ | MABlockRead _ -> true | _ -> false in *)
  let _ = List.iter (fun (iaddr,acc) ->
    let floc = get_floca faddr iaddr in
    let ann = create_annotation floc in
    let _ = GMisc.label ~text:iaddr 
      ~packing:(table#attach ~top:!row ~left:0) () in
    (* let _ = GMisc.label ~text:(pp_str (memaccess_to_pretty acc)) ~xalign:0.0
      ~packing:(table#attach ~top:!row ~left:1) () in *)
    let col = if is_memory_read acc then 3 else 2 in       (* FIX *)
    let text = (pp_str ann#toPretty) in
    let _ = GMisc.label ~text ~packing:(table#attach ~left:col ~top:!row) () in
    row := !row + 1) accessList in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
    

let show_gvars_dialog (index:dw_index_t) (parent:GWindow.window) =  ()
(*
  let faddr = index_to_doubleword index in
  let finfo = get_function_info faddr in
  let fname = get_function_name faddr in
  let memAccesses = finfo#get_global_accesses in
  let memAccesses = List.sort (fun (a1,_) (a2,_) -> a1#compare a2) memAccesses in
  let title = "References to global variables in " ^ fname in
  let dialog = GWindow.dialog ~title ~parent ~modal:false ~show:true 
    ~width:800 ~height:480 () in
  let window = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
    ~packing:dialog#vbox#add () in
  let xrefs = ref [] in
  let _ = assembly_functions#itera
    (fun callerAddress f ->
      f#iteri
	(fun _ iaddr instr ->
	  let operands = get_operands instr#get_opcode in
	  let operands = List.filter (fun op -> 
	    op#is_immediate_value && op#get_immediate_value#to_doubleword#equal faddr) operands in
	  match operands with
	    [] -> ()
	  | _ -> 
	    let loc = make_location callerAddress iaddr in
	    xrefs := loc :: !xrefs)) in
  let xrefCount = List.length !xrefs in
  let nGvars = List.length memAccesses in
  let table =
    GPack.table
      ~col_spacings:25
      ~row_spacings:5
      ~columns:5
      ~rows:(nGvars + 1)
      () in
  let _ =
    GMisc.label
      ~text:"address"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~text:"section"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:1)
      () in
  let _ =
    GMisc.label
      ~text:"inferred type"
      ~xalign:0.0 
      ~packing:(table#attach ~top:0 ~left:2)
      () in
  let _ =
    GMisc.label
      ~text:"writers/readers"
      ~xalign:0.0 
      ~packing:(table#attach ~top:0 ~left:3)
      () in
  let _ =
    GMisc.label
      ~text:"initial value"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:4)
      () in
  let _ = window#add_with_viewport table#coerce in
  let _ = GMisc.label ~text:"other accessors" ~xalign:0.0
    ~packing:(table#attach ~top:0 ~left:5) () in
  let get_type accs =
    let types = get_mem_type (List.map snd accs) in
    String.concat "-" (List.map btype_to_string types) in
  let get_permissions (s:pe_section_int) =
    if s#is_executable then " (RWX)" else if s#is_writable then " (RW)" else 
	if s#is_read_only then " (R)" else "" in
  let memacc_button title tooltip accesses packing =
    let numReaders =
      List.length
        (List.filter (fun (_,a) ->
             match a with
             | MARead _ | MAIndexedRead _ | MABlockRead _ -> true
             | _ -> false) accesses) in
    let numWriters =
      List.length
        (List.filter (fun (_,a) ->
             match a with 
	     | MAWrite _ | MAIndexedWrite _ | MABlockWrite _ -> true
             | _ -> false) accesses) in
    let numAcc = List.length accesses in
    if numAcc > 0 then
      let label = (string_of_int numWriters) ^ " / " ^ (string_of_int numReaders) in
      let button = GButton.button ~label ~packing () in
      let _ =
        button#connect#clicked ~callback:(show_accesses title accesses faddr parent) in
      let _ = button#misc#set_tooltip_text tooltip in
      () in
  let row = ref 1 in
  let _ = List.iter  (fun (gaddr,accs) ->
    let title = "writers/readers of " ^ gaddr#to_hex_string in
    let tooltip = "show " ^ title in
    let optSection = pe_sections#get_containing_section gaddr in
    let faccessors = global_var_accesses#get_gvar_accesses gaddr in
    let faccessors = List.map fst faccessors in
    let faccessors =
      String.concat ", " (List.map (fun f -> f#to_hex_string) faccessors) in
    let sName = match optSection with
      | Some section -> section#get_name ^ (get_permissions section)
      | _ -> "?" in
    let optInitVal = match optSection with
	Some section -> section#get_initialized_doubleword gaddr | _ -> None in
    let initVal = match optInitVal with Some dw -> dw#to_hex_string | _ -> "?" in
    let _ =
      GMisc.label
        ~text:gaddr#to_hex_string 
        ~packing:(table#attach ~left:0 ~top:!row)
        () in
    let _ =
      GMisc.label
        ~text:sName
        ~packing:(table#attach ~left:1 ~top:!row)
        () in
    let _ =
      GMisc.label
        ~text:(get_type accs) 
        ~packing:(table#attach ~left:2 ~top:!row)
        () in
    let _ = memacc_button title tooltip accs (table#attach ~left:3 ~top:!row)  in
    let _ =
      GMisc.label ~text:initVal ~packing:(table#attach ~left:4 ~top:!row) () in
    let _ =
      GMisc.label ~text:faccessors ~packing:(table#attach ~left:5 ~top:!row) () in
    row := !row+1 ) memAccesses in
      let floc = get_floc ~opt_inv:(Some (invio#get_location_invariant loc#i#to_hex_string)) loc in
      let annotation = create_annotation invio floc in
      let fname = get_function_name loc#f in
      let _ = GMisc.label ~text:fname ~xalign:0.0 ~packing:(table#attach ~top:!row ~left:0) () in
      let _ = GMisc.label ~text:loc#i#to_hex_string ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:1) () in
      let _ = GMisc.label ~text:(pp_str annotation#toPretty) ~xalign:0.0
	~packing:(table#attach ~top:!row ~left:2) () in
      row := !row + 1) !xrefs in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp ->dialog#destroy ()) in
  ()
 *)
                                                                  
let show_chif_dialog (function_index:dw_index_t) (parent:GWindow.window) =
  let function_address = TR.tget_ok (index_to_doubleword function_index) in
  let functionName = get_function_name function_address in
  let title = "CHIF for " ^ functionName in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let _ =
    GMisc.label
      ~text:"search: " ~justify:`LEFT ~packing:dialog#action_area#add () in
  let search_entry =
    GEdit.entry
      ~editable:true
      ~visibility:true
      ~show:true
      ~height:30
      ~packing:dialog#action_area#add
      () in
  let display_chif window contents =
    let _ = match contents with Some s -> window#remove s | _ -> () in
    let chifProcedure = chif_system#get_procedure_by_address function_address in
    let view = GText.view () in
    let _ = view#set_pixels_above_lines 5 in
    let _ = view#set_left_margin 10 in
    let buffer = view#buffer in
    let iter = buffer#get_iter `START in
    let _ = buffer#create_tag ~name:"yellow_background" [`BACKGROUND "yellow"] in
    let _ = buffer#insert ~iter (pp_str chifProcedure#toPretty) in
    let newcontents = view#coerce in
    let tagged_iters = ref [] in
    let add_tag s e = tagged_iters := (s,e) :: !tagged_iters in
    let remove_tags () =
      begin
	List.iter (fun (s,e) ->
            buffer#remove_tag_by_name "yellow_background" s e) !tagged_iters;
	tagged_iters := []
      end in
    let last_search = ref None in
    let _ = search_entry#connect#activate (fun () ->
      let text = search_entry#text in
      let _ = match !last_search with
	Some (last_text,_) when not (last_text = text) -> remove_tags ()
      | _ -> () in
      let start = match !last_search with 
	Some (last_text,last_end) when last_text = text -> last_end
      | _ -> buffer#start_iter in
      match start#forward_search text with
	Some (found_begin, found_end) ->
	  let _ = last_search := Some (text,found_end) in
	  let _ = buffer#apply_tag_by_name "yellow_background" found_begin found_end in
	  let _ = add_tag found_begin found_end in
	  let _ = view#scroll_to_iter ~yalign:(0.5) ~use_align:true found_begin in
	  ()
      | _ -> ()) in
    let _ = window#add newcontents in
    Some newcontents in
  let windowcontents = ref (display_chif window None) in
  let refreshButton = GButton.button ~stock:`REFRESH ~packing:dialog#action_area#add () in
  let _ =
    refreshButton#connect#clicked 
      ~callback:(fun () ->windowcontents := display_chif window !windowcontents) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in 
  ()
