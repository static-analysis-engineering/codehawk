(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* chgui *)
open CHCanvasBase

(* chutil *)
open CHLogger
open CHDot
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprToPretty
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionInfo
open BCHFunctionData
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHPreFileIO
open BCHSystemInfo

(* bchlibx86 *)
open BCHX86Opcodes
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHAssemblyInstructions
open BCHDisassemblyUtils
open BCHAssemblyInstructionAnnotations
open BCHLibx86Types

(* bchanalyze *)
open BCHFileIO

let get_function_name (address:doubleword_int) =
  if functions_data#has_function_name address then
    (functions_data#get_function address)#get_function_name
  else
    "function_" ^ address#to_fixed_length_hex_string



class type control_flow_graph_int =
object
  method to_dot:
           dw_index_t
           -> canvas_window_int
           -> (string * CHCanvasBase.canvas_node_item_int list)
  method to_annotated_dot:
           dw_index_t
           -> canvas_window_int
           -> (string * CHCanvasBase.canvas_node_item_int list)
end


let make_va_node_name (va:ctxt_iaddress_t) =  "n" ^ va


let get_address (nodeName:string) =  string_suffix nodeName 1


let get_floca faddr iaddr =
  let loc = ctxt_string_to_location faddr iaddr in
  get_floc loc

let pp_str = string_printer#print 
let sym_printer s = STR s#getBaseName

let get_cfg_menu_options (f:assembly_function_int) parent = 
  let faddr = f#get_address in
  let show_block name () =
    let block = f#get_block (get_address name) in
    let title = "block at " ^ block#get_first_address#to_hex_string in
    let instructionCount = block#get_instruction_count in
    let dialog = GWindow.dialog
      ~title ~parent ~modal:false ~show:true ~width:400 ~height:230 () in
    let window =
      GBin.scrolled_window 
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:dialog#vbox#add () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:10
        ~columns:1
        ~rows:instructionCount 
        ~packing:window#add_with_viewport
        () in
    let row = ref 0 in
    let _ =
      block#itera (fun iaddr instr ->
          let loc = ctxt_string_to_location faddr iaddr in
          let floc = get_floc loc in
          let annotation = create_annotation floc in
          let _ =
            GMisc.label
              ~text:(pp_str annotation#toPretty)
              ~xalign:0.0
	      ~packing:(table#attach ~left:0 ~top:!row)
              () in
          row := !row + 1 ) in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun () -> ()) in
    let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
    () in
  let show_callees name () =
    let block = f#get_block (get_address name) in
    let title = "callees from block " ^ block#get_first_address#to_hex_string in
    let dialog = GWindow.dialog 
      ~title ~parent ~modal:false ~show:true ~width:400 ~height:230 () in
    let window = 
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:dialog#vbox#add
        () in
    let callees = ref [] in
    let _ = block#itera
      (fun iaddr instr ->
	match instr#get_opcode with
	  DirectCall _ | IndirectCall _ ->
	    callees := (ctxt_string_to_location faddr iaddr) :: ! callees
	| _ -> () ) in
      let count = List.length !callees in
      let table =
        GPack.table
          ~col_spacings:25
          ~row_spacings:5
          ~columns:2 ~rows:count 
	  ~packing:window#add_with_viewport
          () in
      let row = ref 0 in
      let _ = List.iter
	(fun loc ->
	  let floc = get_floc loc in
	  let annotation = create_annotation floc in
	  let _ =
            GMisc.label
              ~text:loc#i#to_hex_string
              ~xalign:0.0
	      ~packing:(table#attach ~top:!row ~left:0)
              () in
	  let _ =
            GMisc.label
              ~text:(pp_str annotation#toPretty)
              ~xalign:0.0
	      ~packing:(table#attach ~top:!row ~left:1)
              () in
	  row := !row + 1) (List.rev !callees) in
      let _ = dialog#add_button_stock `CLOSE `CLOSE in
      let _ = dialog#connect#close ~callback:(fun () -> ()) in
      let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
      () in      
  [ make_node_menu_item "show block" show_block ;
    make_node_menu_item "show callees" show_callees ]

class control_flow_graph_t:control_flow_graph_int =
object

  method to_dot (index:dw_index_t) (canvas_window:canvas_window_int) =
    let f = assembly_functions#get_function index in
    let faddr = f#get_address in
    let fname = get_function_name faddr in
    let graphName = fname ^ "_cfg" in
    let graph = mk_dot_graph graphName in
    let  _ = f#itera (fun baddr block ->
	let nodeName = make_va_node_name baddr in
	let label = baddr in
	let _ = graph#addNode ~label nodeName in
	let sourceName = make_va_node_name baddr in
	List.iter
          (fun successor -> graph#addEdge sourceName (make_va_node_name successor))
	  block#get_successors) in
    let _ = graph#setRankdir "TB" in
    let cfg_menu_options = get_cfg_menu_options f canvas_window#get_window in
    let (graphNodes,_) =
      canvas_window#show_graph ~node_menu_options:cfg_menu_options graph graphName in
    (graphName,graphNodes)

  method to_annotated_dot (index:dw_index_t) (canvas_window:canvas_window_int) =
    let f = assembly_functions#get_function index in
    let faddr = f#get_address in
    let fname = get_function_name faddr in
    let finfo = get_function_info faddr in
    let xpr_formatter =
      make_xpr_formatter sym_printer finfo#env#variable_name_to_pretty in
    let pp_expr expr = pp_str (xpr_formatter#pr_expr expr) in
    let graphName = fname ^ "_acfg" in
    let graph = mk_dot_graph graphName in
    let _ = f#itera
      (fun baddr block ->
	let nodeName = make_va_node_name baddr in
	let label = baddr in
	let _ = graph#addNode ~label nodeName in
	let sourceName = make_va_node_name baddr in
	let edgeLabeling =
	  let lastAddress = block#get_last_address in
	  let lastInstruction = (!assembly_instructions)#at_address lastAddress in
	  let opcode = lastInstruction#get_opcode in
	  if is_conditional_jump_instruction opcode && finfo#has_test_expr lastAddress#to_hex_string then
	    let floc = get_floca faddr lastAddress#to_hex_string in
	    let thenExpr = finfo#get_test_expr lastAddress#to_hex_string in
	    let thenExpr = floc#inv#rewrite_expr thenExpr 
	      floc#f#env#get_variable_comparator in
	    let elseExpr = simplify_xpr (XOp (XLNot, [ thenExpr ])) in
	    let thenAddress =
	      let op = get_jump_operand opcode in
	      if op#is_absolute_address then
		op#get_absolute_address
	      else
		begin
		  ch_error_log#add
                    "internal error"
                    (STR "control_flow_graph#to_annotated_dot") ;
		  raise (Internal_error "control_flow_graph#to_annotated_dot")
		end in
	    Some (thenAddress, thenExpr, elseExpr)
	  else
	    None in
	match edgeLabeling with
	| None ->
	   List.iter (fun successor -> graph#addEdge sourceName (make_va_node_name successor))
	             block#get_successors
	| Some (thenAddress, thenExpr, elseExpr) ->
	  match block#get_successors with
	    [ firstSucc ; secondSucc ] ->
            let thenAddress = thenAddress#to_hex_string in
	    let elseAddress =
              if firstSucc = thenAddress then secondSucc else firstSucc in
	      let thenTargetName = make_va_node_name thenAddress in
	      let elseTargetName = make_va_node_name elseAddress in
	      begin
		graph#addEdge ~label:(pp_expr thenExpr) sourceName thenTargetName ;
		graph#addEdge ~label:(pp_expr elseExpr) sourceName elseTargetName
	      end
	  | _ ->
	    begin
	      ch_error_log#add
                "internal error"
                (STR "control_flow_graph#to_annotated_dot") ;
	      raise (Internal_error "control_flow_graph#to_annotated_dot")
	    end) in
    let _ = graph#setRankdir "TB" in
    let cfg_menu_options = get_cfg_menu_options f canvas_window#get_window in
    let (graphNodes,_) = 
      canvas_window#show_graph ~node_menu_options:cfg_menu_options graph graphName in
    (graphName,graphNodes)
      

end

let control_flow_graph = new control_flow_graph_t
