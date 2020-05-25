(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* chutil *)
open CHDot
open CHPrettyUtil

(* chgui *)
open CHCanvasBase

(* bchlib *)
open BCHDoubleword
open BCHLibTypes

(* bchlibx86 *)
open BCHX86Opcodes
open BCHAssemblyBlock
open BCHAssemblyFunctions
open BCHLibx86Types

(* bchgui *)
open BCHGuiUtil

class type orphan_code_int =
object
  method reset: unit
  method to_dot: canvas_window_int -> unit
  method toString: string
end

let make_block_node_name (block:assembly_block_int) =
  "n" ^ (dw_index_to_string block#get_first_address#index)
  
let make_va_node_name (va:doubleword_int) =
  "n" ^ (dw_index_to_string va#index)
  
let get_address (nodeName:string) =
  index_to_doubleword (string_to_dw_index (string_suffix nodeName 1))

let pp_str = string_printer#print 

let is_nop_slide b = 
  List.for_all (fun instr -> is_nop_instruction instr#get_opcode) b#get_instructions

(* the last instruction is a dll jump and all other instructions are nop's *)
let is_nop_slide_to_dll_jump b = false      (* FIX *)
(*  let rec aux instructions = 
    match instructions with
	[] -> false
      | [ instr ] when jump_targets#has_dll_jump instr#get_address -> true
      | instr::tl -> is_nop_instruction instr#get_opcode && aux tl in
  aux b#get_instructions   *)

let get_menu_options parent =
  let add_function_entry_point name () =
    let address = get_address name in
    let action () = ()   (* user_provided_application_facts#add_function_entry_point address *) in     (* FIX *)
    confirmation_dialog ~title:"Confirm function entry point"
      ~label:("Declare " ^ address#to_hex_string ^ " a function entry point") ~yes_action:action
      ~no_action:(fun () -> ()) ~parent in
  [ make_node_menu_item "declare function entry" add_function_entry_point ]
    


class orphan_code_t:orphan_code_int =
object (self)

  val mutable orphan_code = []
  val mutable creation_time = None

  method reset =
    begin
      orphan_code <- [] ;
      creation_time <- None
    end

  method private get_orphan_code =   ()    (* FIX *)
(*
    let get_code () =
      begin
	orphan_code <- BCHDisassemble.get_orphan_code () ;
	creation_time <- Some (Unix.gettimeofday ()) 
      end in
    match creation_time with
	Some cTime -> if creation_times#is_orphan_code_up_to_date cTime then () else get_code ()
      | _ -> if creation_times#is_orphan_code_available then get_code () else ()
*)

  method to_dot (canvas:canvas_window_int) =   ()
(*
    let _ = self#get_orphan_code in
    match creation_time with None -> () | _ ->
      let graphName = "orphan_code" in
      let g = new dot_graph_t graphName in
      let _ =
	List.iter
	  (fun block ->
	    if is_nop_slide block || is_nop_slide_to_dll_jump block then () else
	    g#addNode ~label:block#get_first_address#to_hex_string (make_block_node_name block) )
	  orphan_code in
      let _ = 
	List.iter
	  (fun (src,dst) -> 
	    begin
	      g#addEdge (make_va_node_name src) (make_va_node_name dst);
	      if assembly_functions#includes_instruction_address dst then
		let containingFunction = assembly_functions#get_containing_function dst in
		let fname = if assembly_xreference_service#has_function_name containingFunction then
		    assembly_xreference_service#get_function_name containingFunction 
		  else
		    dst#to_hex_string in
		g#addNode ~label:fname (make_va_node_name dst)
	    end )
	  (List.fold_left
	     (fun a block -> 
	       if is_nop_slide block then a else 
		 (List.map (fun s -> (block#get_first_address,s)) block#get_successors) @ a)
	     [] orphan_code) in
      let _ = g#setRankdir "TB" in
      let node_menu_options = get_menu_options canvas#get_window in
      let (nodes,_) = canvas#show_graph ~node_menu_options g graphName in
      let _ =
	List.iter (fun node ->
	  let va = get_address node#get_name in
	  if assembly_functions#has_function_by_address va then 
	    node#set_color CHCanvasBase.green
	  else if assembly_functions#includes_instruction_address va then
	    node#set_color CHCanvasBase.light_blue) nodes in
      ()
*)	  
	    

  method toString = "TBD" 
(*
    let _ = self#get_orphan_code in
    match creation_time with None -> "Precursors to orphan code are not available" | _ ->
      let nBlocks = List.length orphan_code in
      let nInstrs = List.fold_left (fun a block -> a + block#get_instruction_count) 0 orphan_code in
      let nBlocksSlide = 
	List.length 
	  (List.filter (fun block ->is_nop_slide block || is_nop_slide_to_dll_jump block) orphan_code) in
      let nInstrsSlide = List.fold_left (fun a b -> a + b#get_instruction_count) 0
	(List.fold_left 
	   (fun a block -> if is_nop_slide block || is_nop_slide_to_dll_jump block then block::a else a) 
	   [] orphan_code) in
      let str = List.fold_left
	(fun a block ->
	  let successors = block#get_successors in
	  let (inCodeSuccessors,otherSuccessors) = 
	    List.fold_left (fun (inCode,other) va ->
	      if assembly_functions#includes_instruction_address va then 
		let containingFunction = assembly_functions#get_containing_function va in
		((va,containingFunction)::inCode, other) 
	      else 
		(inCode, va::other)) ([],[]) successors in	
	  let inCodeSuccessorStr = match inCodeSuccessors with
	      [] -> ""
	    | _ -> "in-code successors: " ^ 
	      (String.concat ", " 
		 (List.map (fun (va,fAddress) -> 
		   let fname = if assembly_xreference_service#has_function_name fAddress then
		       assembly_xreference_service#get_function_name fAddress
		     else
		       fAddress#to_hex_string in
		   va#to_hex_string ^ " (in " ^ fname ^ ")") inCodeSuccessors)) ^ "\n" in
	  let otherSuccessorStr = match otherSuccessors with
	      [] -> ""
	    | _ -> "successors: " ^
	      (String.concat ", " (List.map (fun va -> va#to_hex_string) otherSuccessors)) ^ "\n" in
	  if is_nop_slide block || is_nop_slide_to_dll_jump block then
	    a ^ "\n\n" ^ "nop-slide: " ^ block#get_first_address#to_hex_string ^ " to " ^ 
	      inCodeSuccessorStr ^ otherSuccessorStr
	  else
	    a ^ "\n\n" ^ block#toString ^ "\n     " ^ inCodeSuccessorStr  ^ otherSuccessorStr)
	"" orphan_code in
      let preface = Printf.sprintf 
	"Number of orphan blocks: %d (in slides: %d)\nNumber of orphan instructions: %d (in slides: %d)\n\n"
	nBlocks nBlocksSlide nInstrs nInstrsSlide in
      preface ^ str
*)

end

let orphan_code = new orphan_code_t
