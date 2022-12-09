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
open CHPretty
open CHNumerical
open CHLanguage
open CHUtils
open CHIntervals
open CHSymbolicSets

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHCPURegisters
open BCHMemoryReference
open BCHPreFileIO
open BCHSystemInfo
open BCHVariable
open BCHVariableType

(* bchlibx86 *)
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHAssemblyInstructionAnnotations
open BCHIFSystem
open BCHLibx86Types
open BCHVariableNames

(* bchgui *)
open BCHCanvasUtil
open BCHGuiUtil

module TR = CHTraceResult


let pp_str p = string_printer#print p

let get_floca faddr iaddr =
  let loc = ctxt_string_to_location faddr iaddr in
  get_floc loc


let get_function_name (address:doubleword_int) =
  if functions_data#has_function_name address then
    (functions_data#get_function address)#get_function_name
  else
    "function_" ^ address#to_fixed_length_hex_string

class type expr_combo_int =
object
  method add_floc: floc_int -> unit
  method get_colors   : string option * string
  method toPretty : pretty_t
end

class expr_combo_t (finfo:function_info_int) (var:variable_t):expr_combo_int =
object (self)
  val var = var
  val env = finfo#env
  val variable_to_pretty = finfo#env#variable_name_to_pretty
  val mutable range = None
  val vars = new VariableCollections.set_t
  val mutable exprs = []

  method add_floc floc =
    if floc#is_constant var then 
      self#add_range (floc#get_constant var)
    else 
      let expr = floc#inv#rewrite_expr (XVar var) env#get_variable_comparator in
      match expr with
	XVar v -> if (env#is_stack_variable v) then () else vars#add v
      | _ -> self#add_expr expr

  method private add_range c =
    match range with
      None -> range <- Some (mkSingletonInterval c)
    | Some i -> range <- Some (i#join (mkSingletonInterval c))

  method private add_expr e = 
    if List.exists (fun x ->
           syntactically_equal e x) exprs then () else exprs <- e :: exprs

  method private is_constant =
    match exprs with
      [] -> vars#isEmpty && (match range with Some _ -> true | _ -> false)
    | _ -> false

  method private is_external =
    let exprVars = vars_in_expr_list exprs in
    List.exists (fun v -> env#is_function_initial_value v) (vars#toList @ exprVars)

  method private is_unknown =
    match (range,exprs) with
      (None, []) -> vars#isEmpty
    | _ -> false

  method private is_parent_register =
    match (range,exprs) with
      (None, []) ->
	begin
	  match vars#toList with
	    [ v ] -> env#is_initial_register_value v
	  | _ -> false
	end
    | _ -> false
      

  method get_colors =
    if self#is_constant then (None, "orange")
    else if self#is_parent_register then (None, "white")
    else if self#is_external then (Some "white", "red")
    else if self#is_unknown then (None, "gray")
    else (Some "white", "blue")

  method toPretty = 
    let image_base = system_info#get_image_base#to_numerical in
    let pp_constant c = 
      if c#gt image_base then
        STR (TR.tget_ok (numerical_to_hex_string c))
      else
        c#toPretty in
    let pp_interval i =
      match i#singleton with
      | Some c -> pp_constant c
      | _ -> i#toPretty in
    LBLOCK [
      (match range with None -> STR "" | Some i -> LBLOCK [ pp_interval i ; STR "; " ]) ;
      (match vars#toList with
	[] -> STR ""
       | [ v ] -> variable_to_pretty v
                (*
	if (env#is_initial_register_value v) then
	  let assemblyVar = env#get_assembly_variable v#getName in
	    match assemblyVar#get_denotation with
	      AuxiliaryVariable (InitialRegisterValue (CPURegister r,_)) -> 
		LBLOCK [ STR "saved parent register " ; STR (cpureg_to_string r) ]
	    | _ -> variable_to_pretty v
	else
	  variable_to_pretty v *)
      | l -> LBLOCK [ pretty_print_list l 
			(fun v -> variable_to_pretty v) "" ", " "" ; STR "; " ]) ;
      (pretty_print_list exprs (fun e -> xpr_formatter#pr_expr e) "" ", " "") ]

end
    


class type stack_frame_int =
object
  (* reset *)
  method reset: unit

  (* accessors *)
  method get_local_variables    : (variable_t * numerical_t) list 
  method get_parent_variables   : (variable_t * numerical_t) list
  method get_realigned_variables: (variable_t * numerical_t) list
  method display : GWindow.window -> unit
end


class stack_frame_t (f:assembly_function_int) =
object (self)

  val faddr = f#get_address
  val finfo = get_function_info f#get_address
  val env = (get_function_info f#get_address)#env
  val mutable local_variables = []
  val mutable parent_variables = []
  val mutable realigned_variables = []
  val mutable variables_initialized = false

  val expressions = Hashtbl.create 11
  val mutable expressions_initialized = false

  val types = Hashtbl.create 11
  val mutable types_initialized = false

  method reset = 
    begin
      local_variables <- [] ;
      parent_variables <- [] ;
      realigned_variables <- [] ;
      Hashtbl.clear expressions ;
      variables_initialized <- false ;
      expressions_initialized <- false ;
      Hashtbl.clear types ;
      types_initialized <- false
    end

  method trace_fwd op () = canvas#trace_graph_to_dot faddr#index op

  method private probe_vars = 
    if variables_initialized then () else self#initialize_variables

  method private probe_vals = 
    if expressions_initialized then () else self#initialize_expressions

  method private probe_types = if types_initialized then () else self#initialize_types

  method private initialize_variables =
    let localVars = finfo#env#get_local_stack_variables in
    let argVars = finfo#env#get_parent_stack_variables in
    let realgVars = finfo#env#get_realigned_stack_variables in
    (* let api = finfo#get_summary#get_function_api in *)
    let add_offset v =
      let n =
        match finfo#env#get_memvar_offset v with
        | ConstantOffset (n,_) -> n
        | _ -> numerical_zero in
      (v,n) in
        (* (v,(finfo#env#get_memvar_offset v)#get_offsetget_constant_offset) in *)
    begin
      local_variables <- 
	List.sort (fun (_,o1) (_,o2) -> o2#compare o1) (List.map add_offset localVars) ;
      parent_variables <-
	List.sort (fun (_,o1) (_,o2) -> o1#compare o2) (List.map add_offset argVars) ;
      realigned_variables <-
	List.sort (fun (_,o1) (_,o2) -> o2#compare o1) (List.map add_offset realgVars) 
    end
(*
    let proc = chif_system#get_procedure_by_address function_address in
    let variables = proc#getScope#getVariables in
    let variables = List.filter (fun v -> env#is_stack_variable v) variables in
    let variables = List.filter (fun v ->
      (env#get_var_memory_reference v)#get_offset#is_constant_offset) variables in
    let variables = List.sort
      (fun v1 v2 ->
	let m1 = env#get_var_memory_reference v1 in
	let m2 = env#get_var_memory_reference v2 in
	m1#get_offset#get_constant_offset#compare m2#get_offset#get_constant_offset) 
      variables in
    let (realigned, local, parent) = List.fold_left
      (fun (realigned,local,parent) v ->
	let m = env#get_var_memory_reference v in
	match m#get_base with
	  BRealignedStackFrame _ -> (v::realigned, local, parent)
	| BLocalStackFrame _ -> (realigned, v::local, parent)
	| BParentStackFrame _ -> (realigned, local, v::parent)
	| _ -> (realigned, local, parent)) ([],[],[]) variables in
    let add_offset l = 
      List.map (fun v -> 
	(v, (env#get_var_memory_reference v)#get_offset#get_constant_offset)) l in
    begin
      local_variables <- add_offset local ;
      parent_variables <- add_offset parent ;
      realigned_variables <- add_offset realigned ;
      variables_initialized <- true
    end
*)
  method private initialize_expressions =
    let _ = self#probe_vars in
    let _ = f#iteri
      (fun _ iaddr _ ->
	(*  let loc = make_location faddr iaddr in *)
	let floc = get_floca faddr iaddr in
	begin
	  List.iter (fun (v,_) -> self#add_expr floc v) local_variables ;
	  List.iter (fun (v,_) -> self#add_expr floc v) parent_variables ;
	  List.iter (fun (v,_) -> self#add_expr floc v) realigned_variables ;
	end) in
    expressions_initialized <- true
			
  method private add_expr floc v =
    let index = v#getName#getSeqNumber in
    let combo = 
      if Hashtbl.mem expressions index then
	Hashtbl.find expressions index
      else
	let c = new expr_combo_t finfo v in
	begin Hashtbl.add expressions index c ; c end in
    combo#add_floc floc
      
  method private initialize_types =
    let _ = self#probe_vars in
    let _ = f#iteri
      (fun _ iaddr _ ->
	(* let loc = make_location faddr iaddr in *)
	let getType var = topSymbolicSet in
	begin
	  List.iter (fun (v,_) -> self#add_type (getType v) v) local_variables ;
	  List.iter (fun (v,_) -> self#add_type (getType v) v) parent_variables ;
	  List.iter (fun (v,_) -> self#add_type (getType v) v) realigned_variables 
	end) in
    types_initialized <- true

  method private add_type ty v =
    let index = v#getName#getSeqNumber in
    let symset =
      if Hashtbl.mem types index then
	Hashtbl.find types index
      else
	bottomSymbolicSet in
    let newSymset = 
      match ty#getSymbols with
	TOP | BOTTOM -> symset
      | SET s1 -> symset#join ty in
    Hashtbl.replace types index newSymset
	
    
  method get_local_variables = begin self#probe_vars ; local_variables end
  method get_parent_variables = begin self#probe_vars ; parent_variables end
  method get_realigned_variables = begin self#probe_vars ; realigned_variables end

  method private get_flat_variables =
    let _ = self#probe_vars in
    List.concat [ parent_variables ; local_variables ; realigned_variables ]

  method private show_accesses title accessList parent () =
    let dialog = GWindow.dialog 
      ~title ~parent ~modal:false ~show:true ~width:800 ~height:480 () in
    let window =
      GBin.scrolled_window 
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:dialog#vbox#add
        () in
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
    (*	MARead _ | MAIndexedRead _ | MABlockRead _ -> true | _ -> false in *)
    let _ = List.iter (fun (iaddr,acc) ->
      let floc = get_floca faddr iaddr in
      let ann = create_annotation floc in
      let _ =
        GMisc.label ~text:iaddr ~packing:(table#attach ~top:!row ~left:0) () in
      let _ =
        GMisc.label
          (* ~text:(pp_str (memaccess_to_pretty acc)) *)
          ~text:(pp_str (STR "unsupported"))
          ~xalign:0.0
	  ~packing:(table#attach ~top:!row ~left:1)
          () in
      let col = if is_memory_read acc then 3 else 2 in       (* FIX *)
      let text = (pp_str ann#toPretty) in
      let _ = GMisc.label ~text ~packing:(table#attach ~left:col ~top:!row) () in
      row := !row + 1) accessList in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun () -> ()) in
    let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
    ()

  method display (parent:GWindow.window) =
    let _ = self#probe_vals in
    let _ = self#probe_types in
    let memAccesses = [] in (* finfo#get_stack_accesses in *)
    let memAccesses =
      List.map (fun (i,l) ->
          (i, List.map (fun (dw,a)  -> (dw#to_hex_string,a)) l)) memAccesses in
    let fname = get_function_name faddr in
    let variables = self#get_flat_variables in
    let variableCount = List.length variables in
    let title = "Stackframe for " ^ fname in
    let bounded v mn mx = if v > mx then mx else if v < mn then mn else v in
    let height = bounded ((40 * variableCount) + 40) 200 600 in
    let dialog = GWindow.dialog ~title ~parent ~modal:false ~show:true ~width:400 ~height () in
    let get_type v =
      (* let offset = env#get_memvar_offset v in
      let offset = match offset with
        | ConstantOffset (n,_) -> n#toInt
        | _ -> 1 in
      let offset = if memref#get_offset#is_constant_offset then
	  memref#get_offset#get_constant_offset#toInt else 1 in
      let ( _,accesses) = try (List.find (fun (i,_) -> i = offset) memAccesses) with
	  Not_found -> (0,[]) in *)
      let types = [] in
      (* get_mem_type (List.map snd accesses) in *)
      String.concat "-" (List.map btype_to_string types) in
    let memacc_button title tooltip v packing =
      let offset = env#get_memvar_offset v in
      let offset = match offset with
        | ConstantOffset (n,_) -> n#toInt
        | _ -> 1 in
      (* let offset = if memref#get_offset#is_constant_offset then
	  memref#get_offset#get_constant_offset#toInt else 1 in *)
      let (_,accesses) = try (List.find (fun (i,_) -> i = offset) memAccesses) with
	  Not_found -> (0,[]) in
      let numReaders = 0 in
                          (* List.length (List.filter (fun (_,a) -> match a with
	| MARead _ | MAIndexedRead _ | MABlockRead _ -> true | _ -> false) accesses) in *)
      let numWriters = 0 in
      (* List.length (List.filter (fun (_,a) -> match a with 
	  MAWrite _ | MAIndexedWrite _ | MABlockWrite _ -> true | _ -> false) accesses) in *)
      let numAcc = List.length accesses in
      if numAcc > 0 then
	let label = (string_of_int numWriters) ^ " / " ^ (string_of_int numReaders) in
	let button = GButton.button ~label ~packing () in
	let _ = button#connect#clicked ~callback:(self#show_accesses title accesses parent) in
	let _ = button#misc#set_tooltip_text tooltip in
	() in
    let add_frame label variables =
      let len = List.length variables in
      if len > 0 then
	let height = bounded (40 * len) 100 300 in
	let frame = GBin.frame ~label ~border_width:10 ~height ~packing:dialog#vbox#add () in
	let window = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC 
	  ~packing:frame#add () in
	let table = GPack.table ~row_spacings:15 ~col_spacings:10 ~columns:4 ~rows:len 
	  ~border_width:5 ~show:true ~packing:window#add_with_viewport () in
	let _ = GMisc.label ~text:"offset" ~packing:(table#attach ~left:0 ~top:0) () in
	let _ = GMisc.label ~text:"variable" ~packing:(table#attach ~left:1 ~top:0) () in
	let _ = GMisc.label ~text:"inferred type" ~packing:(table#attach ~left:2 ~top:0) () in
	let _ = GMisc.label ~text:"writers/readers" ~packing:(table#attach ~left:3 ~top:0) () in
	let row = ref 1 in
	List.iter (fun (v,offset) ->
            (* let memoffset = env#get_memvar_offset v  in *)
	    let title = "writers/readers of " ^ v#getName#getBaseName in
	    let tooltip = "show " ^ title in
	    let _ = if offset#toInt > 0 then
	              let button =
                        GButton.button
                          ~label:(pp_str offset#toPretty)
		          ~packing:(table#attach ~left:0 ~top:!row)
                          () in
	              let _ =
                        button#connect#clicked
                          ~callback:(self#trace_fwd (offset#toInt / 4)) in
	              ()
	            else 
	              ignore (GMisc.label
                                ~text:(pp_str offset#toPretty) 
	                        ~packing:(table#attach ~left:0 ~top:!row)
                                ()) in
	    let _ =
              GMisc.label
                ~text:v#getName#getBaseName 
	        ~packing:(table#attach ~left:1 ~top:!row)
                () in
	    let _ =
              GMisc.label
                ~text:(get_type v)  
	        ~packing:(table#attach ~left:2 ~top:!row)
                () in
	    let _ = memacc_button title tooltip v (table#attach ~left:3 ~top:!row) in
(*
	  let _ = try match appsig with
	      Some s ->
		begin
		  match label with
		    "arguments" ->
		      let numOffset = offset#toInt in
		      let index = numOffset / 4 in
		      let parameter = List.nth s#get_parameters (index-1) in
		      let _ = GMisc.label ~text:(parameter#get_name) 
			~packing:(table#attach ~left:4 ~top:!row) () in
		      let _ = GMisc.label ~text:(parameter#get_type#toString)
			~packing:(table#attach ~left:5 ~top:!row) () in
		      ()
		  | "local stack frame" ->
		    let numOffset = offset#neg#toInt in
		    if s#has_local numOffset then
		      let _ = GMisc.label ~text:(s#get_name_of_local numOffset) 
			~packing:(table#attach ~left:4 ~top:!row) () in
		      let _ = GMisc.label ~text:(s#get_type_of_local numOffset)#toString
			~packing:(table#attach ~left:5 ~top:!row) () in
		      ()
		  | _ -> ()
		end
	    | _ -> ()
	    with
	      _ -> () in
*)
	  row := !row+1 ) variables 
      else
	() in
    let _ = add_frame "arguments" self#get_parent_variables in
    let _ = add_frame "local stack frame" self#get_local_variables in
    let _ = add_frame "realigned stack frame" self#get_realigned_variables in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun () -> ()) in
    let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
    ()
end
	
let stackframes = Hashtbl.create 113

let get_stack_frame (index:dw_index_t) =
  if Hashtbl.mem stackframes index then
    Hashtbl.find stackframes index
  else
    let stack_frame = new stack_frame_t (assembly_functions#get_function index) in
    begin Hashtbl.add stackframes index stack_frame ; stack_frame end

let reset_stack_frame (function_address:doubleword_int) =
  let index = function_address#index in
  if Hashtbl.mem stackframes index then
    (Hashtbl.find stackframes index)#reset
  else
    ()
