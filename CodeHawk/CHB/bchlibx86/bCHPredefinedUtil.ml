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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprt *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHConstantDefinitions
open BCHCPURegisters
open BCHDoubleword
open BCHFunctionApi
open BCHFunctionData
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHFloc
open BCHLibTypes
open BCHLocation
open BCHMemoryReference
open BCHSystemInfo
open BCHVariableType

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHFunctionHashes
open BCHLibx86Types
open BCHOperand

module H = Hashtbl
module FFU = BCHFileFormatUtil
   

let todw s = string_to_doubleword (littleendian_hexstring_todwstring s)

let tow s = string_to_doubleword (littleendian_hexstring_towstring s)

let todwoff s = ((todw s)#to_signed_numerical)#toInt 

let tooff s = 
  let offset = string_to_doubleword ("0x" ^ s) in
  let offset = offset#to_int in
  if offset > 127 then offset - 256 else offset

let toimm2 s =  (string_to_doubleword ("0x" ^ s))#to_int

let is_code_address (n:numerical_t) = 
  system_info#is_code_address (numerical_to_doubleword n)

let intvalue_to_string (n:int) =
  try
    if n = wordnegone#to_int then
      "neg1"
    else if n = wordnegtwo#to_int then
      "neg2"
    else if system_info#get_image_base#lt (int_to_doubleword n) then
      (int_to_doubleword n)#to_hex_string
    else
	string_of_int n
  with
    _ -> string_of_int n

let regindexstring_to_reg (s:string) =
  match s with
  | "0" -> Eax | "1" -> Ecx | "2" -> Edx | "3" -> Ebx
  | "5" -> Ebp | "6" -> Esi | "7" -> Edi
  | s -> 
    begin
      ch_error_log#add "matched template with unexpected register"
	(LBLOCK [ STR "Character: " ; STR s ]) ;
      raise (BCH_failure
               (LBLOCK [ STR "Unexpected reg character in getregfield: " ;
			 STR s ]))
    end

let xpr_to_basepretty (x:xpr_t) =
  let sym_printer = (fun s -> STR s#getBaseName) in
  let variable_to_pretty v = STR v#getName#getBaseName in
  let xpr_formatter = make_xpr_formatter sym_printer variable_to_pretty in
  xpr_formatter#pr_expr x
    

let xpr_to_pretty (floc:floc_int) (x:xpr_t) =
  let sym_printer = (fun s -> STR s#getBaseName) in
  let variable_to_pretty = floc#env#variable_name_to_pretty in
  let xpr_formatter = make_xpr_formatter sym_printer variable_to_pretty in
  let default () = xpr_formatter#pr_expr x in
  try
    (match x with 
    | XVar v when floc#env#is_bridge_value v -> STR "?"
    | XConst (IntConst n) when FFU.is_image_address n -> (numerical_to_doubleword n)#toPretty
    | XVar v when v#isTemporary -> STR "?"
    | XConst XRandom -> STR "?"
    | _ -> default ())
  with
    _ -> default ()

let xpr_to_hexpretty (floc:floc_int) (x:xpr_t) =
  match x with
  | XConst (IntConst num) -> (numerical_to_doubleword num)#toPretty
  | _ -> xpr_to_pretty floc x

let xpr_to_fppretty (floc:floc_int) (x:xpr_t) = 
  try
    (match x with
     | XConst (IntConst num) ->
        LBLOCK [ STR "fp:" ; (numerical_to_doubleword num)#toPretty ]
     | _ -> xpr_to_pretty floc x)
  with
  | _ -> xpr_to_pretty floc x
       
let xpr_to_dspretty (floc:floc_int) (x:xpr_t) =
  try
    (match  x with
     | XConst (IntConst num) ->
        LBLOCK [ STR "ds:" ; (numerical_to_doubleword num)#toPretty ]
     | _ -> xpr_to_pretty floc x)
  with
  | _ -> xpr_to_pretty floc x
       
let xpr_to_strpretty (floc:floc_int) (x:xpr_t) =
  let default () = xpr_to_pretty floc x in
  try
    (match get_string_reference floc x with
     | Some str -> STR ("\"" ^ str ^ "\"")
     | _ -> match x with
            | XConst (IntConst n) when FFU.is_image_address n ->
	LBLOCK [ STR "ds:" ; (numerical_to_doubleword n)#toPretty ]
            | _ ->
	       if floc#is_address x then
	         let (memref,memoffset) = floc#decompose_address x in
	         if is_constant_offset memoffset then
                   let offset = get_total_constant_offset memoffset in
	           LBLOCK [ STR "&" ; 
		            xpr_to_pretty floc (XVar (floc#env#mk_memory_variable memref offset )) ]
	         else if memref#is_unknown_reference then
	           default ()
	         else
	           memref#toPretty
	       else
	         default ())
  with
  | _ -> default ()
       
let pr_argument_expr ?(typespec=None) (p:api_parameter_t) (xpr:xpr_t) (floc:floc_int) =
  match get_string_reference floc xpr with
  | Some s -> STR ("\"" ^ s ^ "\"")
  | _ -> 
     let x = simplify_xpr xpr in
     match get_xpr_symbolic_name ~typespec x with
     | Some name -> STR name
     | _ -> xpr_to_pretty floc x
          
let patternrhs_to_string (rhs:patternrhs_t) =
  match rhs with
  | PConstantValue n -> intvalue_to_string n#toInt
  | PRegister r -> cpureg_to_string r
  | PArgument i -> "arg" ^ (string_of_int i)
  | PGlobalVar dw -> "gv_" ^ (dw#to_hex_string)
  | PUnknown -> "?"
              
let get_arg args (n:int) (floc:floc_int) =
  let cmpv = floc#env#get_variable_comparator in 
  try
    let (_,arg) = List.find (fun (p,_) -> is_stack_parameter p n) args in
    floc#inv#rewrite_expr arg cmpv
  with
  | Not_found ->
    begin
      ch_error_log#add "get argument" 
	(LBLOCK [ floc#l#toPretty ; STR ": Unable to get argument " ; INT n ]) ;
      random_constant_expr
    end

let get_reg_value (reg:cpureg_t) (floc:floc_int) =
  let cmpv = floc#env#get_variable_comparator in
  floc#inv#rewrite_expr ((register_op reg 4 RD)#to_expr floc) cmpv

let get_gv_value (gv:doubleword_int) (floc:floc_int) =
  let cmpv = floc#env#get_variable_comparator in
  let v = floc#env#mk_global_variable gv#to_numerical in
  floc#inv#rewrite_expr (XVar v) cmpv

let get_reg_derefvalue (reg:cpureg_t) (offset:int) (floc:floc_int) =
  let cmpv = floc#env#get_variable_comparator in
  let deref = (indirect_register_op reg (mkNumerical offset) 4 RD)#to_expr floc in
  floc#inv#rewrite_expr deref cmpv

let get_x_derefvalue (x:xpr_t) (offset:int) (floc:floc_int) =
  let cmpv = floc#env#get_variable_comparator in
  let x = floc#inv#rewrite_expr (XOp (XPlus, [ x ; int_constant_expr offset ])) cmpv in
  let (memref,memoffset) = floc#decompose_address x in
  if is_constant_offset memoffset then
    let memvar = floc#env#mk_memory_variable memref (get_total_constant_offset memoffset) in
    floc#inv#rewrite_expr (XVar memvar) cmpv
  else
    XVar (floc#env#mk_unknown_memory_variable "x-deref")

let get_patternrhs_value ?(args=[]) (rhs:patternrhs_t) (floc:floc_int) =
  match rhs with
  | PConstantValue n -> num_constant_expr n
  | PRegister reg -> get_reg_value reg floc
  | PArgument n -> get_arg args n floc
  | PGlobalVar dw -> get_gv_value dw floc
  | PUnknown -> random_constant_expr
  
(* Semantics of inlined functions are defined relative to the stack pointer
   pointing at the first argument, rather than the return address, so offsets
   are adjusted by -4
*)
let get_var_lhs (varoffset:int) (floc:floc_int) =
  let offset = -(varoffset + 4) in               
  (esp_deref ~with_offset:offset WR)#to_lhs floc

let get_reg_lhs (r:cpureg_t) (floc:floc_int) =
  (register_op r 4 WR)#to_lhs floc

let get_reg_deref_lhs (r:cpureg_t) ?(size=4) (offset:int) (floc:floc_int) =
  (indirect_register_op r (mkNumerical offset) size WR)#to_lhs floc

let get_x_deref_lhs (x:xpr_t) (offset:int) (floc:floc_int) =
  let cmpv = floc#env#get_variable_comparator in
  let x = floc#inv#rewrite_expr (XOp (XPlus, [ x ; int_constant_expr offset ])) cmpv in
  let (memref,memoffset) = floc#decompose_address x in
  if is_constant_offset memoffset then
    floc#env#mk_memory_variable memref (get_total_constant_offset memoffset)
  else
    floc#env#mk_unknown_memory_variable "x-deref-lhs"

let get_nested_deref_lhs (r:cpureg_t) (offsets:int list) (floc:floc_int) =
  match offsets with
  | [] -> raise (BCH_failure 
		   (LBLOCK [ STR "Offsets missing in get_nested_deref_lhs: " ;
			     floc#l#toPretty ]))
  | [ off ] -> let (lhs,_) = get_reg_deref_lhs r off floc in lhs
  | off::tl ->
    let x = get_reg_derefvalue r off floc in
    let rec aux x l =
      match l with
      | [] -> raise (BCH_failure
		       (LBLOCK [ STR "Error in get_nested_deref_lhs"]))
      | [n] -> get_x_deref_lhs x n floc
      | n::ltl -> aux (get_x_derefvalue x n floc) ltl in
    aux x tl

let get_allocavar_lhs (varoffset:int) (allocaoffset:int) (floc:floc_int) =
  let offset = -(varoffset + allocaoffset + 4) in
  (esp_deref ~with_offset:offset WR)#to_lhs floc

let get_arg_lhs (argoffset:int) (floc:floc_int) =
  (esp_deref ~with_offset:(argoffset-4) WR)#to_lhs floc

let get_returnaddress_lhs (floc:floc_int) =
  (esp_deref ~with_offset:(-4) WR)#to_lhs floc

let get_return_value (name:string) (floc:floc_int) =
  let rv = floc#env#mk_return_value floc#cia in
  let name = name ^ "_rtn_" ^ floc#cia in
  let _ = floc#env#set_variable_name rv name in
  rv

let set_functionpointer (name:string) (floc:floc_int) (xpr:xpr_t) =
  let x = floc#inv#rewrite_expr xpr (floc#env#get_variable_comparator) in
  match x with
  | XConst (IntConst num) ->
    begin
      try 
	let dw = numerical_to_doubleword num in
	if system_info#is_code_address dw then
	  begin
	    ignore (functions_data#add_function dw) ;
	    chlog#add
              "predefined semantics declared function entry point"
	      (LBLOCK [ floc#l#toPretty ; STR ": " ; dw#toPretty ;
                        STR " set by " ; STR name ])
	  end
      with
	_ -> ()
    end
  | _ -> ()
       
let set_delphi_exception_handler_table (floc:floc_int) (x:xpr_t) =
  match x with
  | XConst (IntConst num) ->
    let tptr = (numerical_to_doubleword num)#add_int 4 in
    begin
      match FFU.get_read_only_initialized_doubleword tptr with
      | Some jtaddr when system_info#has_jumptable jtaddr ->
	begin
	  system_info#set_virtual_function_table jtaddr ;
	  chlog#add "exception handler table"
	    (LBLOCK [ floc#l#toPretty ; STR ": " ; xpr_to_pretty floc x ])
	end
      | _ ->
	chlog#add "exception handler table not found"
	  (LBLOCK [ floc#l#toPretty ; STR ": " ; xpr_to_pretty floc x ])
    end
  | _ -> ()
	  

let get_adjustment_commands (adj:int) (floc:floc_int) =
  if adj > 0 then
    let (esplhs,esplhscmds) = get_reg_lhs Esp floc in 
    let espv = get_reg_value Esp floc in
    let xadj = int_constant_expr adj in
    let cmds = floc#get_assign_commands esplhs (XOp (XPlus, [ espv ; xadj ])) in
    esplhscmds @ cmds
  else
    []

let get_wrapped_call_commands (hfloc:floc_int) (tgtfloc:floc_int) =
  let api = if tgtfloc#has_call_target_signature then
      tgtfloc#get_call_target_signature
    else
      (default_summary "default")#get_function_api in
  let eax = hfloc#env#mk_cpu_register_variable Eax in
  let opName = new symbol_t ~atts:["WRAPPEDCALL"] api.fapi_name in
  let returnAssign =
    let rvar = hfloc#env#mk_return_value hfloc#cia in
    let rty = api.fapi_returntype in
    if tgtfloc#has_call_target_signature then
      if is_void rty then
	SKIP
      else
	let name = api.fapi_name ^ "_rtn_" ^ hfloc#cia in
	let _ = hfloc#env#set_variable_name rvar name in
	let rty = api.fapi_returntype in
	begin
	  hfloc#f#ftinv#add_function_var_fact rvar rty ;
	  hfloc#add_var_type_fact eax rty ;
	  ASSIGN_NUM (eax, NUM_VAR rvar)
	end
    else
      ASSIGN_NUM (eax, NUM_VAR rvar) in
  let acmd = hfloc#get_abstract_cpu_registers_command [ Ecx ; Edx ] in
  let opcmd = OPERATION { op_name = opName ; op_args = [] } in
  let bridgevars = hfloc#env#get_bridge_values_at hfloc#cia in
  [ opcmd ; acmd ; returnAssign ; ABSTRACT_VARS bridgevars ]

let isnamed_app_call (faddr:doubleword_int) (offset:int) (fname:string) =
  let loc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int offset } in
  let floc = get_floc loc in
  floc#has_application_target &&
    (let tgt = floc#get_application_target in
     ((functions_data#has_function_name tgt) &&
	 ((functions_data#get_function tgt)#get_function_name = fname)))

let isnamed_dll_call (faddr:doubleword_int) (offset:int) (fname:string) =
  let loc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int offset } in  
  let floc = get_floc loc in
  floc#has_dll_target && (let (_,name) = floc#get_dll_target in name = fname)

let isnamed_inlined_call (faddr:doubleword_int) (offset:int) (fname:string) =
  let loc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int offset } in  
  let floc = get_floc loc in
  floc#has_inlined_target && (let (_,name) = floc#get_inlined_target in name = fname)

let isnamed_lib_call (faddr:doubleword_int) (offset:int) (fname:string) =
  let loc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int offset } in  
  let floc = get_floc loc in
  floc#has_static_lib_target &&
    (let (_,_,_,name) = floc#get_static_lib_target in name = fname)

  
let sometemplate ?(msg=STR "") (sem:predefined_callsemantics_int) =
  begin
    chlog#add "matched template function" (LBLOCK [ STR sem#get_name ; msg ]) ;
    Some sem
  end

let get_fnhashes (name:string) (f:string -> int -> predefined_callsemantics_int) =
  List.map (fun (hash,instrs) -> f hash instrs) (get_function_hashes name)

let get_return_assign summary floc = 
  let api = summary#get_function_api in
  let rty = api.fapi_returntype in
  if is_void rty then [] else
    let name = api.fapi_name in
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rv = get_return_value name floc in
    let cmds = floc#get_assign_commands lhs (XVar rv) in
    List.concat [ lhscmds ; cmds ]

let get_esp_adjustment_assign summary floc = 
  let api = summary#get_function_api in
  match api.fapi_stack_adjustment with
  | Some adj when adj > 0 -> get_adjustment_commands adj floc
  | Some _ -> []
  | _ -> [ floc#get_abstract_cpu_registers_command [ Esp ] ]

let get_side_effects summary floc = 
  floc#get_sideeffect_assigns summary#get_function_semantics

class virtual predefined_callsemantics_base_t (md5hash:string) (instrs:int) =
object (self)

  method virtual get_name: string

  method get_md5hash = md5hash

  method get_annotation (floc:floc_int) =
    LBLOCK [ STR "eax := " ; STR self#get_name ; STR "()" ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    List.concat [ lhscmds ; cmds1 ; cmds2 ]

  method virtual get_parametercount: int

  method get_instrcount = instrs

  method get_call_target (a:doubleword_int) = AppTarget a

  method get_description = self#get_name

  method toPretty = STR self#get_name

end
  
class dllfun_semantics_t (dll:string) (summary:function_summary_int) (md5hash:string) 
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name =
    let name = summary#get_function_api.fapi_name in "__" ^ name ^ "__"

  method get_annotation (floc:floc_int) =
    (* let api = summary#get_function_api in *)
    let pr_arg p xpr = 
      let typespec = summary#get_enum_type p in
      pr_argument_expr ~typespec p xpr floc in
    LBLOCK [ STR self#get_name  ;
	     pretty_print_list floc#get_call_args
	       (fun (p,expr) ->
		 LBLOCK [ STR p.apar_name ; STR ":" ; pr_arg p expr]) "(" "," ")" ]

  method get_commands (floc:floc_int) =
    let sideeffects = get_side_effects summary floc in
    let returnassign = get_return_assign summary floc in
    let adjassign = get_esp_adjustment_assign summary floc in
    let abstrassign = [ floc#get_abstract_cpu_registers_command [ Eax ; Ecx ; Edx ] ] in
    List.concat [ abstrassign ; sideeffects ; returnassign ; adjassign ]

  method get_parametercount = get_stack_parameter_count summary#get_function_api

  method get_call_target (a:doubleword_int) =
    let name = summary#get_function_api.fapi_name in
    StaticStubTarget(a, DllFunction (dll, name))

end

let mk_dllfun_semantics (dll:string) (fname:string) =
  let summary = function_summary_library#get_dll_function dll fname in
  new dllfun_semantics_t dll summary

let add_dllfun table (dll:string) (fname:string) =
  if function_summary_library#has_dll_function dll fname then
    begin
      H.add table fname (mk_dllfun_semantics dll fname) ;
      chlog#add "add statically linked dll function" 
	(LBLOCK [ STR dll ; STR ":" ; STR fname ])
    end
  else
    chlog#add "statically linked dll function not registered"
      (LBLOCK [ STR dll ; STR ":" ; STR fname ])

class libfun_semantics_t (pkgs:string list) (fname:string) summary (md5hash:string) 
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = 
    let pkgs = String.concat "::" pkgs in "__" ^ pkgs ^ "::" ^ fname ^ "__"

  method get_annotation (floc:floc_int) =
    let pr_arg p xpr =
      let typespec = summary#get_enum_type p in
      pr_argument_expr ~typespec p xpr floc in
    LBLOCK [ STR self#get_name  ;
	     pretty_print_list floc#get_call_args
	       (fun (p,expr) ->
		 LBLOCK [ STR p.apar_name ; STR ":" ; pr_arg p expr]) "(" "," ")" ]
      
  method get_commands (floc:floc_int) =
    let sideeffects = get_side_effects summary floc in
    let returnassign = get_return_assign summary floc in
    let adjassign = get_esp_adjustment_assign summary floc in
    let abstrassign = [ floc#get_abstract_cpu_registers_command [ Eax ; Ecx ; Edx ] ] in
    List.concat [ abstrassign ; sideeffects ; returnassign ; adjassign ]
      
  method get_parametercount = get_stack_parameter_count summary#get_function_api
    
  method get_call_target (a:doubleword_int) =
    StaticStubTarget(a,PckFunction ("RTL",pkgs,fname))

  method get_description = "RTL function"

end

let mk_libfun_semantics (pkgs:string list) (fname:string) =
  let summary = function_summary_library#get_lib_function pkgs fname in
  new libfun_semantics_t pkgs fname summary

let add_libfun table (pkgs:string list) (fname:string) =
  if function_summary_library#has_lib_function pkgs fname then
    let hname = (String.concat "::" pkgs) ^ "::" ^ fname in
    begin
      H.add table hname (mk_libfun_semantics pkgs fname) ;
      chlog#add "add statically linked library function"
	(LBLOCK [ STR (String.concat "::" pkgs) ; STR "::" ; STR fname])
    end
  else
    chlog#add "statically linked library function not registered"
      (LBLOCK [ STR (String.concat "::" pkgs) ; STR "::" ; STR fname ])


