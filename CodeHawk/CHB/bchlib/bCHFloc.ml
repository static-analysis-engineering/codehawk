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

(* chlib *)
open CHBounds
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHFormatStringParser
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprUtil
open Xsimplify
open XprXml

(* bchlib *)
open BCHApiParameter
open BCHBasicTypes
open BCHBTerm
open BCHCallTarget
open BCHCPURegisters
open BCHDemangler
open BCHDoubleword
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHGlobalState
open BCHJumpTable
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHMakeCallTargetInfo
open BCHMemoryReference
open BCHPostcondition
open BCHPrecondition
open BCHSideeffect
open BCHStrings
open BCHSystemInfo
open BCHSystemSettings
open BCHTypeDefinitions
open BCHUtilities
open BCHVariable
open BCHVariableNames
open BCHVariableType
open BCHXprUtil

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory

module POAnchorCollections = CHCollections.Make
  (struct
    type t = po_anchor_t
    let compare = po_anchor_compare
    let toPretty = po_anchor_to_pretty
   end)

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)

(* Split a list into two lists, the first one with n elements,
   the second list with the remaining (if any) elements
*)
let split_list (n:int) (l:'a list):('a list * 'a list) =
  let rec loop i p l =
    if i = n then 
      (List.rev p,l)
    else loop (i+1) ((List.hd l)::p) (List.tl l) in
  if (List.length l) <= n then (l,[]) else loop 0 [] l

let unknown_write_symbol = new symbol_t "unknown write"

let set_interval inode intv =
  if intv#isTop then () else
    if intv#isBottom then inode#setAttribute "bot" "yes"
    else
      match intv#singleton with
	Some num -> inode#setAttribute "cst" num#toString
      | _ ->
	let low = intv#getMin#getBound in
	let high = intv#getMax#getBound in
	let _ = match low with 
	    NUMBER num -> inode#setAttribute "lo" num#toString
	  | _ -> () in
	let _ = match high with
	    NUMBER num -> inode#setAttribute "hi" num#toString
	  | _ -> () in
	()

let get_rhs_op_args (exp:numerical_exp_t) =
  match exp with
  | NUM _ -> []
  | NUM_VAR v -> [ ("rhs", v, READ) ]
  | PLUS (v1,v2) | MINUS (v1,v2) | MULT (v1,v2) | DIV (v1,v2) ->
     [ ("rhs1",v1,READ) ; ("rhs2",v2,READ) ]

let get_offset_sign offset =
  match offset#singleton with
    Some num -> 
    if num#is_zero then
      "zero"
    else
      if num#gt numerical_zero then "pos" else "neg"
  | _ -> if offset#isTop then "top"
    else if offset#isBottom then "bottom"
    else if offset#isBounded then "bounded"
    else "halfopen"

let compare_ref (m1,o1) (m2,o2) =
  if m1#is_unknown_reference then 1
  else if m2#is_unknown_reference then (-1)
  else 0

let select_best_ref (refs:(memory_reference_int * memory_offset_t) list) =
  List.hd (List.sort compare_ref refs)
  
module ExprCollections = CHCollections.Make (struct
  type t = xpr_t
  let compare = Xprt.syntactic_comparison
  let toPretty = x2p
end)


let check_chain_for_address (cfaddr:doubleword_int) (v:variable_t) = false

class floc_t (finfo:function_info_int) (loc:location_int):floc_int =
object (self)

  method ia = loc#i
  method fa = loc#f
  method cia = loc#ci
  method f = finfo
  method l = loc

  method env = self#f#env
  method inv = self#f#iinv self#cia
  method tinv = self#f#itinv self#cia


  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   *                                                                     return values *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method record_return_value =
    let eax = self#env#mk_cpu_register_variable Eax in
    let returnExpr = self#rewrite_variable_to_external eax in
    self#f#record_return_value self#cia returnExpr

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   *                                                                   type_invariants *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method add_var_type_fact v ?(structinfo=[]) t = 
    if v#isTmp then () else 
      if self#f#env#is_initial_memory_value v || 
	self#f#env#is_initial_register_value v then
	self#f#ftinv#add_function_var_fact v ~structinfo t
      else 
	self#f#ftinv#add_var_fact self#cia v ~structinfo t 

  method add_const_type_fact c t =
    begin
      self#f#ftinv#add_const_fact self#cia c t ;
      match t with
      | TPtr (tty,_) when c#gt numerical_zero ->
         (try
	    let base = numerical_to_doubleword c in
	    if system_info#get_image_base#le base then
	      let gv = self#f#env#mk_global_variable c in
	      begin
	        self#add_var_type_fact gv tty ;
	        match tty with
	        | TNamed (name,_) when type_definitions#has_type name ->
	           let tinfo = type_definitions#get_type name in
	           begin
		     match tinfo with
		     | TComp (SimpleName cname,[],_) when type_definitions#has_compinfo cname ->
		        let cinfo = type_definitions#get_compinfo cname in
		        List.iter (fun fldinfo ->
                            let goffset = c#add (mkNumerical fldinfo.bfoffset) in
		            let gvar = self#f#env#mk_global_variable goffset in
		            self#add_var_type_fact
                              gvar
                              ~structinfo:[name ; fldinfo.bfname ]
                              fldinfo.bftype) cinfo.bcfields
		     | _ -> ()
	           end
	        | _ -> ()
	      end
          with
          | BCH_failure p ->
             let msg = LBLOCK [ STR "add_const_type_fact: " ; c#toPretty ;
                                STR "; " ; self#l#toPretty ; STR " (" ; p ; STR ")" ] in
             begin
               ch_error_log#add "doubleword conversion" msg ;
               ()
             end)
      | _ -> ()
    end

  method add_xpr_type_fact x t =
    if is_random x then () else
      if List.exists (fun v -> v#isTmp) (variables_in_expr x) then () else
	try
	  begin
	    match x with
	    | XVar v -> self#add_var_type_fact v t
	    | XConst (IntConst c) -> self#add_const_type_fact c t
	    | XOp (XPlus, [ XVar v ; XConst _ ])
	    | XOp (XMinus, [ XVar v ; XConst _ ]) when (not (is_pointer t)) -> 
	      self#add_var_type_fact v t
	    | XOp (XMinus, [ XVar v ; XConst (IntConst n) ])
		when self#f#env#is_initial_stackpointer_value v && n#gt numerical_zero ->
	      let memref = self#f#env#mk_local_stack_reference in
	      let localVar = self#f#env#mk_memory_variable memref n#neg in
	      let tty = match t with
		| TPtr (tty,_) -> tty
		| _ ->
                   raise (BCH_failure (STR "Internal error in add_xpr_type_fact")) in
	      begin
		self#add_var_type_fact localVar tty ;
		match tty with 
		| TNamed (name,_) when type_definitions#has_type name ->
		  let tinfo = type_definitions#get_type name in
		  begin
		    match tinfo with
		    | TComp (SimpleName cname,[],_) when type_definitions#has_compinfo cname ->
		      let cinfo = type_definitions#get_compinfo cname in
		      List.iter (fun fldinfo ->
			let off = n#neg#add (mkNumerical fldinfo.bfoffset) in
			let memref = self#f#env#mk_local_stack_reference in
			let svar = self#f#env#mk_memory_variable memref off in
			self#add_var_type_fact
                          svar
                          ~structinfo:[name ; fldinfo.bfname ]
                          fldinfo.bftype) cinfo.bcfields
		    | _ -> ()
		  end
		| _ -> ()
	      end
	    | _ -> self#f#ftinv#add_xpr_fact self#cia x t
	  end
	with
	| Invalid_argument msg -> ()


  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   *                                                                      call targets *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method set_call_target (ctinfo:call_target_info_int) =
    self#f#set_call_target self#cia ctinfo

  method has_call_target = self#f#has_call_target self#cia

  method get_call_target = self#f#get_call_target self#cia

  method update_call_target =
    if self#has_call_target then
      let ctinfo = self#get_call_target in
      if ctinfo#is_signature_valid then
        match self#update_varargs ctinfo#get_signature with
        | Some fapi ->
           let _ =
             chlog#add
               "update call target api"
               (LBLOCK [ self#l#toPretty ; STR ": " ;
                         STR fapi.fapi_name ; STR ": " ;
                         INT (List.length fapi.fapi_parameters) ]) in
           self#set_call_target (update_target_api ctinfo fapi)
        | _ -> ()
      else
        ()
    else
      ()

  method private update_x86_varargs (s:function_api_t) = None

  method private update_mips_varargs (s:function_api_t) =
    let args = self#get_mips_call_arguments in
    let argcount = List.length args in
    let arg =
      List.fold_left
        (fun acc (p,x) ->
          match acc with
          | Some _  -> acc
          | _ -> if is_formatstring_parameter p then Some x else None) None args in
    match arg with
    | Some (XConst (IntConst n)) ->
       let addr = numerical_to_doubleword n in
       if string_table#has_string addr then
         let fmtstring = string_table#get_string addr in
         let _ = pverbose [ STR "Parse formatstring: " ; STR fmtstring ; NL ] in
         let fmtspec = parse_formatstring fmtstring false in
         if fmtspec#has_arguments then
           let args = fmtspec#get_arguments in
           let pars =
             List.mapi
               (fun i arg -> convert_fmt_spec_arg (argcount + i) arg) args in
           let newpars = s.fapi_parameters @ pars in
           begin
             chlog#add
               "format args"
               (LBLOCK [ self#l#toPretty ; STR ": " ;
                         STR s.fapi_name ; STR ": " ; INT (List.length args) ]) ;
             Some { s with fapi_parameters = newpars }
           end
         else
           None
       else
         None
    | _ -> None

  method private update_varargs (s:function_api_t) =
    match s.fapi_va_list with
    | Some _ -> None
    | _ ->
       if system_info#is_mips then
         self#update_mips_varargs s 
       else
         self#update_x86_varargs s

  (* experience so far:
     the first four arguments are passed in $a0-$a3, remaining arguments are passed
     via the stack, with the fifth argument starting at offset sp+16 *)
  method get_mips_call_arguments =
    let get_regargs pars =
      List.mapi
        (fun i p ->
          let reg = get_mipsreg_argument i in
          let avar = self#env#mk_mips_register_variable reg in
          (p, self#inv#rewrite_expr (XVar avar) self#env#get_variable_comparator))
        pars in
    let get_stackargs pars =
      List.map
        (fun p ->
          match p.apar_location with
          | StackParameter i ->
             let memref = self#f#env#mk_local_stack_reference in
             let argvar =
               match self#get_stackpointer_offset "mips" with
               | (0,sprange) ->
                  (match sprange#singleton with
                   | Some num -> 
                      self#f#env#mk_memory_variable memref (num#add (mkNumerical 16))
                   | _ -> self#f#env#mk_unknown_memory_variable p.apar_name)
               | _ -> self#f#env#mk_unknown_memory_variable p.apar_name in
             (p, self#inv#rewrite_expr (XVar argvar) self#env#get_variable_comparator)
          | _ ->
             raise (BCH_failure (LBLOCK [ STR "Unexpected parameter type in " ;
                                          self#l#toPretty ])))
        pars in
    let ctinfo = self#get_call_target in
    if ctinfo#is_signature_valid then
      let fapi = ctinfo#get_signature in
      let npars = List.length fapi.fapi_parameters in
      if npars < 5 then
        get_regargs fapi.fapi_parameters
      else
        let (regpars,stackpars) = split_list 4 fapi.fapi_parameters in
        List.concat [ (get_regargs regpars);  (get_stackargs stackpars) ]
    else
      []

  method set_instruction_bytes (b:string) = self#f#set_instruction_bytes self#cia b

  method get_instruction_bytes = self#f#get_instruction_bytes self#cia

  method private get_wrapped_call_args =
    let ctinfo = self#get_call_target in
    let argmapping = ctinfo#get_wrapped_app_parameter_mapping in
    List.map (fun (p,t) -> 
      let x = match t with
      | ArgValue p -> self#evaluate_api_argument p
      | NumConstant x -> num_constant_expr x
      | _ -> random_constant_expr in
      (p,x)) argmapping

  method get_call_args =
    let ctinfo = self#get_call_target in
    if ctinfo#is_wrapped_app_call then
      self#get_wrapped_call_args
    else if ctinfo#is_signature_valid then
      let api = ctinfo#get_signature in
      let pcompare p1 p2 = 
	parameter_location_compare p1.apar_location p2.apar_location in
      let parameters = List.sort pcompare api.fapi_parameters in 
      List.map (fun p -> (p,self#evaluate_api_argument p)) parameters
    else if system_info#has_esp_adjustment self#l#base_f self#l#i then
      let adj = system_info#get_esp_adjustment self#l#base_f self#l#i in
      let adj = adj / 4 in
      let indices = 
	let rec add acc n = if n <= 0 then acc else add (n::acc) (n-1) in add [] adj in
      List.map (fun p ->
	let par = mk_stack_parameter p in
	let argvar = self#f#env#mk_bridge_value self#cia p in
	let argval = self#get_bridge_variable_value p argvar in
	(par,argval)) indices
    else
      []

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save IndReg (cpureg, offset)   (memrefs1)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
	
  method get_memory_variable_1 (var:variable_t) (offset:numerical_t) =
    let _ = track_function
              ~iaddr:self#cia self#fa
              (LBLOCK [ STR "get_memory_variable_1: " ;  var#toPretty ; STR  " @ " ;
                        offset#toPretty]) in
    let default () =
      self#env#mk_memory_variable
        (self#env#mk_unknown_memory_reference "memref-1") offset in
    let inv = self#inv in
    let get_base_offset_constant inv =
      if inv#is_base_offset_constant var then
	let (base,offsetConstant) = inv#get_base_offset_constant var in
	let memoffset = offsetConstant#add offset in
        let memref = self#env#mk_base_sym_reference base in
        let _ = track_function
                  ~iaddr:self#cia self#fa
                  (LBLOCK [ STR "base-offset: " ;
                            STR "memref: " ; memref#toPretty ;
                            STR "; memoffset: " ; memoffset#toPretty ]) in
        self#env#mk_memory_variable memref memoffset
      else
        default () in
    let get_var_from_address () =
      let addr = XOp (XPlus, [ XVar var ; num_constant_expr offset ]) in
      let _ =
        track_function
          ~iaddr:self#cia self#fa
          (LBLOCK [ STR "get_memory_variable_1: addr: " ; x2p addr ]) in
      let address = inv#rewrite_expr addr (self#env#get_variable_comparator) in
      let _ =
        track_function
          ~iaddr:self#cia self#fa
          (LBLOCK [ STR "get_memory_variable_1: address: " ; x2p address ]) in
      match address with
      | XConst (IntConst n) ->
         (try
            let base = numerical_to_doubleword n in
            if system_info#get_image_base#le base then
              self#env#mk_global_variable n
            else
              default ()
          with
          | BCH_failure p ->
             raise (BCH_failure
                      (LBLOCK [ STR "get_memory_variable_1.get_var_from_address: " ;
                                STR "; " ; self#l#toPretty ;
                                n#toPretty ; STR " (" ; p ; STR ")" ])))
      | _ ->
         let (memref,memoffset) = self#decompose_address  address in
         if is_constant_offset memoffset then
           let memvar = self#env#mk_memory_variable memref (get_total_constant_offset memoffset) in
           let _ =
             track_function
               ~iaddr:self#cia self#fa
               (LBLOCK [ STR "get_memory_variable_1: memvar: " ; memvar#toPretty ;
                         STR " (from " ; memref#toPretty ; STR " and " ;
                         memory_offset_to_pretty memoffset ]) in
           memvar
         else
           default () in
    let memvar = get_base_offset_constant inv in
    let _ =
      track_function
        ~iaddr:self#cia self#fa
        (LBLOCK [ STR "get_memory_variable_1: memvar " ; memvar#toPretty ]) in
    if self#env#is_unknown_memory_variable memvar || memvar#isTmp then
      get_var_from_address ()
    else
      memvar
      										    
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save ScaledReg (cpureg1, cpureg2, 1, offset)   (memrefs2)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_memory_variable_2 (var1:variable_t) (var2:variable_t) (offset:numerical_t) =
    let _ = track_function
              ~iaddr:self#cia self#fa
              (LBLOCK [ STR "get_memory_variable_2: " ;
                        STR "var1: " ;  var1#toPretty ;
                        STR "; var2: " ; var2#toPretty ;
                        STR "; offset: " ; offset#toPretty ]) in
    let addr = XOp (XPlus, [ XVar var1 ; XVar var2 ]) in
    let addr = XOp (XPlus, [ addr ; num_constant_expr offset ]) in
    let address = self#inv#rewrite_expr addr (self#env#get_variable_comparator) in
    let (memref,memoffset) = self#decompose_address address in
    if is_constant_offset memoffset then
      self#env#mk_memory_variable memref (get_total_constant_offset memoffset)
    else
      self#env#mk_memory_variable (self#env#mk_unknown_memory_reference "memref-2") numerical_zero
      											    
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save ScaledReg (cpureg1, cpureg2, s, offset)  (memrefs3)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_memory_variable_3 (base:variable_t) (index:variable_t) (scale:int) 
    (offset:numerical_t) =
    let default () =
        self#env#mk_memory_variable (self#env#mk_unknown_memory_reference "memref-1") offset in      
    let inv = self#inv in
    let comparator = self#env#get_variable_comparator in
    let indexExpr = 
      if inv#is_constant index then 
	num_constant_expr (inv#get_constant index) else XVar index in
    let addr = XOp (XPlus, [ XVar base ; num_constant_expr offset ]) in
    let addr = self#inv#rewrite_expr addr comparator in
    let addr = XOp (XPlus, [ addr ; 
			     XOp (XMult, [ int_constant_expr scale ; indexExpr ]) ]) in
    let address = self#inv#rewrite_expr addr comparator in
    let (memref,memoffset) = self#decompose_address  address in
    if is_constant_offset memoffset then
      self#env#mk_memory_variable memref (get_total_constant_offset memoffset)
    else
      default ()
     											    
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save ScaledReg (None,indexreg, scale, offset)  (scale <> 1)  (memrefs4)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
	
  method get_memory_variable_4 (index:variable_t) (scale:int) (offset:numerical_t) =
    let indexExpr = self#rewrite_variable_to_external index in
    let offsetXpr = simplify_xpr (XOp (XMult, [ int_constant_expr scale ; indexExpr ])) in
    let offsetXpr = simplify_xpr (XOp (XPlus, [num_constant_expr offset ; offsetXpr ])) in
    let default () = self#env#mk_unknown_memory_variable (x2s offsetXpr) in
    match offsetXpr with
    | XConst (IntConst n) when n#geq nume32 ->
       let n = n#modulo nume32 in
       (try
          let base = numerical_to_doubleword n in
          if system_info#get_image_base#le base then
            self#env#mk_global_variable n
          else
            default ()
        with
        | BCH_failure p ->
           raise (BCH_failure
                    (LBLOCK [ STR "get_memory_variable_4: " ; n#toPretty ;
                              STR "; " ; self#l#toPretty ;
                              STR " (" ; p ; STR ")" ])))
    | XConst (IntConst n) ->
       (try
          let base = numerical_to_doubleword n in
          if system_info#get_image_base#le base then
            self#env#mk_global_variable n
          else
            default ()
        with
        | BCH_failure p ->
           raise (BCH_failure
                    (LBLOCK [ STR "get_memory_variable_4: " ; n#toPretty ;
                              STR "; " ; self#l#toPretty ;
                              STR " (" ; p ; STR ")" ])))
    | _ ->
       begin
         track_function
           ~iaddr:self#cia self#fa
           (LBLOCK [ STR "get_memory_variable_4: " ;
                     STR "index: " ; index#toPretty ;
                     STR "scale: " ; INT scale ;
                     STR "offset: " ; offset#toPretty ]) ;
         self#env#mk_unknown_memory_variable (x2s offsetXpr)
       end
      											
  (* Creates expressions in the environment of the call target with variables
     wrapped in external variables                                            *)
  method externalize_expr (tgt_faddr:doubleword_int) (x:xpr_t) = [] 

  method rewrite_variable_to_external (var:variable_t) = 
    self#inv#rewrite_expr (XVar var) (self#env#get_variable_comparator)
    
  method private rewrite_numerical_exp (exp:numerical_exp_t) =
    let rewrite = self#rewrite_variable_to_external in
    match exp with
    | NUM n -> num_constant_expr n
    | NUM_VAR v -> rewrite v
    | PLUS (v1,v2) -> simplify_xpr (XOp (XPlus, [ rewrite v1 ; rewrite v2 ]))
    | MINUS (v1,v2) -> simplify_xpr (XOp (XMinus, [ rewrite v1 ; rewrite v2 ]))
    | MULT (v1,v2) -> simplify_xpr (XOp (XMult, [ rewrite v1 ; rewrite v2 ]))
    | DIV (v1,v2) -> simplify_xpr (XOp (XDiv, [ rewrite v1 ; rewrite v2 ]))
      
  method has_initial_value = self#inv#var_has_initial_value 

  method private is_initial_value_variable (v:variable_t) =
    (self#f#env#is_initial_memory_value v) || (self#env#is_initial_register_value v)
      
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * esp offset                                                                         *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_stackpointer_offset arch =
    match arch with
    | "x86" -> self#get_esp_offset
    | "mips" -> self#get_sp_offset
    | _ ->
       raise (BCH_failure
                (LBLOCK [ STR "Architecture not recognized: " ; STR arch ]))

  method stackpointer_offset_to_string arch =
    match arch with
    | "x86" -> self#esp_offset_to_string
    | "mips" -> self#sp_offset_to_string
    | _ ->
       raise (BCH_failure
                (LBLOCK [ STR "Architecture not recognized: " ; STR arch ]))

  method private get_esp_offset =    (* specific to x86 *)
    let inv = self#inv in
    let espreg = CPURegister Esp in
    let esp = self#env#mk_register_variable espreg in
    let esp0 = self#env#mk_initial_register_value ~level:0 espreg in
    let esp0Offset = inv#get_interval_offset esp0 esp in
    if esp0Offset#isTop then
      let esp1 = self#env#mk_initial_register_value ~level:1 espreg in
      let esp1Offset = inv#get_interval_offset esp1 esp in
      if esp1Offset#isTop then
	(0,topInterval)
      else
	(1,esp1Offset)
    else 
      (0,esp0Offset)

  method private get_sp_offset =     (* specific to mips *)
    let inv = self#inv in
    let spreg = MIPSRegister MRsp in
    let sp = self#env#mk_register_variable spreg in
    let sp0 = self#env#mk_initial_register_value ~level:0 spreg in
    let sp0Offset = inv#get_interval_offset sp0 sp in
    if sp0Offset#isTop then
      let sp1 = self#env#mk_initial_register_value ~level:1 spreg in
      let sp1Offset = inv#get_interval_offset sp1 sp in
      if sp1Offset#isTop then
        (0,topInterval)
      else
        (1,sp1Offset)
    else
      (0,sp0Offset)
      
  method private esp_offset_to_string =
    let (level,offset) = self#get_esp_offset in
    let openB = string_repeat "[" (level+1) in
    let closeB = string_repeat "]" (level+1) in
    let offset = if offset#isTop then " ? "	else
	match offset#singleton with
	| Some num -> num#toString
	| _ -> 
	  match (offset#getMin#getBound, offset#getMax#getBound) with
	    (NUMBER lb, NUMBER ub) -> lb#toString  ^ " ; " ^ ub#toString
	  | (NUMBER lb, _ ) -> lb#toString ^ " ; oo"
	  | (_, NUMBER ub ) -> "-oo ; " ^ ub#toString
	  | _ -> "?" in
    openB ^ " " ^ offset ^ " " ^ closeB

  method private sp_offset_to_string =
    let (level,offset) = self#get_sp_offset in
    let openB = string_repeat "[" (level+1) in
    let closeB = string_repeat "]" (level+1) in
    let offset = if offset#isTop then " ? "	else
	match offset#singleton with
	  Some num -> num#toString
	| _ -> 
	  match (offset#getMin#getBound, offset#getMax#getBound) with
	    (NUMBER lb, NUMBER ub) -> lb#toString  ^ " ; " ^ ub#toString
	  | (NUMBER lb, _ ) -> lb#toString ^ " ; oo"
	  | (_, NUMBER ub ) -> "-oo ; " ^ ub#toString
	  | _ -> "?" in
    openB ^ " " ^ offset ^ " " ^ closeB
     
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * jump tables                                                                         *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method set_jumptable_target (base:doubleword_int)  (t:jumptable_int) (reg:register_t) =
    self#f#set_jumptable_target self#cia base t reg
      
  method get_jump_target = self#f#get_jump_target self#cia

  method get_jump_successors =
    let tgt = self#get_jump_target in
    match tgt with
    | JumptableTarget (base,jt,reg) ->
      let indexVar = self#env#mk_register_variable reg in
      if self#is_interval indexVar then
	let range = self#get_interval indexVar in
	match (range#getMin#getBound, range#getMax#getBound) with
	| (NUMBER lb, NUMBER ub) -> jt#get_targets base lb#toInt ub#toInt
	| (_, NUMBER ub) -> jt#get_targets base 0 ub#toInt
	| _ -> jt#get_all_targets
      else
	jt#get_all_targets
    | OffsettableTarget (base,jt,db) ->
      if db#is_offset_table then
	match db#get_offset_range with
	| Some (min,max) -> jt#get_targets base min max
	| _ -> []
      else
	[]
    | JumpOnTerm _ -> []
    | DllJumpTarget _ -> []
    | SOJumpTarget _ -> []
    | UnknownJumpTarget -> []
      				
  method has_jump_target = self#f#has_jump_target self#cia 
    
  method set_test_expr (x:xpr_t) = self#f#set_test_expr self#cia x

  method set_test_variables (l:(variable_t * variable_t) list) = 
    self#f#set_test_variables self#cia l
    
  method has_test_expr = self#f#has_test_expr self#cia
        
  method get_function_arg_value (argIndex:int) = random_constant_expr

  method get_api_parameter_expr (api_parameter_int) = None
    
  method private get_offset ox = 
    let oxs = simplify_xpr ox in
    match oxs with
      XConst (IntConst n) -> ConstantOffset (n, NoOffset)
    | XVar v -> IndexOffset (v, 1, NoOffset)
    | XOp (XMult, [ XConst (IntConst n) ; XVar v ]) when n#is_int -> 
      IndexOffset (v, n#toInt, NoOffset)
    | XOp (XMult, [ XConst (IntConst n) ; XVar v ]) ->
      let msg = LBLOCK [ self#l#toPretty ; STR ": floc#get_offset: " ; x2p oxs ] in
      begin
	ch_error_log#add "number too large" msg ;
	UnknownOffset
      end
    | XOp (XPlus, [ XConst (IntConst n) ; y ]) -> 
      ConstantOffset (n, self#get_offset y)
    | _ -> 
      let msg = (LBLOCK [ STR "offset expr:  " ; x2p oxs ]) in
      begin
	ch_error_log#add "unknown offset expr" 
	  (LBLOCK [ self#l#toPretty ; STR "  " ; msg ]) ;
	UnknownOffset
      end 
	
	
  (* the objective is to extract a base pointer and an offset expression 
   * first check whether the expression contains any variables that are known base pointers;
   * if so, that variable must be the base (any address can only have one pointer, as pointers
   * cannot be added);
   * if not, identify the variable most likely to be the base pointer.
   *)
  method decompose_address (x:xpr_t):(memory_reference_int * memory_offset_t) =
    let _ = track_function
              ~iaddr:self#cia self#fa
              (LBLOCK [ STR "decompose_address: " ; x2p x ]) in
    let default () = (self#env#mk_unknown_memory_reference (x2s x),UnknownOffset) in
     let is_external_constant v = 
       (self#f#env#is_return_value v) || 
	 (self#f#env#is_sideeffect_value v) ||
	 (self#f#env#is_calltarget_value v) in 
     let vars = vars_as_positive_terms x in
     let _ = track_function
               ~iaddr:self#cia self#fa
               (LBLOCK [ STR "decompose-address: vars: " ;
                         pretty_print_list vars (fun v -> v#toPretty) "" "," "" ]) in
     let knownPointers = List.filter self#f#is_base_pointer vars in
     let _ =
       track_function
         ~iaddr:self#cia self#fa
         (LBLOCK [ STR "decompose-address: pointers: " ;
                   pretty_print_list knownPointers (fun v -> v#toPretty) "" "," "" ]) in           
     let optBaseOffset = match knownPointers with
       | [ base ] ->
          let offset = simplify_xpr (XOp (XMinus, [ x ; XVar base ])) in
          let _ =
            track_function
              ~iaddr:self#cia self#fa
              (LBLOCK [ STR "decompose-address: base: " ; base#toPretty ;
                        STR "; offset: " ; x2p offset ]) in
          Some (XVar base, offset)
       | [] ->
	 let maxC = largest_constant_term x in
	 if maxC#gt system_info#get_image_base#to_numerical
            && (match vars with [] -> true | _ -> false) then
	   (* base address is an absolute address *)
           let _ =
             track_function
               ~iaddr:self#cia self#fa
               (LBLOCK [ STR "decompose-address: make global: " ; maxC#toPretty ]) in
	   Some (num_constant_expr maxC, 
		 simplify_xpr (XOp (XMinus, [ x ; num_constant_expr maxC ])))
	 else
	   begin
	     match vars  with
	     | [ base ] when (self#is_initial_value_variable base) || 
		 (is_external_constant base) ->
	        begin
                  track_function
                    ~iaddr:self#cia self#fa
                    (LBLOCK [ STR "add base pointer: " ; base#toPretty ]) ;
		  self#f#add_base_pointer base ;
		  Some (XVar base, simplify_xpr (XOp (XMinus, [ x ; XVar base ])))
	       end
	     | [ base ] when self#env#is_stack_parameter_variable base && 
		 self#f#env#has_constant_offset base && self#has_initial_value base ->
	       let baseInit = self#f#env#mk_initial_memory_value base in
	       begin
                 track_function
                   ~iaddr:self#cia self#fa
                   (LBLOCK [ STR "add baseInit pointer: " ; baseInit#toPretty ]) ;
		 self#f#add_base_pointer baseInit ;
		 Some (XVar base, simplify_xpr (XOp (XMinus, [ x ; XVar base ])))
	       end
             | [ base ] ->
                begin
                  track_function
                    ~iaddr:self#cia self#fa
                    (LBLOCK [ STR "not recognized as base pointer: " ;
                              base#toPretty ]) ;
                  None
                end
	     | [] ->      (* suspicious address below the image base *)
	       begin
		 let _ = match x with
		     (XConst (IntConst num)) ->
		       if num#equal numerical_zero then
			 begin
			   chlog#add "null dereference" 
			     (LBLOCK [ self#l#toPretty ]) ;
			 end
		       else if num#lt numerical_zero then
			 begin
			   chlog#add "negative address" 
			     (LBLOCK [ self#l#toPretty ; STR ": " ; num#toPretty ]) ;
			 end
		       else
			 begin
			   chlog#add "low address" 
			     (LBLOCK [ self#l#toPretty ; STR ": " ; x2p x ]) ;
			 end
		   | _ -> 
		     begin
		       chlog#add "low address" 
			 (LBLOCK [ self#l#toPretty ; STR ": " ; x2p x ]) ;
		     end in
		 None
	       end
	     | _ -> 
		 None
	   end
       | ptrs ->
	 let msg = LBLOCK [  
	   x2p x ; 
	   pretty_print_list ptrs 
	     (fun v -> self#env#variable_name_to_pretty v)  " (" ", " ")" ] in
	 begin
	   chlog#add "error:multiple pointers" 
	     (LBLOCK [ self#l#toPretty ; STR ": " ; msg ]) ;
	   None
	 end in
     try
       match optBaseOffset with
       | Some (XVar v, xoffset) ->
          let memref = self#env#mk_base_variable_reference v in
          let offset = match xoffset with
            | XConst (IntConst n) -> ConstantOffset (n, NoOffset)
            | _ -> UnknownOffset in
          (memref,offset)
       | _ -> default ()
     with
       Invalid_argument s ->
	 let msg = LBLOCK [ STR " address: " ; x2p x ; STR " : " ; STR s ] in
	 begin
	   chlog#add "error:memory reference"	
	     (LBLOCK [ self#l#toPretty ; STR ": " ; msg ]) ;
	   default ()
	 end
     | Invocation_error s ->
       begin
	 ch_error_log#add "variable_manager" 
	   (LBLOCK [ self#l#toPretty ; STR ". get_memory_reference_from_address: " ; 
		     x2p x ; STR " (" ; STR s ; STR ")" ]) ;
	 default ()
       end
       
   method get_lhs_from_address (xpr:xpr_t) =
     let xpr = self#inv#rewrite_expr xpr (self#env#get_variable_comparator) in
     let default () =
       self#env#mk_memory_variable
         (self#env#mk_unknown_memory_reference "lhs-from-address")
         numerical_zero in
     match xpr with
     | XConst (IntConst n) when n#gt numerical_zero ->
        (try
           let base = numerical_to_doubleword n in
           if system_info#get_image_base#le base then
	     self#env#mk_global_variable n
           else
             default ()
         with
         | BCH_failure p ->
            raise (BCH_failure
                     (LBLOCK [  STR "get_lhs_from_address: " ; n#toPretty ;
                                STR "; " ; self#l#toPretty ;
                                STR " (" ;  p ; STR ")"  ])))
     | _ ->
        default ()
	 
   method get_bridge_variable_value (par_index:int) (var:variable_t) = 
     if self#f#has_constant var then
       num_constant_expr (self#f#get_constant var )
     else 
       let x = self#rewrite_variable_to_external var in
       match x with
       | XVar v when v#equal var ->
	 begin
	   try
	     begin
	       match self#get_esp_offset with
	       | (0,range) ->
		 begin
		   match range#singleton with
		   | Some n -> 
		     let offset = n#add (mkNumerical (4*(par_index-1))) in
		     let stackRef = self#env#mk_local_stack_reference in
		     let stackVar = self#env#mk_memory_variable stackRef offset in
		     self#rewrite_variable_to_external stackVar
		   | _ -> x
		 end
	       | _ -> x
	     end
	   with
	   | _ -> x
	 end
       | _ -> x
	 
   method get_test_variables = self#f#get_test_variables self#cia
     
   method get_test_expr = 
     self#inv#rewrite_expr (self#f#get_test_expr self#cia) (self#env#get_variable_comparator)
     
   (* return the address of the memory reference *)
   method private get_address_bterm
                    (memref:memory_reference_int) (targetty:btype_t):bterm_t option = None
                                                                                    
   method private get_variable_bterm (v:variable_t) =
     try
       if self#env#is_stack_parameter_variable v then
         match self#env#get_stack_parameter_index v with
         | Some index -> ArgValue (self#f#set_stack_par index t_unknown)
         | _ -> RunTimeValue
       else if self#env#is_initial_register_value v then
         let reg = self#env#get_initial_register_value_register v in
         let par = self#f#set_register_par reg t_unknown in
         ArgValue par
       else if self#env#is_global_variable v then
         if self#env#has_constant_offset v then
	   let address = self#env#get_global_variable_address v in
	   ArgValue (self#f#set_global_par address t_unknown)
         else
	   RunTimeValue
       else if self#env#is_initial_memory_value v then
         let memref = self#env#get_memory_reference v in
         match self#get_address_bterm memref t_unknown with
         | Some bterm -> ArgAddressedValue (bterm, NumConstant numerical_zero)
         | _ -> RunTimeValue
       else
         RunTimeValue
     with
     | BCH_failure p ->
        raise (BCH_failure (LBLOCK [ STR "Floc:get-variable-bterm: " ; p ]))

   method private get_xpr_bterm (x:xpr_t) =
     let vars = variables_in_expr x in
     let pars = H.create 5 in
     let _ = List.iter (fun v ->
       H.add pars v#getName#getSeqNumber (self#get_variable_bterm v)) vars in
     let subst v = if H.mem pars v#getName#getSeqNumber then 
	 H.find pars v#getName#getSeqNumber
       else
	 RunTimeValue in
     match xpr_to_bterm x subst with Some bterm -> bterm | _ -> RunTimeValue
            
   method private record_block_write 
                    (memref:memory_reference_int) (size:xpr_t) (ty:btype_t) =
     try
       match self#get_address_bterm memref ty with
       | Some dest ->
          begin
	    match dest with
	    (* null dereference is taken care of elsewhere, so it can be ignored here *)
	    | NumConstant x when x#equal numerical_zero ->
	       ()    
	      
	    (* recording side effects on global variables has been disabled *)
	    | NumConstant n
                 when system_settings#is_sideeffects_on_global_enabled
                    (numerical_to_hex_string n) ->
	       let sizeTerm = self#get_xpr_bterm size in
	       self#f#record_sideeffect (BlockWrite (ty, dest, sizeTerm))
            | _ -> ()
          end
       | _ -> self#f#record_sideeffect UnknownSideeffect
     with BCH_failure p ->
       let msg = LBLOCK [ STR "record-block-write: " ; self#l#toPretty ;
                          memref#toPretty ; STR ": " ; p ] in
       begin
         ch_error_log#add "record-block-write" msg ;
         raise (BCH_failure msg)
       end

   method private get_assignment_type (lhs:variable_t) (rhs:xpr_t) =
     match rhs with
     | XVar v -> 
       let typefacts = self#f#ftinv#get_variable_facts self#l#i#to_hex_string v in
       begin
	 match typefacts with
	 | [ t ] -> 
	   begin
	     match t#get_fact with
	     | VarTypeFact (_, ty,[]) -> ty
	     | _ -> t_unknown
	   end
	 | _ -> t_unknown
       end
     | _ -> t_unknown
       

   method get_assign_commands 
     (lhs:variable_t) 
     ?(size=random_constant_expr) 
     ?(vtype=t_unknown)
     (rhs_expr:xpr_t) =
     let is_external v = self#env#is_function_initial_value v in
     let is_composite_symbolic_value x =
       let rec is_symbolic_expr x =
         match x with
         | XOp (_, l) -> List.for_all is_symbolic_expr l
         | XVar v -> is_external v
         | XConst _ -> true
         | XAttr _ -> false in
       match x with
       | XOp (_, l) -> List.for_all is_symbolic_expr l
       | _ -> false in
     
     let rhs_expr = self#inv#rewrite_expr rhs_expr self#env#get_variable_comparator in

     (* if the rhs_expr is a composite symbolic expression, create a new variable for it *)
     let rhs_expr =
       if is_composite_symbolic_value rhs_expr then
         XVar (self#env#mk_symbolic_value rhs_expr)
       else
         rhs_expr in
     
     let vtype = if btype_compare vtype t_unknown = 0 then
	 self#get_assignment_type lhs rhs_expr
       else
	 vtype in
     let reqN () = self#env#mk_num_temp in
     let reqC = self#env#request_num_constant in
     let (rhsCmds,rhs) = xpr_to_numexpr reqN reqC rhs_expr in
     let get_gvalue (x:xpr_t) = match x with
       | XConst (IntConst n) -> GConstant n 
       | XVar v when self#env#is_return_value v -> 
	 let callSite = self#env#get_call_site v in
	 GReturnValue (ctxt_string_to_location self#fa callSite)
       | XVar v when self#env#is_sideeffect_value v ->
	 let callSite = self#env#get_call_site v in
	 let argdescr = self#env#get_se_argument_descriptor v in
	 GSideeffectValue (ctxt_string_to_location self#fa callSite,argdescr)
       | XVar v when self#env#is_stack_parameter_variable v ->
	  begin
            try
	      match self#env#get_stack_parameter_index v with
	      | Some index -> GArgValue (self#fa,index,[])
	      | _ -> GUnknownValue
            with
            | BCH_failure p ->
               raise (BCH_failure (LBLOCK [ STR "Floc:get-assign-commands: " ; p ]))
	 end
       | _ -> GUnknownValue in

     (* if the lhs is an external variable, record the assignment as a side effect *)
     let _ =
       if is_external lhs (* && (not (is_constant rhs_expr)) *) then
	 let memref = self#env#get_memory_reference lhs in
	 self#record_block_write memref size vtype in

     (* if the lhs is a global variable, record the assignment in the global state *)
     let _ = 
       let size = match size with
	 | XConst (IntConst n) -> Some n#toInt | _ -> None in
       if self#env#is_global_variable lhs && self#env#has_constant_offset lhs then
	 global_system_state#add_writer ~ty:vtype ~size
	   (get_gvalue rhs_expr) (self#env#get_global_variable_address lhs) self#l in

     let _ = if is_known_type vtype then 
	 begin
	   self#add_var_type_fact lhs vtype ;
	   self#add_xpr_type_fact rhs_expr vtype 
	 end in

     (* if the lhs is unknown, add an operation to record an unknown write *)
     if lhs#isTmp || self#env#is_unknown_memory_variable lhs then
       let op_args = get_rhs_op_args rhs in
       [ OPERATION ( { op_name = unknown_write_symbol ; op_args = op_args }) ;
	 ASSIGN_NUM (lhs,rhs) ]

     (* else add the assignment to the lhs variable *)
     else
       rhsCmds @ [ ASSIGN_NUM (lhs,rhs) ]
	 
   method private evaluate_api_argument (p:api_parameter_t) =
     match p.apar_location with
     | StackParameter index ->
       let argvar = self#env#mk_bridge_value self#cia index in
       self#get_bridge_variable_value index argvar
     | RegisterParameter r ->
       let argvar = self#env#mk_register_variable r in
       self#rewrite_variable_to_external argvar
     | GlobalParameter a ->
       let argvar = self#env#mk_global_variable a#to_numerical in
       self#rewrite_variable_to_external argvar
     | _ -> random_constant_expr
       
   method evaluate_summary_term (t:bterm_t) (returnvar:variable_t) =
     match t with
     | ArgValue p -> self#evaluate_api_argument p
     | ReturnValue -> XVar returnvar
     | NumConstant n -> num_constant_expr n
     | NamedConstant name -> XVar (self#env#mk_runtime_constant name)
     | ByteSize t -> self#evaluate_summary_term t returnvar
     | ArithmeticExpr (op, t1, t2) ->
       let xpr1 = self#evaluate_summary_term t1 returnvar in
       let xpr2 = self#evaluate_summary_term t2 returnvar in
       XOp (arithmetic_op_to_xop op, [ xpr1 ; xpr2 ])
     | _ -> random_constant_expr

   method private evaluate_api_address_argument (p:api_parameter_t) = None

   method evaluate_summary_address_term (t:bterm_t) =
     try
       match t with
       | ArgValue p -> self#evaluate_api_address_argument p
       | NumConstant num ->
          (try
             let base = numerical_to_doubleword num in
             if system_info#get_image_base#le base then
	       Some (self#env#mk_global_variable num)
             else
               None
           with
           | BCH_failure p ->
              raise (BCH_failure
                       (LBLOCK [ STR "evaluate_summary_address_term: " ;
                                 num#toPretty ; STR "; " ;
                                 self#l#toPretty ; STR " (" ; p ; STR ")" ])))
       | ArgAddressedValue (subT,NumConstant offset) ->
	 let optBase = self#evaluate_summary_address_term subT in
	 begin
	   match optBase with
	     Some baseVar ->
	       let memref = self#env#mk_base_variable_reference baseVar in
	       Some (self#env#mk_memory_variable memref offset)
	   | _ -> None
	 end
       | _ -> None
     with
       Invalid_argument s ->
	 begin
	   ch_error_log#add "invalid argument"
	     (LBLOCK [ STR "evaluate_summary_address_term: " ; self#l#toPretty ; STR ": " ;
		       bterm_to_pretty t ]) ;
	   None
	 end
       
   method get_abstract_commands 
     (lhs:variable_t) ?(size=random_constant_expr) ?(vtype=t_unknown) () = 
     [ ABSTRACT_VARS [ lhs ] ]

   method get_abstract_cpu_registers_command (regs:cpureg_t list) =
     let regs =
       List.fold_left (fun lst r ->
           if List.mem r lst then
             lst
           else
             lst @ (r::(registers_affected_by r))) [] regs in
     ABSTRACT_VARS (List.map self#env#mk_cpu_register_variable regs)

   method get_abstract_registers_command (regs:register_t list) =
     ABSTRACT_VARS (List.map self#env#mk_register_variable regs)

   method get_operation_commands 
            (lhs:variable_t)
            ?(size=random_constant_expr)
            ?(vtype=t_unknown)
            (opname:symbol_t)
            (args:op_arg_t list) =
     [ ABSTRACT_VARS [ lhs ] ]
     
   method private assert_post
                    (name:string)
                    (post:postcondition_t)
                    (returnvar:variable_t)
                    (string_retriever:doubleword_int -> string option) =
     let get_zero () = self#env#request_num_constant numerical_zero in
     let reqN () = self#env#mk_num_temp in
     let reqC = self#env#request_num_constant in
     let get_function_pointer_commands (fnameTerm:bterm_t) =
       try
	 let nameAddr = self#evaluate_summary_term fnameTerm returnvar in
	 let fname = match nameAddr with
	   | XConst (IntConst n) ->
              (try
                 string_retriever (numerical_to_doubleword n)
               with
               | BCH_failure p ->
                  let msg = LBLOCK [ STR "assert_post: " ; STR  name ;
                                     STR " with " ; n#toPretty ;
                                     STR " (" ; p ; STR ")" ] in
                  begin
                    ch_error_log#add "doubleword conversion" msg ;
                    None
                  end)
	   | _ -> 
	     begin
	       chlog#add "function-pointer: no address" (self#l#toPretty) ;
	       None 
	     end in
	 match fname with
	   Some fname ->
	     let fpVar = self#env#mk_function_pointer_value fname name self#cia in
	     let msg = self#env#variable_name_to_pretty fpVar in
	     begin
	       translation_log#add
                 "function-pointer variable" (LBLOCK [ self#l#toPretty ; STR ":  " ; msg ]) ;
	       [ ASSERT (EQ (fpVar, returnvar)) ] 
	     end
	 | _ -> 
	   begin
	     chlog#add "function-pointer: no name" (self#l#toPretty) ;
	     [] 
	   end 
       with
	 Invalid_argument s ->
	   begin
	     ch_error_log#add "invalid argument" 
	       (LBLOCK [ STR "assert post: " ; self#l#toPretty ; STR ": " ; STR s ;
			 STR " " ; STR name ]) ;
	     []
	   end in
     let get_null_var (term:bterm_t) =
       let termXpr = self#evaluate_summary_term term returnvar in
       xpr_to_numvar reqN reqC termXpr in
     let get_null_commands (term:bterm_t) =
       let (cmds,termVar) = get_null_var term in
       cmds @ [ ASSERT (EQ (termVar, get_zero ())) ] in
     let get_not_null_commands (term:bterm_t) =
       let (cmds,termVar) = get_null_var term in
       cmds @ [ ASSERT (GT (termVar, get_zero ())) ] in
     let get_post_expr_commands op t1 t2 =
       let xpr1 = self#evaluate_summary_term t1 returnvar in
       let xpr2 = self#evaluate_summary_term t2 returnvar in
       let xop = relational_op_to_xop op in
       let xpr = XOp (xop, [ xpr1 ; xpr2 ]) in
       let (cmds,bxpr) = xpr_to_boolexpr reqN reqC xpr in
       cmds @ [ ASSERT bxpr ] in
     match post with
     | PostNewMemoryRegion (ReturnValue, sizeParameter) ->
        [] (* get_new_memory_commands sizeParameter *)
     | PostFunctionPointer (ReturnValue, nameParameter) ->
        get_function_pointer_commands nameParameter
     | PostNull term -> get_null_commands term
     | PostNotNull term -> get_not_null_commands term
     | PostRelationalExpr (op, t1, t2) -> get_post_expr_commands op t1 t2
     | PostFalse ->
        let ctinfo = self#get_call_target in
        if ctinfo#is_nonreturning then
          [] (* was known during translation, or has been established earlier *)
        else
	  begin
	    (* ctinfo#set_nonreturning ; *)
	    chlog#add
              "function retracing"
              (LBLOCK [ self#l#toPretty ; STR ": " ; STR name ]) ;
	    raise Request_function_retracing
	  end
     | _ ->
       let msg = postcondition_to_pretty post in
       begin
	 chlog#add "postcondition not used" (LBLOCK [ self#l#toPretty ; msg ]) ;
	 []
       end
	 
   method private get_postcondition_assertions
                    (summary:function_summary_int)
                    (returnvar:variable_t)
                    (string_retriever:doubleword_int -> string option) =
     let name = summary#get_name in
     let postCommands = List.concat 
       (List.map (fun post -> 
	 self#assert_post name post returnvar string_retriever) summary#get_postconditions) in
     let errorPostCommands = List.concat
       (List.map (fun epost -> 
	 self#assert_post name epost returnvar string_retriever) 
	  summary#get_errorpostconditions) in
     match (postCommands, errorPostCommands) with
       ([],[]) -> []
     | (_, []) -> postCommands 
     | ([], _) -> errorPostCommands
     | _ -> [ BRANCH [ LF.mkCode postCommands ; LF.mkCode errorPostCommands ] ]
  
   method private record_precondition_effect (pre:precondition_t) =
     match pre with
     | PreFunctionPointer (_,t) ->
       begin
	 match self#evaluate_summary_term t self#env#mk_num_temp with
	 | XConst (IntConst n) ->
	   begin
	     try
	       let a = numerical_to_doubleword n in
	       if system_info#is_code_address a then
		 begin
		   ignore (functions_data#add_function a) ;
		   chlog#add "function entry point from precondition"
		     (LBLOCK [ self#l#toPretty ; STR ": " ; a#toPretty ])
		 end
	       else
		 chlog#add
                   "function pointer precondition error"
		   (LBLOCK [ self#l#toPretty ; STR ": " ; a#toPretty ;
                             STR " is not a code address" ])
	     with
	     | BCH_failure p ->
	        chlog#add
                  "function pointer precondition error"
		  (LBLOCK [ self#l#toPretty ;
                            STR ": argument cannot be converted to address" ])
	   end
	 | x -> 
	   chlog#add "function pointer precondition"
	     (LBLOCK [ self#l#toPretty ; STR ": unknown argument " ;
		       xpr_formatter#pr_expr x ])
       end
     | _ -> ()
	 
       
   method private get_sideeffect_assign (side_effect:sideeffect_t) =
     let msg = LBLOCK [ self#l#toPretty ; STR ": " ; sideeffect_to_pretty side_effect ] in
     match side_effect with
     | BlockWrite (ty, dest, size) ->
       let get_index_size k =
	 match get_size_of_type ty with
	 | Some s -> num_constant_expr (k#mult (mkNumerical s))
	 | _ -> random_constant_expr in
       begin
	 match self#evaluate_summary_address_term dest with
	 | Some memVar ->
	   let sizeExpr = 
	     match size with
	     | IndexSize (NumConstant n) -> get_index_size n
	     | IndexSize (ArgValue p) ->
	       begin
		 match self#evaluate_api_argument p with
		 | XConst (IntConst n) -> get_index_size n
		 | _ -> random_constant_expr
	       end
	     | _ ->
	       self#evaluate_summary_term size (self#env#mk_num_temp) in
	   let sizeExpr = simplify_xpr sizeExpr in
	   let _ = if is_zero sizeExpr then
	       ch_error_log#add "zero size" 
		 (LBLOCK [ self#l#toPretty ; STR " " ; 
			   sideeffect_to_pretty side_effect ] ) in
	   let rhs = 
 	     match dest with
 	     | NumConstant n ->
                (try
	           let argDescr = (numerical_to_doubleword n)#to_hex_string in
	           self#env#mk_side_effect_value self#cia ~global:true argDescr
                 with
                 | BCH_failure p ->
                    let msg = LBLOCK [ STR "get_sideeffect_assign: " ;
                                       sideeffect_to_pretty side_effect ;
                                       STR " (" ; p ; STR ")" ] in
                    begin
                      ch_error_log#add "doubleword conversion" msg ;
                      self#env#mk_side_effect_value self#cia (bterm_to_string dest)
                    end)
	     | _ ->
	       self#env#mk_side_effect_value self#cia (bterm_to_string dest) in
	   let seAssign =
	     self#get_assign_commands memVar ~size:sizeExpr ~vtype:ty (XVar rhs) in
	   let fldAssigns = [] in
	   seAssign @ fldAssigns
	 | _ -> 
	    begin	
	      chlog#add "side-effect ignored" msg ; 
	      [] 
	    end
       end 
     | StartsThread (sa,pars) ->
       let _ = 
	 match self#evaluate_summary_term sa self#env#mk_num_temp with
	 | XConst (IntConst n) ->
	   begin
	     try
	       let a = numerical_to_doubleword n in
	       if system_info#is_code_address a then
		 system_info#set_thread_start_address self#fa self#cia a [] 
	     with
	     | _ -> ()
	   end
	 | _ -> () in
       []
     | AllocatesStackMemory size ->
       begin
	 let sizeExpr = self#evaluate_summary_term size (self#env#mk_num_temp) in
	 let sizeExpr = simplify_xpr sizeExpr in
	 let esp = self#env#mk_cpu_register_variable Esp in
	 match sizeExpr with
	 | XConst (IntConst num) ->
	   let adj = self#env#request_num_constant num in
	   [ ASSIGN_NUM (esp, MINUS (esp, adj)) ]
	 | _ -> 
	   begin
	     chlog#add "alloca" (LBLOCK [ self#l#toPretty ; STR " size not known: " ; 
					  x2p sizeExpr ]) ;
	     [ ABSTRACT_VARS [ esp ] ]
	   end
       end
     | _ -> 
       begin 
	 chlog#add "side-effect ignored" msg ;
	 [] 
       end

   method private record_precondition_effects (sem:function_semantics_t) =
     List.iter self#record_precondition_effect sem.fsem_pre
	 
   method get_sideeffect_assigns  (sem:function_semantics_t) = 
     List.concat (List.map self#get_sideeffect_assign sem.fsem_sideeffects)

   method private record_call_argument_types api =
     let add_type_facts v x t =
       if is_known_type t then
	 begin
	   self#add_var_type_fact v t ;
	   self#add_xpr_type_fact x t
	 end in
     List.iter (fun p ->
       match p.apar_location with
	 | StackParameter index ->
	   let argvar = self#f#env#mk_bridge_value self#cia index in
	   let argval = self#get_bridge_variable_value index argvar in
	   add_type_facts argvar argval p.apar_type
	 | RegisterParameter r ->
	   let argvar = self#f#env#mk_register_variable r in
	   let argval = self#rewrite_variable_to_external argvar in
	   add_type_facts argvar argval p.apar_type
	 | GlobalParameter a ->
	   let argvar = self#f#env#mk_global_variable a#to_numerical in
	   let argval = self#rewrite_variable_to_external argvar in
	   add_type_facts argvar argval p.apar_type
	 | _ -> ()) api.fapi_parameters

   method private record_memory_reads (pres:precondition_t list) =
     List.iter (fun pre ->
       match pre with
       | PreDerefRead (ty,src,size,_) ->
	 let get_index_size k =
	   match get_size_of_type ty with
	   | Some s -> num_constant_expr (k#mult (mkNumerical s))
	   | _ -> random_constant_expr in
	 begin
	   match self#evaluate_summary_address_term src with
	   | Some memVar ->
	     if self#env#is_global_variable memVar && 
	       self#env#has_constant_offset memVar then
	       let sizeExpr =
		 match size with
		 | IndexSize (NumConstant n) -> get_index_size n
		 | IndexSize (ArgValue p) ->
		   begin
		     match self#evaluate_api_argument p with
		     | XConst (IntConst n) -> get_index_size n
		     | _ -> random_constant_expr
		   end
		 | _ -> self#evaluate_summary_term size self#env#mk_num_temp in
	       let sizeExpr = simplify_xpr sizeExpr in
	       let size = match sizeExpr with
		 | XConst (IntConst n) -> Some n#toInt | _ -> None in
	       global_system_state#add_reader ~ty ~size
		 (self#env#get_global_variable_address memVar) self#l
	   | _ -> ()
	 end
       | _ -> ()) pres

   method get_call_commands (string_retriever:doubleword_int -> string option) =
     let ctinfo = self#get_call_target in
     let api = ctinfo#get_signature in
     (* ------------------------------------------------------------ abstract registers *)
     let eax = self#env#mk_cpu_register_variable Eax in
     let esp = self#env#mk_cpu_register_variable Esp in

     (* --------------------------------------------------------- create operation name *)
     let opName = new symbol_t ~atts:["CALL"] api.fapi_name in

     (* ----------------------------------------------------------- get return variable *)

     let returnAssign = 
       let rvar = self#env#mk_return_value self#cia in
       if ctinfo#is_signature_valid then
         let rty = ctinfo#get_returntype in
	 if is_void rty then
	   SKIP
	 else
	   let name = ctinfo#get_name ^ "_rtn_" ^ self#cia in
	   let _ = self#env#set_variable_name rvar name in
	   let rty = ctinfo#get_returntype in
	   begin
	     self#f#ftinv#add_function_var_fact rvar rty ;
	     self#add_var_type_fact eax rty ;
	     ASSIGN_NUM (eax, NUM_VAR rvar)
	   end
       else
	 ASSIGN_NUM (eax, NUM_VAR rvar) in

     (* ------------------------------------------------- assign side effects *)
     let sideEffectAssigns =
	 self#get_sideeffect_assigns self#get_call_target#get_semantics  in
     let _ =
	 self#record_precondition_effects self#get_call_target#get_semantics in

     (* ------------------------------------------------- record memory reads *)
     let _ =
	 self#record_memory_reads self#get_call_target#get_semantics.fsem_pre in

     (* ------------------------------------------------ adjust stack pointer *)
     let espAdjustment = 
       let oAdj =
	 if system_info#has_esp_adjustment self#l#base_f self#l#i then
	   Some (system_info#get_esp_adjustment self#l#base_f self#l#i)
	 else
           self#get_call_target#get_stack_adjustment in
       match oAdj with
       | Some adj ->
	 if adj > 0 then
	   let adj = self#env#request_num_constant (mkNumerical adj) in
	   [ ASSIGN_NUM (esp, PLUS (esp, adj) ) ]
	 else if adj < 0 then
	   [ ABSTRACT_VARS [ esp ] ]
	 else
	   []
       | _ -> [] in
   (* | _ -> [ ABSTRACT_VARS [ esp ] ] in *)
     let bridgeVars = self#env#get_bridge_values_at self#cia in
     let defClobbered = List.map (fun r -> (CPURegister r)) [ Eax ; Ecx ; Edx ] in
     let regsClobbered = List.fold_left (fun acc reg ->
       List.filter (fun r -> not (r=reg)) acc)
       defClobbered api.fapi_registers_preserved in
     let abstrRegs = List.map self#env#mk_register_variable regsClobbered in
     [ OPERATION { op_name = opName ; op_args = [] } ;
       ABSTRACT_VARS abstrRegs ] @
       (* postAsserts @ *)
       [ returnAssign ] @ sideEffectAssigns @ espAdjustment @
         [ ABSTRACT_VARS bridgeVars ]

   method get_mips_call_commands =
     let ctinfo = self#get_call_target in
     let v0 = self#env#mk_mips_register_variable MRv0 in
     (* v1 may be an additional return value from the callee, abstract it for now *)
     let v1 = self#env#mk_mips_register_variable MRv1 in
     let opname = new symbol_t ~atts:["CALL"] ctinfo#get_name in
     let returnassign =
       let rvar = self#env#mk_return_value self#cia in
       let _ =
         if ctinfo#is_signature_valid then
           let name = ctinfo#get_name ^ "_rtn_" ^ self#cia in
           self#env#set_variable_name rvar name in
       ASSIGN_NUM (v0, NUM_VAR rvar) in
     let defClobbered = List.map (fun r -> (MIPSRegister r)) mips_temporaries in
     let abstrRegs = List.map self#env#mk_register_variable defClobbered in
     [ OPERATION { op_name = opname ; op_args = [] } ;
       ABSTRACT_VARS (v1::abstrRegs) ; returnassign ]

   method is_constant (var:variable_t) = self#inv#is_constant var

   method is_interval (var:variable_t) = self#inv#is_interval var

   method is_base_offset (var:variable_t) = self#inv#is_base_offset var
     
   method get_constant (var:variable_t) =
     if self#is_constant var then self#inv#get_constant var
     else
       raise (Invocation_error ("floc#get_constant"))
	 
   method get_interval (var:variable_t) = 
     if self#is_interval var then
       self#inv#get_interval var
     else
       raise (Invocation_error ("floc#get_interval"))

  method private normalize_address (address:xpr_t) =
    let is_external = self#env#is_function_initial_value in
    let normalize_offset (offset:xpr_t) =
      match offset with
	XConst _ -> offset
      | XVar _ -> offset
      | XOp (XMult, [ XConst _ ; XVar _ ]) -> offset
      | XOp (XMult, [ XVar v ; XConst (IntConst n) ]) -> 
	XOp (XMult, [ XConst (IntConst n) ; XVar v ])
      | _ -> 
	begin
	  chlog#add "unrecognized offset" (x2p offset) ;
	  offset
	end in
    match address with
      XVar v -> address
    | XOp (XPlus, [ XVar v1 ; XVar v2 ]) when not (is_external v1) && is_external v2 ->
      XOp (XPlus, [ XVar v2 ; XVar v1 ])
    | XOp (XPlus, [ XVar v ; offset ]) 
    | XOp (XPlus, [ offset ; XVar v ]) -> XOp (XPlus, [ XVar v ; normalize_offset offset ]) 
    | XOp (XMinus, [ XVar v ; XConst (IntConst n) ]) -> 
      XOp (XPlus, [ XVar v ; XConst (IntConst n#neg) ])
    | _ -> address

  method is_address (x:xpr_t) = 
    match self#normalize_address x with 
    | XVar v
    | XOp (XPlus, [ XVar v ; _ ]) -> self#f#is_base_pointer v
    | _ -> false
end

let get_floc (loc:location_int) =
  new floc_t (get_function_info loc#f) loc

let get_i_floc (floc:floc_int) (iaddr:doubleword_int) =
  let loc = make_i_location floc#l iaddr in
  new floc_t (get_function_info floc#fa) loc
