(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHTimingLog
open CHTraceResult

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypePretty
open BCHBCTypeUtil
open BCHBTerm
open BCHCallSemanticsRecorder
open BCHCPURegisters
open BCHDoubleword
open BCHExternalPredicate
open BCHFtsParameter
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionInterface
open BCHGlobalState
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHMemoryRecorder
open BCHMemoryReference
open BCHStrings
open BCHSystemInfo
open BCHSystemSettings
open BCHTypeDefinitions
open BCHUtilities
open BCHXprUtil

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory
module TR = CHTraceResult

module POAnchorCollections = CHCollections.Make
  (struct
    type t = po_anchor_t
    let compare = po_anchor_compare
    let toPretty = po_anchor_to_pretty
   end)

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)

let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("floc:" ^ tag) msg


let unknown_write_symbol = new symbol_t "unknown write"


let get_rhs_op_args (exp:numerical_exp_t) =
  match exp with
  | NUM _ -> []
  | NUM_VAR v -> [("rhs", v, READ)]
  | PLUS (v1,v2) | MINUS (v1,v2) | MULT (v1,v2) | DIV (v1,v2) ->
     [("rhs1",v1,READ); ("rhs2",v2,READ)]


module ExprCollections = CHCollections.Make (struct
  type t = xpr_t
  let compare = Xprt.syntactic_comparison
  let toPretty = x2p
end)


class mips_argument_type_propagator_t
        (finfo: function_info_int)
        (callargs: (fts_parameter_t * xpr_t) list): argument_type_propagator_int =
object (self)

  method finfo = finfo

  method callargs = callargs

  method elevate_call_arguments =
    let set_regpar (fty: btype_t) (reg: mips_reg_t) =
      let register = register_of_mips_register reg in
      self#finfo#update_summary
        (self#finfo#get_summary#add_register_parameter_location register fty 4) in
    let set_stackpar (fty: btype_t) (offset: int) =
      self#finfo#update_summary
        (self#finfo#get_summary#add_stack_parameter_location offset  fty 4) in
    List.iter (fun (par, x) ->
        match x with
        | XVar v when self#finfo#env#is_initial_register_value v ->
           log_tfold
             (log_error "elevate_call_arguments" "invalid register")
             ~ok:(fun reg ->
               let fty = par.apar_type in
               (match reg with
                | MIPSRegister MRa0 -> set_regpar fty MRa0
                | MIPSRegister MRa1 -> set_regpar fty MRa1
                | MIPSRegister MRa2 -> set_regpar fty MRa2
                | MIPSRegister MRa3 -> set_regpar fty MRa3
                | _ -> ()))
             ~error:(fun _ -> ())
             (self#finfo#env#get_initial_register_value_register v)
        | XVar v when self#finfo#env#is_stack_parameter_value v ->
           let indexopt = self#finfo#env#get_stack_parameter_index v in
           (match indexopt with
            | Some index ->
               let fty = par.apar_type in
               set_stackpar fty (4 * index)
            | _ -> ())
        | _ -> ()) self#callargs

end


class arm_expression_externalizer_t
        (finfo: function_info_int): expression_externalizer_int =
object

  method finfo = finfo

  method xpr_to_bterm (_: btype_t) (_: xpr_t) = None

end


class mips_expression_externalizer_t
        (finfo: function_info_int): expression_externalizer_int =
object (self)

  method finfo = finfo

  method xpr_to_bterm (btype: btype_t) (xpr: xpr_t): bterm_t option =
    match xpr with
    | XConst (IntConst n) -> Some (NumConstant n)
    | XVar v when self#finfo#env#is_initial_register_value v ->
       log_tfold
         (log_error "xpr_to_bterm" "invalid register")
         ~ok:(fun reg ->
           let _ =
             self#finfo#update_summary
               (self#finfo#get_summary#add_register_parameter_location
                  reg btype 4) in
           let ftspar = self#finfo#get_summary#get_parameter_for_register reg in
           Some (ArgValue ftspar))
         ~error:(fun _ -> None)
         (self#finfo#env#get_initial_register_value_register v)
    | XVar v when self#finfo#env#is_stack_parameter_value v ->
       let indexopt = self#finfo#env#get_stack_parameter_index v in
       (match indexopt with
       | Some index ->
          let _ =
            self#finfo#update_summary
              (self#finfo#get_summary#add_stack_parameter_location
                 (4 * index) btype 4) in
          let ftspar =
            self#finfo#get_summary#get_parameter_at_stack_offset (4 * index) in
          Some (ArgValue ftspar)
       | _ -> None)
    | XOp ((Xf "indexsize"), [xx]) ->
       let optt = self#xpr_to_bterm t_int xx in
       (match optt with
        | Some tt -> Some (IndexSize tt)
        | _ -> None)
    | XOp ((Xf "ntpos"), [xx]) ->
       let optt = self#xpr_to_bterm t_int xx in
       (match optt with
        | Some tt -> Some (ArgNullTerminatorPos tt)
        | _ -> None)
    | _ -> None

end


class arm_bterm_evaluator_t
        (finfo: function_info_int)
        (callargs: (fts_parameter_t * xpr_t) list): bterm_evaluator_int =
object (self)

  val finfo = finfo
  val callargs = callargs

  method finfo = finfo

  method bterm_xpr (t: bterm_t): xpr_t option =
    match t with
    | ArgValue par ->
       List.fold_left (fun acc (cpar, x) ->
           match acc with
           | Some _ -> acc
           | _ ->
              if (fts_parameter_equal cpar par) then Some x else None)
         None callargs
    | NumConstant n -> Some (XConst (IntConst n))
    | IndexSize t ->
       (match self#bterm_xpr t with
        | Some x -> Some (XOp ((Xf "indexsize"), [x]))
        | _ -> None)
    | ByteSize t -> self#bterm_xpr t
    | ArgNullTerminatorPos t ->
       (match self#bterm_xpr t with
        | Some x -> Some (XOp ((Xf "ntpos"), [x]))
        | _ -> None)
    | _ -> None

  method xpr_local_stack_address (x: xpr_t): int option =
    match x with
    | XOp (XMinus, [XVar v; XConst (IntConst n)]) when n#geq numerical_zero ->
       let sp0 =
         self#finfo#env#mk_initial_register_value ~level:0 (ARMRegister ARSP) in
       if v#equal sp0 then
         Some n#toInt
       else
         None
    | _ -> None

  method bterm_stack_address (t: bterm_t): xpr_t option =
    match self#bterm_xpr t with
    | Some (XOp (XMinus, [XVar v; c]) as addr) ->
       let sp0 =
         self#finfo#env#mk_initial_register_value ~level:0 (ARMRegister ARSP) in
       (match c with
        | XConst (IntConst n) when n#geq numerical_zero ->
           if v#equal sp0 then
             Some addr
           else
             None
        | _ -> None)
    | _ -> None

  method constant_bterm (t: bterm_t): bterm_t option =
    match t with
    | NumConstant _ -> Some t
    | ArgValue par ->
       List.fold_left (fun acc (cpar, x) ->
           match acc with
           | Some _ -> acc
           | _ ->
              if (fts_parameter_equal cpar par) then
                match x with
                | XConst (IntConst n) -> Some (NumConstant n)
                | _ -> None
              else
                None) None callargs
    | IndexSize tt ->
       (match self#constant_bterm tt with
        | Some subterm -> Some (IndexSize subterm)
        | _ -> None)
    | ByteSize tt ->
       (match self#constant_bterm tt with
        | Some subterm -> Some (ByteSize subterm)
        | _ -> None)
    | ArgSizeOf _ -> Some t
    | NamedConstant _ -> Some t
    | _ -> None

end


class mips_bterm_evaluator_t
        (finfo: function_info_int)
        (callargs: (fts_parameter_t * xpr_t) list): bterm_evaluator_int =
object (self)

  val finfo = finfo
  val callargs = callargs

  method finfo = finfo

  method bterm_xpr (t: bterm_t): xpr_t option =
    match t with
    | ArgValue par ->
       List.fold_left (fun acc (cpar, x) ->
           match acc with
           | Some _ -> acc
           | _ ->
              if (fts_parameter_equal cpar par) then Some x else None)
         None callargs
    | NumConstant n -> Some (XConst (IntConst n))
    | IndexSize t ->
       (match self#bterm_xpr t with
        | Some x -> Some (XOp ((Xf "indexsize"), [x]))
        | _ -> None)
    | ByteSize t -> self#bterm_xpr t
    | ArgNullTerminatorPos t ->
       (match self#bterm_xpr t with
        | Some x -> Some (XOp ((Xf "ntpos"), [x]))
        | _ -> None)
    | _ -> None

  method xpr_local_stack_address (x: xpr_t): int option =
    match x with
    | XOp (XMinus, [XVar v; XConst (IntConst n)]) when n#geq numerical_zero ->
       let sp0 =
         self#finfo#env#mk_initial_register_value ~level:0 (MIPSRegister MRsp) in
       if v#equal sp0 then
         Some n#toInt
       else
         None
    | _ -> None

  method bterm_stack_address (t: bterm_t): xpr_t option =
    match self#bterm_xpr t with
    | Some (XOp (XMinus, [XVar v; c]) as addr) ->
       let sp0 =
         self#finfo#env#mk_initial_register_value ~level:0 (MIPSRegister MRsp) in
       (match c with
        | XConst (IntConst n) when n#geq numerical_zero ->
           if v#equal sp0 then
             Some addr
           else
             None
        | _ -> None)
    | _ -> None

  method constant_bterm (t: bterm_t): bterm_t option =
    match t with
    | NumConstant _ -> Some t
    | ArgValue par ->
       List.fold_left (fun acc (cpar, x) ->
           match acc with
           | Some _ -> acc
           | _ ->
              if (fts_parameter_equal cpar par) then
                match x with
                | XConst (IntConst n) -> Some (NumConstant n)
                | _ -> None
              else
                None) None callargs
    | IndexSize tt ->
       (match self#constant_bterm tt with
        | Some subterm -> Some (IndexSize subterm)
        | _ -> None)
    | ByteSize tt ->
       (match self#constant_bterm tt with
        | Some subterm -> Some (ByteSize subterm)
        | _ -> None)
    | ArgSizeOf _ -> Some t
    | NamedConstant _ -> Some t
    | _ -> None

end


class floc_t (finfo:function_info_int) (loc:location_int):floc_int =
object (self)

  method ia = loc#i
  method fa = loc#f
  method cia = loc#ci
  method f = finfo
  method l = loc

  method env = self#f#env
  method inv = self#f#iinv self#cia

  method varinv = self#f#ivarinv self#cia

  method memrecorder = mk_memory_recorder self#f self#cia

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   *                                                           return values *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method record_return_value =
    let eax = self#env#mk_cpu_register_variable Eax in
    let returnExpr = self#rewrite_variable_to_external eax in
    self#f#record_return_value self#cia returnExpr


  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   *                                                            call targets *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method set_call_target (ctinfo:call_target_info_int) =
    self#f#set_call_target self#cia ctinfo

  method has_call_target = self#f#has_call_target self#cia

  method get_call_target = self#f#get_call_target self#cia

  method update_call_target =
    if self#has_call_target then
      let ctinfo = self#get_call_target in
      let ctinfo =
        if ctinfo#is_app_call then
          (* update call target with new analysis results for target function *)
          let newctinfo = mk_app_target ctinfo#get_app_address in
          let _ = self#set_call_target newctinfo in
          newctinfo
        else
          ctinfo in
      if ctinfo#is_signature_valid then
        begin
          (try
             match self#update_varargs ctinfo#get_function_interface with
             | Some fintf ->
                let _ =
                  chlog#add
                    "update call target api"
                    (LBLOCK [
                         self#l#toPretty;
                         STR ": ";
                         (function_interface_to_pretty fintf)]) in
                self#set_call_target (update_target_interface ctinfo fintf)
             | _ -> ()
           with _ ->
             ());
        end
    else
      ()

  method private update_x86_varargs (_s: function_interface_t) = None

  method private update_arm_varargs (fintf: function_interface_t) =
    let args = self#get_call_arguments in
    let argcount = List.length args in
    if argcount = 0 then
      None
    else
      let (lastpar, lastx) = List.nth args (argcount - 1) in
      let arg = if is_formatstring_parameter lastpar then Some lastx else None in
      match arg with
      | Some (XConst (IntConst n)) ->
         log_tfold_default
           (mk_tracelog_spec
              ~tag:"update_arm_varargs"
              (self#cia ^ ": constant: " ^ n#toString))
           (fun addr ->
             if string_table#has_string addr then
               let fmtstring = string_table#get_string addr in
               let fmtspec = parse_formatstring fmtstring false in
               if fmtspec#has_arguments then
                 let fmtargs = fmtspec#get_arguments in
                 let newfintf = add_format_spec_parameters fintf fmtargs in
                 Some newfintf
               else
                 None
             else
               None)
           None
           (numerical_to_doubleword n)
      | _ -> None

  method private update_mips_varargs (fintf: function_interface_t) =
    let args = self#get_call_arguments in
    let argcount = List.length args in
    if argcount = 0 then
      None
    else
      let (lastpar, lastx) = List.nth args (argcount - 1) in
      let arg = if is_formatstring_parameter lastpar then Some lastx else None in
      match arg with
      | Some (XConst (IntConst n)) ->
         log_tfold_default
           (mk_tracelog_spec
              ~tag:"update_mips_varargs"
              (self#cia ^ ": constant: " ^ n#toString))
           (fun addr ->
             if string_table#has_string addr then
               let fmtstring = string_table#get_string addr in
               let fmtspec = parse_formatstring fmtstring false in
               if fmtspec#has_arguments then
                 let fmtargs = fmtspec#get_arguments in
                 let newfintf = add_format_spec_parameters fintf fmtargs in
                 Some newfintf
               else
                 None
             else
               None)
           None
           (numerical_to_doubleword n)
      | _ -> None

  method private update_varargs (fintf: function_interface_t) =
    let fts = fintf.fintf_type_signature in
    match fts.fts_va_list with
    | Some _ -> None
    | _ ->
       if system_settings#is_mips then
         self#update_mips_varargs fintf
       else if system_settings#is_arm then
         self#update_arm_varargs fintf
       else
         self#update_x86_varargs fintf

  (* Power32 uses r3 through r10 as default argument registers *)
      (*
  method get_pwr_call_arguments =
    let get_regargs pars =
      List.mapi
        (fun i p ->
          let reg = (i + 3) in
          let avar = self#env#mk_pwr_gp_register_variable reg in
          (p, self#inv#rewrite_expr (XVar avar) self#env#get_variable_comparator))
        pars in
    let ctinfo = self#get_call_target in
    if ctinfo#is_signature_valid then
      let fintf = ctinfo#get_function_interface in
      let fts = fintf.fintf_type_signature in
      let npars = List.length fts.fts_parameters in
      if npars <= 8 then
        get_regargs fts.fts_parameters
      else
        []
    else
      []
       *)

  method set_instruction_bytes (b:string) =
    self#f#set_instruction_bytes self#cia b

  method get_instruction_bytes =
    self#f#get_instruction_bytes self#cia

  method private get_wrapped_call_args =
    let ctinfo = self#get_call_target in
    let argmapping = ctinfo#get_wrapped_app_parameter_mapping in
    List.map (fun (p,t) ->
      let x = match t with
      | ArgValue p -> self#evaluate_fts_argument p
      | NumConstant x -> num_constant_expr x
      | _ -> random_constant_expr in
      (p,x)) argmapping

  method get_call_arguments: (fts_parameter_t * xpr_t) list =
    let get_regargs (pars: fts_parameter_t list): (fts_parameter_t * xpr_t) list =
      List.map (fun p ->
          let reg =
            fail_tvalue
              (trerror_record (STR "get_call_arguments: get_regargs"))
              (get_register_parameter_register p) in
          let rvar = self#env#mk_register_variable reg in
          let xpr = self#inv#rewrite_expr (XVar rvar) in
          (p, xpr)) pars in
    let get_stackargs (pars: fts_parameter_t list):
          (fts_parameter_t * xpr_t) list =
      List.map (fun p ->
          let name = get_parameter_name p in
          let memref = self#f#env#mk_local_stack_reference in
          let p_offset =
            fail_tvalue
              (trerror_record (STR "get_call_arguments: get_stackargs(p-offset)"))
              (get_stack_parameter_offset p) in
          let svar =
            log_tfold_default
              (mk_tracelog_spec ("get_call_arguments: get_stackargs(svar)"))
              (fun s_offset ->
                self#f#env#mk_memory_variable
                  memref (s_offset#add (mkNumerical p_offset)))
              (self#f#env#mk_unknown_memory_variable name)
              self#get_singleton_stackpointer_offset in
          (p, self#inv#rewrite_expr (XVar svar))
        ) pars in
    let ctinfo = self#get_call_target in
    let fintf = ctinfo#get_function_interface in
    let stackpars = get_stack_parameters fintf in
    let regpars = get_register_parameters fintf in
    let _ =
      chlog#add
        "floc:get_call_arguments"
        (LBLOCK [
             self#l#toPretty;
             STR "  ";
             STR ctinfo#get_name;
             STR ": ";
             INT (List.length stackpars);
             STR " stackparameters; ";
             INT (List.length regpars);
             STR " register parameters"]) in

    List.concat [(get_regargs regpars); (get_stackargs stackpars)]

  method get_call_args =
    let ctinfo = self#get_call_target in
    if ctinfo#is_wrapped_app_call then
      self#get_wrapped_call_args
    else if ctinfo#is_signature_valid then
      let fintf = ctinfo#get_function_interface in
      let fts = fintf.fintf_type_signature in
      let pcompare p1 p2 =
	list_compare p1.apar_location p2.apar_location parameter_location_compare in
      let parameters = List.sort pcompare fts.fts_parameters in
      List.map (fun p -> (p,self#evaluate_fts_argument p)) parameters
    else if system_info#has_esp_adjustment self#l#base_f self#l#i then
      let adj = system_info#get_esp_adjustment self#l#base_f self#l#i in
      let adj = adj / 4 in
      let indices =
	let rec add acc n =
          if n <= 0 then acc else add (n::acc) (n-1) in
        add [] adj in
      List.map (fun p ->
          let offset = 4 * p in
	  let par = mk_indexed_stack_parameter offset p in
	  let argvar = self#f#env#mk_bridge_value self#cia p in
	  let argval = self#get_bridge_variable_value p argvar in
	  (par,argval)) indices
    else
      let _ =
        chlog#add
          "floc:get_call_args"
          (LBLOCK [
               self#l#toPretty;
               STR ": calltarget: ";
               ctinfo#toPretty;
               STR "; no arguments found"]) in
      []

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save IndReg (cpureg, offset)   (memrefs1)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_memory_variable_1
           ?(align=1)    (* alignment of var value *)
           ?(size=4)
           (var:variable_t)
           (offset:numerical_t) =
    let default () =
      self#env#mk_memory_variable
        (self#env#mk_unknown_memory_reference "memref-1") offset in
    let inv = self#inv in
    let get_base_offset_constant inv =
      if inv#is_base_offset_constant var then
	let (base,offsetConstant) = inv#get_base_offset_constant var in
	let memoffset = offsetConstant#add offset in
        log_tfold
          (log_error "get_memory_variable_1" "invalid memref")
          ~ok:(fun memref ->
            self#env#mk_memory_variable ~size memref memoffset)
          ~error:(fun _ -> default ())
          (self#env#mk_base_sym_reference base)
      else
        default () in
    let get_var_from_address () =
      let varx =
        if align > 1 then
          let alignx = int_constant_expr align in
          XOp (XMult, [XOp (XDiv, [XVar var; alignx]); alignx])
        else
          XVar var in
      let addr = XOp (XPlus, [varx; num_constant_expr offset]) in
      let address = inv#rewrite_expr addr in
      match address with
      | XConst (IntConst n) ->
         log_tfold_default
           (log_error
              "get_memory_variable_1"
              (self#cia ^ ": constant: " ^ n#toString))
           (fun base ->
             if system_info#get_image_base#le base then
               self#env#mk_global_variable ~size n
             else
               default ())
           (default ())
           (numerical_to_doubleword n)
      | XVar v when self#f#env#is_memory_address_variable v ->
         log_tfold_default
           (log_error
              "get_memory_variable_1"
              (self#cia ^ ": memory address variable: " ^ (p2s var#toPretty)))
           (fun v -> v)
           (default ())
           (self#env#mk_memory_address_deref_variable v)
      | XOp (XPlus, [XVar v; XConst (IntConst n)])
           when self#f#env#is_memory_address_variable v ->
         log_tfold_default
           (log_error
              "get_memory_variable_1"
              (self#cia ^ ": memory address variable: " ^ (p2s var#toPretty)))
           (fun v -> v)
           (default ())
           (self#env#mk_memory_address_deref_variable ~offset:n#toInt v)
      | _ ->
         let (memref, memoffset) = self#decompose_address address in
         if is_constant_offset memoffset then
           let memvar =
             if memref#is_global_reference then
               self#env#mk_global_variable (get_total_constant_offset memoffset)
             else
               self#env#mk_memory_variable
                 memref (get_total_constant_offset memoffset) in
           memvar
         else
           default () in
    let memvar = get_base_offset_constant inv in
    if self#env#is_unknown_memory_variable memvar || memvar#isTmp then
      get_var_from_address ()
    else
      memvar

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save ScaledReg (cpureg1, cpureg2, 1, offset)   (memrefs2)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_memory_variable_2
           ?(size=4) (var1:variable_t) (var2:variable_t) (offset:numerical_t) =
    let _ = track_function
              ~iaddr:self#cia self#fa
              (LBLOCK [
                   STR "get_memory_variable_2: ";
                   STR "var1: ";
                   var1#toPretty;
                   STR "; var2: ";
                   var2#toPretty;
                   STR "; offset: ";
                   offset#toPretty]) in
    let addr = XOp (XPlus, [XVar var1; XVar var2]) in
    let addr = XOp (XPlus, [addr; num_constant_expr offset]) in
    let address = self#inv#rewrite_expr addr in
    let (memref, memoffset) = self#decompose_address address in
    if is_constant_offset memoffset then
      self#env#mk_memory_variable ~size memref (get_total_constant_offset memoffset)
    else
      self#env#mk_memory_variable
        (self#env#mk_unknown_memory_reference "memref-2") numerical_zero

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save ScaledReg (cpureg1, cpureg2, s, offset)  (memrefs3)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_memory_variable_3
           ?(size=4)
           (base:variable_t)
           (index:variable_t)
           (scale:int)
           (offset:numerical_t) =
    let default () =
      self#env#mk_memory_variable
        (self#env#mk_unknown_memory_reference "memref-1") offset in
    let inv = self#inv in
    let indexExpr =
      if inv#is_constant index then
	num_constant_expr (inv#get_constant index)
      else
        XVar index in
    let addr = XOp (XPlus, [XVar base; num_constant_expr offset]) in
    let addr = self#inv#rewrite_expr addr in
    let addr =
      XOp (XPlus,
           [addr; XOp (XMult, [int_constant_expr scale; indexExpr])]) in
    let address = self#inv#rewrite_expr addr in
    let (memref, memoffset) = self#decompose_address address in
    if is_constant_offset memoffset then
      if memref#is_global_reference then
        self#env#mk_global_variable (get_total_constant_offset memoffset)
      else
        self#env#mk_memory_variable
          ~size memref (get_total_constant_offset memoffset)
    else
      match memoffset with
      | IndexOffset _ ->
         self#env#mk_index_offset_memory_variable memref memoffset
      | ConstantOffset (n, IndexOffset (v, s, o)) ->
         self#env#mk_index_offset_global_memory_variable n (IndexOffset (v, s, o))
      | _ ->
         default ()


  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * resolve and save ScaledReg (None,indexreg, scale, offset)
   *      (scale <> 1)  (memrefs4)
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_memory_variable_4 (index:variable_t) (scale:int) (offset:numerical_t) =
    let indexExpr = self#rewrite_variable_to_external index in
    let offsetXpr =
      simplify_xpr (XOp (XMult, [int_constant_expr scale; indexExpr])) in
    let offsetXpr =
      simplify_xpr (XOp (XPlus, [num_constant_expr offset; offsetXpr])) in
    let default () = self#env#mk_unknown_memory_variable (x2s offsetXpr) in
    match offsetXpr with
    | XConst (IntConst n) when n#geq nume32 ->
       let n = n#modulo nume32 in
       log_tfold_default
         (mk_tracelog_spec
            ~tag:"get_memory_variable_4"
            (self#cia ^ ": constant: " ^ n#toString))
         (fun base ->
           if system_info#get_image_base#le base then
             self#env#mk_global_variable n
           else
             default ())
         (default ())
         (numerical_to_doubleword n)

    | XConst (IntConst n) ->
       log_tfold_default
         (mk_tracelog_spec
            ~tag:"get_memory_variable_4"
            (self#cia ^ ": constant: " ^ n#toString))
         (fun base ->
           if system_info#get_image_base#le base then
             self#env#mk_global_variable n
           else
             default ())
         (default ())
         (numerical_to_doubleword n)
    | _ ->
       begin
         track_function
           ~iaddr:self#cia self#fa
           (LBLOCK [
                STR "get_memory_variable_4: ";
                STR "index: "; index#toPretty;
                STR "scale: "; INT scale;
                STR "offset: "; offset#toPretty]);
         self#env#mk_unknown_memory_variable (x2s offsetXpr)
       end

  (* Creates expressions in the environment of the call target with variables
     wrapped in external variables                                            *)
  method externalize_expr (_tgt_faddr:doubleword_int) (_x:xpr_t) = []

  method rewrite_variable_to_external (var:variable_t) =
    self#inv#rewrite_expr (XVar var)

  method private rewrite_numerical_exp (exp:numerical_exp_t) =
    let rewrite = self#rewrite_variable_to_external in
    match exp with
    | NUM n -> num_constant_expr n
    | NUM_VAR v -> rewrite v
    | PLUS (v1,v2) -> simplify_xpr (XOp (XPlus, [rewrite v1; rewrite v2]))
    | MINUS (v1,v2) -> simplify_xpr (XOp (XMinus, [rewrite v1; rewrite v2]))
    | MULT (v1,v2) -> simplify_xpr (XOp (XMult, [rewrite v1; rewrite v2]))
    | DIV (v1,v2) -> simplify_xpr (XOp (XDiv, [rewrite v1; rewrite v2]))

  method has_initial_value = self#inv#var_has_initial_value

  method private is_initial_value_variable (v:variable_t) =
    (self#f#env#is_initial_memory_value v)
    || (self#env#is_initial_register_value v)

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * esp offset                                                               *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method get_singleton_stackpointer_offset: numerical_t traceresult =
    let ename = "get_singleton_stackpointer_offset" in
    let arch = system_settings#get_architecture in
    let roffset = self#get_stackpointer_offset arch in
    match roffset with
    | (0, sprange) ->
       (match sprange#singleton with
        | Some num -> Ok num
        | _ ->
           Error [ename ^ ": " ^ (self#stackpointer_offset_to_string arch)])
    | (level, _) ->
       Error [ename ^ ": level: " ^ (string_of_int level)]

  method get_stackpointer_offset arch =
    match arch with
    | "x86" -> self#get_esp_offset
    | "mips" -> self#get_sp_offset
    | "arm" -> self#get_arm_sp_offset
    | "pwr" -> self#get_pwr_sp_offset
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Architecture not recognized: "; STR arch]))

  method stackpointer_offset_to_string arch =
    match arch with
    | "x86" -> self#esp_offset_to_string
    | "mips" -> self#sp_offset_to_string
    | "arm" -> self#arm_sp_offset_to_string
    | "pwr" -> self#pwr_sp_offset_to_string
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Architecture not recognized: "; STR arch]))

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

  method private get_arm_sp_offset =  (* specific to arm *)
    let inv = self#inv in
    let spreg = ARMRegister ARSP in
    let sp = self#env#mk_register_variable spreg in
    let sp0 = self#env#mk_initial_register_value ~level:0 spreg in
    let sp0Offset = inv#get_interval_offset sp0 sp in
    if sp0Offset#isTop then
      let sp1 = self#env#mk_initial_register_value ~level:1 spreg in
      let sp1Offset = inv#get_interval_offset sp1 sp in
      if sp1Offset#isTop then
        (0, topInterval)
      else
        (1, sp1Offset)
    else
      (0, sp0Offset)

  method private get_pwr_sp_offset =  (* specific to power32 *)
    let inv = self#inv in
    let spreg = PowerGPRegister 1 in
    let sp = self#env#mk_register_variable spreg in
    let sp0 = self#env#mk_initial_register_value ~level:0 spreg in
    let sp0Offset = inv#get_interval_offset sp0 sp in
    if sp0Offset#isTop then
      let sp1 = self#env#mk_initial_register_value ~level:1 spreg in
      let sp1Offset = inv#get_interval_offset sp1 sp in
      if sp1Offset#isTop then
        (0, topInterval)
      else
        (1, sp1Offset)
    else
      (0, sp0Offset)

  method private esp_offset_to_string =
    let (level,offset) = self#get_esp_offset in
    let openB = string_repeat "[" (level+1) in
    let closeB = string_repeat "]" (level+1) in
    let offset = if offset#isTop then " ? "	else
	match offset#singleton with
	| Some num -> num#toString
	| _ ->
	  match (offset#getMin#getBound, offset#getMax#getBound) with
	    (NUMBER lb, NUMBER ub) -> lb#toString  ^ "; " ^ ub#toString
	  | (NUMBER lb, _ ) -> lb#toString ^ "; oo"
	  | (_, NUMBER ub ) -> "-oo; " ^ ub#toString
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
	    (NUMBER lb, NUMBER ub) -> lb#toString  ^ "; " ^ ub#toString
	  | (NUMBER lb, _ ) -> lb#toString ^ "; oo"
	  | (_, NUMBER ub ) -> "-oo; " ^ ub#toString
	  | _ -> "?" in
    openB ^ " " ^ offset ^ " " ^ closeB

  method private arm_sp_offset_to_string =
    let (level,offset) = self#get_arm_sp_offset in
    let openB = string_repeat "[" (level+1) in
    let closeB = string_repeat "]" (level+1) in
    let offset = if offset#isTop then " ? "	else
	match offset#singleton with
	  Some num -> num#toString
	| _ ->
	  match (offset#getMin#getBound, offset#getMax#getBound) with
	    (NUMBER lb, NUMBER ub) -> lb#toString  ^ "; " ^ ub#toString
	  | (NUMBER lb, _ ) -> lb#toString ^ "; oo"
	  | (_, NUMBER ub ) -> "-oo; " ^ ub#toString
	  | _ -> "?" in
    openB ^ " " ^ offset ^ " " ^ closeB

  method private pwr_sp_offset_to_string =
    let (level,offset) = self#get_pwr_sp_offset in
    let openB = string_repeat "[" (level+1) in
    let closeB = string_repeat "]" (level+1) in
    let offset = if offset#isTop then " ? "	else
	match offset#singleton with
	| Some num -> num#toString
	| _ ->
	  match (offset#getMin#getBound, offset#getMax#getBound) with
	  | (NUMBER lb, NUMBER ub) -> lb#toString  ^ "; " ^ ub#toString
	  | (NUMBER lb, _) -> lb#toString ^ "; oo"
	  | (_, NUMBER ub) -> "-oo; " ^ ub#toString
	  | _ -> "?" in
    openB ^ " " ^ offset ^ " " ^ closeB

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * jump tables                                                               *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method set_jumptable_target
           (base:doubleword_int)  (t:jumptable_int) (reg:register_t) =
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

  method get_function_arg_value (_argIndex: int) = random_constant_expr

  method get_fts_parameter_expr (_p: fts_parameter_t) = None

  method decompose_memvar_address
           (x: xpr_t): (memory_reference_int * memory_offset_t) option =
    let _ = chlog#add "decompose_array_address" (LBLOCK [STR "xpr: "; x2p x]) in
    let vars = vars_as_positive_terms x in
    let memaddrs = List.filter self#f#env#is_memory_address_variable vars in
    let optbase =
      match memaddrs with
      | [base] ->
         let (_, _, _, optty) =
           TR.tget_ok (self#f#env#varmgr#get_memory_address_meminfo base) in
         let offset = simplify_xpr (XOp (XMinus, [x; XVar base])) in
         Some (XVar base, offset, optty)
      | _ ->
         None in
    match optbase with
    | None -> None
    | Some (_, _, None) -> None
    | Some (XVar base, xoffset, Some ty) when is_array_type ty ->
       let _ =
         chlog#add
           "decompose_array_address" (LBLOCK [STR "xoffset: "; x2p xoffset]) in
       let eltty = get_element_type ty in
       let elttysize = size_of_btype eltty in
       let optmemref = TR.to_option (self#env#mk_base_variable_reference base) in
       let optindex = get_array_index_offset xoffset elttysize in
       let memoffset =
         match optindex with
         | None ->
            let _ =
              chlog#add
                "decompose_array_address"
                (LBLOCK [
                     STR "Unable to get array index offset for ";
                     x2p xoffset;
                     STR " with size ";
                     INT elttysize]) in
            UnknownOffset
         | Some (indexxpr, rem) ->
            let remoffset = mk_maximal_memory_offset rem eltty in
            ArrayIndexOffset (indexxpr, remoffset) in
       (match (optmemref, memoffset) with
        | (_, UnknownOffset) -> None
        | (Some memref, memoffset) -> Some (memref, memoffset)
        | _ ->
           None)
    | Some (XVar base, xoffset, Some ty) when is_struct_type ty ->
       let _ =
         chlog#add
           "decompose_struct_address" (LBLOCK [STR "xoffset: "; x2p xoffset]) in
       let optmemref = TR.to_option (self#env#mk_base_variable_reference base) in
       let cinfo = get_struct_type_compinfo ty in
       (match xoffset with
        | XConst (IntConst n) ->
           let optfinfo = get_struct_field_at_offset cinfo n#toInt in
           (match optfinfo with
            | None -> None
            | Some (finfo, rem) when rem = 0 ->
               let memoffset = FieldOffset ((finfo.bfname, cinfo.bckey), NoOffset) in
               (match optmemref with
                | Some memref -> Some (memref, memoffset)
                | _ -> None)
            | _ -> None)
        | _ -> None)
    | _ -> None


  (* the objective is to extract a base pointer and an offset expression
   * first check whether the expression contains any variables that are known
   * base pointers;
   * if so, that variable must be the base (any address can only have one
   * pointer, as pointers cannot be added);
   * if not, identify the variable most likely to be the base pointer.
   *)
  method decompose_address (x:xpr_t):(memory_reference_int * memory_offset_t) =
    let default () =
      (self#env#mk_unknown_memory_reference (x2s x), UnknownOffset) in
     let is_external_constant v = self#env#is_function_initial_value v in
(*       (self#f#env#is_return_value v) ||
	 (self#f#env#is_sideeffect_value v) ||
	 (self#f#env#is_calltarget_value v) in *)
     let vars = vars_as_positive_terms x in
     let knownPointers = List.filter self#f#is_base_pointer vars in
     let optBaseOffset = match knownPointers with
       | [base] ->
          let offset = simplify_xpr (XOp (XMinus, [x; XVar base])) in
          Some (XVar base, offset)
       | [] ->
	 let maxC = largest_constant_term x in
	 if maxC#gt system_info#get_image_base#to_numerical
            && (match vars with [] -> true | _ -> false) then
	   (* base address is an absolute address *)
	   Some (num_constant_expr maxC,
		 simplify_xpr (XOp (XMinus, [x; num_constant_expr maxC])))
	 else
	   begin
	     match vars  with
	     | [base] when (self#is_initial_value_variable base) ||
		 (is_external_constant base) ->
	        begin
		  self#f#add_base_pointer base;
		  Some (XVar base, simplify_xpr (XOp (XMinus, [x; XVar base])))
	       end
	     | [base] when self#env#is_stack_parameter_variable base &&
		 self#f#env#has_constant_offset base && self#has_initial_value base ->
	       let baseInit = self#f#env#mk_initial_memory_value base in
	       begin
		 self#f#add_base_pointer baseInit;
		 Some (XVar base, simplify_xpr (XOp (XMinus, [x; XVar base])))
	       end
             | [_] -> None
	     | [] ->      (* suspicious address below the image base *)
	       begin
		 let _ = match x with
		     (XConst (IntConst num)) ->
		       if num#equal numerical_zero then
			 begin
			   chlog#add
                             "null dereference"
			     (LBLOCK [self#l#toPretty]);
			 end
		       else if num#lt numerical_zero then
			 begin
			   chlog#add
                             "negative address"
			     (LBLOCK [self#l#toPretty; STR ": "; num#toPretty]);
			 end
		       else
			 begin
			   chlog#add
                             "low address"
			     (LBLOCK [self#l#toPretty; STR ": "; x2p x]);
			 end
		   | _ ->
		     begin
		       chlog#add
                         "low address"
			 (LBLOCK [self#l#toPretty; STR ": "; x2p x]);
		     end in
		 None
	       end
	     | _ ->
		 None
	   end
       | ptrs ->
	 let msg = LBLOCK [
	   x2p x;
	   pretty_print_list ptrs
	     (fun v -> self#env#variable_name_to_pretty v)  " (" ", " ")"] in
	 begin
	   chlog#add "error:multiple pointers"
	     (LBLOCK [self#l#toPretty; STR ": "; msg]);
	   None
	 end in
     try
       match optBaseOffset with
       | Some (XVar v, xoffset) ->
          log_tfold
            (log_error "decompose_address" "invalid memref")
            ~ok:(fun memref ->
              let offset = match xoffset with
                | XConst (IntConst n) -> ConstantOffset (n, NoOffset)
                | XOp (XMult, [XConst (IntConst n); XVar v]) ->
                   IndexOffset (v, n#toInt, NoOffset)
                | _ -> UnknownOffset in
              (memref, offset))
            ~error:(fun _ -> default ())
            (self#env#mk_base_variable_reference v)
       | Some (XConst (IntConst n), xoffset) ->
          let offset = match xoffset with
            | XConst (IntConst n) -> ConstantOffset (n, NoOffset)
            | XOp (XMult, [XConst (IntConst n); XVar v]) ->
               IndexOffset (v, n#toInt, NoOffset)
            | XOp (XMult, [XConst (IntConst n); x])
                 when self#is_composite_symbolic_value x ->
               let v = self#env#mk_symbolic_value x in
               IndexOffset (v, n#toInt, NoOffset)
            | _ -> UnknownOffset in
          let offset = ConstantOffset (n, offset) in
          let memref = self#env#mk_global_memory_reference in
          (memref, offset)
       | Some (_base, _offset) ->  default ()
       | _ -> default ()
     with
       Invalid_argument s ->
	 let msg = LBLOCK [STR " address: "; x2p x; STR " : "; STR s] in
	 begin
	   chlog#add "error:memory reference"
	     (LBLOCK [self#l#toPretty; STR ": "; msg]);
	   default ()
	 end
     | Invocation_error s ->
       begin
	 ch_error_log#add
           "variable_manager"
	   (LBLOCK [
                self#l#toPretty;
                STR ". get_memory_reference_from_address: ";
		x2p x;
                STR " (";
                STR s;
                STR ")"]);
	 default ()
       end

   method get_lhs_from_address (xpr:xpr_t) =
     let xpr = self#inv#rewrite_expr xpr in
     let default () =
       self#env#mk_memory_variable
         (self#env#mk_unknown_memory_reference "lhs-from-address")
         numerical_zero in
     match xpr with
     | XConst (IntConst n) when n#gt numerical_zero ->
        log_tfold_default
          (mk_tracelog_spec
             ~tag:"get_lhs_from_address"
             (self#cia ^ ": constant: " ^ n#toString))
          (fun base ->
            if system_info#get_image_base#le base then
	      self#env#mk_global_variable n
            else
              default ())
          (default ())
          (numerical_to_doubleword n)
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

   method get_test_expr = self#f#get_test_expr self#cia

   method get_conditional_assign_commands
            (test_expr:xpr_t)
            (lhs:variable_t)
            (rhs_expr:xpr_t) =
     let reqN () = self#env#mk_num_temp in
     let reqC = self#env#request_num_constant in
     let testxpr = self#inv#rewrite_expr test_expr in
     let ftestxpr = simplify_xpr (XOp (XLNot, [testxpr])) in
     let assigncmds = self#get_assign_commands lhs rhs_expr in
     let (tcmds,txpr) = xpr_to_boolexpr reqN reqC testxpr in
     let (fcmds,fxpr) = xpr_to_boolexpr reqN reqC ftestxpr in
     let asserttcmd = ASSERT txpr in
     let assertfcmd = ASSERT fxpr in
     let truecmds = tcmds @ [asserttcmd] @ assigncmds in
     let falsecmds = fcmds @ [assertfcmd] in
     [BRANCH [LF.mkCode truecmds; LF.mkCode falsecmds]]

   method private is_composite_symbolic_value (x: xpr_t): bool =
     let is_external v = self#f#env#is_function_initial_value v in
     let is_fixed_type v =
       (is_external v)
       || (self#f#env#is_symbolic_value v) in
     let vars = variables_in_expr x in
     (List.length vars) > 0
     && List.for_all is_fixed_type (variables_in_expr x)

   (* Note: recording of loads and stores is performed by the different
      architectures directly in FnXXXDictionary.*)
   method get_assign_commands
     (lhs:variable_t)
     ?(size=random_constant_expr)
     ?(vtype=t_unknown)
     (rhs_expr:xpr_t) =
     let rhs_expr = simplify_xpr rhs_expr in
     let rhs_expr = self#inv#rewrite_expr rhs_expr in

     (* if the rhs_expr is a composite symbolic expression, create a
        new variable for it *)
     let rhs_expr =
       if self#is_composite_symbolic_value rhs_expr then
         XVar (self#env#mk_symbolic_value rhs_expr)
       else
         rhs_expr in

     let _ =
       match size with
       | XConst XRandom -> ()
       | XConst (IntConst n) when n#equal (mkNumerical 4) ->
          ()
       | XConst (IntConst n) ->
          chlog#add
            "assignment size not used"
            (LBLOCK [
                 lhs#toPretty;
                 STR " := ";
                 x2p rhs_expr;
                 STR " with size ";
                 n#toPretty])
       | _ ->
          chlog#add
            "assignment size expression not used"
            (LBLOCK [
                 lhs#toPretty;
                 STR " := ";
                 x2p rhs_expr;
                 STR " with size ";
                 x2p size]) in

     let _ =
       if not (is_unknown_type vtype) then
         chlog#add
           "assignment type not used"
           (LBLOCK [
                lhs#toPretty;
                STR " := ";
                x2p rhs_expr;
                STR " with type ";
                btype_to_pretty vtype]) in

     let reqN () = self#env#mk_num_temp in
     let reqC = self#env#request_num_constant in
     let (rhsCmds, rhs) = xpr_to_numexpr reqN reqC rhs_expr in

     (* if the lhs is unknown, add an operation to record an unknown write *)
     if lhs#isTmp || self#env#is_unknown_memory_variable lhs then
       let op_args = get_rhs_op_args rhs in
       [OPERATION ({ op_name = unknown_write_symbol; op_args = op_args});
	ASSIGN_NUM (lhs, rhs)]

     else
       rhsCmds @ [ASSIGN_NUM (lhs, rhs)]

   method get_ssa_assign_commands
            (reg: register_t) ?(vtype=t_unknown) (rhs: xpr_t):
            variable_t * cmd_t list =
     let rhsx = simplify_xpr rhs in
     let rhsx = self#inv#rewrite_expr rhsx in
     let rhsx_assign =
       if self#is_composite_symbolic_value rhsx then
         let sv = self#env#mk_symbolic_value rhsx in
         begin
           (match vtype with
            | TUnknown _ -> ()
            | _ ->
               begin
                 chlog#add
                   "set constant-value variable type"
                   (LBLOCK [
                        STR self#cia;
                        STR ": ";
                        sv#toPretty;
                        STR ": ";
                        STR (btype_to_string vtype)]);
                 self#f#set_btype sv vtype
               end);
           XVar sv
         end
       else
         rhsx in
     let reqN () = self#env#mk_num_temp in
     let reqC = self#env#request_num_constant in
     let (rhscmds, rhs_chif) = xpr_to_numexpr reqN reqC rhsx_assign in
     let regvar = self#env#mk_register_variable reg in
     let assigns = [ASSIGN_NUM (regvar, rhs_chif)] in
     (regvar, rhscmds @ assigns)

   method get_vardef_commands
            ?(defs: variable_t list = [])
            ?(clobbers: variable_t list = [])
            ?(use: variable_t list = [])
            ?(usehigh: variable_t list = [])
            ?(flagdefs: variable_t list = [])
            (iaddr: string): cmd_t list =
     let op_name (kind: string) = new symbol_t ~atts:[iaddr] kind in
     let def_op_name = op_name "def" in
     let clobber_op_name = op_name "clobber" in
     let use_op_name = op_name "use" in
     let usehigh_op_name = op_name "use_high" in
     let flagdef_op_name = op_name "def" in
     let mk_ops (doms: string list) (opname: symbol_t) (vars: variable_t list) =
       List.map (fun v ->
           let symv = self#f#env#mk_symbolic_variable ~domains:doms v in
           let op = {op_name = opname; op_args = [("dst", symv, WRITE)]} in
           OPERATION op) vars in
     let defdoms = ["reachingdefs"; "defuse"; "defusehigh"] in
     let defops = mk_ops defdoms def_op_name defs in
     let clobberops = mk_ops defdoms clobber_op_name clobbers in
     let useops = mk_ops ["defuse"] use_op_name use in
     let usehighops = mk_ops ["defusehigh"] usehigh_op_name usehigh in
     let flagdefops = mk_ops ["flagreachingdefs"] flagdef_op_name flagdefs in
     useops @ usehighops @ defops @ clobberops @ flagdefops

   method get_set_btype_commands (v: variable_t) (t: btype_t): cmd_t list =
     let abtype = btype_abstract t in
     let op_name = new symbol_t ~atts:[abtype#getBaseName] "btype-set" in
     let op_args = [("type", v, WRITE)] in
     let op = {op_name = op_name; op_args = op_args} in
     [OPERATION op]

   method get_propagate_btype_commands
            (vdst: variable_t) (vsrc: variable_t): cmd_t list =
     let op_name = new symbol_t "btype-prop" in
     let op_args = [("dst", vdst, WRITE); ("src", vsrc, READ)] in
     let op = {op_name = op_name; op_args = op_args} in
     [OPERATION op]

   method private evaluate_fts_argument (p: fts_parameter_t) =
     match p.apar_location with
     | [StackParameter (offset, _)] ->
        let index = offset / 4 in
        let argvar = self#env#mk_bridge_value self#cia index in
        self#get_bridge_variable_value index argvar
     | [RegisterParameter (r, _)] ->
        let argvar = self#env#mk_register_variable r in
        self#rewrite_variable_to_external argvar
     | [GlobalParameter (a, _)] ->
        let argvar = self#env#mk_global_variable a#to_numerical in
        self#rewrite_variable_to_external argvar
     | _ -> random_constant_expr

   method evaluate_summary_term (t:bterm_t) (returnvar:variable_t) =
     match t with
     | ArgValue p -> self#evaluate_fts_argument p
     | ReturnValue _ -> XVar returnvar
     | NumConstant n -> num_constant_expr n
     | NamedConstant name -> XVar (self#env#mk_runtime_constant name)
     | ByteSize t -> self#evaluate_summary_term t returnvar
     | ArithmeticExpr (op, t1, t2) ->
       let xpr1 = self#evaluate_summary_term t1 returnvar in
       let xpr2 = self#evaluate_summary_term t2 returnvar in
       XOp (arithmetic_op_to_xop op, [xpr1; xpr2])
     | _ -> random_constant_expr

   method private evaluate_fts_address_argument (p: fts_parameter_t) =
     let _ =
       chlog#add
         "evaluate-fts-address-argument: failure"
         (LBLOCK [
              STR self#cia;
              STR ": ";
              fts_parameter_to_pretty p]) in
     None

   method evaluate_summary_address_term (t:bterm_t) =
     match t with
     | ArgValue p -> self#evaluate_fts_address_argument p
     | NumConstant num ->
        log_tfold_default
          (mk_tracelog_spec
             ~tag:"evaluate_summary_address_term"
             (self#cia ^ ": constant: " ^ num#toString))
          (fun base ->
            if system_info#get_image_base#le base then
	      Some (self#env#mk_global_variable num)
            else
              None)
          None
          (numerical_to_doubleword num)
     | ArgAddressedValue (subT,NumConstant offset) ->
	let optBase = self#evaluate_summary_address_term subT in
	begin
	  match optBase with
	    Some baseVar ->
             log_tfold
               (log_error "evaluate_summary_address_term" "invalid memref")
               ~ok:(fun memref ->
	         Some (self#env#mk_memory_variable memref offset))
               ~error:(fun _ -> None)
               (self#env#mk_base_variable_reference baseVar)
	  | _ -> None
	end
     | _ -> None

   method get_abstract_commands
            (lhs:variable_t) ?(size=random_constant_expr) ?(vtype=t_unknown) () =
     let _ =
       match (size, vtype) with
       | (XConst XRandom, TUnknown _) ->
          ()
       | _ ->
          log_debug
            "Ignoring size: %s and type %s in get_abstract_commands"
            (x2s size) (btype_to_string vtype) in
     [ABSTRACT_VARS [lhs]]

   method get_ssa_abstract_commands (reg: register_t) () =
     let regvar = self#env#mk_register_variable reg in
     (regvar, [ABSTRACT_VARS [regvar]])

   method get_abstract_cpu_registers_command (regs:cpureg_t list) =
     let regs =
       List.fold_left (fun lst r ->
           if List.mem r lst then
             lst
           else
             lst @ (r::(registers_affected_by r))) [] regs in
     match regs with
     | [] -> SKIP
     | _ -> ABSTRACT_VARS (List.map self#env#mk_cpu_register_variable regs)

   method get_abstract_registers_command (regs:register_t list) =
     match regs with
     | [] -> SKIP
     | _ -> ABSTRACT_VARS (List.map self#env#mk_register_variable regs)

   method get_operation_commands
            (lhs:variable_t)
            ?(size=random_constant_expr)
            ?(vtype=t_unknown)
            (opname:symbol_t)
            (args:op_arg_t list) =
     let _ =
       match (size, vtype, args) with
       | (XConst XRandom, TUnknown _, []) ->
          ()
       | _ ->
          log_debug
            "Ignoring size: %s and type %s in operation %s:"
            (x2s size) (btype_to_string vtype) (p2s opname#toPretty) in

     [ABSTRACT_VARS [lhs]]

   method private assert_post
                    (name:string)
                    (post: xxpredicate_t)
                    (returnvar: variable_t)
                    (string_retriever:doubleword_int -> string option) =
     let get_zero () = self#env#request_num_constant numerical_zero in
     let reqN () = self#env#mk_num_temp in
     let reqC = self#env#request_num_constant in

     let get_function_pointer_commands (fnameTerm:bterm_t) =
       let nameAddr = self#evaluate_summary_term fnameTerm returnvar in
       let fname = match nameAddr with
	 | XConst (IntConst n) ->
            log_tfold_default
              (mk_tracelog_spec
                 ~tag:"assert_post"
                 (self#cia ^ ": constant: " ^ n#toString))
              (fun dw -> string_retriever dw)
              None
              (numerical_to_doubleword n)
	 | _ ->
	    begin
	      chlog#add "function-pointer: no address" (self#l#toPretty);
	      None
	    end in
       match fname with
	 Some fname ->
	  let fpVar = self#env#mk_function_pointer_value fname name self#cia in
	  let msg = self#env#variable_name_to_pretty fpVar in
	  begin
	    translation_log#add
              "function-pointer variable"
              (LBLOCK [self#l#toPretty; STR ":  "; msg]);
	    [ASSERT (EQ (fpVar, returnvar))]
	  end
       | _ ->
	  begin
	    chlog#add "function-pointer: no name" (self#l#toPretty);
	    []
	  end in

     let get_null_var (term:bterm_t) =
       let termXpr = self#evaluate_summary_term term returnvar in
       xpr_to_numvar reqN reqC termXpr in
     let get_null_commands (term:bterm_t) =
       let (cmds,termVar) = get_null_var term in
       cmds @ [ASSERT (EQ (termVar, get_zero ()))] in
     let get_not_null_commands (term:bterm_t) =
       let (cmds,termVar) = get_null_var term in
       cmds @ [ASSERT (GT (termVar, get_zero ()))] in
     let get_post_expr_commands op t1 t2 =
       let xpr1 = self#evaluate_summary_term t1 returnvar in
       let xpr2 = self#evaluate_summary_term t2 returnvar in
       let xop = relational_op_to_xop op in
       let xpr = XOp (xop, [xpr1; xpr2]) in
       let (cmds,bxpr) = xpr_to_boolexpr reqN reqC xpr in
       cmds @ [ASSERT bxpr] in
     match post with
     | XXNewMemory (ReturnValue _, _sizeParameter) ->
        [] (* get_new_memory_commands sizeParameter *)
     | XXFunctionPointer (_, ReturnValue nameParameter) ->
        get_function_pointer_commands nameParameter
     | XXNull term -> get_null_commands term
     | XXNotNull term -> get_not_null_commands term
     | XXRelationalExpr (op, t1, t2) -> get_post_expr_commands op t1 t2
     | XXFalse ->
        let ctinfo = self#get_call_target in
        if ctinfo#is_nonreturning then
          [] (* was known during translation, or has been established earlier *)
        else
	  begin
	    (* ctinfo#set_nonreturning; *)
	    chlog#add
              "function retracing"
              (LBLOCK [self#l#toPretty; STR ": "; STR name]);
	    raise Request_function_retracing
	  end
     | _ ->
       let msg = xxpredicate_to_pretty post in
       begin
	 chlog#add "postcondition not used" (LBLOCK [self#l#toPretty; msg]);
	 []
       end

   method private get_postcondition_assertions
                    (summary:function_summary_int)
                    (returnvar:variable_t)
                    (string_retriever:doubleword_int -> string option) =
     let name = summary#get_name in
     let postCommands = List.concat
       (List.map (fun post ->
	    self#assert_post name post returnvar string_retriever)
          summary#get_postconditions) in
     let errorPostCommands = List.concat
       (List.map (fun epost ->
	 self#assert_post name epost returnvar string_retriever)
	  summary#get_errorpostconditions) in
     match (postCommands, errorPostCommands) with
     | ([],[]) -> []
     | (_, []) -> postCommands
     | ([], _) -> errorPostCommands
     | _ -> [BRANCH [LF.mkCode postCommands; LF.mkCode errorPostCommands]]

   method private record_precondition_effect (pre:xxpredicate_t) =
     match pre with
     | XXFunctionPointer (_,t) ->
       begin
	 match self#evaluate_summary_term t self#env#mk_num_temp with
	 | XConst (IntConst n) ->
            log_titer
              (mk_tracelog_spec
                 ~tag:"record_precondition_effect"
                 (self#cia ^ ": constant: " ^ n#toString))
              (fun a ->
	        if system_info#is_code_address a then
		  begin
		    ignore (functions_data#add_function a);
		    chlog#add
                      "function entry point from precondition"
		      (LBLOCK [self#l#toPretty; STR ": "; a#toPretty])
		  end
	        else
		  chlog#add
                    "function pointer precondition error"
		    (LBLOCK [
                         self#l#toPretty;
                         STR ": ";
                         a#toPretty;
                         STR " is not a code address"]))
              (numerical_to_doubleword n)
	 | x ->
	    chlog#add
              "function pointer precondition"
	      (LBLOCK [
                   self#l#toPretty;
                   STR ": unknown argument ";
		   xpr_formatter#pr_expr x])
       end
     | _ -> ()

   method private get_sideeffect_assign (side_effect: xxpredicate_t) =
     let msg =
       LBLOCK [
           self#l#toPretty; STR ": "; xxpredicate_to_pretty side_effect] in
     match side_effect with
     | XXBlockWrite (ty, dest, size) ->
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
		 match self#evaluate_fts_argument p with
		 | XConst (IntConst n) -> get_index_size n
		 | _ -> random_constant_expr
	       end
	     | _ ->
	       self#evaluate_summary_term size (self#env#mk_num_temp) in
	   let sizeExpr = simplify_xpr sizeExpr in
	   let _ =
             if is_zero sizeExpr then
	       ch_error_log#add
                 "zero size"
		 (LBLOCK [
                      self#l#toPretty;
                      STR " ";
		      xxpredicate_to_pretty side_effect]) in
	   let rhs =
 	     match dest with
 	     | NumConstant n ->
                log_tfold_default
                  (mk_tracelog_spec
                     ~tag:"get_sideeffect_assign:BlockWrite"
                     (self#cia ^ ": constant: " ^ n#toString))
                  (fun dw ->
	            let argDescr = dw#to_hex_string in
	            self#env#mk_side_effect_value self#cia ~global:true argDescr)
                  (self#env#mk_side_effect_value self#cia (bterm_to_string dest))
                  (numerical_to_doubleword n)
	     | _ ->
	        self#env#mk_side_effect_value self#cia (bterm_to_string dest) in
	   let seAssign =
             let _ =
               chlog#add
                 "side-effect assign"
                 (LBLOCK [
                      self#l#toPretty;
                      STR " ";
                      xxpredicate_to_pretty side_effect;
                      STR ": ";
                      memVar#toPretty;
                      STR " := ";
                      x2p (XVar rhs)]) in
	     self#get_assign_commands memVar ~size:sizeExpr ~vtype:ty (XVar rhs) in
	   let fldAssigns = [] in
	   seAssign @ fldAssigns
	 | _ ->
	    begin
	      chlog#add "side-effect ignored" msg;
	      []
	    end
       end
     | XXStartsThread (sa, _pars) ->
       let _ =
	 match self#evaluate_summary_term sa self#env#mk_num_temp with
	 | XConst (IntConst n) ->
            log_titer
              (mk_tracelog_spec
                 ~tag:"get_sideeffect_assign:StartsThread"
                 (self#cia ^ ": constant: " ^ n#toString))
              (fun a ->
	        if system_info#is_code_address a then
		  system_info#set_thread_start_address self#fa self#cia a [])
              (numerical_to_doubleword n)
	 | _ -> () in
       []
     | _ ->
       begin
	 chlog#add "side-effect ignored" msg;
	 []
       end

   method private record_precondition_effects (sem:function_semantics_t) =
     List.iter self#record_precondition_effect sem.fsem_pre

   method get_sideeffect_assigns  (sem:function_semantics_t) =
     List.concat (List.map self#get_sideeffect_assign sem.fsem_sideeffects)

   (* Records reads of global memory *)
   method private record_memory_reads (pres:xxpredicate_t list) =
     List.iter (fun pre ->
       match pre with
       | XXBuffer (ty,src,size) ->
	 let get_index_size k =
	   match get_size_of_type ty with
	   | Some s -> num_constant_expr (k#mult (mkNumerical s))
	   | _ -> random_constant_expr in
	 begin
	   match self#evaluate_summary_address_term src with
	   | Some memVar ->
	      if self#env#is_global_variable memVar
	         && self#env#has_global_variable_address memVar then
	        let sizeExpr =
		  match size with
		  | IndexSize (NumConstant n) -> get_index_size n
		  | IndexSize (ArgValue p) ->
		     begin
		       match self#evaluate_fts_argument p with
		       | XConst (IntConst n) -> get_index_size n
		       | _ -> random_constant_expr
		     end
		  | _ -> self#evaluate_summary_term size self#env#mk_num_temp in
	        let sizeExpr = simplify_xpr sizeExpr in
	        let size = match sizeExpr with
		  | XConst (IntConst n) -> Some n#toInt | _ -> None in
                log_tfold
                  (log_error "record_memory_reads" "invalid global address")
                  ~ok:(fun gaddr ->
	            global_system_state#add_reader ~ty ~size gaddr self#l)
                  ~error:(fun _ -> ())
		  (self#env#get_global_variable_address memVar)
              else
                ()
	   | _ -> ()
	 end
       | _ -> ()) pres

   (* Returns the CHIF code associated with a call (x86) *)
   method get_call_commands (_string_retriever:doubleword_int -> string option) =
     let ctinfo = self#get_call_target in
     let fintf = ctinfo#get_function_interface in
     let fts = fintf.fintf_type_signature in
     (* ---------------------------------------------------- abstract registers *)
     let eax = self#env#mk_cpu_register_variable Eax in
     let esp = self#env#mk_cpu_register_variable Esp in

     (* ------------------------------------------------- create operation name *)
     let opName = new symbol_t ~atts:["CALL"] fintf.fintf_name in

     (* --------------------------------------------------- get return variable *)

     let returnAssign =
       let rvar = self#env#mk_return_value self#cia in
       if ctinfo#is_signature_valid then
         let rty = ctinfo#get_returntype in
	 if is_void rty then
	   SKIP
	 else
	   let name = ctinfo#get_name ^ "_rtn_" ^ self#cia in
	   let _ = self#env#set_variable_name rvar name in
	   ASSIGN_NUM (eax, NUM_VAR rvar)
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
	   [ASSIGN_NUM (esp, PLUS (esp, adj) )]
	 else if adj < 0 then
	   [ABSTRACT_VARS [esp]]
	 else
	   []
       | _ -> [] in
   (* | _ -> [ABSTRACT_VARS [esp]] in *)
     let bridgeVars = self#env#get_bridge_values_at self#cia in
     let defClobbered = List.map (fun r -> (CPURegister r)) [Eax; Ecx; Edx] in
     let regsClobbered = List.fold_left (fun acc reg ->
       List.filter (fun r -> not (r=reg)) acc)
       defClobbered fts.fts_registers_preserved in
     let abstrRegs = List.map self#env#mk_register_variable regsClobbered in
     [OPERATION { op_name = opName; op_args = [] }]
     @ (match abstrRegs with
        | [] -> []
        | _ -> [ABSTRACT_VARS abstrRegs])
     @ [returnAssign]
     @ sideEffectAssigns
     @ espAdjustment
     @ (match bridgeVars with
        | [] -> []
        | _ -> [ABSTRACT_VARS bridgeVars])

   method get_mips_syscall_commands =
     let ctinfo = self#get_call_target in
     let v0 = self#env#mk_mips_register_variable MRv0 in
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
     [OPERATION { op_name = opname; op_args = [] };
       ABSTRACT_VARS (v1::abstrRegs); returnassign]

   method private get_bterm_xpr
                    (t: bterm_t)
                    (parargs: (fts_parameter_t * xpr_t) list): xpr_t option =
     match t with
     | ArgValue p ->
        List.fold_left (fun acc (par, x) ->
            match acc with
            | Some _ -> acc
            | _ ->
               if (fts_parameter_compare p par) = 0 then
                 Some x
               else
                 acc) None parargs
     | ArgBufferSize tt -> self#get_bterm_xpr tt parargs
     | IndexSize tt -> self#get_bterm_xpr tt parargs
     | ByteSize tt -> self#get_bterm_xpr tt parargs
     | ArgNullTerminatorPos tt -> self#get_bterm_xpr tt parargs
     | _ -> None

   method get_mips_call_commands =
     let parargs = self#get_call_arguments in
     let ctinfo = self#get_call_target in
     let argumentpropagator = new mips_argument_type_propagator_t self#f parargs in
     let _ = argumentpropagator#elevate_call_arguments in
     let termev = new mips_bterm_evaluator_t self#f parargs in
     let xprxt = new mips_expression_externalizer_t self#f in
     let semrecorder =
       mk_callsemantics_recorder self#l self#f termev xprxt ctinfo in
     let _ = semrecorder#record_callsemantics in
     let v0 = self#env#mk_mips_register_variable MRv0 in
     (* v1 may be an additional return value from the callee, abstract it for now *)
     let v1 = self#env#mk_mips_register_variable MRv1 in
     let opname = new symbol_t ~atts:["CALL"] ctinfo#get_name in
     let returnassign =
       let rvar = self#env#mk_return_value self#cia in
       if ctinfo#is_signature_valid then
         let rty = ctinfo#get_returntype in
         if is_void rty then
           SKIP
         else
           let name = ctinfo#get_name ^ "_rtn_" ^ self#cia in
           let _ = self#env#set_variable_name rvar name in
           ASSIGN_NUM (v0, NUM_VAR rvar)
       else
         ASSIGN_NUM (v0, NUM_VAR rvar) in
     let _ =
       self#record_memory_reads self#get_call_target#get_semantics.fsem_pre in
     let defClobbered = List.map (fun r -> (MIPSRegister r)) mips_temporaries in
     let abstrRegs = List.map self#env#mk_register_variable defClobbered in
     [OPERATION { op_name = opname; op_args = [] };
      ABSTRACT_VARS (v1::abstrRegs)]
     @ [returnassign]

   method get_arm_call_commands =
     let parargs = self#get_call_arguments in
     let ctinfo = self#get_call_target in
     let termev = new arm_bterm_evaluator_t self#f parargs in
     let xprxt = new arm_expression_externalizer_t self#f in
     let semrecorder =
       mk_callsemantics_recorder self#l self#f termev xprxt ctinfo in
     let _ = semrecorder#record_callsemantics in
     let r0 = self#env#mk_arm_register_variable AR0 in
     let opname = new symbol_t ~atts:["CALL"] ctinfo#get_name in
     let returnassign =
       let rvar = self#env#mk_return_value self#cia in
       let _ =
         if ctinfo#is_signature_valid then
           let name = ctinfo#get_name ^ "_rtn_" ^ self#cia in
           self#env#set_variable_name rvar name in
       ASSIGN_NUM (r0, NUM_VAR rvar) in
     let bridgeVars = self#env#get_bridge_values_at self#cia in
     let sideeffect_assigns =
       self#get_sideeffect_assigns self#get_call_target#get_semantics in
     let _ =
       self#record_memory_reads self#get_call_target#get_semantics.fsem_pre in
     let defClobbered = List.map (fun r -> (ARMRegister r)) arm_temporaries in
     let abstrRegs = List.map self#env#mk_register_variable defClobbered in
     [OPERATION {op_name = opname; op_args = []}]
     @ (match abstrRegs with
        | [] -> []
        | _ -> [ABSTRACT_VARS abstrRegs])
     @ [returnassign]
     @ sideeffect_assigns
     @ (match bridgeVars with
        | [] -> []
        | _ -> [ABSTRACT_VARS bridgeVars])

   method get_pwr_call_commands =
     let ctinfo = self#get_call_target in
     let rv = self#env#mk_pwr_gp_register_variable 3 in
     let opname = new symbol_t ~atts:["CALL"] ctinfo#get_name in
     let returnassign =
       let rvar = self#env#mk_return_value self#cia in
       let _ =
         if ctinfo#is_signature_valid then
           let name = ctinfo#get_name ^ "_rtn_" ^ self#cia in
           self#env#set_variable_name rvar name in
       ASSIGN_NUM (rv, NUM_VAR rvar) in
     let bridgevars = self#env#get_bridge_values_at self#cia in
     let defClobbered =
       List.map (fun i -> PowerGPRegister i) [3; 4; 5; 6; 7; 8; 9; 10; 11; 12] in
     let abstrregs = List.map self#env#mk_register_variable defClobbered in
     [OPERATION {op_name = opname; op_args = []}]
     @ (match abstrregs with
        | [] -> []
        | _ -> [ABSTRACT_VARS abstrregs]);
     @ [returnassign]
     @ (match bridgevars with
        | [] -> []
        | _ -> [ABSTRACT_VARS bridgevars])

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
      | XConst _ -> offset
      | XVar _ -> offset
      | XOp (XMult, [XConst _; XVar _]) -> offset
      | XOp (XMult, [XVar v; XConst (IntConst n)]) ->
	XOp (XMult, [XConst (IntConst n); XVar v])
      | _ ->
	begin
	  chlog#add "unrecognized offset" (x2p offset);
	  offset
	end in
    match address with
    | XVar _ -> address
    | XOp (XPlus, [XVar v1; XVar v2]) when not (is_external v1) && is_external v2 ->
       XOp (XPlus, [XVar v2; XVar v1])
    | XOp (XPlus, [XVar v; offset])
      | XOp (XPlus, [offset; XVar v]) ->
       XOp (XPlus, [XVar v; normalize_offset offset])
    | XOp (XMinus, [XVar v; XConst (IntConst n)]) ->
      XOp (XPlus, [XVar v; XConst (IntConst n#neg)])
    | _ -> address

  method is_address (x:xpr_t) =
    match self#normalize_address x with
    | XVar v
    | XOp (XPlus, [XVar v; _]) -> self#f#is_base_pointer v
    | _ -> false
end


let get_floc (loc:location_int) =
  new floc_t (get_function_info loc#f) loc


let get_floc_by_address (faddr: doubleword_int) (iaddr: doubleword_int) =
  get_floc (make_location {loc_faddr = faddr; loc_iaddr = iaddr})


let get_i_floc (floc:floc_int) (iaddr:doubleword_int) =
  let loc = make_i_location floc#l iaddr in
  new floc_t (get_function_info floc#fa) loc
