(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2025  Aarno Labs LLC

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
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHPrettyUtil
open CHTraceResult
open CHXmlDocument

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFtsParameter
open BCHFunctionData
open BCHFunctionInterface
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMConditionalExpr
open BCHARMDisassemblyUtils
open BCHARMOperand
open BCHARMOpcodeRecords
open BCHARMTestSupport
open BCHARMTypes

module H = Hashtbl
module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string

let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("FnARMDictionary:" ^ tag) msg


let ixd = BCHInterfaceDictionary.interface_dictionary
let bcd = BCHBCDictionary.bcdictionary


class arm_opcode_dictionary_t
        (faddr:doubleword_int)
        (vard:vardictionary_int): arm_opcode_dictionary_int =
object (self)

  val sp_offset_table = mk_index_table "sp-offset-table"
  val instrx_table = mk_index_table "instrx-table"
  val xd = vard#xd
  val fndata = BCHFunctionData.functions_data#get_function faddr

  val mutable tables = []

  initializer
    tables <- [
      sp_offset_table;
      instrx_table
    ]

  method index_sp_offset (o:(int * interval_t)) =
    let (level, offset) = o in
    let key = ([], [level; xd#index_interval offset]) in
    sp_offset_table#add key

  method get_sp_offset (index:int) =
    let (_, args) = sp_offset_table#retrieve index in
    let a = a "sp-offset" args in
    (a 0, xd#get_interval (a 1))

  (* Legend for tags:
     "nop": instruction is no-op,
     "save": saving a register to the stack,
     "a:" (prefix,arg-key) (if present should be first):
          a: address xpr; x: xpr; v: variable ; l: literal int ; s: string
   *)

  method index_instr
           (instr:arm_assembly_instruction_int)
           (floc:floc_int) =
    let varinv = floc#varinv in
    let e16_c = int_constant_expr e16 in
    let e32_c = int_constant_expr e32 in

    let get_regvar_type_annotation (): btype_t option =
      if fndata#has_regvar_type_annotation floc#l#i then
        TR.tfold
          ~ok:(fun t -> Some t)
          ~error:(fun e ->
            begin
              log_error_result __FILE__ __LINE__ e;
              None
            end)
          (fndata#get_regvar_type_annotation floc#l#i)
      else
        None in

    let log_dc_error_result (file: string) (line: int) (e: string list) =
      if BCHSystemSettings.system_settings#collect_data then
        log_error_result ~msg:(p2s floc#l#toPretty) file line e
      else
        () in
    let rewrite_expr ?(restrict:int option) (x: xpr_t): xpr_t =
      try
        let xpr = floc#inv#rewrite_expr x in
        let xpr = simplify_xpr xpr in
        let xpr =
          let vars = variables_in_expr xpr in
          let varssize = List.length vars in
          if varssize = 1 then
            let xvar = List.hd vars in
            if floc#env#is_frozen_test_value xvar then
              log_tfold
                (log_error "index_instr" "invalid test address")
              ~ok:(fun (testvar, testiaddr, _) ->
                let testloc = ctxt_string_to_location floc#fa testiaddr in
                let testfloc = get_floc testloc in
                let extxprs = testfloc#inv#get_external_exprs testvar in
                let extxprs =
                  List.map (fun e -> substitute_expr (fun _v -> e) xpr) extxprs in
                (match extxprs with
                 | [] -> xpr
                 | _ -> List.hd extxprs))
              ~error:(fun _ -> xpr)
              (floc#env#get_frozen_variable xvar)
            else
              xpr
          else
            xpr in
        match (restrict, xpr) with
        | (Some 4, XConst (IntConst n)) ->
           if n#geq numerical_e32 then
             XConst (IntConst (n#sub numerical_e32))
           else
             xpr
        | _ ->
           xpr
      with IO.No_more_input ->
            begin
              pr_debug [
                  STR "Error in rewriting expression: ";
                  x2p x;
                  STR ": No more input";
                  NL];
              raise IO.No_more_input
            end in
    let rewrite_floc_expr (floc: floc_int) (x:xpr_t) =
      (* use floc from different location *)
      let xpr = floc#inv#rewrite_expr x in
      simplify_xpr xpr in
    let rewrite_test_expr (csetter: ctxt_iaddress_t) (x: xpr_t) =
      let testloc = ctxt_string_to_location floc#fa csetter in
      let testfloc = get_floc testloc in
      let xpr = testfloc#inv#rewrite_expr x in
      let xpr =
        let vars = variables_in_expr xpr in
        let varssize = List.length vars in
        if varssize = 1 then
          let xvar = List.hd vars in
          if floc#env#is_frozen_test_value xvar then
            log_tfold
              (log_error "rewrite_test_expr" "invalid test address")
              ~ok:(fun (testvar, testiaddr, _) ->
                let testloc = ctxt_string_to_location floc#fa testiaddr in
                let testfloc = get_floc testloc in
                let extxprs = testfloc#inv#get_external_exprs testvar in
                let extxprs =
                  List.map (fun e -> substitute_expr (fun _v -> e) xpr) extxprs in
                (match extxprs with
                 | [] -> xpr
                 | _ -> List.hd extxprs))
              ~error:(fun _ -> xpr)
              (floc#env#get_frozen_variable xvar)
          else
            xpr
        else
          xpr in
      simplify_xpr xpr in
    let add_instr_condition
          (tags: string list)
          (args: int list)
          (x: xpr_t): (string list) * (int list) =
      let _ =
        if (List.length tags) = 0 then
          raise
            (BCH_failure
               (LBLOCK [STR "Empty tag list in add_instr_condition"])) in
      let argslen = List.length args in
      let xtag = (List.hd tags) ^ "xx" in
      let ictag = "ic:" ^ (string_of_int argslen) in
      let icrtag = "icr:" ^ (string_of_int (argslen + 1)) in
      let tags = xtag :: ((List.tl tags) @ [ictag; icrtag]) in
      let xneg = XOp (XLNot, [x]) in
      let xneg = simplify_xpr xneg in
      let args = args @ [xd#index_xpr x; xd#index_xpr xneg] in
      (tags, args) in

    let flagrdefs: int list =
      let flags_used = get_arm_flags_used instr#get_opcode in
      List.concat
        (List.map (fun f ->
          let flagvar = floc#f#env#mk_flag_variable (ARMCCFlag f) in
          let symflagvar = floc#f#env#mk_symbolic_variable flagvar in
          let varinvs = varinv#get_var_flag_reaching_defs symflagvar in
          List.map (fun vinv -> vinv#index) varinvs) flags_used) in

    let get_rdef (xpr: xpr_t): int =
      match xpr with
      | XVar v
        | XOp (XXlsh, [XVar v])
        | XOp (XXlsb, [XVar v])
        | XOp (XXbyte, [_; XVar v])
        | XOp (XLsr, [XVar v; _])
        | XOp (XLsl, [XVar v; _]) ->
         let symvar = floc#f#env#mk_symbolic_variable v in
         let varinvs = varinv#get_var_reaching_defs symvar in
         (match varinvs with
          | [vinv] ->
             let _ =
               if vinv#has_multiple_reaching_defs then
                 let rdefs = vinv#get_reaching_defs in
                 chlog#add
                   "multiple reaching definitions"
                   (LBLOCK [
                        floc#l#toPretty;
                        STR " ";
                        v#toPretty;
                        STR ": ";
                        pretty_print_list
                          rdefs (fun d -> d#toPretty) "[" ", " "]"]) in
             vinv#index
          | _ -> -1)
      | XOp (_, [XVar v; c]) when is_intconst c ->
         let symvar = floc#f#env#mk_symbolic_variable v in
         let varinvs = varinv#get_var_reaching_defs symvar in
         (match varinvs with
          | [vinv] -> vinv#index
          | _ -> -1)
      | _ -> -1 in

    let get_rdef_r (x_r: xpr_t traceresult): int =
      TR.tfold_default get_rdef (-1) x_r in

    let get_all_rdefs (xpr: xpr_t): int list =
      let vars = floc#env#variables_in_expr xpr in
      List.fold_left (fun acc v ->
          let symvar = floc#env#mk_symbolic_variable v in
          let varinvs = varinv#get_var_reaching_defs symvar in
          let newixs =
            List.fold_left (fun newacc vinv ->
                let vix = vinv#index in
                if List.mem vix acc then
                  newacc
                else
                  vix :: newacc) [] varinvs in
          newixs @ acc) [] vars in

    let get_all_rdefs_r (x_r: xpr_t traceresult): int list =
      TR.tfold_default get_all_rdefs [] x_r in

    let get_rdef_memvar (v: variable_t): int =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = varinv#get_var_reaching_defs symvar in
      match varinvs with
      | [vinv] -> vinv#index
      | _ -> -1 in

    let get_rdef_memvar_r (v_r: variable_t traceresult): int =
      TR.tfold_default get_rdef_memvar (-1) v_r in

    let get_def_use (v: variable_t): int =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = varinv#get_var_def_uses symvar in
      match varinvs with
      | [vinv] -> vinv#index
      | _ -> -1 in

    let get_def_use_r (v_r: variable_t traceresult): int =
      TR.tfold_default get_def_use (-1) v_r in

    let get_def_use_high (v: variable_t): int =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = varinv#get_var_def_uses_high symvar in
      match varinvs with
      | [vinv] -> vinv#index
      | _ -> -1 in

    let get_def_use_high_r (v_r: variable_t traceresult): int =
      TR.tfold_default get_def_use_high (-1) v_r in

    let index_variable (v_r: variable_t traceresult): int =
      TR.tfold
        ~ok:xd#index_variable
        ~error:(fun e ->
          begin log_dc_error_result __FILE__ __LINE__ e; -2 end)
        v_r in

    let index_xpr (x_r: xpr_t traceresult): int =
      TR.tfold
        ~ok:xd#index_xpr
        ~error:(fun e ->
          begin log_dc_error_result __FILE__ __LINE__ e; -2 end)
        x_r in

    let add_base_update
          (tags: string list)
          (args: int list)
          (v: variable_t traceresult)
          (inc: int)
          (x: xpr_t traceresult): (string list) * (int list) =
      let _ =
        if (List.length tags) = 0 then
          raise
            (BCH_failure
               (LBLOCK [
                    STR __FILE__; STR ":"; INT __LINE__; STR ": ";
                    STR "Empty tag list"])) in
      let xtag = (List.hd tags) ^ "vtlxdh" in
      let uses = [get_def_use_r v] in
      let useshigh = [get_def_use_high_r v] in
      let argslen = List.length args in
      let vbutag = "vbu:" ^ (string_of_int argslen) in
      let xbutag = "xbu:" ^ (string_of_int (argslen + 3)) in
      let tags = xtag :: ((List.tl tags) @ [vbutag; xbutag]) in
      let args =
        args
        @ [index_variable v;
           bcd#index_typ t_unknown;
           inc;
           index_xpr x]
        @ uses @ useshigh in
      (tags, args) in

    let add_return_value
          (tags: string list)
          (args: int list)
          (rv: xpr_t traceresult)
          (rrv: xpr_t traceresult): (string list) * (int list) =
      let _ =
        if (List.length tags) = 0 then
          raise
            (BCH_failure
               (LBLOCK [
                    STR __FILE__; STR ":"; INT __LINE__; STR ": ";
                    STR "Empty tag list"])) in
      let rdefs = [get_rdef_r rv] @ (get_all_rdefs_r rrv) in
      let xtag = (List.hd tags) ^ "xx" ^ (string_repeat "r" (List.length rdefs)) in
      let argslen = List.length args in
      let returntag = "return:" ^ (string_of_int argslen) in
      let tags = xtag :: ((List.tl tags) @ [returntag]) in
      let args = args @ [index_xpr rv; index_xpr rrv] @ rdefs in
      (tags, args)in

    let mk_instrx_data
          ?(vars: variable_t list = [])
          ?(types: btype_t list = [])
          ?(xprs: xpr_t list = [])
          ?(rdefs: int list = [])
          ?(uses: int list = [])
          ?(useshigh: int list = [])
          ?(integers: int list = [])
          () =
      (*
      let _ =
        if testsupport#requested_instrx_data then
          testsupport#submit_instrx_data instr#get_address vars xprs in
       *)
      let varcount = List.length vars in
      let xprcount = List.length xprs in
      let rdefcount = List.length rdefs in
      let defusecount = List.length uses in
      let defusehighcount = List.length useshigh in
      let flagrdefcount = List.length flagrdefs in
      let integercount = List.length integers in
      let varstring = string_repeat "v" varcount in
      let typestring = string_repeat "t" varcount in
      let xprstring = string_repeat "x" xprcount in
      let rdefstring = string_repeat "r" rdefcount in
      let defusestring = string_repeat "d" defusecount in
      let defusehighstring = string_repeat "h" defusehighcount in
      let flagrdefstring = string_repeat "f" flagrdefcount in
      let integerstring = string_repeat "l" integercount in
      let tagstring =
        "a:"
        ^ varstring
        ^ typestring
        ^ xprstring
        ^ rdefstring
        ^ defusestring
        ^ defusehighstring
        ^ flagrdefstring
        ^ integerstring in
      let varargs = List.map xd#index_variable vars in
      let xprargs = List.map xd#index_xpr xprs in
      let typeargs =
        let types =
          if (List.length types) < varcount then
            List.map (fun _ -> t_unknown) vars
          else
            types in
        List.map bcd#index_typ types in
      (tagstring,
       varargs
       @ typeargs
       @ xprargs
       @ rdefs
       @ uses
       @ useshigh
       @ flagrdefs
       @ integers) in

    let mk_instrx_data_r
          ?(vars_r: variable_t traceresult list = [])
          ?(cvars_r: variable_t traceresult list = [])
          ?(types: btype_t list = [])
          ?(xprs_r: xpr_t traceresult list = [])
          ?(cxprs_r: xpr_t traceresult list = [])
          ?(rdefs: int list = [])
          ?(uses: int list = [])
          ?(useshigh: int list = [])
          ?(integers: int list = [])
          () =
      let _ =
        if testsupport#requested_instrx_data then
          testsupport#submit_instrx_data instr#get_address vars_r xprs_r in
      let varcount = List.length vars_r in
      let cvarcount = List.length cvars_r in
      let xprcount = List.length xprs_r in
      let cxprcount = List.length cxprs_r in
      let rdefcount = List.length rdefs in
      let defusecount = List.length uses in
      let defusehighcount = List.length useshigh in
      let flagrdefcount = List.length flagrdefs in
      let integercount = List.length integers in
      let varstring = string_repeat "v" varcount in
      let cvarstring = string_repeat "w" cvarcount in
      let typestring = string_repeat "t" varcount in
      let xprstring = string_repeat "x" xprcount in
      let cxprstring = string_repeat "c" cxprcount in
      let rdefstring = string_repeat "r" rdefcount in
      let defusestring = string_repeat "d" defusecount in
      let defusehighstring = string_repeat "h" defusehighcount in
      let flagrdefstring = string_repeat "f" flagrdefcount in
      let integerstring = string_repeat "l" integercount in
      let tagstring =
        "ar:"
        ^ varstring
        ^ cvarstring
        ^ typestring
        ^ xprstring
        ^ cxprstring
        ^ rdefstring
        ^ defusestring
        ^ defusehighstring
        ^ flagrdefstring
        ^ integerstring in
      let varargs = List.map index_variable vars_r in
      let cvarargs = List.map index_variable cvars_r in
      let xprargs = List.map index_xpr xprs_r in
      let cxprargs = List.map index_xpr cxprs_r in
      let typeargs =
        let types =
          if (List.length types) < varcount then
            List.map (fun _ -> t_unknown) vars_r
          else
            types in
        List.map bcd#index_typ types in
      (tagstring,
       varargs
       @ cvarargs
       @ typeargs
       @ xprargs
       @ cxprargs
       @ rdefs
       @ uses
       @ useshigh
       @ flagrdefs
       @ integers) in

    let add_optional_instr_condition
          (tagstring: string)
          (args: int list)
          (c: arm_opcode_cc_t): (string list * int list) =
      match c with
      | ACCAlways -> ([tagstring], args)
      | _ when instr#is_condition_covered -> ([tagstring], args)
      | c when is_cond_conditional c && floc#has_test_expr ->
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter floc#get_test_expr in
         add_instr_condition [tagstring] args tcond
      | _ -> (tagstring :: ["uc"], args) in

    let add_optional_subsumption (tags: string list): string list =
      match instr#is_in_aggregate with
      | Some va -> tags @ ["subsumed"; va#to_hex_string]
      | _ -> tags in

    let add_subsumption_dependents
          (agg: arm_instruction_aggregate_int) (tags: string list) =
      let iaddr = instr#get_address in
      let deps =
        List.fold_left (fun acc agginstr ->
            if iaddr#equal agginstr#get_address then
              acc
            else
              agginstr#get_address#to_hex_string :: acc) [] agg#instrs in
      tags @ ("subsumes" :: deps) in

    let add_bx_call_defs_r
          ?(xprs_r: xpr_t traceresult list = [])
          ?(rdefs: int list = [])
          (tags: string list)
          (args: int list): (string list * int list) =
      let tagstring = List.hd tags in
      let xprcount = List.length xprs_r in
      let rdefcount = List.length rdefs in
      let tagstring = tagstring ^ (string_repeat "x" xprcount) in
      let tagstring = tagstring ^ (string_repeat "r" rdefcount) in
      (* move the call target index (into the interface dictionary) to the
         end of args list, so it is not interpreted as an expression *)
      let args_calltgt_ix = List.hd (List.rev args) in
      let args_proper = List.rev (List.tl (List.rev args)) in
      let args = args_proper @ (List.map index_xpr xprs_r) @ rdefs in
      let args = args @ [args_calltgt_ix] in
      let tags = (tagstring :: (List.tl tags)) @ ["bx-call"] in
      (tags, args) in

    let register_function_prototype (name: string) =
      if function_summary_library#has_so_function name then
        let fs = function_summary_library#get_so_function name in
        match fs#get_function_interface.fintf_bctype with
        | Some fty -> bcfiles#add_fundef name fty
        | _ ->
           chlog#add
             "function prototype registration"
             (LBLOCK [
                  STR "Function summary for ";
                  STR name;
                  STR " does not have a type"])
      else
        chlog#add
          "function prototype registration"
          (LBLOCK [STR "No function summary found for "; STR name]) in

    let check_for_functionptr_args callargs =
      List.iter (fun (p, x) ->
          let ptype = get_parameter_type p in
          if is_function_type ptype then
            match x with
            | XConst (IntConst n) ->
               (match numerical_to_doubleword n with
                | Error _ -> ()
                | Ok dw ->
                   if elf_header#is_code_address dw then
                     begin
                       ignore (functions_data#add_function dw);
                       chlog#add
                         "add function entry point"
                         (LBLOCK [
                              floc#l#toPretty;
                              STR ": function addr: ";
                              dw#toPretty])
                     end)
            | _ -> ()
          else
            ()) callargs in

    let callinstr_key (): (string list * int list) =
      let callargs = floc#get_call_arguments in
      let _ = check_for_functionptr_args callargs in
      let (xprs, xvars, rdefs, _) =
        List.fold_left (fun (xprs, xvars, rdefs, index) (p, x) ->
            let xvar_r =
              if is_register_parameter p then
                let regarg = TR.tget_ok (get_register_parameter_register p) in
                let pvar = floc#f#env#mk_register_variable regarg in
                Ok (XVar pvar)
              else if is_stack_parameter p then
                let p_offset_r = get_stack_parameter_offset p in
                let sp_r = (sp_r RD)#to_expr floc in
                TR.tmap2 (fun p_offset sp ->
                    XOp (XPlus, [sp; int_constant_expr p_offset]))
                  p_offset_r sp_r
              else
                Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                       ^ "Parameter type not recognized in call instruction"] in
            let xx = rewrite_expr ?restrict:(Some 4) x in
            let ptype = get_parameter_type p in
            let xx =
              if is_pointer ptype then
                let _ = floc#memrecorder#record_argument xx index in
                match get_string_reference floc xx with
                | Some _ -> xx
                | _ ->
                   match xx with
                   | XVar _ -> xx
                   | _ ->
                      TR.tfold_default
                        (fun v -> XOp ((Xf "addressofvar"), [(XVar v)]))
                        xx
                        (floc#get_var_at_address ~btype:(ptr_deref ptype) xx)
              else
                xx in
            let xx = TR.tvalue (floc#convert_xpr_offsets xx) ~default:xx in
            let rdef = get_rdef_r xvar_r in
            (xx :: xprs, xvar_r :: xvars, rdef :: rdefs, index + 1))
          ([], [], [], 1) callargs in
      let (vrd, rtype) =
        let fintf = floc#get_call_target#get_function_interface in
        let rtype = get_fts_returntype fintf in
        let rtype = if is_void_pointer rtype then t_ptrto t_uchar else rtype in
        let reg =
          if is_float rtype then
            let regtype =
              if is_float_float rtype then
                XSingle
              else if is_float_double rtype then
                XDouble
              else
                XQuad in
            register_of_arm_extension_register
              ({armxr_type = regtype; armxr_index = 0})
          else
            register_of_arm_register AR0 in
        (floc#f#env#mk_register_variable reg, rtype) in
      let xrdefs =
        List.fold_left (fun acc x ->
            let rdefs = get_all_rdefs x in
            let newixs = List.filter (fun ix -> not (List.mem ix acc)) rdefs in
            acc @ newixs) [] xprs in
      let (tagstring, args) =
        mk_instrx_data_r
          ~vars_r:[Ok vrd]
          ~types:[rtype]
          ~xprs_r:((List.rev (List.map (fun x -> Ok x) xprs)) @ (List.rev xvars))
          ~rdefs:((List.rev rdefs) @ xrdefs)
          ~uses:[get_def_use vrd]
          ~useshigh:[get_def_use_high vrd]
          () in
      let tags =
        if instr#is_inlined_call then
          tagstring :: ["call"; "inlined"]
        else
          tagstring
          :: ["call"; "argcount:" ^ (string_of_int (List.length callargs))] in
      let args =
        args @ [ixd#index_call_target floc#get_call_target#get_target] in
      (tags, args) in

    let key =
      match instr#get_opcode with
      | Add _ when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_jumptable then
           let jt = agg#jumptable in
           let indexregop = jt#index_operand in
           let xrn_r = indexregop#to_expr floc in
           let xxrn_r = TR.tmap rewrite_expr xrn_r in
           let rdefs = (get_rdef_r xrn_r) :: (get_all_rdefs_r xxrn_r) in
           let (tagstring, args) =
             mk_instrx_data_r
               ~xprs_r:[xrn_r; xxrn_r]
               ~rdefs:rdefs
               () in
           let tags = tagstring :: ["agg-jt"] in
           let tags = add_subsumption_dependents agg tags in
           (tags, args)
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Aggregate for Add not recognized at "; iaddr#toPretty]))

      | Add (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XPlus, [xrn; xrm])) xrn_r xrm_r in
         let xxrn_r = TR.tmap rewrite_expr xrn_r in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rresult_r = TR.tmap (rewrite_expr ?restrict:(Some 4)) result_r in
         let _ =
           TR.tfold_default
             (fun r -> ignore (get_string_reference floc r)) () rresult_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = get_def_use_r vrd_r in
         let useshigh = get_def_use_high_r vrd_r in
         let vrtype =
           match get_regvar_type_annotation () with
           | Some t -> t
           | _ -> t_unknown in
         (*
         let rresult_r =
           TR.tmap
             (fun rresult ->
               TR.tfold_default
                 (fun v -> XOp ((Xf "addressofvar"), [(XVar v)]))
                 rresult
                 (floc#get_var_at_address rresult))
             rresult_r in
          *)
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~types:[vrtype]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r; xxrn_r; xxrm_r]
             ~rdefs:rdefs
             ~uses:[uses]
             ~useshigh:[useshigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | AddCarry (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XPlus, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let _ =
           TR.tfold_default
             (fun r -> ignore (get_string_reference floc r)) () rresult_r in
         let rdefs = [get_rdef_r xrn_r; get_rdef_r xrm_r] in
         let uses = get_def_use_r vrd_r in
         let useshigh = get_def_use_high_r vrd_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs:rdefs
             ~uses:[uses]
             ~useshigh:[useshigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Adr (c, rd, imm) ->
         let vrd_r = rd#to_variable floc in
         let ximm_r = imm#to_expr floc in
         let _ =
           TR.tfold_default
             (fun x -> ignore (get_string_reference floc x)) () ximm_r in
         let uses = get_def_use_r vrd_r in
         let useshigh = get_def_use_high_r vrd_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[ximm_r]
             ~uses:[uses]
             ~useshigh:[useshigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | ArithmeticShiftRight (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2
             (fun xrn xrm ->
               match xrm with
               | XConst (IntConst n) when n#toInt = 2 ->
                  XOp (XDiv, [xrn; XConst (IntConst (mkNumerical 4))])
               | _ -> XOp (XAsr, [xrn; xrm]))
             xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | BitFieldClear (c, rd, _, _, _) ->
         let vrd_r = rd#to_variable floc in
         let xrd_r = rd#to_expr floc in
         let rdefs = [get_rdef_r xrd_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrd_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitFieldInsert (c, rd, rn, _, _, _) ->
         let vrd_r = rd#to_variable floc in
         let xrd_r = rd#to_expr floc in
         let xrn_r = rn#to_expr floc in
         let rdefs = [get_rdef_r xrd_r; get_rdef_r xrn_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrd_r; xrn_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseAnd (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XBAnd, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseBitClear (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2
             (fun xrn xrm -> XOp (XBAnd, [xrn; XOp (XBNot, [xrm])]))
             xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseExclusiveOr (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XBXor, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseNot (_, c, rd, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let result_r = TR.tmap (fun xrm -> XOp (XBNot, [xrm])) xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs = [get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseOr (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XBOr, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let _ =
           TR.tfold_default
             (fun r -> ignore (get_string_reference floc r)) () rresult_r  in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseOrNot (_, c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xrmn_r = TR.tmap (fun xrm -> XOp (XBNot, [xrm])) xrm_r in
         let result_r =
           TR.tmap2
             (fun xrn xrmn -> XOp (XBOr, [xrn; xrmn])) xrn_r xrmn_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; xrmn_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BranchExchange (_, tgt) when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_jumptable then
           let jt = agg#jumptable in
           let indexregop = jt#index_operand in
           let xrn_r = indexregop#to_expr floc in
           let xxrn_r = TR.tmap rewrite_expr xrn_r in
           let rdefs = (get_rdef_r xrn_r) :: (get_all_rdefs_r xxrn_r) in
           let (tagstring, args) =
             mk_instrx_data_r
               ~xprs_r:[xrn_r; xxrn_r]
               ~rdefs
               () in
           let tags = tagstring :: ["agg-jt"] in
           let tags = add_subsumption_dependents agg tags in
           (tags, args)
         else if agg#is_bx_call then
           let (tags, args) = callinstr_key() in
           let xtgt_r = tgt#to_expr floc in
           let xxtgt_r = TR.tmap rewrite_expr xtgt_r in
           let rdefs = (get_rdef_r xtgt_r) :: (get_all_rdefs_r xxtgt_r) in
           let (tags, args) =
             add_bx_call_defs_r ~xprs_r:[xtgt_r; xxtgt_r] ~rdefs tags args in
           let tags = add_subsumption_dependents agg tags in
           (tags, args)
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Aggregate for BranchExchange not recognized at ";
                     iaddr#toPretty]))

      | Branch _
        | BranchExchange _ when floc#has_call_target ->
         callinstr_key ()

      | Branch _ when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_jumptable then
           let jt = agg#jumptable in
           let indexregop = jt#index_operand in
           let xrn_r = indexregop#to_expr floc in
           let xxrn_r = TR.tmap rewrite_expr xrn_r in
           let rdefs = (get_rdef_r xrn_r) :: (get_all_rdefs_r xxrn_r) in
           let (tagstring, args) =
             mk_instrx_data_r
               ~xprs_r:[xrn_r; xxrn_r]
               ~rdefs
               () in
           let tags = tagstring :: ["agg-jt"] in
           let tags = add_subsumption_dependents agg tags in
           (tags, args)
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Aggregate branch not recognized at "; iaddr#toPretty]))

      | Branch (c, tgt, _)
           when is_cond_conditional c
                && tgt#is_absolute_address
                && floc#has_test_expr ->
         let xtgt_r = tgt#to_expr floc in
         let txpr = floc#get_test_expr in
         let fxpr = simplify_xpr (XOp (XLNot, [txpr])) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
         let tcond_r = floc#convert_xpr_offsets ~size:(Some 4) tcond in
         let fcond_r = floc#convert_xpr_offsets ~size:(Some 4) fcond in
         let bytestr =
           try
             let instr =
               fail_tvalue
                 (trerror_record
                    (LBLOCK [STR "Internal error in FnARMDictionary:Branch"]))
                 (get_arm_assembly_instruction
                    (fail_tvalue
                       (trerror_record
                          (LBLOCK [STR "FnARMDictionary:Branch: "; STR csetter]))
                       (string_to_doubleword csetter))) in
             instr#get_bytes_ashexstring
           with
           | _ -> "0x0" in
         let rdefs = (get_all_rdefs txpr) @ (get_all_rdefs tcond) in
         let (tagstring, args) =
           mk_instrx_data_r
             ~xprs_r:[Ok txpr; Ok fxpr; tcond_r; fcond_r; xtgt_r]
             ~rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | Branch (_, tgt, _) ->
         let xtgt_r = tgt#to_expr floc in
         let xxtgt_r = TR.tmap rewrite_expr xtgt_r in
         let rdefs = (get_rdef_r xtgt_r) :: (get_all_rdefs_r xxtgt_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xtgt_r; xxtgt_r] ~rdefs () in
         let tags = add_optional_subsumption [tagstring] in
         (tags, args)

      | BranchExchange (c, tgt)
           when tgt#is_register && tgt#get_register = ARLR ->
         let r0_op = arm_register_op AR0 RD in
         let xr0_r = r0_op#to_expr floc in
         let xxr0_r = TR.tmap rewrite_expr xr0_r in
         let (tagstring, args) = mk_instrx_data_r () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) = add_return_value tags args xr0_r xxr0_r in
         (tags, args)

      | BranchExchange (c, tgt) ->
         let xtgt_r = tgt#to_expr floc in
         let xxtgt_r = TR.tmap rewrite_expr xtgt_r in
         let rdefs = (get_rdef_r xtgt_r) :: (get_all_rdefs_r xxtgt_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xtgt_r; xxtgt_r] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BranchLink _
        | BranchLinkExchange _
           when floc#has_call_target
                && floc#get_call_target#is_signature_valid ->
         callinstr_key ()

      | BranchLink (c, tgt)
        | BranchLinkExchange (c, tgt) ->
         let xtgt_r = tgt#to_expr floc in
         let xxtgt_r = TR.tmap rewrite_expr xtgt_r in
         let args =
           List.map (fun r -> arm_register_op r RD) [AR0; AR1; AR2; AR3] in
         let argxprs_r =
           List.map (fun (a: arm_operand_int) -> a#to_expr floc) args in
         let rdefs = (get_rdef_r xtgt_r) :: (get_all_rdefs_r xxtgt_r)  in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:(xxtgt_r :: argxprs_r) ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | ByteReverseWord(c, rd, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let xrmm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = [get_rdef_r xrm_r] @ (get_all_rdefs_r xrmm_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; xrmm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | ByteReversePackedHalfword (c, rd, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let xrmm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = [get_rdef_r xrm_r] @ (get_all_rdefs_r xrmm_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; xrmm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Compare (c, rn, rm, _) ->
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xresult_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMinus, [xrn; xrm])) xrn_r xrm_r in
         let result_r = TR.tmap rewrite_expr xresult_r in
         let result_r =
           TR.tbind (floc#convert_xpr_offsets ~size:(Some 4)) result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r result_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xrn_r; xrm_r; result_r] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | CompareBranchNonzero (rn, tgt) ->
         let xrn_r = rn#to_expr floc in
         let xtgt_r = tgt#to_expr floc in
         let txpr_r =
           TR.tmap (fun xrn -> XOp (XNe, [xrn; zero_constant_expr])) xrn_r in
         let fxpr_r =
           TR.tmap (fun xrn -> XOp (XEq, [xrn; zero_constant_expr])) xrn_r in
         let tcond_r = TR.tmap rewrite_expr txpr_r in
         let fcond_r = TR.tmap rewrite_expr fxpr_r in
         let rdefs = [get_rdef_r xrn_r] @ (get_all_rdefs_r tcond_r) in
         let (tagstring, args) =
           mk_instrx_data_r
             ~xprs_r:[xrn_r; txpr_r; fxpr_r; tcond_r; fcond_r; xtgt_r]
             ~rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"], args) in
         (tags, args)

      | CompareBranchZero (rn, tgt) ->
         let xrn_r = rn#to_expr floc in
         let xtgt_r = tgt#to_expr floc in
         let txpr_r =
           TR.tmap (fun xrn -> XOp (XEq, [xrn; zero_constant_expr])) xrn_r in
         let fxpr_r =
           TR.tmap (fun xrn -> XOp (XNe, [xrn; zero_constant_expr])) xrn_r in
         let tcond_r = TR.tmap rewrite_expr txpr_r in
         let fcond_r = TR.tmap rewrite_expr fxpr_r in
         let rdefs = [get_rdef_r xrn_r] @ (get_all_rdefs_r tcond_r) in
         let (tagstring, args) =
           mk_instrx_data_r
             ~xprs_r:[xrn_r; txpr_r; fxpr_r; tcond_r; fcond_r; xtgt_r]
             ~rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"], args) in
         (tags, args)

      | CompareNegative (c, rn, rm) ->
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xresult_r =
           TR.tmap2 (fun xrn xrm -> XOp (XPlus, [xrn; xrm])) xrn_r xrm_r in
         let xresult_r = TR.tmap rewrite_expr xresult_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r xresult_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xrn_r; xrm_r; xresult_r] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | CountLeadingZeros (c, rd, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = [get_rdef_r xrm_r] @ (get_all_rdefs_r xxrm_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; xxrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | IfThen _ when instr#is_aggregate_anchor ->
         let finfo = floc#f in
         let ctxtiaddr = floc#l#ci in
         if finfo#has_associated_cc_setter ctxtiaddr then
           let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
           let testloc = ctxt_string_to_location faddr testiaddr in
           let testaddr = testloc#i in
           let testinstr =
             fail_tvalue
               (trerror_record
                  (LBLOCK [STR "FnDictionary:IfThen: "; floc#ia#toPretty]))
               (get_arm_assembly_instruction testaddr) in
           let agg = get_aggregate floc#ia in
           (match agg#it_sequence#kind with
            | ITPredicateAssignment (inverse, dstop) ->
               let (_, optpredicate, _opsused) =
                 arm_conditional_expr
                   ~condopc:instr#get_opcode
                   ~testopc:testinstr#get_opcode
                   ~condloc:floc#l
                   ~testloc:testloc in
               let (tags, args) =
                 (match optpredicate with
                  | Some p ->
                     let p = if inverse then XOp (XLNot, [p]) else p in
                     let lhs_r = dstop#to_variable floc in
                     let rdefs = get_all_rdefs p in
                     let xp = rewrite_expr p in
                     let uses = [get_def_use_r lhs_r] in
                     let useshigh = [get_def_use_high_r lhs_r] in
                     let (tagstring, args) =
                       mk_instrx_data_r
                         ~vars_r:[lhs_r]
                         ~xprs_r:[Ok p; Ok xp]
                         ~rdefs
                         ~uses
                         ~useshigh
                         () in
                     ([tagstring], args)
                  | _ ->
                     ([], [])) in
               let dependents =
                 List.map (fun d ->
                     (make_i_location floc#l d#get_address)#ci) agg#instrs in
               let tags = tags @ ["subsumes"] @ dependents in
               (tags, args))
         else
           ([], [])

      | IfThen _ when instr#is_block_condition && floc#has_test_expr ->
         let txpr = floc#get_test_expr in
         let fxpr = XOp (XLNot, [txpr]) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let testloc = ctxt_string_to_location floc#fa csetter in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
         let instr =
           fail_tvalue
             (trerror_record
                (LBLOCK [STR "Internal error in FnARMDictionary:IfThen"]))
             (get_arm_assembly_instruction testloc#i) in
         let bytestr = instr#get_bytes_ashexstring in
         let rdefs = get_all_rdefs tcond in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond]
             ~rdefs:rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         (tags, args)

      | IfThen _  -> ([], [])

      | LoadMultipleDecrementAfter (wback, c, base, rl, _) ->
         let reglhs_rl = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let (memreads_r, _) =
           List.fold_left
               (fun (acc, off) _reglhs ->
                 let memop = arm_reg_deref ~with_offset:off basereg RD in
                 let memrhs_r = memop#to_expr floc in
                 (acc @ [memrhs_r], off + 4)) ([], 4 -(4 * regcount)) reglhs_rl in
         let rdefs = List.map get_rdef_r (baserhs_r :: memreads_r) in
         let uses = List.map get_def_use_high_r (baselhs_r :: reglhs_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: reglhs_rl) in
         let wbackresults_r =
           if wback then
             let decrem = int_constant_expr (4 * regcount) in
             let baseresult_r =
               TR.tmap
                 (fun baserhs -> XOp (XMinus, [baserhs; decrem])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             [baseresult_r; rbaseresult_r]
           else
             [baserhs_r; baserhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: reglhs_rl)
             ~xprs_r:((baserhs_r :: wbackresults_r) @ memreads_r)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | LoadMultipleDecrementBefore (wback, c, base, rl, _) ->
         let reglhs_rl = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let (memreads_r, _) =
           List.fold_left
             (fun (acc, off) _reglhs ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs_r = memop#to_expr floc in
               (acc @ [memrhs_r], off + 4)) ([], -(4 * regcount)) reglhs_rl in
         let rdefs = List.map get_rdef_r (baserhs_r :: memreads_r) in
         let uses = List.map get_def_use_high_r (baselhs_r :: reglhs_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: reglhs_rl) in
         let wbackresults_r =
           if wback then
             let decrem = int_constant_expr (4 * regcount) in
             let baseresult_r =
               TR.tmap
                 (fun baserhs -> XOp (XMinus, [baserhs; decrem])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             [baseresult_r; rbaseresult_r]
           else
             [baserhs_r; baserhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: reglhs_rl)
             ~xprs_r:((baserhs_r :: wbackresults_r) @ memreads_r)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | LoadMultipleIncrementAfter (wback, c, base, rl, _) ->
         let lhsvars_rl = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let (rhsexprs_r, _) =
           List.fold_left
             (fun (acc, off) _lhsvar ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs_r = memop#to_expr floc in
               (acc @ [memrhs_r], off + 4)) ([], 0) lhsvars_rl in
         let xaddrs_r =
           List.init
             rl#get_register_count
             (fun i ->
               let xaddr_r =
                 TR.tmap
                   (fun baserhs -> XOp (XPlus, [baserhs; int_constant_expr (i + 4)]))
                   baserhs_r in
               TR.tmap rewrite_expr xaddr_r) in
         let rdefs = List.map get_rdef_r (baserhs_r :: rhsexprs_r) in
         let uses = List.map get_def_use_high_r (baselhs_r :: lhsvars_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: lhsvars_rl) in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: lhsvars_rl)
             ~xprs_r:(baserhs_r :: (rhsexprs_r @ xaddrs_r))
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         let (tags, args) =
           if wback then
             let inc = 4 * regcount in
             let xinc = int_constant_expr inc in
             let baseresult_r =
               TR.tmap (fun baserhs -> XOp (XPlus, [baserhs; xinc])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             add_base_update tags args baselhs_r inc rbaseresult_r
           else
             (tags, args) in
         (tags, args)

      | LoadMultipleIncrementBefore (wback, c, base, rl, _) ->
         let reglhs_rl = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let (memreads_r, _) =
           List.fold_left
             (fun (acc, off) _reglhs ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs_r = memop#to_expr floc in
               (acc @ [memrhs_r], off + 4)) ([], 4) reglhs_rl in
         let rdefs = List.map get_rdef_r (baserhs_r :: memreads_r) in
         let uses = List.map get_def_use_high_r (baselhs_r :: reglhs_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: reglhs_rl) in
         let wbackresults_r =
           if wback then
             let increm = int_constant_expr (4 * regcount) in
             let baseresult_r =
               TR.tmap
                 (fun baserhs -> XOp (XPlus, [baserhs; increm])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             [baseresult_r; rbaseresult_r]
           else
             [baserhs_r; baserhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: reglhs_rl)
             ~xprs_r:((baserhs_r :: wbackresults_r) @ memreads_r)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | LoadRegister _ when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_jumptable then
           let jt = agg#jumptable in
           let indexregop = jt#index_operand in
           let xrn_r = indexregop#to_expr floc in
           let xxrn_r = TR.tmap rewrite_expr xrn_r in
           let rdefs = (get_rdef_r xrn_r) :: (get_all_rdefs_r xxrn_r) in
           let (tagstring, args) =
             mk_instrx_data_r ~xprs_r:[xrn_r; xxrn_r] ~rdefs () in
           let tags = tagstring :: ["agg-jt"] in
           let tags = add_subsumption_dependents agg tags in
           (tags, args)
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Aggregate loadregister not recognized: ";
                     iaddr#toPretty]))

      | LoadRegister (c, rt, rn, rm, mem, _) ->
         let vrt_r = rt#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xaddr_r = mem#to_address floc in
         let vmem_r = mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_memvar_r vmem_r]
           @ (get_all_rdefs_r xmem_r) in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let xrmem_r =
           TR.tbind (floc#convert_xpr_offsets ~size:(Some 4)) xrmem_r in
         let _ =
           TR.tfold_default
             (fun xrmem -> ignore (get_string_reference floc xrmem)) () xrmem_r in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:false
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:4
             ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrm_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterByte (c, rt, rn, rm, mem, _) ->
         let vrt_r = rt#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xaddr_r = mem#to_address floc in
         let vmem_r = mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_memvar_r vmem_r]
           @ (get_all_rdefs_r xmem_r) in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:false
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:1
             ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrm_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         let tags =
           match instr#is_in_aggregate with
           | Some dw when (get_aggregate dw)#is_pseudo_ldrsb ->
              add_subsumption_dependents (get_aggregate dw) tags
           | _ -> tags in
         (tags, args)

      | LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
         let vrt_r = rt#to_variable floc in
         let vrt2_r = rt2#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let vmem_r = mem#to_variable floc in
         let vmem2_r = mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let xmem2_r = mem2#to_expr floc in
         let xrmem2_r = TR.tmap rewrite_expr xmem2_r in
         let xaddr1_r = mem#to_address floc in
         let xaddr2_r = mem#to_address floc in
         let rdefs = [
             get_rdef_r xrn_r;
             get_rdef_r xrm_r;
             get_rdef_memvar_r vmem_r;
             get_rdef_memvar_r vmem2_r] in
         let uses = [get_def_use_r vrt_r; get_def_use_r vrt2_r] in
         let useshigh = [get_def_use_high_r vrt_r; get_def_use_high_r vrt2_r] in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:false
             ~addr_r:xaddr1_r
             ~var_r:vmem_r
             ~size:4
             ~vtype:t_unknown in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:false
             ~addr_r:xaddr2_r
             ~var_r:vmem2_r
             ~size:4
             ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vrt2_r; vmem_r; vmem2_r]
             ~xprs_r:[xrn_r; xrm_r; xmem_r; xrmem_r; xmem2_r;
                      xrmem2_r; xaddr1_r; xaddr2_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterExclusive (c, rt, rn, rm, mem) ->
         let vrt_r = rt#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xaddr_r = mem#to_address floc in
         let vmem_r = mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_memvar_r vmem_r]
           @ (get_all_rdefs_r xmem_r) in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let _ =
           TR.tfold_default
             (fun xrmem -> ignore (get_string_reference floc xrmem)) () xrmem_r in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:false
             ~addr_r:xaddr_r
             ~var_r:vmem_r
             ~size:4
             ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrm_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterHalfword (c, rt, rn, rm, mem, _) ->
         let vrt_r = rt#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xaddr_r = mem#to_address floc in
         let vmem_r = mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let xrmem_r = TR.tbind floc#convert_xpr_offsets xrmem_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_memvar_r vmem_r]
           @ (get_all_rdefs_r xmem_r) in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:false
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:2
             ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrm_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         let tags =
           match instr#is_in_aggregate with
           | Some dw when (get_aggregate dw)#is_pseudo_ldrsh ->
              add_subsumption_dependents (get_aggregate dw) tags
           | _ -> tags in
         (tags, args)

      | LoadRegisterSignedByte (c, rt, rn, rm, mem, _) ->
         let vrt_r = rt#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xaddr_r = mem#to_address floc in
         let vmem_r= mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_memvar_r vmem_r]
           @ (get_all_rdefs_r xmem_r) in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:true
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:1
             ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrm_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterSignedHalfword (c, rt, rn, rm, mem, _) ->
         let vrt_r = rt#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xaddr_r = mem#to_address floc in
         let vmem_r = mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_memvar_r vmem_r] in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let _ =
           floc#memrecorder#record_load_r
             ~signed:true
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:2
             ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrm_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | LogicalShiftLeft (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XLsl, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | LogicalShiftRight (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XLsr, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Move _ when instr#is_aggregate_anchor ->
         let finfo = floc#f in
         let ctxtiaddr = floc#l#ci in
         if finfo#has_associated_cc_setter ctxtiaddr then
           let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
           let testloc = ctxt_string_to_location faddr testiaddr in
           let testaddr = testloc#i in
           let testinstr =
             fail_tvalue
               (trerror_record
                  (LBLOCK [
                       STR "FnDictionary: predicate assignment"; floc#ia#toPretty]))
               (get_arm_assembly_instruction testaddr) in
           let agg = get_aggregate floc#ia in
           (match agg#kind with
            | ARMPredicateAssignment (inverse, dstop) ->
               let (_, optpredicate, _) =
                 arm_conditional_expr
                   ~condopc:instr#get_opcode
                   ~testopc:testinstr#get_opcode
                   ~condloc:floc#l
                   ~testloc:testloc in
               let (tags, args) =
                 (match optpredicate with
                  | Some p ->
                     let p = if inverse then XOp (XLNot, [p]) else p in
                     let lhs_r = dstop#to_variable floc in
                     let rdefs = get_all_rdefs p in
                     let xp = rewrite_expr p in
                     let (tagstring, args) =
                       mk_instrx_data_r
                         ~vars_r:[lhs_r]
                         ~xprs_r:[Ok p; Ok xp]
                         ~rdefs
                         ~uses:[get_def_use_r lhs_r]
                         ~useshigh:[get_def_use_high_r lhs_r]
                         () in
                     ([tagstring], args)
                  | _ ->
                     ([], [])) in
               let dependents =
                 List.map (fun d ->
                     (make_i_location floc#l d#get_address)#ci) agg#instrs in
               let tags = tags @ ["subsumes"] @ dependents in
               (tags, args)
            | _ ->
               ([], []))
         else
           ([], [])

      | Move _ when (Option.is_some instr#is_in_aggregate) ->
         (match instr#is_in_aggregate with
          | Some va ->
             let ctxtva = (make_i_location floc#l va)#ci in
             ("a:" :: ["subsumed"; ctxtva], [])
          | _ -> (["a:"], []))

      | Move (_, _, rd, rm, _, _)
           when rm#is_register && rd#get_register = rm#get_register ->
         (["nop"], [])

      | Move (_, c, rd, rm, _, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let result_r = TR.tmap (rewrite_expr ?restrict:(Some 4)) xrm_r in
         let rdefs = (get_rdef_r xrm_r) :: (get_all_rdefs_r result_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let _ =
           TR.tfold_default
             (fun result -> ignore (get_string_reference floc result))
             () result_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; result_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MoveRegisterCoprocessor (c, _, _, rt, _, _, _) ->
         let vrt_r = rt#to_variable floc in
         let (tagstring, args) = mk_instrx_data_r ~vars_r:[vrt_r] () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MoveToCoprocessor (c, _, _, rt, _, _, _) ->
         let xrt_r = rt#to_expr floc in
         let xxrt_r = TR.tmap rewrite_expr xrt_r in
         let (tagstring, args) = mk_instrx_data_r ~xprs_r:[xrt_r; xxrt_r] () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MoveTop (c, rd, imm) ->
         let vrd_r = rd#to_variable floc in
         let ximm_r = imm#to_expr floc in
         let xrd_r = rd#to_expr floc in
         let ximm16_r =
           TR.tmap (fun ximm -> XOp (XMult, [ximm; e16_c])) ximm_r in
         let xrdm16_r = TR.tmap (fun xrd -> XOp (XXlsh, [xrd])) xrd_r in
         let result_r =
           TR.tmap2
             (fun xrdm16 ximm16 -> XOp (XPlus, [xrdm16; ximm16]))
             xrdm16_r ximm16_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let _ =
           TR.tfold_default
             (fun r -> ignore (get_string_reference floc r)) () rresult_r in
         let rdefs = [get_rdef_r xrd_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[ximm_r; xrd_r; xrdm16_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MoveTwoRegisterCoprocessor (c, _, _, rt, rt2, _) ->
         let vrt1_r = rt#to_variable floc in
         let vrt2_r = rt2#to_variable floc in
         let (tagstring, args) = mk_instrx_data_r ~vars_r:[vrt1_r; vrt2_r] () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Multiply(_, c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MultiplyAccumulate (_, c, rd, rn, rm, ra) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xra_r = ra#to_expr floc in
         let xprd_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let xrprd_r = TR.tmap rewrite_expr xprd_r in
         let xrhs_r =
           TR.tmap2 (fun xprd xra -> XOp (XPlus, [xprd; xra])) xprd_r xra_r in
         let xrrhs_r = TR.tmap rewrite_expr xrhs_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_r xra_r]
           @ (get_all_rdefs_r xrrhs_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; xra_r; xprd_r; xrprd_r; xrhs_r; xrrhs_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MultiplySubtract (c, rd, rn, rm, ra) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xra_r = ra#to_expr floc in
         let xprod_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let xxprod_r = TR.tmap rewrite_expr xprod_r in
         let xdiff_r =
           TR.tmap2 (fun xra xprod -> XOp (XMinus, [xra; xprod])) xra_r xprod_r in
         let xxdiff_r = TR.tmap rewrite_expr xdiff_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_r xra_r]
           @ (get_all_rdefs_r xxdiff_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; xra_r; xprod_r; xxprod_r; xdiff_r; xxdiff_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Pop (c, sp, rl, _) ->
         let splhs_r = sp#to_variable floc in
         let sprhs_r = sp#to_expr floc in
         let regcount = rl#get_register_count in
         let spresult_r =
           TR.tmap
             (fun sprhs -> XOp (XPlus, [sprhs; int_constant_expr (regcount * 4)]))
             sprhs_r in
         let rspresult_r = TR.tmap rewrite_expr spresult_r in
         let lhsvars_r =
           List.map (fun (op: arm_operand_int) ->
               op#to_variable floc) rl#get_register_op_list in
         let rhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset RD)
             (List.init rl#get_register_count (fun i -> 4 * i)) in
         let rhsexprs_r =
           List.map (fun (x: arm_operand_int) -> x#to_expr floc) rhsops in
         let xaddrs_r =
           List.init
             rl#get_register_count
             (fun i ->
               let xaddr_r =
                 TR.tmap
                   (fun sprhs -> XOp (XPlus, [sprhs; int_constant_expr (i * 4)]))
                   sprhs_r in
               TR.tmap rewrite_expr xaddr_r) in
         let rrhsexprs_r = List.map (TR.tmap rewrite_expr) rhsexprs_r in
         let rdefs = List.map get_rdef_r (sprhs_r :: rhsexprs_r) in
         let uses = List.map get_def_use_r (splhs_r :: lhsvars_r) in
         let useshigh = List.map get_def_use_high_r (splhs_r :: lhsvars_r) in
         let xprs_r =
           (sprhs_r :: spresult_r :: rspresult_r :: rrhsexprs_r) @ xaddrs_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(splhs_r :: lhsvars_r)
             ~xprs_r
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if rl#includes_pc then
             let r0_op = arm_register_op AR0 RD in
             let xr0_r = r0_op#to_expr floc in
             let xxr0_r = TR.tmap rewrite_expr xr0_r in
             add_return_value tags args xr0_r xxr0_r
           else
             (tags, args) in
         (tags, args)

      | PreloadData (_, c, base, mem) ->
         let xbase_r = base#to_expr floc in
         let xmem_r = mem#to_expr floc in
         let (tagstring, args) = mk_instrx_data_r ~xprs_r:[xbase_r; xmem_r] () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Push (c, sp, rl, _) ->
         let splhs_r = sp#to_variable floc in
         let sprhs_r = sp#to_expr floc in
         let rhsexprs_rl =
           List.map (fun (op: arm_operand_int) ->
               op#to_expr floc) rl#get_register_op_list in
         let rrhsexprs_rl = List.map (TR.tmap rewrite_expr) rhsexprs_rl in
         let regcount = rl#get_register_count in
         let lhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset WR)
             (List.init regcount (fun i -> ((- (4 * regcount)) + (4 * i)))) in
         let lhsvars_rl = List.map (fun v -> v#to_variable floc) lhsops in
         let rdefs = List.map get_rdef_r (sprhs_r :: rhsexprs_rl) in
         let uses = List.map get_def_use_r (splhs_r :: lhsvars_rl) in
         let useshigh = List.map get_def_use_high_r (splhs_r :: lhsvars_rl) in
         let spresult_r =
           TR.tmap
             (fun sprhs ->
               XOp (XMinus, [sprhs; int_constant_expr (regcount * 4)]))
             sprhs_r in
         let rspresult_r = TR.tmap rewrite_expr spresult_r in
         let xaddrs =
           List.init
             regcount
             (fun i ->
               let xaddr_r =
                 TR.tmap
                   (fun rspresult ->
                     XOp (XPlus, [rspresult; int_constant_expr (i * 4)]))
                   rspresult_r in
               TR.tmap rewrite_expr xaddr_r) in
         let xprs_r =
           (sprhs_r :: spresult_r :: rspresult_r :: rrhsexprs_rl) @ xaddrs in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(splhs_r :: lhsvars_rl)
             ~xprs_r
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | ReverseSubtract (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMinus, [xrm; xrn])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SelectBytes (c, rd, rn, rm) ->
         let lhs_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xxrn_r = TR.tmap rewrite_expr xrn_r in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = [get_rdef_r xrn_r; get_rdef_r xrm_r] in
         let uses = [get_def_use_r lhs_r] in
         let useshigh = [get_def_use_high_r lhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[lhs_r]
             ~xprs_r:[xrn_r; xrm_r; xxrn_r; xxrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedBitFieldExtract (c, rd, rn) ->
         let lhs_r = rd#to_variable floc in
         let rhs_r = rn#to_expr floc in
         let rrhs_r = TR.tmap rewrite_expr rhs_r in
         let rdefs = [get_rdef_r rhs_r] in
         let uses = [get_def_use_r lhs_r] in
         let useshigh = [get_def_use_high_r lhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[lhs_r]
             ~xprs_r:[rhs_r; rrhs_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedDivide (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XDiv, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedExtendByte (c, rd, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = (get_rdef_r xrm_r) :: (get_all_rdefs_r xxrm_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; xxrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedExtendHalfword (c, rd, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = (get_rdef_r xrm_r) :: (get_all_rdefs_r xxrm_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; xxrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedMostSignificantWordMultiply (c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let result_r =
           TR.tmap (fun r -> XOp (XDiv, [r; e32_c])) result_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedMostSignificantWordMultiplyAccumulate (c, rd, rn, rm, ra, _) ->
         let vrd_r = rd#to_variable floc in
         let xra_r = ra#to_expr floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let xra32_r = TR.tmap (fun xra -> XOp (XMult, [xra; e32_c])) xra_r in
         let result_r =
           TR.tmap2 (fun r a -> XOp (XPlus, [r; a])) result_r xra32_r in
         let result_r = TR.tmap (fun r -> XOp (XDiv, [r; e32_c])) result_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xra_r; get_rdef_r xrn_r; get_rdef_r xrm_r]
           @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; xra_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedMultiplyLong (_, c, rdlo, rdhi, rn, rm) ->
         let vlo_r = rdlo#to_variable floc in
         let vhi_r = rdhi#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let result_r = TR.tmap rewrite_expr result_r in
         let loresult_r = TR.tmap (fun r -> XOp (XMod, [r; e32_c])) result_r in
         let hiresult_r = TR.tmap (fun r -> XOp (XDiv, [r; e32_c])) result_r in
         let loresultr_r = TR.tmap rewrite_expr loresult_r in
         let hiresultr_r = TR.tmap rewrite_expr hiresult_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r result_r) in
         let uses = [get_def_use_r vlo_r; get_def_use_r vhi_r] in
         let useshigh = [get_def_use_high_r vlo_r; get_def_use_high_r vhi_r] in
         let xprs_r =
           [xrn_r; xrm_r; loresult_r; hiresult_r; loresultr_r; hiresultr_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vlo_r; vhi_r]
             ~xprs_r
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedMultiplyWordB (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2
             (fun xrn xrm -> XOp (XMult, [xrn; XOp (XMod, [xrm; e16_c])]))
             xrn_r xrm_r in
         let xxrn_r = TR.tmap rewrite_expr xrn_r in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rresult_r = TR.tmap (rewrite_expr ?restrict:(Some 4)) result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r; xxrn_r; xxrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedMultiplyWordT (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2
             (fun xrn xrm -> XOp (XMult, [xrn; XOp (XShiftrt, [xrm; e16_c])]))
             xrn_r xrm_r in
         let xxrn_r = TR.tmap rewrite_expr xrn_r in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rresult_r = TR.tmap (rewrite_expr ?restrict:(Some 4)) result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r; xxrn_r; xxrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreMultipleDecrementAfter (wback, c, base, rl, _) ->
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let rhss_rl = rl#to_multiple_expr floc in
         let rrhss_rl = List.map (TR.tmap rewrite_expr) rhss_rl in
         let (memlhss_rl, _) =
           List.fold_left
             (fun (acc, off) _reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs_r = memop#to_variable floc in
               (acc @ [memlhs_r], off + 4))
             ([], 4 - (4 * regcount)) rl#get_register_op_list in
         let rdefs = List.map get_rdef_r (baserhs_r :: rrhss_rl) in
         let uses = List.map get_def_use_r (baselhs_r :: memlhss_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: memlhss_rl) in
         let wbackresults_r =
           if wback then
             let decrem = int_constant_expr (4 * regcount) in
             let baseresult_r =
               TR.tmap (fun baserhs -> XOp (XMinus, [baserhs; decrem])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             [baseresult_r; rbaseresult_r]
           else
             [baserhs_r; baserhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: memlhss_rl)
             ~xprs_r:((baserhs_r :: wbackresults_r) @ rrhss_rl)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreMultipleDecrementBefore (wback, c, base, rl, _) ->
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let rhss_rl = rl#to_multiple_expr floc in
         let rrhss_rl = List.map (TR.tmap rewrite_expr) rhss_rl in
         let (memlhss_rl, _) =
           List.fold_left
             (fun (acc, off) _reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs_r = memop#to_variable floc in
               (acc @ [memlhs_r], off + 4))
             ([], - (4 * regcount)) rl#get_register_op_list in
         let rdefs = List.map get_rdef_r (baserhs_r :: rrhss_rl) in
         let uses = List.map get_def_use_r (baselhs_r :: memlhss_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: memlhss_rl) in
         let wbackresults_r =
           if wback then
             let decrem = int_constant_expr (4 * regcount) in
             let baseresult_r =
               TR.tmap (fun baserhs -> XOp (XMinus, [baserhs; decrem])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             [baseresult_r; rbaseresult_r]
           else
             [baserhs_r; baserhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: memlhss_rl)
             ~xprs_r:((baserhs_r :: wbackresults_r) @ rrhss_rl)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreMultipleIncrementAfter _ when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_ldm_stm_sequence then
           let seq = agg#ldm_stm_sequence in
           let srcop = seq#srcreg in
           let dstop = seq#dstreg in
           let size = seq#registers#get_register_count * 4 in
           let srcfloc = get_floc (make_i_location floc#l (iaddr#add_int (-4))) in
           let xsrc_r = srcop#to_expr srcfloc in
           let xdst_r = dstop#to_expr floc in
           let xxsrc_r = TR.tmap (rewrite_floc_expr srcfloc) xsrc_r in
           let xxdst_r = TR.tmap (rewrite_expr ?restrict:(Some 4)) xdst_r in
           let xxdst_r =
             TR.tmap
               (fun v -> XOp ((Xf "addressofvar"), [(XVar v)]))
               (TR.tbind floc#get_var_at_address xxdst_r) in
           let rdefs = [(get_rdef_r xsrc_r); (get_rdef_r xdst_r)] in
           let _ =
             TR.tfold_default
               (fun xxsrc ->
                 match get_string_reference srcfloc xxsrc with
                 | Some _ -> register_function_prototype "strcpy"
                 | _ -> register_function_prototype "memcpy")
               ()
               xxsrc_r in
           let (tagstring, args) =
             mk_instrx_data_r
               ~xprs_r:[xdst_r; xsrc_r; xxdst_r; xxsrc_r]
               ~integers:[size]
               ~rdefs
               () in
           let tags = tagstring :: ["agg-ldmstm"] in
           let tags = add_subsumption_dependents agg tags in
           (tags, args)
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Aggregate for StoreMultipleIncrement not recognized at ";
                     iaddr#toPretty]))

      | StoreMultipleIncrementAfter (wback, c, base, rl, _, _) ->
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let rhss_rl = rl#to_multiple_expr floc in
         let rrhss_rl = List.map (TR.tmap rewrite_expr) rhss_rl in
         let (memlhss_rl, _) =
           List.fold_left
             (fun (acc, off) _reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs_r = memop#to_variable floc in
               (acc @ [memlhs_r], off + 4)) ([], 0) rl#get_register_op_list in
         let rdefs = List.map get_rdef_r (baserhs_r :: rrhss_rl) in
         let uses = List.map get_def_use_r (baselhs_r :: memlhss_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: memlhss_rl) in
         let wbackresults_r =
           if wback then
             let increm = int_constant_expr (4 * regcount) in
             let baseresult_r =
               TR.tmap (fun baserhs -> XOp (XPlus, [baserhs; increm])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             [baseresult_r; rbaseresult_r]
           else
             [baserhs_r; baserhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: memlhss_rl)
             ~xprs_r:((baserhs_r :: wbackresults_r) @ rrhss_rl)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreMultipleIncrementBefore (wback, c, base, rl, _) ->
         let basereg = base#get_register in
         let baselhs_r = base#to_variable floc in
         let baserhs_r = base#to_expr floc in
         let regcount = rl#get_register_count in
         let rhss_rl = rl#to_multiple_expr floc in
         let rrhss_rl = List.map (TR.tmap rewrite_expr) rhss_rl in
         let (memlhss_rl, _) =
           List.fold_left
             (fun (acc, off) _reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs_r = memop#to_variable floc in
               let memlhs_r =
                 let r =
                   TR.tbind
                     (floc#convert_variable_offsets ~size:(Some 4)) memlhs_r in
                 if Result.is_ok r then r else memlhs_r in
               (acc @ [memlhs_r], off + 4)) ([], 4) rl#get_register_op_list in
         let rdefs = List.map get_rdef_r (baserhs_r :: rrhss_rl) in
         let uses = List.map get_def_use_r (baselhs_r :: memlhss_rl) in
         let useshigh = List.map get_def_use_high_r (baselhs_r :: memlhss_rl) in
         let wbackresults_r =
           if wback then
             let increm = int_constant_expr (4 * regcount) in
             let baseresult_r =
               TR.tmap (fun baserhs -> XOp (XPlus, [baserhs; increm])) baserhs_r in
             let rbaseresult_r = TR.tmap rewrite_expr baseresult_r in
             [baseresult_r; rbaseresult_r]
           else
             [baserhs_r; baserhs_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(baselhs_r :: memlhss_rl)
             ~xprs_r:((baserhs_r :: wbackresults_r) @ rrhss_rl)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreRegister (c, rt, rn, rm, mem, _) ->
         let vmem_r = mem#to_variable floc in
         let vmem_r =
           let r = TR.tbind (floc#convert_variable_offsets ~size:(Some 4)) vmem_r in
           if Result.is_ok r then r else vmem_r in
         let xaddr_r = mem#to_address floc in
         let xrt_r = rt#to_expr floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xxrt_r = TR.tmap rewrite_expr xrt_r in
         let xxrtc_r = TR.tbind floc#convert_xpr_offsets xxrt_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let lhsvar_r = TR.tbind floc#get_var_at_address xxaddr_r in
         let rdefs =
           [get_rdef_r xrn_r;
            get_rdef_r xrm_r;
            get_rdef_r xrt_r;
            get_rdef_r xxrt_r] in
         let uses = [get_def_use_r vmem_r] in
         let useshigh = [get_def_use_high_r vmem_r] in
         let xprs_r = [xrn_r; xrm_r; xrt_r; xxrt_r; xxrtc_r; xaddr_r] in
         let vars_r = [vmem_r; lhsvar_r] in
         let _ =
           floc#memrecorder#record_store_r
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:4
             ~vtype:t_unknown
             ~xpr_r:xxrt_r in
         let (tagstring, args) =
           mk_instrx_data_r ~vars_r ~xprs_r ~rdefs ~uses ~useshigh () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | StoreRegisterByte (c, rt, rn, rm, mem, _) ->
         let vmem_r = mem#to_variable floc in
         let vmem_r =
           let r = TR.tbind (floc#convert_variable_offsets ~size:(Some 1)) vmem_r in
           if Result.is_ok r then r else vmem_r in
         let xaddr_r = mem#to_address floc in
         let xrt_r = rt#to_expr floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xxrt_r = TR.tmap rewrite_expr xrt_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let lhsvar_r =
           TR.tbind (floc#get_var_at_address ~size:(Some 1)) xxaddr_r in
         let rdefs =
           [get_rdef_r xrn_r;
            get_rdef_r xrm_r;
            get_rdef_r xrt_r;
            get_rdef_r xxrt_r] in
         let uses = [get_def_use_r vmem_r] in
         let useshigh = [get_def_use_high_r vmem_r] in
         let _ =
           floc#memrecorder#record_store_r
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:1
             ~vtype:t_unknown
             ~xpr_r:xxrt_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vmem_r; lhsvar_r]
             ~xprs_r:[xrn_r; xrm_r; xrt_r; xxrt_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
                  let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | StoreRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
         let vmem_r = mem#to_variable floc in
         let vmem_r =
           let r = TR.tbind (floc#convert_variable_offsets ~size:(Some 4)) vmem_r in
           if Result.is_ok r then r else vmem_r in
         let vmem2_r = mem2#to_variable floc in
         let vmem2_r =
           let r = TR.tbind (floc#convert_variable_offsets ~size:(Some 4)) vmem2_r in
           if Result.is_ok r then r else vmem2_r in
         let xaddr1_r = mem#to_address floc in
         let xaddr2_r = mem2#to_address floc in
         let xaddr1_r = TR.tmap rewrite_expr xaddr1_r in
         let xaddr2_r = TR.tmap rewrite_expr xaddr2_r in
         let xrt_r = rt#to_expr floc in
         let xxrt_r = TR.tmap rewrite_expr xrt_r in
         let xrt2_r = rt2#to_expr floc in
         let xxrt2_r = TR.tmap rewrite_expr xrt2_r in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xprs_r =
           [xrn_r; xrm_r; xrt_r; xxrt_r; xrt2_r; xxrt2_r; xaddr1_r; xaddr2_r] in
         let vars_r = [vmem_r; vmem2_r] in
         let uses = [get_def_use_r vmem_r; get_def_use_r vmem2_r] in
         let useshigh = [get_def_use_high_r vmem_r; get_def_use_high_r vmem2_r] in
         let _ =
           floc#memrecorder#record_store_r
             ~addr_r:xaddr1_r
             ~var_r:vmem_r
             ~size:4
             ~vtype:t_unknown
             ~xpr_r:xxrt_r in
         let _ =
           floc#memrecorder#record_store_r
             ~addr_r:xaddr2_r
             ~var_r:vmem2_r
             ~size:4
             ~vtype:t_unknown
             ~xpr_r:xxrt2_r in
         let rdefs = [
             get_rdef_r xrn_r;
             get_rdef_r xrm_r;
             get_rdef_r xrt_r;
             get_rdef_r xxrt_r;
             get_rdef_r xrt2_r;
             get_rdef_r xxrt2_r] in
         let (tagstring, args) =
           mk_instrx_data_r ~vars_r ~xprs_r ~rdefs ~uses ~useshigh () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | StoreRegisterExclusive (c, rd, rt, rn, mem) ->
         let vmem_r = mem#to_variable floc in
         let xaddr_r = mem#to_address floc in
         let vrd_r = rd#to_variable floc in
         let xrt_r = rt#to_expr floc in
         let xrn_r = rn#to_expr floc in
         let xxrt_r = TR.tmap rewrite_expr xrt_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let rdefs = [get_rdef_r xrn_r; get_rdef_r xrt_r; get_rdef_r xxrt_r] in
         let uses = [get_def_use_r vmem_r; get_def_use_r vrd_r] in
         let useshigh = [get_def_use_r vmem_r; get_def_use_r vrd_r] in
         let _ =
           floc#memrecorder#record_store_r
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:4
             ~vtype:t_unknown
             ~xpr_r:xxrt_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vmem_r; vrd_r]
             ~xprs_r:[xrn_r; xrt_r; xxrt_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreRegisterHalfword (c, rt, rn, rm, mem, _) ->
         let vmem_r = mem#to_variable floc in
         let vmem_r =
           let r = TR.tbind (floc#convert_variable_offsets ~size:(Some 2)) vmem_r in
           if Result.is_ok r then r else vmem_r in
         let xaddr_r = mem#to_address floc in
         let xrt_r = rt#to_expr floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let xxrt_r = TR.tmap rewrite_expr xrt_r in
         let xxrt_r = TR.tbind floc#convert_xpr_offsets xxrt_r in
         let xxaddr_r = TR.tmap rewrite_expr xaddr_r in
         let rdefs =
           [get_rdef_r xrn_r;
            get_rdef_r xrm_r;
            get_rdef_r xrt_r;
            get_rdef_r xxrt_r] in
         let uses = [get_def_use_r vmem_r] in
         let useshigh = [get_def_use_high_r vmem_r] in
         let _ =
           floc#memrecorder#record_store_r
             ~addr_r:xxaddr_r
             ~var_r:vmem_r
             ~size:2
             ~vtype:t_unknown
             ~xpr_r:xxrt_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vmem_r]
             ~xprs_r:[xrn_r; xrm_r; xrt_r; xxrt_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn_r = rn#to_variable floc in
             TR.tfold
               ~ok:(fun (inc, xaddr) ->
                 add_base_update tags args vrn_r inc (Ok xaddr))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   (tags, args)
                 end)
               (mem#to_updated_offset_address floc)
           else
             (tags, args) in
         (tags, args)

      | Subtract (_, c, rd, rn, rm, _, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMinus, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SubtractCarry (_, c, rd, rn, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMinus, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SupervisorCall (c, _) ->
         let r7 = arm_register_op AR7 RD in
         let xr7_r = r7#to_expr floc in
         let rdefs = [get_rdef_r xr7_r] in
         let (tagstring, args) = mk_instrx_data_r ~xprs_r:[xr7_r] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Swap (c, rt, rt2, rn, mem) ->
         let vrt_r = rt#to_variable floc in
         let vmem_r = mem#to_variable floc in
         let xaddr_r = mem#to_address floc in
         let xrt2_r = rt2#to_expr floc in
         let xxrt2_r = TR.tmap rewrite_expr xrt2_r in
         let xrn_r = rn#to_expr floc in
         let xmem_r = mem#to_expr floc in
         let rdefs =
           [get_rdef_r xrt2_r; get_rdef_r xrn_r; get_rdef_memvar_r vmem_r]
           @ (get_all_rdefs_r xmem_r) in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let _ =
           TR.tfold_default
             (fun xrmem -> ignore (get_string_reference floc xrmem)) () xrmem_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrt2_r; xxrt2_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SwapByte (c, rt, rt2, rn, mem) ->
         let vrt_r = rt#to_variable floc in
         let vmem_r = mem#to_variable floc in
         let xaddr_r = mem#to_address floc in
         let xrt2_r = rt2#to_expr floc in
         let xxrt2_r = TR.tmap rewrite_expr xrt2_r in
         let xrn_r = rn#to_expr floc in
         let xmem_r = mem#to_expr floc in
         let rdefs =
           [get_rdef_r xrt2_r; get_rdef_r xrn_r; get_rdef_memvar_r vmem_r]
           @ (get_all_rdefs_r xmem_r) in
         let uses = [get_def_use_r vrt_r] in
         let useshigh = [get_def_use_high_r vrt_r] in
         let xrmem_r = TR.tmap rewrite_expr xmem_r in
         let _ =
           TR.tfold_default
             (fun xrmem -> ignore (get_string_reference floc xrmem)) () xrmem_r in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrt_r; vmem_r]
             ~xprs_r:[xrn_r; xrt2_r; xxrt2_r; xmem_r; xrmem_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | TableBranchByte (_, _, rm, _) ->
         let iaddr = instr#get_address in
         let xrm_r = rm#to_expr floc in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = (get_rdef_r xrm_r) :: (get_all_rdefs_r xxrm_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xrm_r; xxrm_r] ~rdefs () in
         let tags = tagstring :: ["agg-jt"] in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         let tags = add_subsumption_dependents agg tags in
         (tags, args)

      | TableBranchHalfword (_, _, rm, _) ->
         let iaddr = instr#get_address in
         let xrm_r = rm#to_expr floc in
         let xxrm_r = TR.tmap rewrite_expr xrm_r in
         let rdefs = (get_rdef_r xrm_r) :: (get_all_rdefs_r xxrm_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xrm_r; xxrm_r] ~rdefs () in
         let tags = tagstring :: ["agg-jt"] in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         let tags = add_subsumption_dependents agg tags in
         (tags, args)

      | Test (c, rn, rm, _) ->
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XBAnd, [xrn; xrm])) xrn_r xrm_r in
         let rdefs = (get_rdef_r xrm_r) :: (get_all_rdefs_r result_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xrm_r; xrn_r; result_r] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | TestEquivalence (c, rn, rm) ->
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XBXor, [xrn; xrm])) xrn_r xrm_r in
         let rdefs = (get_rdef_r xrm_r) :: (get_all_rdefs_r result_r) in
         let (tagstring, args) =
           mk_instrx_data_r ~xprs_r:[xrm_r; xrn_r; result_r] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedAdd8 (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let rdefs = [get_rdef_r xrm_r; get_rdef_r xrn_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedBitFieldExtract (c, rd, rn) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xxrn_r = TR.tmap rewrite_expr xrn_r in
         let rdefs = [get_rdef_r xrn_r] @ (get_all_rdefs_r xxrn_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xxrn_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedDivide (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let rdefs = [get_rdef_r xrn_r; get_rdef_r xrm_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedExtendAddByte (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let rdefs = [get_rdef_r xrn_r; get_rdef_r xrm_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedExtendAddHalfword (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let rdefs = [get_rdef_r xrn_r; get_rdef_r xrm_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedExtendByte (c, rd, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let result_r = TR.tmap (fun xrm -> XOp (XXlsb, [xrm])) xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs = [get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedExtendHalfword (c, rd, rm, _) ->
         let vrd_r = rd#to_variable floc in
         let xrm_r = rm#to_expr floc in
         let result_r = TR.tmap (fun xrm -> XOp (XXlsh, [xrm])) xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs = [get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedMultiplyAccumulateLong (_, c, rdlo, rdhi, rn, rm) ->
         let vlo_r = rdlo#to_variable floc in
         let vhi_r = rdhi#to_variable floc in
         let xlo_r = rdlo#to_expr floc in
         let xhi_r = rdhi#to_expr floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let acc_r = TR.tmap (fun xhi -> XOp (XMult, [xhi; e32_c])) xhi_r in
         let acc_r =
           TR.tmap2 (fun acc xlo -> XOp (XPlus, [acc; xlo])) acc_r xlo_r in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let result_r =
           TR.tmap2 (fun result acc -> XOp (XPlus, [result; acc])) result_r acc_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r; get_rdef_r xlo_r; get_rdef_r xhi_r]
           @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vlo_r; get_def_use_r vhi_r] in
         let useshigh = [get_def_use_high_r vlo_r; get_def_use_high_r vhi_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vlo_r; vhi_r]
             ~xprs_r:[xrn_r; xrm_r; xlo_r; xhi_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedMultiplyLong (_, c, rdlo, rdhi, rn, rm) ->
         let vlo_r = rdlo#to_variable floc in
         let vhi_r = rdhi#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let result_r =
           TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
         let rresult_r = TR.tmap rewrite_expr result_r in
         let rdefs =
           [get_rdef_r xrn_r; get_rdef_r xrm_r] @ (get_all_rdefs_r rresult_r) in
         let uses = [get_def_use_r vlo_r; get_def_use_r vhi_r] in
         let useshigh = [get_def_use_high_r vlo_r; get_def_use_high_r vhi_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vlo_r; vhi_r]
             ~xprs_r:[xrn_r; xrm_r; result_r; rresult_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedSaturate (c, rd, imm, rn) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let ximm_r = imm#to_expr floc in
         let rdefs = [get_rdef_r xrn_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[ximm_r; xrn_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedSaturatingSubtract8 (c, rd, rn, rm) ->
         let vrd_r = rd#to_variable floc in
         let xrn_r = rn#to_expr floc in
         let xrm_r = rm#to_expr floc in
         let rdefs = [get_rdef_r xrn_r; get_rdef_r xrm_r] in
         let uses = [get_def_use_r vrd_r] in
         let useshigh = [get_def_use_high_r vrd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vrd_r]
             ~xprs_r:[xrn_r; xrm_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorAbsolute (c, _, dst, src) ->
         let vdst_r = dst#to_variable floc in
         let xsrc_r = src#to_expr floc in
         let rxsrc_r = TR.tmap rewrite_expr xsrc_r in
         let rdefs = [get_rdef_r xsrc_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[xsrc_r; rxsrc_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VCompare (_, c, _, fdst, src1, src2) ->
         let v_fpscr_r = fdst#to_variable floc in
         let xsrc1_r = src1#to_expr floc in
         let xsrc2_r = src2#to_expr floc in
         let rxsrc1_r = TR.tmap rewrite_expr xsrc1_r in
         let rxsrc2_r = TR.tmap rewrite_expr xsrc2_r in
         let rdefs = [get_rdef_r xsrc1_r; get_rdef_r xsrc2_r] in
         let uses = [get_def_use_r v_fpscr_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[v_fpscr_r]
             ~xprs_r:[xsrc1_r; xsrc2_r; rxsrc1_r; rxsrc2_r]
             ~rdefs
             ~uses
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorConvert (_, _, c, _, _, dst, src, _) ->
         let vdst_r = dst#to_variable floc in
         let xsrc_r = src#to_expr floc in
         let rxsrc_r = TR.tmap rewrite_expr xsrc_r in
         let rdefs = [get_rdef_r xsrc_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[xsrc_r; rxsrc_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VDivide (c, _, dst, src1, src2) ->
         let vdst_r = dst#to_variable floc in
         let xsrc1_r = src1#to_expr floc in
         let xsrc2_r = src2#to_expr floc in
         let rxsrc1_r = TR.tmap rewrite_expr xsrc1_r in
         let rxsrc2_r = TR.tmap rewrite_expr xsrc2_r in
         let rdefs = [get_rdef_r xsrc1_r; get_rdef_r xsrc2_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[xsrc1_r; xsrc2_r; rxsrc1_r; rxsrc2_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorDuplicate (c, _, _, _, dst, src) ->
         let vdst_r = dst#to_variable floc in
         let src_r = src#to_expr floc in
         let rsrc_r = TR.tmap rewrite_expr src_r in
         let rdefs = (get_rdef_r rsrc_r) :: (get_all_rdefs_r rsrc_r) in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[src_r; rsrc_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VLoadRegister (c, vd, base, mem) ->
         let vvd_r = vd#to_variable floc in
         let xbase_r = base#to_expr floc in
         let xaddr_r = mem#to_address floc in
         let vmem_r = mem#to_variable floc in
         let xmem_r = mem#to_expr floc in
         let rxbase_r = TR.tmap rewrite_expr xbase_r in
         let rxmem_r = TR.tmap rewrite_expr xmem_r in
         let rdefs =
           [get_rdef_memvar_r vmem_r; get_rdef_r xmem_r]
           @ (get_all_rdefs_r rxmem_r) in
         let uses = [get_def_use_high_r vvd_r] in
         let useshigh = [get_def_use_high_r vvd_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vvd_r; vmem_r]
             ~xprs_r:[xmem_r; rxmem_r; xbase_r; rxbase_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDS (c, _, dst, src) ->
         let vdst_r = dst#to_variable floc in
         let xsrc_r = src#to_expr floc in
         let rxsrc_r = TR.tmap rewrite_expr xsrc_r in
         let rdefs = [get_rdef_r xsrc_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[xsrc_r; rxsrc_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDDSS (c, _, dst1, dst2, ddst, src1, src2, ssrc) ->
         let vdst1_r = dst1#to_variable floc in
         let vdst2_r = dst2#to_variable floc in
         let vddst_r = ddst#to_variable floc in
         let xsrc1_r = src1#to_expr floc in
         let xsrc2_r = src2#to_expr floc in
         let xssrc_r = ssrc#to_expr floc in
         let rxsrc1_r = TR.tmap rewrite_expr xsrc1_r in
         let rxsrc2_r = TR.tmap rewrite_expr xsrc2_r in
         let rxssrc_r = TR.tmap rewrite_expr xssrc_r in
         let rdefs =
           [get_rdef_r xsrc1_r; get_rdef_r xsrc2_r; get_rdef_r xssrc_r] in
         let uses =
           [get_def_use_r vdst1_r; get_def_use_r vdst2_r; get_def_use_r vddst_r] in
         let useshigh = [
             get_def_use_high_r vdst1_r;
             get_def_use_high_r vdst2_r;
             get_def_use_high_r vddst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst1_r; vdst2_r; vddst_r]
             ~xprs_r:[xsrc1_r; xsrc2_r; xssrc_r; rxsrc1_r; rxsrc2_r; rxssrc_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDSS (c, _, dst, src1, src2, ssrc) ->
         let vdst_r = dst#to_variable floc in
         let xsrc1_r = src1#to_expr floc in
         let xsrc2_r = src2#to_expr floc in
         let xssrc_r = ssrc#to_expr floc in
         let rxsrc1_r = TR.tmap rewrite_expr xsrc1_r in
         let rxsrc2_r = TR.tmap rewrite_expr xsrc2_r in
         let rxssrc_r = TR.tmap rewrite_expr xssrc_r in
         let rdefs =
           [get_rdef_r xsrc1_r; get_rdef_r xsrc2_r; get_rdef_r xssrc_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[xsrc1_r; xsrc2_r; xssrc_r; rxsrc1_r; rxsrc2_r; rxssrc_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDDS (c, _, dst1, dst2, ddst, src) ->
         let vdst1_r = dst1#to_variable floc in
         let vdst2_r = dst2#to_variable floc in
         let vddst_r = ddst#to_variable floc in
         let xsrc_r = src#to_expr floc in
         let rxsrc_r = TR.tmap rewrite_expr xsrc_r in
         let rdefs = [get_rdef_r xsrc_r] in
         let uses =
           [get_def_use_r vdst1_r; get_def_use_r vdst2_r; get_def_use_r vddst_r] in
         let useshigh = [
               get_def_use_high_r vdst1_r;
               get_def_use_high_r vdst2_r;
               get_def_use_high_r vddst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst1_r; vdst2_r; vddst_r]
             ~xprs_r:[xsrc_r; rxsrc_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VMoveRegisterStatus (c, dst, src) ->
         let vdst_r = dst#to_variable floc in
         let xsrc_r = src#to_expr floc in
         let rdefs = [get_rdef_r xsrc_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r] ~xprs_r:[xsrc_r] ~rdefs ~uses ~useshigh () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VMoveToSystemRegister (c, _, src) ->
         let xsrc_r = src#to_expr floc in
         let rdefs = [get_rdef_r xsrc_r] in
         let (tagstring, args) = mk_instrx_data_r ~xprs_r:[xsrc_r] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMultiplySubtract (c, _, dst, src1, src2) ->
         let vdst_r = dst#to_variable floc in
         let xdst_r = dst#to_expr floc in
         let rxdst_r = TR.tmap rewrite_expr xdst_r in
         let xsrc1_r = src1#to_expr floc in
         let rxsrc1_r = TR.tmap rewrite_expr xsrc1_r in
         let xsrc2_r = src2#to_expr floc in
         let rxsrc2_r = TR.tmap rewrite_expr xsrc2_r in
         let rdefs = [get_rdef_r xsrc1_r; get_rdef_r xsrc2_r; get_rdef_r xdst_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[xsrc1_r; xsrc2_r; xdst_r; rxsrc1_r; rxsrc2_r; rxdst_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorPop (c, sp, rl, _) ->
         let splhs_r = sp#to_variable floc in
         let sprhs_r = sp#to_expr floc in
         let regcount = rl#get_register_count in
         let regsize =
           if rl#is_double_extension_register_list then 8 else 4 in
         let spresult_r =
           TR.tmap
             (fun sprhs ->
               XOp (XPlus, [sprhs; int_constant_expr (regcount * regsize)]))
             sprhs_r in
         let rspresult_r = TR.tmap rewrite_expr spresult_r in
         let lhsvars_rl =
           List.map (fun (op: arm_operand_int) ->
               op#to_variable floc) rl#get_extension_register_op_list in
         let rhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset RD)
             (List.init rl#get_register_count (fun i -> regsize * i)) in
         let rhsexprs_rl =
           List.map (fun (x: arm_operand_int) -> x#to_expr floc) rhsops in
         let xaddrs_rl =
           List.init
             regcount
             (fun i ->
               let xaddr_r =
                 TR.tmap
                   (fun sprhs ->
                     XOp (XPlus, [sprhs; int_constant_expr (i * regsize)]))
                   sprhs_r in
               TR.tmap rewrite_expr xaddr_r) in
         let rrhsexprs_rl = List.map (TR.tmap rewrite_expr) rhsexprs_rl in
         let rdefs = List.map get_rdef_r (sprhs_r :: rhsexprs_rl) in
         let uses = List.map get_def_use_r (splhs_r :: lhsvars_rl) in
         let useshigh = List.map get_def_use_high_r (splhs_r :: lhsvars_rl) in
         let xprs_r =
           (sprhs_r :: spresult_r :: rspresult_r :: rrhsexprs_rl) @ xaddrs_rl in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(splhs_r :: lhsvars_rl)
             ~xprs_r
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorPush (c, sp, rl, _) ->
         let splhs_r = sp#to_variable floc in
         let sprhs_r = sp#to_expr floc in
         let rhsexprs_rl =
           List.map (fun (op: arm_operand_int) ->
               op#to_expr floc) rl#get_extension_register_op_list in
         let rrhsexprs_rl = List.map (TR.tmap rewrite_expr) rhsexprs_rl in
         let regcount = List.length rhsexprs_rl in
         let regsize = if rl#is_double_extension_register_list then 8 else 4 in
         let lhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset WR)
             (List.init
                regcount (fun i -> ((- regsize * regcount) + (regsize * i)))) in
         let lhsvars_rl = List.map (fun v -> v#to_variable floc) lhsops in
         let rdefs = List.map get_rdef_r (sprhs_r :: rhsexprs_rl) in
         let uses = List.map get_def_use_r (splhs_r :: lhsvars_rl) in
         let useshigh = List.map get_def_use_high_r (splhs_r :: lhsvars_rl) in
         let spresult_r =
           TR.tmap
             (fun sprhs ->
               XOp (XMinus, [sprhs; int_constant_expr (regcount * regsize)]))
             sprhs_r in
         let rspresult_r = TR.tmap rewrite_expr spresult_r in
         let xaddrs_rl =
           List.init
             regcount
             (fun i ->
               let xaddr_r =
                 TR.tmap
                   (fun rspresult ->
                     XOp (XPlus, [rspresult; int_constant_expr (i * regsize)]))
                   rspresult_r in
               TR.tmap rewrite_expr xaddr_r) in
         let xprs_r =
           ((sprhs_r :: spresult_r :: rspresult_r :: rrhsexprs_rl) @ xaddrs_rl) in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:(splhs_r :: lhsvars_rl)
             ~xprs_r
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VStoreRegister (c, src, base, mem) ->
         let vmem_r = mem#to_variable floc in
         let xaddr_r = mem#to_address floc in
         let xsrc_r = src#to_expr floc in
         let xbase_r = base#to_expr floc in
         let rxsrc_r = TR.tmap rewrite_expr xsrc_r in
         let rxbase_r = TR.tmap rewrite_expr xbase_r in
         let rdefs = [get_rdef_r xsrc_r; get_rdef_r xbase_r] in
         let uses = [get_def_use_r vmem_r] in
         let useshigh = [get_def_use_high_r vmem_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vmem_r]
             ~xprs_r:[xsrc_r; rxsrc_r; xbase_r; rxbase_r; xaddr_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorSubtract (c, _, dst, src1, src2) ->
         let vdst_r = dst#to_variable floc in
         let xdst_r = dst#to_expr floc in
         let rxdst_r = TR.tmap rewrite_expr xdst_r in
         let xsrc1_r = src1#to_expr floc in
         let rxsrc1_r = TR.tmap rewrite_expr xsrc1_r in
         let xsrc2_r = src2#to_expr floc in
         let rxsrc2_r = TR.tmap rewrite_expr xsrc2_r in
         let rdefs = [get_rdef_r xsrc1_r; get_rdef_r xsrc2_r] in
         let uses = [get_def_use_r vdst_r] in
         let useshigh = [get_def_use_high_r vdst_r] in
         let (tagstring, args) =
           mk_instrx_data_r
             ~vars_r:[vdst_r]
             ~xprs_r:[xsrc1_r; xsrc2_r; xdst_r; rxsrc1_r; rxsrc2_r; rxdst_r]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | _ -> ([], []) in
    let _ =
      if testsupport#requested_instrx_tags then
        testsupport#submit_instrx_tags instr#get_address (fst key) in
    instrx_table#add key

  method write_xml_sp_offset
           ?(tag="isp") (node:xml_element_int) (o:int * interval_t) =
    node#setIntAttribute tag (self#index_sp_offset o)

  method write_xml_instr
           ?(tag="iopx")
           (node:xml_element_int)
           (instr:arm_assembly_instruction_int)
           (floc:floc_int) =
    try
      node#setIntAttribute tag (self#index_instr instr floc)
    with
    | BCH_failure p ->
       let msg =
         LBLOCK [
             STR __FILE__; STR ":"; INT __LINE__; STR ": ";
             STR "Error in writing xml instruction: ";
             floc#l#i#toPretty;
             STR "  ";
             instr#toPretty;
             STR ": ";
             p] in
       raise (BCH_failure msg)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end


let mk_arm_opcode_dictionary = new arm_opcode_dictionary_t
