(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs LLC

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
open BCHLocation
open BCHFtsParameter
open BCHFunctionInterface
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMConditionalExpr
open BCHARMDisassemblyUtils
open BCHARMOperand
open BCHARMOpcodeRecords
open BCHARMPseudocode
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

  val mutable tables = []

  initializer
    tables <- [
      sp_offset_table;
      instrx_table
    ]

  method index_sp_offset (o:(int * interval_t)) =
    let (level,offset) = o in
    let key = ([],[level; xd#index_interval offset]) in
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
      let xtag = (List.hd tags) ^ "xx" in
      let tags = xtag :: ((List.tl tags) @ ["ic"; "icr"]) in
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

    let get_rdef_memvar (v: variable_t): int =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = varinv#get_var_reaching_defs symvar in
      match varinvs with
      | [vinv] -> vinv#index
      | _ -> -1 in

    let get_def_use (v: variable_t): int =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = varinv#get_var_def_uses symvar in
      match varinvs with
      | [vinv] -> vinv#index
      | _ -> -1 in

    let get_def_use_high (v: variable_t): int =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = varinv#get_var_def_uses_high symvar in
      match varinvs with
      | [vinv] -> vinv#index
      | _ -> -1 in

    let add_base_update
          (tags: string list)
          (args: int list)
          (v: variable_t)
          (inc: int)
          (x: xpr_t): (string list) * (int list) =
      let _ =
        if (List.length tags) = 0 then
          raise
            (BCH_failure
               (LBLOCK [STR "Empty tag list in add_base_update"])) in
      let xtag = (List.hd tags) ^ "vtlxdh" in
      let uses = [get_def_use v] in
      let useshigh = [get_def_use_high v] in
      let tags = xtag :: ((List.tl tags) @ ["bu"]) in
      let args =
        args
        @ [xd#index_variable v;
           bcd#index_typ t_unknown;
           inc;
           xd#index_xpr x]
        @ uses @ useshigh in
      (tags, args) in

    let mk_instrx_data
          ?(vars: variable_t list = [])
          ?(types: btype_t list = [])
          ?(xprs: xpr_t list = [])
          ?(rdefs: int list = [])
          ?(uses: int list = [])
          ?(useshigh: int list = [])
          ?(integers: int list = [])
          () =
      let _ =
        if testsupport#requested_instrx_data then
          testsupport#submit_instrx_data instr#get_address vars xprs in
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

    let add_optional_subsumption (tags: string list) =
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

    let callinstr_key (): (string list * int list) =
      let callargs = floc#get_call_arguments in
      let (xprs, xvars, rdefs) =
        List.fold_left (fun (xprs, xvars, rdefs) (p, x) ->
            let xvar =
              if is_register_parameter p then
                let regarg = TR.tget_ok (get_register_parameter_register p) in
                let pvar = floc#f#env#mk_register_variable regarg in
                XVar pvar
              else if is_stack_parameter p then
                let p_offset = TR.tget_ok (get_stack_parameter_offset p) in
                let sp = (sp_r RD)#to_expr floc in
                XOp (XPlus, [sp; int_constant_expr p_offset])
              else
                raise
                  (BCH_failure
                     (LBLOCK [
                          floc#l#toPretty;
                          STR ": Parameter type not recognized in call ";
                          STR "instruction"])) in
            let xx = rewrite_expr ?restrict:(Some 4) x in
            let xx =
              let optmemvar = floc#decompose_memvar_address xx in
              match optmemvar with
              | Some (memref, memoff) ->
                 XOp ((Xf "addressofvar"),
                      [XVar (floc#f#env#mk_index_offset_memory_variable memref memoff)])
              | _ -> xx in
            let rdef = get_rdef xvar in
            (xx :: xprs, xvar :: xvars, rdef :: rdefs)) ([], [], []) callargs in
      let (vrd, rtype) =
        let fintf = floc#get_call_target#get_function_interface in
        let rtype = get_fts_returntype fintf in
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
        mk_instrx_data
          ~vars:[vrd]
          ~types:[rtype]
          ~xprs:((List.rev xprs) @ (List.rev xvars))
          ~rdefs:((List.rev rdefs) @ xrdefs)
          ~uses:[get_def_use vrd]
          ~useshigh:[get_def_use_high vrd]
          () in
      let tags =
        if instr#is_inlined_call then
          tagstring :: ["call"; "inlined"]
        else
          tagstring :: ["call"; string_of_int (List.length callargs)] in
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
           let xrn = indexregop#to_expr floc in
           let xxrn = rewrite_expr xrn in
           let rdefs = (get_rdef xrn) :: (get_all_rdefs xxrn) in
           let (tagstring, args) =
             mk_instrx_data
               ~xprs:[xrn; xxrn]
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
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XPlus, [xrn; xrm]) in
         let xxrn = rewrite_expr xrn in
         let xxrm = rewrite_expr xrm in
         let rresult = rewrite_expr ?restrict:(Some 4) result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let uses = get_def_use vrd in
         let useshigh = get_def_use_high vrd in
         let optmemvar = floc#decompose_memvar_address rresult in
         let rresult =
           match optmemvar with
           | Some (memref, memoff) ->
              let memvar =
                floc#f#env#mk_index_offset_memory_variable memref memoff in
              XOp ((Xf "addressofvar"), [XVar memvar])
           | _ -> rresult in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult; xxrn; xxrm]
             ~rdefs:rdefs
             ~uses:[uses]
             ~useshigh:[useshigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | AddCarry (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XPlus, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrn; get_rdef xrm] in
         let uses = get_def_use vrd in
         let useshigh = get_def_use_high vrd in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[uses]
             ~useshigh:[useshigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Adr (c, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm = imm#to_expr floc in
         let _ = ignore (get_string_reference floc ximm) in
         let uses = get_def_use vrd in
         let useshigh = get_def_use_high vrd in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[ximm]
             ~uses:[uses]
             ~useshigh:[useshigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | ArithmeticShiftRight (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result =
           match xrm with
           | XConst (IntConst n) when n#toInt = 2 ->
              XOp (XDiv, [xrn; XConst (IntConst (mkNumerical 4))])
           | _ -> XOp (XAsr, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitFieldClear (c, rd, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xrd = rd#to_expr floc in
         let rdefs = [get_rdef xrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrd]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitFieldInsert (c, rd, rn, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xrd = rd#to_expr floc in
         let xrn = rn#to_expr floc in
         let rdefs = [get_rdef xrd; get_rdef xrn] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrd; xrn]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseAnd (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBAnd, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseBitClear (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBAnd, [xrn; XOp (XBNot, [xrm])]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseExclusiveOr (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBXor, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseNot (_, c, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBNot, [xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseOr (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBOr, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let _ = ignore (get_string_reference floc rresult) in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BitwiseOrNot (_, c, rd, rn, rm) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xrmn = XOp (XBNot, [xrm]) in
         let result = XOp (XBOr, [xrn; xrmn]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; xrmn; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Branch (_, tgt, _)
           when tgt#is_absolute_address && floc#has_call_target ->
         callinstr_key ()

      | Branch _ when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_jumptable then
           let jt = agg#jumptable in
           let indexregop = jt#index_operand in
           let xrn = indexregop#to_expr floc in
           let xxrn = rewrite_expr xrn in
           let rdefs = (get_rdef xrn) :: (get_all_rdefs xxrn) in
           let (tagstring, args) =
             mk_instrx_data
               ~xprs:[xrn; xxrn]
               ~rdefs:rdefs
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
         let xtgt = tgt#to_expr floc in
         let txpr = floc#get_test_expr in
         let fxpr = simplify_xpr (XOp (XLNot, [txpr])) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
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
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond; xtgt]
             ~rdefs:rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | Branch (_, tgt, _) ->
         let xtgt = tgt#to_expr floc in
         let xxtgt = rewrite_expr xtgt in
         let rdefs = (get_rdef xtgt) :: (get_all_rdefs xxtgt) in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xtgt; xxtgt]
             ~rdefs
             () in
         let tags = add_optional_subsumption [tagstring] in
         (tags, args)

      | BranchExchange _ when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_jumptable then
           let jt = agg#jumptable in
           let indexregop = jt#index_operand in
           let xrn = indexregop#to_expr floc in
           let xxrn = rewrite_expr xrn in
           let rdefs = (get_rdef xrn) :: (get_all_rdefs xxrn) in
           let (tagstring, args) =
             mk_instrx_data
               ~xprs:[xrn; xxrn]
               ~rdefs:rdefs
               () in
           let tags = tagstring :: ["agg-jt"] in
           let tags = add_subsumption_dependents agg tags in
           (tags, args)
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Aggregate for BranchExchange not recognized at ";
                     iaddr#toPretty]))

      | BranchExchange (c, tgt)
           when tgt#is_register && tgt#get_register = ARLR ->
         let r0_op = arm_register_op AR0 RD in
         let xr0 = r0_op#to_expr floc in
         let xxr0 = rewrite_expr xr0 in
         let rdefs = [get_rdef xr0] @ (get_all_rdefs xxr0) in
         let (tagstring, args) =
           mk_instrx_data ~xprs:[xr0; xxr0] ~rdefs:rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BranchExchange (c, tgt) ->
         let xtgt = tgt#to_expr floc in
         let xxtgt = rewrite_expr xtgt in
         let rdefs = (get_rdef xtgt) :: (get_all_rdefs xxtgt) in
         let (tagstring, args) =
           mk_instrx_data ~xprs:[xtgt; xxtgt] ~rdefs () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | BranchLink _
        | BranchLinkExchange _
           when floc#has_call_target
                && floc#get_call_target#is_signature_valid ->
         callinstr_key()

      | BranchLink (_, tgt)
      | BranchLinkExchange (_, tgt) ->
         let xtgt = tgt#to_expr floc in
         let args =
           List.map (fun r -> arm_register_op r RD) [AR0; AR1; AR2; AR3] in
         let argxprs =
           List.map (fun (a: arm_operand_int) -> a#to_expr floc) args in
         let rdef = get_rdef xtgt in
         let rargxprs = List.map rewrite_expr argxprs in
         (["a:xxxxxr"],
          ((xd#index_xpr xtgt) :: (List.map xd#index_xpr rargxprs)) @ [rdef])

      | ByteReverseWord(c, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let xrmm = rewrite_expr xrm in
         let rdefs = [get_rdef xrm] @ (get_all_rdefs xrmm) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; xrmm]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | ByteReversePackedHalfword (c, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let xrmm = rewrite_expr xrm in
         let rdefs = [get_rdef xrm] @ (get_all_rdefs xrmm) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; xrmm]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Compare (c, rn, rm, _) ->
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xresult = XOp (XMinus, [xrn; xrm]) in
         let xresult = rewrite_expr xresult in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs xresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrn; xrm; xresult]
             ~rdefs:rdefs
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | CompareBranchNonzero (rn, tgt) ->
         let xrn = rn#to_expr floc in
         let xtgt = tgt#to_expr floc in
         let txpr = XOp (XNe, [xrn; int_constant_expr 0]) in
         let fxpr = XOp (XEq, [xrn; int_constant_expr 0]) in
         let tcond = rewrite_expr txpr in
         let fcond = rewrite_expr fxpr in
         let rdefs = [get_rdef xrn] @ (get_all_rdefs tcond) in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrn; txpr; fxpr; tcond; fcond; xtgt]
             ~rdefs:rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"], args) in
         (tags, args)

      | CompareBranchZero (rn, tgt) ->
         let xrn = rn#to_expr floc in
         let xtgt = tgt#to_expr floc in
         let txpr = XOp (XEq, [xrn; int_constant_expr 0]) in
         let fxpr = XOp (XNe, [xrn; int_constant_expr 0]) in
         let tcond = rewrite_expr txpr in
         let fcond = rewrite_expr fxpr in
         let rdefs = [get_rdef xrn] @ (get_all_rdefs tcond) in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrn; txpr; fxpr; tcond; fcond; xtgt]
             ~rdefs:rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"], args) in
         (tags, args)

      | CompareNegative (c, rn, rm) ->
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xresult = XOp (XPlus, [xrn; xrm]) in
         let xresult = rewrite_expr xresult in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs xresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrn; xrm; xresult]
             ~rdefs:rdefs
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | CountLeadingZeros (c, rd, rm) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let xxrm = rewrite_expr xrm in
         let rdefs = [get_rdef xrm] @ (get_all_rdefs xxrm) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; xxrm]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
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
                     let lhs = dstop#to_variable floc in
                     let rdefs = get_all_rdefs p in
                     let xp = rewrite_expr p in
                     let (tagstring, args) =
                       mk_instrx_data
                         ~vars:[lhs]
                         ~xprs:[p; xp]
                         ~rdefs:rdefs
                         ~uses:[get_def_use lhs]
                         ~useshigh:[get_def_use_high lhs]
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

      | LoadMultipleDecrementAfter (_, _, base, rl, _) ->
         let reglhss = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let (memreads, _) =
           List.fold_left
             (fun (acc, off) _reglhs ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs = memop#to_expr floc in
               (acc @ [memrhs], off + 4)) ([], 4 -(4 * regcount)) reglhss in
         let xtag =
           "a:"
           ^ (string_repeat "v" regcount)
           ^ (string_repeat "x" regcount)
           ^ "x" in    (* base expression *)
         ([xtag],
          (List.map xd#index_variable reglhss)
          @ (List.map xd#index_xpr memreads)
          @ [xd#index_xpr (base#to_expr floc)])

      | LoadMultipleDecrementBefore (_, _, base, rl, _) ->
         let reglhss = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let (memreads, _) =
           List.fold_left
             (fun (acc, off) _reglhs ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs = memop#to_expr floc in
               (acc @ [memrhs], off + 4)) ([], -(4 * regcount)) reglhss in
         let xtag =
           "a:"
           ^ (string_repeat "v" regcount)
           ^ (string_repeat "x" regcount)
           ^ "x" in    (* base expression *)
         ([xtag],
          (List.map xd#index_variable reglhss)
          @ (List.map xd#index_xpr memreads)
          @ [xd#index_xpr (base#to_expr floc)])

      | LoadMultipleIncrementAfter _ when (Option.is_some instr#is_in_aggregate) ->
         (match instr#is_in_aggregate with
          | Some va ->
             let ctxtva = (make_i_location floc#l va)#ci in
             ("a:" :: ["subsumed"; ctxtva], [])
          | _ -> (["a:"], []))

      | LoadMultipleIncrementAfter (wback, c, base, rl, _) ->
         let reglhss = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let baselhs = base#to_variable floc in
         let baserhs = base#to_expr floc in
         let regcount = rl#get_register_count in
         let (memreads, _) =
           List.fold_left
             (fun (acc, off) _reglhs ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs = memop#to_expr floc in
               (acc @ [memrhs], off + 4)) ([], 0) reglhss in
         let rdefs = List.map get_rdef (baserhs :: memreads) in
         let uses = List.map get_def_use_high (baselhs :: reglhss) in
         let useshigh = List.map get_def_use_high (baselhs :: reglhss) in
         let wbackresults =
           if wback then
             let increm = int_constant_expr (4 * regcount) in
             let baseresult = XOp (XPlus, [baserhs; increm]) in
             let rbaseresult = rewrite_expr baseresult in
             [baseresult; rbaseresult]
           else
             [baserhs; baserhs] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(baselhs :: reglhss)
             ~xprs:((baserhs :: wbackresults) @ memreads)
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | LoadMultipleIncrementBefore (_, _, base, rl, _) ->
         let reglhss = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let (memreads, _) =
           List.fold_left
             (fun (acc, off) _reglhs ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs = memop#to_expr floc in
               (acc @ [memrhs], off + 4)) ([], 4) reglhss in
         let xtag =
           "a:"
           ^ (string_repeat "v" regcount)
           ^ (string_repeat "x" regcount)
           ^ "x" in    (* base expression *)
         ([xtag],
          (List.map xd#index_variable reglhss)
          @ (List.map xd#index_xpr memreads)
          @ [xd#index_xpr (base#to_expr floc)])

      | LoadRegister _ when instr#is_aggregate_anchor ->
         let iaddr = instr#get_address in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         if agg#is_jumptable then
           let jt = agg#jumptable in
           let indexregop = jt#index_operand in
           let xrn = indexregop#to_expr floc in
           let xxrn = rewrite_expr xrn in
           let rdefs = (get_rdef xrn) :: (get_all_rdefs xxrn) in
           let (tagstring, args) =
             mk_instrx_data
               ~xprs:[xrn; xxrn]
               ~rdefs
               () in
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
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rdefs =
           [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem]
           @ (get_all_rdefs xmem) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let xrmem = rewrite_expr xmem in
         let _ = ignore (get_string_reference floc xrmem) in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let addr_r = mem#to_updated_offset_address floc in
             log_tfold_default
               (log_error "invalid write-back address" ((p2s floc#l#toPretty) ^ ": LDR"))
               (fun (inc, xaddr) -> add_base_update tags args vrn inc xaddr)
               (tags, args)
               addr_r
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterByte (c, rt, rn, rm, mem, _) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = XOp (XXlsb, [mem#to_expr floc]) in
         let xrmem = rewrite_expr xmem in
         let rdefs =
           [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem]
           @ (get_all_rdefs xmem) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let addr_r = mem#to_updated_offset_address floc in
             log_tfold_default
               (log_error
                  "invalid write-back address" ((p2s floc#l#toPretty) ^ ": LDRB"))
               (fun (inc, xaddr) -> add_base_update tags args vrn inc xaddr)
               (tags, args)
               addr_r
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
         let vrt = rt#to_variable floc in
         let vrt2 = rt2#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let vmem = mem#to_variable floc in
         let vmem2 = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let xmem2 = mem2#to_expr floc in
         let xrmem2 = rewrite_expr xmem2 in
         let xaddr1 = mem#to_address floc in
         let xaddr2 = mem#to_address floc in
         let rdefs = [
             get_rdef xrn;
             get_rdef xrm;
             get_rdef_memvar vmem;
             get_rdef_memvar vmem2] in
         let uses = [get_def_use vrt; get_def_use vrt2] in
         let useshigh = [get_def_use_high vrt; get_def_use_high vrt2] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vrt2; vmem; vmem2]
             ~xprs:[xrn; xrm; xmem; xrmem; xmem2; xrmem2; xaddr1; xaddr2]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let addr_r = mem#to_updated_offset_address floc in
             log_tfold_default
               (log_error
                  "invalid write-back address" ((p2s floc#l#toPretty) ^ ": LDRB"))
               (fun (inc, xaddr) -> add_base_update tags args vrn inc xaddr)
               (tags, args)
               addr_r
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterExclusive (c, rt, rn, rm, mem) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rdefs =
           [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem]
           @ (get_all_rdefs xmem) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let xrmem = rewrite_expr xmem in
         let _ = ignore (get_string_reference floc xrmem) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let addr_r = mem#to_updated_offset_address floc in
             log_tfold_default
               (log_error
                  "invalid write-back address" ((p2s floc#l#toPretty) ^ ": LDREX"))
               (fun (inc, xaddr) -> add_base_update tags args vrn inc xaddr)
               (tags, args)
               addr_r
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterHalfword (c, rt, rn, rm, mem, _) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let rdefs =
           [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem]
           @ (get_all_rdefs xmem) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let addr_r = mem#to_updated_offset_address floc in
             log_tfold_default
               (log_error
                  "invalid write-back address" ((p2s floc#l#toPretty) ^ ": LDRH"))
               (fun (inc, xaddr) -> add_base_update tags args vrn inc xaddr)
               (tags, args)
               addr_r
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterSignedByte (c, rt, rn, rm, mem, _) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let rdefs =
           [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem]
           @ (get_all_rdefs xmem) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let addr_r = mem#to_updated_offset_address floc in
             log_tfold_default
               (log_error
                  "invalid write-back address" ((p2s floc#l#toPretty) ^ ": LDRSB"))
               (fun (inc, xaddr) -> add_base_update tags args vrn inc xaddr)
               (tags, args)
               addr_r
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterSignedHalfword (c, rt, rn, rm, mem, _) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem] in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let addr_r = mem#to_updated_offset_address floc in
             log_tfold_default
               (log_error
                  "invalid write-back address" ((p2s floc#l#toPretty) ^ ": LDRSH"))
               (fun (inc, xaddr) -> add_base_update tags args vrn inc xaddr)
               (tags, args)
               addr_r
           else
             (tags, args) in
         (tags, args)

      | LogicalShiftLeft (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XLsl, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         let tags = add_optional_subsumption tags in
         (tags, args)

      | LogicalShiftRight (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XLsr, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Move _ when (Option.is_some instr#is_in_aggregate) ->
         (match instr#is_in_aggregate with
          | Some va ->
             let ctxtva = (make_i_location floc#l va)#ci in
             ("a:" :: ["subsumed"; ctxtva], [])
          | _ -> (["a:"], []))

      | Move(_, c, rd, rm, _, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let result = rewrite_expr ?restrict:(Some 4) xrm in
         let rdefs = (get_rdef xrm) :: (get_all_rdefs result) in
         let _ = ignore (get_string_reference floc result) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; result]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MoveRegisterCoprocessor (_, _, _, dst, _, _, _) ->
         let vdst = dst#to_variable floc in
         (["a:v"], [xd#index_variable vdst])

      | MoveToCoprocessor (_, _, _, rt, _, _, _) ->
         let src = rt#to_expr floc in
         let rsrc = rewrite_expr src in
         (["a:xx"], [xd#index_xpr src; xd#index_xpr rsrc])

      | MoveTop (c, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm = imm#to_expr floc in
         let xrd = rd#to_expr floc in
         let ximm16 = XOp (XMult, [ximm; int_constant_expr e16]) in
         let xrdm16 = XOp (XXlsh, [xrd]) in
         let result = XOp (XPlus, [xrdm16; ximm16]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrd] in
         let uses = get_def_use vrd in
         let useshigh = get_def_use_high vrd in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[ximm; xrd; xrdm16; result; rresult]
             ~rdefs:rdefs
             ~uses:[uses]
             ~useshigh:[useshigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MoveTwoRegisterCoprocessor (_, _, _, rt, rt2, _) ->
         let v1 = rt#to_variable floc in
         let v2 = rt2#to_variable floc in
         (["a:vv"], [xd#index_variable v1; xd#index_variable v2])

      | Multiply(_, c, rd, rn, rm) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XMult, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | MultiplyAccumulate (_, _, rd, rn, rm, ra) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xra = ra#to_expr floc in
         let xprd = XOp (XMult, [xrn; xrm]) in
         let xrprd = rewrite_expr xprd in
         let xrhs = XOp (XPlus, [xprd; xra]) in
         let xrrhs = rewrite_expr xrhs in
         (["a:vxxxxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr xra;
           xd#index_xpr xprd;
           xd#index_xpr xrprd;
           xd#index_xpr xrhs;
           xd#index_xpr xrrhs])

      | MultiplySubtract (_, rd, rn, rm, ra) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xra = ra#to_expr floc in
         let xprod = XOp (XMult, [xrn; xrm]) in
         let xxprod = rewrite_expr xprod in
         let xdiff = XOp (XMinus, [xra; xprod]) in
         let xxdiff = rewrite_expr xdiff in
         (["a:vxxxxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr xra;
           xd#index_xpr xprod;
           xd#index_xpr xxprod;
           xd#index_xpr xdiff;
           xd#index_xpr xxdiff])

      | Pop (c, sp, rl, _) ->
         let splhs = sp#to_variable floc in
         let sprhs = sp#to_expr floc in
         let regcount = rl#get_register_count in
         let spresult = XOp (XPlus, [sprhs; int_constant_expr (regcount * 4)]) in
         let rspresult = rewrite_expr spresult in
         let lhsvars =
           List.map (fun (op: arm_operand_int) ->
               op#to_variable floc) rl#get_register_op_list in
         let rhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset RD)
             (List.init rl#get_register_count (fun i -> 4 * i)) in
         let rhsexprs =
           List.map (fun (x: arm_operand_int) -> x#to_expr floc) rhsops in
         let xaddrs =
           List.init
             rl#get_register_count
             (fun i ->
               let xaddr = XOp (XPlus, [sprhs; int_constant_expr (i * 4)]) in
               rewrite_expr xaddr) in
         let rrhsexprs = List.map rewrite_expr rhsexprs in
         let (r0rdefs, xr0) =
           if rl#includes_pc then
             let r0_op = arm_register_op AR0 RD in
             let xr0 = r0_op#to_expr floc in
             let xxr0 = rewrite_expr xr0 in
             ([get_rdef xr0] @ (get_all_rdefs xxr0), Some xxr0)
           else
             ([], None) in
         let rdefs = List.map get_rdef (sprhs :: rhsexprs) in
         let uses = List.map get_def_use (splhs :: lhsvars) in
         let useshigh = List.map get_def_use_high (splhs :: lhsvars) in
         let xprs =
           (sprhs :: spresult :: rspresult :: rrhsexprs)
           @ xaddrs
           @ (match xr0 with Some x -> [x] | _ -> []) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(splhs :: lhsvars)
             ~xprs
             ~rdefs:(rdefs @ r0rdefs)
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | PreloadData (_, _, base, mem) ->
         let xbase = base#to_expr floc in
         let xmem = mem#to_expr floc in
         (["a:xx"], [xd#index_xpr xbase; xd#index_xpr xmem])

      | Push (c, sp, rl, _) ->
         let splhs = sp#to_variable floc in
         let sprhs = sp#to_expr floc in
         let rhsexprs =
           List.map (fun (op: arm_operand_int) ->
               op#to_expr floc) rl#get_register_op_list in
         let rrhsexprs = List.map rewrite_expr rhsexprs in
         let regcount = List.length rhsexprs in
         let lhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset WR)
             (List.init
                rl#get_register_count (fun i -> ((-4*regcount) + (4*i)))) in
         let lhsvars = List.map (fun v -> v#to_variable floc) lhsops in
         let rdefs = List.map get_rdef (sprhs :: rhsexprs) in
         let uses = List.map get_def_use (splhs :: lhsvars) in
         let useshigh = List.map get_def_use_high (splhs :: lhsvars) in
         let spresult = XOp (XMinus, [sprhs; int_constant_expr (regcount * 4)]) in
         let rspresult = rewrite_expr spresult in
         let xaddrs =
           List.init
             rl#get_register_count
             (fun i ->
               let xaddr = XOp (XPlus, [rspresult; int_constant_expr (i * 4)]) in
               rewrite_expr xaddr) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(splhs :: lhsvars)
             ~xprs:((sprhs :: spresult :: rspresult :: rrhsexprs) @ xaddrs)
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | ReverseSubtract (_, c, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XMinus, [xrm; xrn]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SignedBitFieldExtract (_, rd, rn) ->
         let lhs = rd#to_variable floc in
         let rhs = rn#to_expr floc in
         let rrhs = rewrite_expr rhs in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr rhs; xd#index_xpr rrhs])

      | SelectBytes (_, rd, rn, rm) ->
         let lhs = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr xrn; xd#index_xpr xrm])

      | SignedDivide (_, rd, rn, rm) ->
         let lhs = rd#to_variable floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         let result = XOp (XDiv, [rhs1; rhs2]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable lhs;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | SignedExtendByte (_, rd, rm, _) ->
         let lhs = rd#to_variable floc in
         let rhs = rm#to_expr floc in
         let xrhs = rewrite_expr rhs in
         (["a:vxx"], [xd#index_variable lhs; xd#index_xpr rhs; xd#index_xpr xrhs])

      | SignedExtendHalfword (_, rd, rm, _) ->
         let lhs = rd#to_variable floc in
         let rhs = rm#to_expr floc in
         let xrhs = rewrite_expr rhs in
         (["a:vxx"], [xd#index_variable lhs; xd#index_xpr rhs; xd#index_xpr xrhs])

      | SignedMostSignificantWordMultiply (_, rd, rn, rm, _) ->
         let lhs = rd#to_variable floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         let result = XOp (XMult, [rhs1; rhs2]) in
         let result = XOp (XDiv, [result; int_constant_expr e32]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable lhs;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | SignedMostSignificantWordMultiplyAccumulate (_, rd, rn, rm, ra, _) ->
         let lhs = rd#to_variable floc in
         let lhsra = ra#to_variable floc in
         let rhsra = ra#to_expr floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         let result = XOp (XMult, [rhs1; rhs2]) in
         let result = XOp (XDiv, [result; int_constant_expr e32]) in
         let rresult = rewrite_expr result in
         (["a:vvxxxxx"],
          [xd#index_variable lhs;
           xd#index_variable lhsra;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr rhsra;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | SignedMultiplyLong (_, _, rdlo, rdhi, rn, rm) ->
         let lhslo = rdlo#to_variable floc in
         let lhshi = rdhi#to_variable floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         let result = XOp (XMult, [rhs1; rhs2]) in
         let rresult = rewrite_expr result in
         (["a:vvxxxx"],
          [xd#index_variable lhslo;
           xd#index_variable lhshi;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | StoreMultipleDecrementBefore (wback, c, base, rl, _) ->
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let baselhs = base#to_variable floc in
         let baserhs = base#to_expr floc in
         let rhss = rl#to_multiple_expr floc in
         let rrhss = List.map rewrite_expr rhss in
         let (memlhss, _) =
           List.fold_left
             (fun (acc, off) _reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs = memop#to_variable floc in
               let memop1 = arm_reg_deref ~with_offset:(off+1) basereg WR in
               let memlhs1 = memop1#to_variable floc in
               let memop2 = arm_reg_deref ~with_offset:(off+2) basereg WR in
               let memlhs2 = memop2#to_variable floc in
               let memop3 = arm_reg_deref ~with_offset:(off+3) basereg WR in
               let memlhs3 = memop3#to_variable floc in
               (acc @ [memlhs; memlhs1; memlhs2; memlhs3], off + 4))
             ([], -(4 * regcount)) rl#get_register_op_list in
         let rdefs = List.map get_rdef (baserhs :: rhss) in
         let uses = List.map get_def_use_high (baselhs :: memlhss) in
         let useshigh = List.map get_def_use_high (baselhs :: memlhss) in
         let wbackresults =
           if wback then
             let decrem = int_constant_expr (4 * regcount) in
             let baseresult = XOp (XMinus, [baserhs; decrem]) in
             let rbaseresult = rewrite_expr baseresult in
             [baseresult; rbaseresult]
           else
             [baserhs; baserhs] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(baselhs :: memlhss)
             ~xprs:((baserhs :: wbackresults) @ rhss @ rrhss)
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
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
           let xsrc = srcop#to_expr srcfloc in
           let xdst = dstop#to_expr floc in
           let xxsrc = rewrite_floc_expr srcfloc xsrc in
           let xxdst = rewrite_expr ?restrict:(Some 4) xdst in
           let xxdst =
             let optmemvar = floc#decompose_memvar_address xxdst in
             match optmemvar with
             | Some (memref, memoff) ->
                let memvar =
                  floc#f#env#mk_index_offset_memory_variable memref memoff in
                XOp ((Xf "addressofvar"), [XVar memvar])
             | _ -> xxdst in
           let rdefs = [(get_rdef xsrc); (get_rdef xdst)] in
           let _ =
             match get_string_reference srcfloc xxsrc with
             | Some cstr -> register_function_prototype "strcpy"
             | _ -> register_function_prototype "memcpy" in
           let (tagstring, args) =
             mk_instrx_data
               ~xprs:[xdst; xsrc; xxdst; xxsrc]
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
         let baselhs = base#to_variable floc in
         let baserhs = base#to_expr floc in
         let regcount = rl#get_register_count in
         let rhss = rl#to_multiple_expr floc in
         let rrhss = List.map rewrite_expr rhss in
         let (memlhss, _) =
           List.fold_left
             (fun (acc, off) _reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs = memop#to_variable floc in
               (acc @ [memlhs], off + 4)) ([], 0) rl#get_register_op_list in
         let rdefs = List.map get_rdef (baserhs :: rrhss) in
         let uses = List.map get_def_use (baselhs :: memlhss) in
         let useshigh = List.map get_def_use_high (baselhs :: memlhss) in
         let wbackresults =
           if wback then
             let increm = int_constant_expr (4 * regcount) in
             let baseresult = XOp (XPlus, [baserhs; increm]) in
             let rbaseresult = rewrite_expr baseresult in
             [baseresult; rbaseresult]
           else
             [baserhs; baserhs] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(baselhs :: memlhss)
             ~xprs:((baserhs :: wbackresults) @ rrhss)
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreMultipleIncrementBefore (_, _, base, rl, _) ->
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let rhss = rl#to_multiple_expr floc in
         let rrhss = List.map rewrite_expr rhss in
         let (memlhss, _) =
           List.fold_left
             (fun (acc, off) _reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs = memop#to_variable floc in
               (acc @ [memlhs], off + 4)) ([], 4) rl#get_register_op_list in
         let xtag =
           "a:"
           ^ (string_repeat "v" regcount)
           ^ (string_repeat "x" regcount)
           ^ "x" in  (* base expression *)
         ([xtag],
          (List.map xd#index_variable memlhss)
          @ (List.map xd#index_xpr rrhss)
          @ [xd#index_xpr (base#to_expr floc)])

      | StoreRegister (c, rt, rn, rm, mem, _) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrt = rt#to_expr floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef xrt; get_rdef xxrt] in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let (vars, uses, useshigh) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             ([vmem; vrn],
               uses @ [get_def_use vrn],
               useshigh @ [get_def_use_high vrn])
           else
             ([vmem], uses, useshigh) in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_unknown ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars
             ~xprs:[xrn; xrm; xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreRegisterByte (c, rt, rn, rm, mem, _) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrt = XOp (XXlsb, [rt#to_expr floc]) in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef xrt; get_rdef xxrt] in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let (vars, uses, useshigh) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             ([vmem; vrn],
               uses @ [get_def_use vrn],
               useshigh @ [get_def_use_high vrn])
           else
             ([vmem], uses, useshigh) in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:1 ~vtype:t_unknown ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrn; xrm; xrt; xxrt; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
         let vmem = mem#to_variable floc in
         let vmem2 = mem2#to_variable floc in
         let xaddr1 = mem#to_address floc in
         let xaddr2 = mem2#to_address floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let xrt2 = rt2#to_expr floc in
         let xxrt2 = rewrite_expr xrt2 in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let rdefs = [
             get_rdef xrn;
             get_rdef xrm;
             get_rdef xrt;
             get_rdef xxrt;
             get_rdef xrt2;
             get_rdef xxrt2] in
         let uses = [get_def_use vmem; get_def_use vmem2] in
         let useshigh = [get_def_use_high vmem; get_def_use_high vmem2] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem; vmem2]
             ~xprs:[xrn; xrm; xrt; xxrt; xrt2; xxrt2; xaddr1; xaddr2]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreRegisterExclusive (c, rd, rt, rn, mem) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xrn = rn#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrn; get_rdef xrt; get_rdef xxrt] in
         let uses = [get_def_use vmem; get_def_use vrd] in
         let useshigh = [get_def_use vmem; get_def_use vrd] in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_unknown ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem; vrd]
             ~xprs:[xrn; xrt; xxrt; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | StoreRegisterHalfword (c, rt, rn, rm, mem, _) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrt = XOp (XXlsh, [rt#to_expr floc]) in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef xrt; get_rdef xxrt] in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let (vars, uses, useshigh) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             ([vmem; vrn],
               uses @ [get_def_use vrn],
               useshigh @ [get_def_use_high vrn])
           else
             ([vmem], uses, useshigh) in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:2 ~vtype:t_unknown ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars
             ~xprs:[xrn; xrm; xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | Subtract (_, c, rd, rn, rm, _, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XMinus, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let uses = get_def_use vrd in
         let usehigh = get_def_use_high vrd in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[uses]
             ~useshigh:[usehigh]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SubtractCarry (_, _, rd, rn, rm, _) ->
         let lhs = rd#to_variable floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         let result = XOp (XMinus, [rhs1; rhs2]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable lhs;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | SupervisorCall (_, _) ->
         let r7 = arm_register_op AR7 RD in
         let xr7 = r7#to_expr floc in
         (["a:x"], [xd#index_xpr xr7])

      | Swap (c, rt, rt2, rn, mem) ->
         let vrt = rt#to_variable floc in
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrt2 = rt2#to_expr floc in
         let xxrt2 = rewrite_expr xrt2 in
         let xrn = rn#to_expr floc in
         let xmem = mem#to_expr floc in
         let rdefs =
           [get_rdef xrt2; get_rdef xrn; get_rdef_memvar vmem]
           @ (get_all_rdefs xmem) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let xrmem = rewrite_expr xmem in
         let _ = ignore (get_string_reference floc xrmem) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrt2; xxrt2; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | SwapByte (c, rt, rt2, rn, mem) ->
         let vrt = rt#to_variable floc in
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrt2 = rt2#to_expr floc in
         let xxrt2 = rewrite_expr xrt2 in
         let xrn = rn#to_expr floc in
         let xmem = mem#to_expr floc in
         let rdefs =
           [get_rdef xrt2; get_rdef xrn; get_rdef_memvar vmem]
           @ (get_all_rdefs xmem) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let xrmem = rewrite_expr xmem in
         let _ = ignore (get_string_reference floc xrmem) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrt2; xxrt2; xmem; xrmem; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | TableBranchByte (_, _, rm, _) ->
         let iaddr = instr#get_address in
         let xrm = rm#to_expr floc in
         let xxrm = rewrite_expr xrm in
         let rdefs = (get_rdef xrm) :: (get_all_rdefs xxrm) in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrm; xxrm]
             ~rdefs
             () in
         let tags = tagstring :: ["agg-jt"] in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         let tags = add_subsumption_dependents agg tags in
         (tags, args)

      | TableBranchHalfword (_, _, rm, _) ->
         let iaddr = instr#get_address in
         let xrm = rm#to_expr floc in
         let xxrm = rewrite_expr xrm in
         let rdefs = (get_rdef xrm) :: (get_all_rdefs xxrm) in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrm; xxrm]
             ~rdefs
             () in
         let tags = tagstring :: ["agg-jt"] in
         let agg = (!arm_assembly_instructions)#get_aggregate iaddr in
         let tags = add_subsumption_dependents agg tags in
         (tags, args)

      | Test (_, rn, rm, _) ->
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         (["a:xx"], [xd#index_xpr xrn; xd#index_xpr xrm])

      | UnsignedDivide (_, rd, rn, rm) ->
         let lhs = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr xrn; xd#index_xpr xrm])

      | UnsignedAdd8 (_, rd, rn, rm) ->
         let lhs = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr xrn; xd#index_xpr xrm])

      | UnsignedBitFieldExtract (c, rd, rn) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xxrn = rewrite_expr xrn in
         let rdefs = [get_rdef xrn] @ (get_all_rdefs xxrn) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xxrn]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | UnsignedExtendAddByte (_, rd, rn, rm) ->
         let lhs = rd#to_variable floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr rhs1; xd#index_xpr rhs2])

      | UnsignedExtendAddHalfword (_, rd, rn, rm) ->
         let lhs = rd#to_variable floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr rhs1; xd#index_xpr rhs2])

      | UnsignedExtendByte (c, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = XOp (XXlsb, [rm#to_expr floc]) in
         let result = xrm in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedExtendHalfword (c, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XXlsh, [xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedMultiplyAccumulateLong (_, _, rdlo, rdhi, rn, rm) ->
         let lhslo = rdlo#to_variable floc in
         let lhshi = rdhi#to_variable floc in
         let rhs1 = rn#to_expr floc in
         let rhs2 = rm#to_expr floc in
         let result = XOp (XMult, [rhs1; rhs2]) in
         let rresult = rewrite_expr result in
         (["a:vvxxxx"],
          [xd#index_variable lhslo;
           xd#index_variable lhshi;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | UnsignedMultiplyLong (_, c, rdlo, rdhi, rn, rm) ->
         let vlo = rdlo#to_variable floc in
         let vhi = rdhi#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XMult, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vlo; vhi]
             ~xprs:[xrn; xrm; result; rresult]
             ~rdefs:rdefs
             ~uses:[get_def_use vlo; get_def_use vhi]
             ~useshigh:[get_def_use_high vlo; get_def_use_high vhi]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedSaturate (c, rd, imm, rn) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let ximm = imm#to_expr floc in
         let rdefs = [get_rdef xrn] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[ximm; xrn]
             ~rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | UnsignedSaturatingSubtract8 (c, rd, rn, rm) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let rdefs = [get_rdef xrn; get_rdef xrm] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrn; xrm]
             ~rdefs
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorAbsolute (c, _, dst, src) ->
         let vdst = dst#to_variable floc in
         let xsrc = src#to_expr floc in
         let rxsrc = rewrite_expr xsrc in
         let rdefs = [get_rdef xsrc] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc; rxsrc]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VCompare (_, c, _, fdst, src1, src2) ->
         let v_fpscr = fdst#to_variable floc in
         let xsrc1 = src1#to_expr floc in
         let xsrc2 = src2#to_expr floc in
         let rxsrc1 = rewrite_expr xsrc1 in
         let rxsrc2 = rewrite_expr xsrc2 in
         let rdefs = [get_rdef xsrc1; get_rdef xsrc2] in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xsrc1; xsrc2; rxsrc1; rxsrc2]
             ~rdefs:rdefs
             ~uses:[get_def_use v_fpscr]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorConvert (_, _, c, _, _, dst, src, _) ->
         let vdst = dst#to_variable floc in
         let xsrc = src#to_expr floc in
         let rxsrc = rewrite_expr xsrc in
         let rdefs = [get_rdef xsrc] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc; rxsrc]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VDivide (c, _, dst, src1, src2) ->
         let vdst = dst#to_variable floc in
         let xsrc1 = src1#to_expr floc in
         let xsrc2 = src2#to_expr floc in
         let rxsrc1 = rewrite_expr xsrc1 in
         let rxsrc2 = rewrite_expr xsrc2 in
         let rdefs = [get_rdef xsrc1; get_rdef xsrc2] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc1; xsrc2; rxsrc1; rxsrc2]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorDuplicate (_, _, _, _, _, src) ->
         let src = src#to_expr floc in
         let rsrc = rewrite_expr src in
         (["a:xx"], [xd#index_xpr src; xd#index_xpr rsrc])

      | VLoadRegister (c, vd, base, mem) ->
         let vvd = vd#to_variable floc in
         let xbase = base#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rxbase = rewrite_expr xbase in
         let rxmem = rewrite_expr xmem in
         let rdefs = [get_rdef_memvar vmem; get_rdef xmem] @ (get_all_rdefs rxmem) in
         let uses = [get_def_use_high vvd] in
         let useshigh = [get_def_use_high vvd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vvd; vmem]
             ~xprs:[xmem; rxmem; xbase; rxbase; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDS (c, _, dst, src) ->
         let vdst = dst#to_variable floc in
         let xsrc = src#to_expr floc in
         let rxsrc = rewrite_expr xsrc in
         let rdefs = [get_rdef xsrc] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc; rxsrc]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDDSS (c, _, dst1, dst2, ddst, src1, src2, ssrc) ->
         let vdst1 = dst1#to_variable floc in
         let vdst2 = dst2#to_variable floc in
         let vddst = ddst#to_variable floc in
         let xsrc1 = src1#to_expr floc in
         let xsrc2 = src2#to_expr floc in
         let xssrc = ssrc#to_expr floc in
         let rxsrc1 = rewrite_expr xsrc1 in
         let rxsrc2 = rewrite_expr xsrc2 in
         let rxssrc = rewrite_expr xssrc in
         let rdefs = [get_rdef xsrc1; get_rdef xsrc2; get_rdef xssrc] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst1; vdst2; vddst]
             ~xprs:[xsrc1; xsrc2; xssrc; rxsrc1; rxsrc2; rxssrc]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst1; get_def_use vdst2; get_def_use vddst]
             ~useshigh:[
               get_def_use_high vdst1;
               get_def_use_high vdst2;
               get_def_use_high vddst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDSS (c, _, dst, src1, src2, ssrc) ->
         let vdst = dst#to_variable floc in
         let xsrc1 = src1#to_expr floc in
         let xsrc2 = src2#to_expr floc in
         let xssrc = ssrc#to_expr floc in
         let rxsrc1 = rewrite_expr xsrc1 in
         let rxsrc2 = rewrite_expr xsrc2 in
         let rxssrc = rewrite_expr xssrc in
         let rdefs = [get_rdef xsrc1; get_rdef xsrc2; get_rdef xssrc] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc1; xsrc2; xssrc; rxsrc1; rxsrc2; rxssrc]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorMoveDDS (c, _, dst1, dst2, ddst, src) ->
         let vdst1 = dst1#to_variable floc in
         let vdst2 = dst2#to_variable floc in
         let vddst = ddst#to_variable floc in
         let xsrc = src#to_expr floc in
         let rxsrc = rewrite_expr xsrc in
         let rdefs = [get_rdef xsrc] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst1; vdst2; vddst]
             ~xprs:[xsrc; rxsrc]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst1; get_def_use vdst2; get_def_use vddst]
             ~useshigh:[
               get_def_use_high vdst1;
               get_def_use_high vdst2;
               get_def_use_high vddst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VMoveRegisterStatus (c, dst, src) ->
         let vdst = dst#to_variable floc in
         let xsrc = src#to_expr floc in
         let rdefs = [get_rdef xsrc] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VMoveToSystemRegister (_, _, src) ->
         let xsrc = src#to_expr floc in
         (["a:x"], [xd#index_xpr xsrc])

      | VectorMultiplySubtract (c, _, dst, src1, src2) ->
         let vdst = dst#to_variable floc in
         let xdst = dst#to_expr floc in
         let rxdst = rewrite_expr xdst in
         let xsrc1 = src1#to_expr floc in
         let rxsrc1 = rewrite_expr xsrc1 in
         let xsrc2 = src2#to_expr floc in
         let rxsrc2 = rewrite_expr xsrc2 in
         let rdefs = [get_rdef xsrc1; get_rdef xsrc2; get_rdef xdst] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc1; xsrc2; xdst; rxsrc1; rxsrc2; rxdst]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorPop (c, sp, rl, _) ->
         let splhs = sp#to_variable floc in
         let sprhs = sp#to_expr floc in
         let regcount = rl#get_register_count in
         let regsize =
           if rl#is_double_extension_register_list then 8 else 4 in
         let spresult =
           XOp (XPlus, [sprhs; int_constant_expr (regcount * regsize)]) in
         let rspresult = rewrite_expr spresult in
         let lhsvars =
           List.map (fun (op: arm_operand_int) ->
               op#to_variable floc) rl#get_extension_register_op_list in
         let rhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset RD)
             (List.init rl#get_register_count (fun i -> regsize * i)) in
         let rhsexprs =
           List.map (fun (x: arm_operand_int) -> x#to_expr floc) rhsops in
         let xaddrs =
           List.init
             regcount
             (fun i ->
               let xaddr =
                 XOp (XPlus, [sprhs; int_constant_expr (i * regsize)]) in
               rewrite_expr xaddr) in
         let rrhsexprs = List.map rewrite_expr rhsexprs in
         let rdefs = List.map get_rdef (sprhs :: rhsexprs) in
         let uses = List.map get_def_use (splhs :: lhsvars) in
         let useshigh = List.map get_def_use_high (splhs :: lhsvars) in
         let xprs = (sprhs :: spresult :: rspresult :: rrhsexprs) @ xaddrs in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(splhs :: lhsvars)
             ~xprs
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorPush (c, sp, rl, _) ->
         let splhs = sp#to_variable floc in
         let sprhs = sp#to_expr floc in
         let rhsexprs =
           List.map (fun (op: arm_operand_int) ->
               op#to_expr floc) rl#get_extension_register_op_list in
         let rrhsexprs = List.map rewrite_expr rhsexprs in
         let regcount = List.length rhsexprs in
         let regsize =
           if rl#is_double_extension_register_list then 8 else 4 in
         let lhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset WR)
             (List.init
                regcount (fun i -> ((- regsize * regcount) + (regsize * i)))) in
         let lhsvars = List.map (fun v -> v#to_variable floc) lhsops in
         let rdefs = List.map get_rdef (sprhs :: rhsexprs) in
         let uses = List.map get_def_use (splhs :: lhsvars) in
         let useshigh = List.map get_def_use_high (splhs :: lhsvars) in
         let spresult =
           XOp (XMinus, [sprhs; int_constant_expr (regcount * regsize)]) in
         let rspresult = rewrite_expr spresult in
         let xaddrs =
           List.init
             regcount
             (fun i ->
               let xaddr =
                 XOp (XPlus, [rspresult; int_constant_expr (i * regsize)]) in
               rewrite_expr xaddr) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(splhs :: lhsvars)
             ~xprs:((sprhs :: spresult :: rspresult :: rrhsexprs) @ xaddrs)
             ~rdefs
             ~uses
             ~useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VStoreRegister (c, src, base, mem) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xsrc = src#to_expr floc in
         let xbase = base#to_expr floc in
         let rxsrc = rewrite_expr xsrc in
         let rxbase = rewrite_expr xbase in
         let rdefs = [get_rdef xsrc; get_rdef xbase] in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xsrc; rxsrc; xbase; rxbase; xaddr]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) = add_optional_instr_condition tagstring args c in
         (tags, args)

      | VectorSubtract (c, _, dst, src1, src2) ->
         let vdst = dst#to_variable floc in
         let xdst = dst#to_expr floc in
         let rxdst = rewrite_expr xdst in
         let xsrc1 = src1#to_expr floc in
         let rxsrc1 = rewrite_expr xsrc1 in
         let xsrc2 = src2#to_expr floc in
         let rxsrc2 = rewrite_expr xsrc2 in
         let rdefs = [get_rdef xsrc1; get_rdef xsrc2] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vdst]
             ~xprs:[xsrc1; xsrc2; xdst; rxsrc1; rxsrc2; rxdst]
             ~rdefs:rdefs
             ~uses:[get_def_use vdst]
             ~useshigh:[get_def_use_high vdst]
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
         LBLOCK [STR "Error in writing xml instruction: ";
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
