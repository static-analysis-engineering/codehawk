(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs LLC

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
open BCHDoubleword
open BCHFloc
open BCHLibTypes
open BCHLocation

(* bchlibpower32 *)
open BCHPowerAssemblyInstructions
open BCHPowerDisassemblyUtils
open BCHPowerOperand
open BCHPowerTypes


module B = Big_int_Z
module H = Hashtbl
module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr

let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("FnPowerDictionary:"^ tag) msg


let _bd = BCHDictionary.bdictionary
let ixd = BCHInterfaceDictionary.interface_dictionary


class pwr_opcode_dictionary_t
        (_faddr: doubleword_int)
        (vard: vardictionary_int): pwr_opcode_dictionary_int =
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
    let (_tags, args) = sp_offset_table#retrieve index in
    let a = a "sp-offset" args in
    (a 0, xd#get_interval (a 1))

  (* Legend for tags:
     "nop": instruction is no-op,
     "save": saving a register to the stack,
     "a:" (prefix,arg-key) (if present should be first):
          a: address xpr; x: xpr; v: variable ; l: literal int ; s: string
   *)

  method index_instr
           (instr: pwr_assembly_instruction_int)
           (floc: floc_int) =
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
          | [vinv] -> vinv#index
          | _ -> -1)
      | _ -> -1 in

    let get_all_rdefs (xpr: xpr_t): int list =
      let vars = variables_in_expr xpr in
      List.fold_left (fun acc v ->
          let symvar = floc#env#mk_symbolic_variable v in
          let varinvs = varinv#get_var_reaching_defs symvar in
          (List.map (fun vinv -> vinv#index) varinvs) @ acc) [] vars in

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

    let mk_instrx_data
          ?(vars: variable_t list = [])
          ?(xprs: xpr_t list = [])
          ?(rdefs: int list = [])
          ?(uses: int list = [])
          ?(useshigh: int list = [])
          () =
      let varcount = List.length vars in
      let xprcount = List.length xprs in
      let rdefcount = List.length rdefs in
      let defusecount = List.length uses in
      let defusehighcount = List.length useshigh in
      let varstring = string_repeat "v" varcount in
      let xprstring = string_repeat "x" xprcount in
      let rdefstring = string_repeat "r" rdefcount in
      let defusestring = string_repeat "d" defusecount in
      let defusehighstring = string_repeat "h" defusehighcount in
      let tagstring =
        "a:"
        ^ varstring
        ^ xprstring
        ^ rdefstring
        ^ defusestring
        ^ defusehighstring in
      let varargs = List.map xd#index_variable vars in
      let xprargs = List.map xd#index_xpr xprs in
      (tagstring, varargs @ xprargs @ rdefs @ uses @ useshigh) in

    let key =
      match instr#get_opcode with
      | Add (_, _, _, rd, ra, rb, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xrb = rb#to_expr floc in
         let rhs = XOp (XPlus, [xra; xrb]) in
         let rrhs = rewrite_expr rhs in
         let rdefs = [get_rdef xra; get_rdef xrb] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xra; xrb; rhs; rrhs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | AddImmediate (_, _, _, _, _, rd, ra, simm, _) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xsimm = simm#to_expr floc in
         let rhs = XOp (XPlus, [xra; xsimm]) in
         let rrhs = rewrite_expr rhs in
         let _ = ignore (get_string_reference floc rrhs) in
         let rdefs = [get_rdef xra] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xra; xsimm; rhs; rrhs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | BranchLink _
           when floc#has_call_target
                && floc#get_call_target#is_signature_valid ->
         let args = List.map snd floc#get_call_arguments in
         let rdefs = List.concat (List.map get_all_rdefs args) in
         let regargs =
           List.map
             floc#f#env#mk_pwr_gp_register_variable
             (List.init (List.length args) (fun i -> i + 3)) in
         let regrdefs = List.map (fun r -> get_rdef (XVar r)) regargs in
         let vrd = (pwr_gp_register_op ~index:3 ~mode:WR)#to_variable floc in
         let rv = floc#env#mk_return_value floc#cia in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[rv]
             ~xprs:args
             ~rdefs:(rdefs @ regrdefs)
             ~uses:[get_def_use vrd]
             ~useshigh:[get_def_use_high vrd]
             () in
         let tags = tagstring :: ["call"] in
         let args =
           args @ [ixd#index_call_target floc#get_call_target#get_target] in
         (tags, args)

      | CBranchEqual (_, _, _, _, _, _, bd)
           when bd#is_absolute_address && floc#has_test_expr ->
         let xtgt = bd#to_expr floc in
         let txpr = floc#get_test_expr in
         let fxpr = XOp (XLNot, [txpr]) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
         let instr =
           fail_tvalue
             (trerror_record
                (LBLOCK [STR "Internal error in FnPowerDictionary:beq"]))
             (get_pwr_assembly_instruction
                (fail_tvalue
                   (trerror_record
                      (LBLOCK [STR "FnPowerDictionary:beq: "; STR csetter]))
                   (string_to_doubleword csetter))) in
         let bytestr = instr#get_bytes_as_hexstring in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond; xtgt]
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         (tags, args)

      | CBranchGreaterThan (_, _, _, _, _, _, bd)
           when bd#is_absolute_address && floc#has_test_expr ->
         let xtgt = bd#to_expr floc in
         let txpr = floc#get_test_expr in
         let fxpr = XOp (XLNot, [txpr]) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
         let instr =
           fail_tvalue
             (trerror_record
                (LBLOCK [STR "Internal error in FnPowerDictionary:bgt"]))
             (get_pwr_assembly_instruction
                (fail_tvalue
                   (trerror_record
                      (LBLOCK [STR "FnPowerDictionary:bgt: "; STR csetter]))
                   (string_to_doubleword csetter))) in
         let bytestr = instr#get_bytes_as_hexstring in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond; xtgt]
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         (tags, args)

      | CBranchLessEqual (_, _, _, _, _, _, bd)
           when bd#is_absolute_address && floc#has_test_expr ->
         let xtgt = bd#to_expr floc in
         let txpr = floc#get_test_expr in
         let fxpr = XOp (XLNot, [txpr]) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
         let instr =
           fail_tvalue
             (trerror_record
                (LBLOCK [STR "Internal error in FnPowerDictionary:ble"]))
             (get_pwr_assembly_instruction
                (fail_tvalue
                   (trerror_record
                      (LBLOCK [STR "FnPowerDictionary:ble: "; STR csetter]))
                   (string_to_doubleword csetter))) in
         let bytestr = instr#get_bytes_as_hexstring in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond; xtgt]
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         (tags, args)

      | CBranchLessThan (_, _, _, _, _, _, bd)
           when bd#is_absolute_address && floc#has_test_expr ->
         let xtgt = bd#to_expr floc in
         let txpr = floc#get_test_expr in
         let fxpr = XOp (XLNot, [txpr]) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
         let instr =
           fail_tvalue
             (trerror_record
                (LBLOCK [STR "Internal error in FnPowerDictionary:blt"]))
             (get_pwr_assembly_instruction
                (fail_tvalue
                   (trerror_record
                      (LBLOCK [STR "FnPowerDictionary:blt: "; STR csetter]))
                   (string_to_doubleword csetter))) in
         let bytestr = instr#get_bytes_as_hexstring in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond; xtgt]
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         (tags, args)

      | CBranchNotEqual (_, _, _, _, _, _, bd)
           when bd#is_absolute_address && floc#has_test_expr ->
         let xtgt = bd#to_expr floc in
         let txpr = floc#get_test_expr in
         let fxpr = XOp (XLNot, [txpr]) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let tcond = rewrite_test_expr csetter txpr in
         let fcond = rewrite_test_expr csetter fxpr in
         let instr =
           fail_tvalue
             (trerror_record
                (LBLOCK [STR "Internal error in FnPowerDictionary:bne"]))
             (get_pwr_assembly_instruction
                (fail_tvalue
                   (trerror_record
                      (LBLOCK [STR "FnPowerDictionary:bne: "; STR csetter]))
                   (string_to_doubleword csetter))) in
         let bytestr = instr#get_bytes_as_hexstring in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond; xtgt]
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         (tags, args)

      | ClearLeftWordImmediate (_, _, ra, rs, mb) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xmb = mb#to_expr floc in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vra] in
         let useshigh = [get_def_use_high vra] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; rxrs; xmb]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | DivideWordUnsigned (_, _, _, rd, ra, rb, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xrb = rb#to_expr floc in
         let xrhs = XOp (XDiv, [xra; xrb]) in
         let rxrhs = rewrite_expr xrhs in
         let rdefs = [get_rdef xra; get_rdef xrb] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xra; xrb; xrhs; rxrhs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | ExtendSignHalfword (_, _, ra, rs, _) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vra] in
         let useshigh = [get_def_use_high vra] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; rxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | ExtractRightJustifyWordImmediate (_, _, ra, rs, n, b, _) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xn = n#to_expr floc in
         let xb = b#to_expr floc in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vra] in
         let useshigh = [get_def_use_high vra] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; rxrs; xn; xb]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadImmediate (_, _, shifted, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm =
           if shifted then
             imm#to_shifted_expr 16
           else
             imm#to_expr floc in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[ximm]
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadByteZero (_, update, rd, ra, mem) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rxmem = rewrite_expr xmem in
         let rdefs = [get_rdef xra; get_rdef_memvar vmem] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (upduses, updhigh) =
           if update then
             let vra = ra#to_variable floc in
             let uses = [get_def_use vra] in
             let useshigh = [get_def_use_high vra] in
             (uses, useshigh)
           else
             ([], []) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd; vmem]
             ~xprs:[xra; xmem; rxmem; xaddr]
             ~rdefs
             ~uses:(uses @ upduses)
             ~useshigh:(useshigh @ updhigh)
             () in
         ([tagstring], args)

      | LoadHalfwordZero (_, update, rd, ra, mem) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rxmem = rewrite_expr xmem in
         let rdefs = [get_rdef xra; get_rdef_memvar vmem] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (upduses, updhigh) =
           if update then
             let vra = ra#to_variable floc in
             let uses = [get_def_use vra] in
             let useshigh = [get_def_use_high vra] in
             (uses, useshigh)
           else
             ([], []) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd; vmem]
             ~xprs:[xra; xmem; rxmem; xaddr]
             ~rdefs
             ~uses:(uses @ upduses)
             ~useshigh:(useshigh @ updhigh)
             () in
         ([tagstring], args)

      | LoadWordZero (_, update, rd, ra, mem) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rxmem = rewrite_expr xmem in
         let rdefs = [get_rdef xra; get_rdef_memvar vmem] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (upduses, updhigh) =
           if update then
             let vra = ra#to_variable floc in
             let uses = [get_def_use vra] in
             let useshigh = [get_def_use_high vra] in
             (uses, useshigh)
           else
             ([], []) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd; vmem]
             ~xprs:[xra; xmem; rxmem; xaddr]
             ~rdefs
             ~uses:(uses @ upduses)
             ~useshigh:(useshigh @ updhigh)
             () in
         ([tagstring], args)

      | MoveFromLinkRegister (_, rd, lr) ->
         let vrd = rd#to_variable floc in
         let xlr = lr#to_expr floc in
         let rxlr = rewrite_expr xlr in
         let rdefs = [get_rdef xlr] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xlr; rxlr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveRegister (_, _, rd, rs) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; rxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveToLinkRegister (_, lr, rs) ->
         let vlr = lr#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vlr] in
         let useshigh = [get_def_use_high vlr] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vlr]
             ~xprs:[xrs; rxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | Or (_, _, ra, rs, rb, _) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrb = rb#to_expr floc in
         let xrhs = XOp (XBOr, [xrs; xrb]) in
         let rxrhs = rewrite_expr xrhs in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vra] in
         let useshigh = [get_def_use_high vra] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; xrb; xrhs; rxrhs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | OrImmediate (_, _, shifted, _, ra, rs, uimm, _) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let xuimm =
           if shifted then
             uimm#to_shifted_expr 16
           else
             uimm#to_expr floc in
         let xrhs = XOp (XBOr, [xrs; xuimm]) in
         let rxrhs = rewrite_expr xrhs in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vra] in
         let useshigh = [get_def_use_high vra] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; xuimm; xrhs; rxrhs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | RotateLeftWordImmediateAndMask (_, _, ra, rs, sh, mb, me, _) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xsh = sh#to_expr floc in
         let xmb = mb#to_expr floc in
         let xme = me#to_expr floc in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vra] in
         let useshigh = [get_def_use_high vra] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; rxrs; xsh; xmb; xme]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | ShiftLeftWordImmediate (_, _, ra, rs, sh, _) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xsh = sh#to_expr floc in
         let rdefs = [get_rdef xrs] in
         let uses = [get_def_use vra] in
         let useshigh = [get_def_use_high vra] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; rxrs; xsh]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreByte (_, update, rs, ra, mem) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xra = ra#to_expr floc in
         let rxra = rewrite_expr xra in
         let rdefs = [get_rdef xrs; get_rdef xra] in
         if update then
           let vra = ra#to_variable floc in
           let uses = [get_def_use vmem; get_def_use vra] in
           let useshigh = [get_def_use_high vmem; get_def_use_high vra] in
           let (tagstring, args) =
             mk_instrx_data
               ~vars:[vmem; vra]
               ~xprs:[xrs; rxrs; xra; rxra; xaddr]
               ~rdefs
               ~uses
               ~useshigh
               () in
           ([tagstring], args)
         else
           let uses = [get_def_use vmem] in
           let useshigh = [get_def_use_high vmem] in
           let (tagstring, args) =
             mk_instrx_data
               ~vars:[vmem]
               ~xprs:[xrs; rxrs; xra; rxra; xaddr]
               ~rdefs
               ~uses
               ~useshigh
               () in
           ([tagstring], args)

      | StoreHalfword (_, update, rs, ra, mem) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xra = ra#to_expr floc in
         let rxra = rewrite_expr xra in
         let rdefs = [get_rdef xrs; get_rdef xra] in
         if update then
           let vra = ra#to_variable floc in
           let uses = [get_def_use vmem; get_def_use vra] in
           let useshigh = [get_def_use_high vmem; get_def_use_high vra] in
           let (tagstring, args) =
             mk_instrx_data
               ~vars:[vmem; vra]
               ~xprs:[xrs; rxrs; xra; rxra; xaddr]
               ~rdefs
               ~uses
               ~useshigh
               () in
           ([tagstring], args)
         else
           let uses = [get_def_use vmem] in
           let useshigh = [get_def_use_high vmem] in
           let (tagstring, args) =
             mk_instrx_data
               ~vars:[vmem]
               ~xprs:[xrs; rxrs; xra; rxra; xaddr]
               ~rdefs
               ~uses
               ~useshigh
               () in
           ([tagstring], args)

      | StoreWord (_, update, rs, ra, mem) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xra = ra#to_expr floc in
         let rxra = rewrite_expr xra in
         let rdefs = [get_rdef xrs; get_rdef xra] in
         if update then
           let vra = ra#to_variable floc in
           let uses = [get_def_use vmem; get_def_use vra] in
           let useshigh = [get_def_use_high vmem; get_def_use_high vra] in
           let (tagstring, args) =
             mk_instrx_data
               ~vars:[vmem; vra]
               ~xprs:[xrs; rxrs; xra; rxra; xaddr]
               ~rdefs
               ~uses
               ~useshigh
               () in
           ([tagstring], args)
         else
           let uses = [get_def_use vmem] in
           let useshigh = [get_def_use_high vmem] in
           let (tagstring, args) =
             mk_instrx_data
               ~vars:[vmem]
               ~xprs:[xrs; rxrs; xra; rxra; xaddr]
               ~rdefs
               ~uses
               ~useshigh
               () in
           ([tagstring], args)

      | SubtractFrom (_, _, _, rd, ra, rb, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xrb = rb#to_expr floc in
         let xrhs = XOp (XMinus, [xrb; xra]) in
         let rxrhs = rewrite_expr xrhs in
         let rdefs = [get_rdef xra; get_rdef xrb] in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xra; xrb; xrhs; rxrhs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | _ -> ([], []) in
    instrx_table#add key

  method write_xml_sp_offset
           ?(tag="isp") (node: xml_element_int) (o: int * interval_t) =
    node#setIntAttribute tag (self#index_sp_offset o)

  method write_xml_instr
           ?(tag="iopx")
           (node: xml_element_int)
           (instr: pwr_assembly_instruction_int)
           (floc: floc_int) =
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

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end


let mk_pwr_opcode_dictionary = new pwr_opcode_dictionary_t
