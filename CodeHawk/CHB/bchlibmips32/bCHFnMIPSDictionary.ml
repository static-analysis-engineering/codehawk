(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
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
open Xsimplify

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHBCTypeUtil
open BCHByteUtilities
open BCHConstantDefinitions
open BCHCPURegisters
open BCHFloc
open BCHFunctionInterface
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo

(* bchlibelf *)
open BCHELFHeader

(* bchlibmips32 *)
open BCHMIPSAssemblyInstructions
open BCHMIPSDictionary
open BCHMIPSDisassemblyUtils
open BCHMIPSLoopStructure
open BCHMIPSOperand
open BCHMIPSOpcodeRecords
open BCHMIPSTypes



module B = Big_int_Z
module H = Hashtbl

let x2p = xpr_formatter#pr_expr

let bd = BCHDictionary.bdictionary
let ixd = BCHInterfaceDictionary.interface_dictionary

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let get_multiplier (n:numerical_t) =
  int_constant_expr (pow 2 n#toInt)


class mips_opcode_dictionary_t
        (faddr:doubleword_int)
        (vard:vardictionary_int):mips_opcode_dictionary_int =
object (self)

  val sp_offset_table = mk_index_table "sp-offset-table"
  val instrx_table = mk_index_table "instrx-table"
  val xd = vard#xd

  val mutable tables = []

  initializer
    tables <- [
      sp_offset_table ;
      instrx_table
    ]

  method index_sp_offset (o:(int * interval_t)) =
    let (level,offset) = o in
    let key = ([],[ level ; xd#index_interval offset ]) in
    sp_offset_table#add key

  method get_sp_offset (index:int) =
    let (tags,args) = sp_offset_table#retrieve index in
    let a = a "sp-offset" args in
    (a 0, xd#get_interval (a 1))

  (* Legend for tags:
     "nop": instruction is no-op,
     "save": saving a register to the stack,
     "a:" (prefix,arg-key) (if present should be first):
          a: address xpr; x: xpr; v: variable ; l: literal int ; s: string
   *)

  method index_instr
           (instr:mips_assembly_instruction_int)
           (floc:floc_int)
           (restriction:block_restriction_t option) =
    let varinv = floc#varinv in
    let rewrite_expr x:xpr_t =
      try
        let rec expand x =
          match x with
          | XVar v
               when floc#env#is_global_variable v
                    && elf_header#is_program_address
                         (floc#env#get_global_variable_address v) ->
             num_constant_expr
               (elf_header#get_program_value
                  (floc#env#get_global_variable_address v))#to_numerical
          | XVar v when floc#env#is_symbolic_value v ->
             expand (floc#env#get_symbolic_value_expr v)
          | XOp (op,l) -> XOp (op, List.map expand l)
          | _ -> x in
        let xpr =
          floc#inv#rewrite_expr (expand x) floc#env#get_variable_comparator in
        simplify_xpr (expand xpr)
      with IO.No_more_input ->
        begin
          pr_debug [ STR "Error in rewriting expression: " ; x2p x ;
                     STR ": No more input"; NL ];
          raise IO.No_more_input
        end in

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
      let vars = floc#env#variables_in_expr xpr in
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
      let ssavalues = floc#ssa_register_values in
      let varcount = List.length vars in
      let xprcount = List.length xprs in
      let rdefcount = List.length rdefs in
      let defusecount = List.length uses in
      let defusehighcount = List.length useshigh in
      let ssacount = List.length ssavalues in
      let varstring = string_repeat "v" varcount in
      let xprstring = string_repeat "x" xprcount in
      let rdefstring = string_repeat "r" rdefcount in
      let defusestring = string_repeat "d" defusecount in
      let defusehighstring = string_repeat "h" defusehighcount in
      let ssastring = string_repeat "c" ssacount in
      let tagstring =
        "a:"
        ^ varstring
        ^ xprstring
        ^ rdefstring
        ^ defusestring
        ^ defusehighstring
        ^ ssastring in
      let varargs = List.map xd#index_variable vars in
      let xprargs = List.map xd#index_xpr xprs in
      let ssaargs = List.map xd#index_variable ssavalues in
      (tagstring,
       varargs @ xprargs @ rdefs @ uses @ useshigh @ ssaargs) in

    let get_condition_exprs thenxpr elsexpr =
      match restriction with
      | Some (BranchAssert false) -> (false_constant_expr, elsexpr)
      | Some (BranchAssert true) -> (thenxpr, false_constant_expr)
      | _ -> (thenxpr, elsexpr) in

    let key =
      match instr#get_opcode with
      | Add (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XPlus, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh () in
         ([tagstring], args)

      | AddImmediate (rt, rs, imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XPlus, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh () in
         ([tagstring], args)

      | AddUpperImmediate (rt, rs, imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm =
           num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
         let result = XOp (XPlus, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh () in
         ([tagstring], args)

      | AddImmediateUnsigned (rt, rs, imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XPlus, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh () in
         ([tagstring], args)

      | AddUnsigned (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XPlus, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh () in
         ([tagstring], args)

      | And (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XBAnd, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | AndImmediate (rt, rs, imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XBAnd, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | BranchEqual (rs, rt, offset) ->
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XEq, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrs; xrt; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchEqualLikely (rs, rt, offset) ->
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XEq, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrs; xrt; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchGEZero (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XGe, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchGEZeroLikely (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XGe, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchGEZeroLink (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XGe, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchGTZero (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XGt, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchGTZeroLikely (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XGt, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchLEZero (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XLe, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchLEZeroLikely (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XLe, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchLTZero (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XLt, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchLTZeroLikely (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XLt, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchLTZeroLink (rs, offset) ->
         let xrs = rs#to_expr floc in
         let result = XOp (XLt, [xrs; zero_constant_expr]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data  ~xprs:[xrs; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchNotEqual (rs, rt, offset) ->
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XNe, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrs; xrt; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | BranchNotEqualLikely (rs, rt, offset) ->
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XNe, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [rresult])) in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let (rresult, negresult) = get_condition_exprs rresult negresult in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[xrs; xrt; result; rresult; negresult] ~rdefs () in
         ([tagstring], args)

      | CountLeadingZeros (rd, rs) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | DivideWord (hi, lo, rs, rt) ->
         let vhi = hi#to_variable floc in
         let vlo = lo#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let resultlo = XOp (XDiv, [xrs; xrt]) in
         let resulthi = XOp (XMod, [xrs; xrt]) in
         let rresultlo = rewrite_expr resultlo in
         let rresulthi = rewrite_expr resulthi in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresultlo) in
         let uses = [get_def_use vhi; get_def_use vlo] in
         let useshigh = [get_def_use_high vhi; get_def_use_high vlo] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vlo; vhi]
             ~xprs:[xrs; xrt; resultlo; resulthi; rresultlo; rresulthi]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | DivideUnsignedWord (hi, lo, rs, rt) ->
         let vhi = hi#to_variable floc in
         let vlo = lo#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let resultlo = XOp (XDiv, [xrs; xrt]) in
         let resulthi = XOp (XMod, [xrs; xrt]) in
         let rresultlo = rewrite_expr resultlo in
         let rresulthi = rewrite_expr resulthi in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresultlo) in
         let uses = [get_def_use vhi; get_def_use vlo] in
         let useshigh = [get_def_use_high vhi; get_def_use_high vlo] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vlo; vhi]
             ~xprs:[xrs; xrt; resultlo; resulthi; rresultlo; rresulthi]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | ExtractBitField (rt, rs, pos, size) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; xxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | InsertBitField (rt, rs, pos, size) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; xxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | JumpLink _
        | BranchLink _
        | Jump _
        | JumpLinkRegister _
        | JumpRegister _ when floc#has_call_target ->
         let args = List.map snd floc#get_mips_call_arguments in
         let rdefs = List.concat (List.map get_all_rdefs args) in
         let regargs =
           match List.length(args) with
           | 0 -> []
           | 1 -> [MRa0]
           | 2 -> [MRa0; MRa1]
           | 3 -> [MRa0; MRa1; MRa2]
           | _ -> [MRa0; MRa1; MRa2; MRa3] in
         let regargs = List.map (fun r -> mips_register_op r RD) regargs in
         let regrdefs =
           List.map
             (fun (r: mips_operand_int) -> get_rdef (r#to_expr floc)) regargs in
         let vr0 = (mips_register_op MRv0 WR)#to_variable floc in
         let vr1 = (mips_register_op MRv1 WR)#to_variable floc in
         let returnval = floc#env#mk_return_value floc#cia in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[returnval]
             ~xprs:args
             ~rdefs:(rdefs @ regrdefs)
             ~uses:[get_def_use vr0; get_def_use vr1]
             ~useshigh:[get_def_use_high vr0; get_def_use_high vr1]
             () in
         let tags = tagstring :: ["call"] in
         let args =
           args @ [ixd#index_call_target floc#get_call_target#get_target] in
         (tags, args)

      | JumpLink _ | BranchLink _ -> (["a:"; "u"],[])

      | JumpLinkRegister (rd, rs) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         let tags = tagstring :: ["u"] in
         (tags, args)

      | JumpRegister rs ->
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let rdefstring = string_repeat "r" (List.length rdefs) in
         let iaddr = floc#ia in
         let faddr = floc#fa in
         if system_info#has_jump_table_target faddr iaddr then
           let (jt, jta, lb, ub) =
             system_info#get_jump_table_target faddr iaddr in
           let tgts = jt#get_indexed_targets jta lb ub in
           (["a:x" ^ rdefstring; "table"],
            (xd#index_xpr xxrs) ::
              ((rdefs
                @ (List.concat
                     (List.map (fun (i, dw) -> [i; bd#index_address dw]) tgts)))))
         else if
           (match xrs with
            | XVar v
                 when
                   floc#env#is_initial_register_value v
                   && (match floc#env#get_initial_register_value_register v with
                       | MIPSRegister MRra -> true
                       | _ -> false) -> true
            | _ -> false) then
             let v0_op = mips_register_op MRv0 RD in
             let xv0 = v0_op#to_expr floc in
             let xxv0 = rewrite_expr xv0 in
             let rdefs = [get_rdef xv0] @ (get_all_rdefs xxv0) in
             let (tagstring, args) = mk_instrx_data ~xprs:[xxv0] ~rdefs () in
             let tags = tagstring :: ["rv"] in
             (tags, args)
           else
             (["a:x"], [xd#index_xpr xxrs])

      | LoadByte (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:1 ~vtype:t_char in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadByteUnsigned (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:1 ~vtype:t_uchar in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadDoublewordToFP (ft, addr) ->
         let vft = ft#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vft] in
         let useshigh = [get_def_use_high vft] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:8 ~vtype:t_double in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vft; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadHalfWord (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:2 ~vtype:t_short in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadHalfWordUnsigned (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:2 ~vtype:t_ushort in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadImmediate (rt, imm) ->
         let vrt = rt#to_variable floc in
         let ximm = imm#to_expr floc in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data ~vars:[vrt] ~xprs:[ximm] ~uses ~useshigh () in
         ([tagstring], args)

      | LoadLinkedWord (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_int in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadUpperImmediate (rt, imm) ->
         let vrt = rt#to_variable floc in
         let ximm =
           num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data ~vars:[vrt] ~xprs:[ximm] ~uses ~useshigh () in
         ([tagstring], args)

      | LoadWord (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_int in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadWordFP (ft, addr) ->
         let vft = ft#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vft] in
         let useshigh = [get_def_use_high vft] in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_float in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vft; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadWordLeft (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let alignment = addr#get_address_alignment in
         let size =
           if system_info#is_little_endian then
             alignment + 1
           else
             4 - alignment in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | LoadWordRight (rt, addr) ->
         let vrt = rt#to_variable floc in
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xmem = rewrite_expr (addr#to_expr floc) in
         let rdefs =
           (get_rdef_memvar vmem) :: ((get_all_rdefs xaddr) @ (get_all_rdefs xmem)) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let alignment = addr#get_address_alignment in
         let size =
           if system_info#is_little_endian then
             4 - alignment
           else
             alignment + 1 in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xmem; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveConditionalNotZero (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let xrd = rd#to_expr floc in
         let cond = XOp (XNe, [xrt; zero_constant_expr]) in
         let ccond = rewrite_expr cond in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs ccond) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; cond; ccond; xrd]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveConditionalZero (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let xrd = rd#to_expr floc in
         let cond = XOp (XEq, [xrt; zero_constant_expr]) in
         let ccond = rewrite_expr cond in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs ccond) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; cond; ccond; xrd]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveFromLo (rd, lo) ->
         let vrd = rd#to_variable floc in
         let xlo = lo#to_expr floc in
         let xxlo = rewrite_expr xlo in
         let rdefs = [get_rdef xlo] @ (get_all_rdefs xxlo) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xlo; xxlo]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveFromHi (rd, hi) ->
         let vrd = rd#to_variable floc in
         let xhi = hi#to_expr floc in
         let xxhi = rewrite_expr xhi in
         let rdefs = [get_rdef xhi] @ (get_all_rdefs xxhi) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xhi; xxhi]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveToLo (lo, rs) ->
         let vlo = lo#to_variable floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let uses = [get_def_use vlo] in
         let useshigh = [get_def_use_high vlo] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vlo]
             ~xprs:[xrs; xxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveToHi (hi, rs) ->
         let vhi = hi#to_variable floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let uses = [get_def_use vhi] in
         let useshigh = [get_def_use_high vhi] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vhi]
             ~xprs:[xrs; xxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | Move (rd, rs) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr xrs in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs xxrs) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xxrs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveWordFromFP (rt, fs) ->
         let vrt = rt#to_variable floc in
         let xfs = fs#to_expr floc in
         let xxfs = rewrite_expr xfs in
         let rdefs = [get_rdef xfs] in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xfs; xxfs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveWordFromHighHalfFP (rt, fs) ->
         let vrt = rt#to_variable floc in
         let xfs = fs#to_expr floc in
         let xxfs = rewrite_expr xfs in
         let rdefs = [get_rdef xfs] in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xfs; xxfs]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveWordToHighHalfFP (rt, fs) ->
         let vfs = fs#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vfs] in
         let useshigh = [get_def_use_high vfs] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vfs]
             ~xprs:[xrt; xxrt]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveWordToFP (rt, fs) ->
         let vfs = fs#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vfs] in
         let useshigh = [get_def_use_high vfs] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vfs]
             ~xprs:[xrt; xxrt]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MoveFromCoprocessor0 (rt, rd, _) ->
         let vrt = rt#to_variable floc in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) = mk_instrx_data ~vars:[vrt] ~uses ~useshigh () in
         ([tagstring], args)

      | MoveToCoprocessor0 (rt, rd, _) ->
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let (tagstring, args) = mk_instrx_data ~xprs:[xrt; xxrt] ~rdefs () in
         ([tagstring], args)

      | MoveFromHighCoprocessor0 (rt, rd, _) ->
         let vrt = rt#to_variable floc in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) = mk_instrx_data ~vars:[vrt] ~uses ~useshigh () in
         ([tagstring], args)

      | MoveToHighCoprocessor0 (rt, rd,_) ->
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let (tagstring, args) = mk_instrx_data ~xprs:[xrt; xxrt] ~rdefs () in
         ([tagstring], args)

      | MoveWordFromCoprocessor2 (rt, _, _) ->
         let vrt = rt#to_variable floc in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) = mk_instrx_data ~vars:[vrt] ~uses ~useshigh () in
         ([tagstring], args)

      | MoveWordToCoprocessor2 (rt, _, _) ->
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let (tagstring, args) = mk_instrx_data ~xprs:[xrt; xxrt] ~rdefs () in
         ([tagstring], args)

      | MoveWordFromHighHalfCoprocessor2 (rt, _, _) ->
         let vrt = rt#to_variable floc in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) = mk_instrx_data ~vars:[vrt] ~uses ~useshigh () in
         ([tagstring], args)

      | MultiplyWord (hi, lo, rs, rt) ->
         let vhi = hi#to_variable floc in
         let vlo = lo#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XMult, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vhi; get_def_use vlo] in
         let useshigh = [get_def_use_high vhi; get_def_use_high vlo] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vhi; vlo]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MultiplyWordToGPR (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XMult, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MultiplyUnsignedWord (hi, lo, rs, rt) ->
         let vhi = hi#to_variable floc in
         let vlo = lo#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XMult, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vhi; get_def_use vlo] in
         let useshigh = [get_def_use_high vhi; get_def_use_high vlo] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vhi; vlo]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MultiplyAddWord (hi, lo, rs, rt) ->
         let vhi = hi#to_variable floc in
         let vlo = lo#to_variable floc in
         let xhi = hi#to_expr floc in
         let xlo = lo#to_expr floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XMult, [xrs; xrt]) in
         let result = XOp (XPlus, [xlo; result]) in
         let rresult = rewrite_expr result in
         let rdefs =
           [get_rdef xrs; get_rdef xrt; get_rdef xlo; get_rdef xhi]
           @ (get_all_rdefs rresult) in
         let uses = [get_def_use vhi; get_def_use vlo] in
         let useshigh = [get_def_use_high vhi; get_def_use_high vlo] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vhi; vlo]
             ~xprs:[xrs; xrt; xlo; xhi; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | MultiplyAddUnsignedWord (hi,lo,rs,rt) ->
         let vhi = hi#to_variable floc in
         let vlo = lo#to_variable floc in
         let xhi = hi#to_expr floc in
         let xlo = lo#to_expr floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XMult, [xrs; xrt]) in
         let result = XOp (XPlus, [xlo; result]) in
         let rresult = rewrite_expr result in
         let rdefs =
           [get_rdef xrs; get_rdef xrt; get_rdef xlo; get_rdef xhi]
           @ (get_all_rdefs rresult) in
         let uses = [get_def_use vhi; get_def_use vlo] in
         let useshigh = [get_def_use_high vhi; get_def_use_high vlo] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vhi; vlo]
             ~xprs:[xrs; xrt; xlo; xhi; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | Nor (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XBNor, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | Or (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XBOr, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | OrImmediate (rt, rs, imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XBOr, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | Prefetch (addr, hint) ->
         let xaddr = addr#to_expr floc in
         let vmem = addr#to_variable floc in
         let rdefs = (get_rdef_memvar vmem) :: (get_all_rdefs xaddr) in
         let _ =
           floc#memrecorder#record_load
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_unknown in
         let (tagstring, args) =
           mk_instrx_data ~vars:[vmem] ~xprs:[xaddr] ~rdefs () in
         ([tagstring], args)

      | ReadHardwareRegister (rt, index) ->
         let vrt = rt#to_variable floc in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) = mk_instrx_data ~vars:[vrt] ~uses ~useshigh () in
         ([tagstring], args)

      | SetLT (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XLt, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | SetLTImmediate (rt, rs, imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XLt, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | SetLTImmediateUnsigned (rt,rs,imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XLt, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | SetLTUnsigned (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XLt, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | ShiftLeftLogical (rd, rt, sa) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xsa = sa#to_expr floc in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         (match xsa with
          | XConst (IntConst n) ->
             let m = get_multiplier n in
             let result = XOp (XMult, [xrt ; m]) in
             let rresult = rewrite_expr result in
             let rdefs = [get_rdef xrt] @ (get_all_rdefs rresult) in
             let (tagstring, args) =
               mk_instrx_data
                 ~vars:[vrd]
                 ~xprs:[xrt; xsa; result; rresult]
                 ~rdefs
                 ~uses
                 ~useshigh
                 () in
             ([tagstring], args)
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Unexpected operand for ShiftLeftLogical: ";
                       sa#toPretty])))

      | ShiftLeftLogicalVariable (rd, rt, rs) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr (XOp (XMod, [xrs; int_constant_expr 32])) in
         let result = XOp (XLsl, [xrt; xxrs]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrt; get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrt; xrs; xxrs; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | ShiftRightArithmetic (rd, rt, sa) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xsa = sa#to_expr floc in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         (match xsa with
          | XConst (IntConst n) ->
             let m = get_multiplier n in
             let result = XOp (XDiv, [xrt ; m]) in
             let rresult = rewrite_expr result in
             let rdefs = [get_rdef xrt] @ (get_all_rdefs rresult) in
             let (tagstring, args) =
               mk_instrx_data
                 ~vars:[vrd]
                 ~xprs:[xrt; xsa; result; rresult]
                 ~rdefs
                 ~uses
                 ~useshigh
                 () in
             ([tagstring], args)
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Unexpected operand for ShiftRightArithmetic: ";
                       sa#toPretty])))

      | ShiftRightArithmeticVariable (rd, rt, rs) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr (XOp (XMod, [xrs; int_constant_expr 32])) in
         let result = XOp (XAsr, [xrt; xxrs]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrt; get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrt; xrs; xxrs; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | ShiftRightLogical (rd, rt, sa) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xsa = sa#to_expr floc in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         (match xsa with
          | XConst (IntConst n) ->
             let m = get_multiplier n in
             let result = XOp (XDiv, [xrt ; m]) in
             let rresult = rewrite_expr result in
             let rdefs = [get_rdef xrt] @ (get_all_rdefs rresult) in
             let (tagstring, args) =
               mk_instrx_data
                 ~vars:[vrd]
                 ~xprs:[xrt; xsa; result; rresult]
                 ~rdefs
                 ~uses
                 ~useshigh
                 () in
             ([tagstring], args)
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Unexpected operand for ShiftRightLogical: ";
                       sa#toPretty])))

      | ShiftRightLogicalVariable (rd, rt, rs) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xrs = rs#to_expr floc in
         let xxrs = rewrite_expr (XOp (XMod, [xrs; int_constant_expr 32])) in
         let result = XOp (XLsr, [xrt; xxrs]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrt; get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrt; xrs; xxrs; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | SignExtendByte (rd, rt) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd] ~xprs:[xrt; xxrt] ~rdefs ~uses ~useshigh () in
         ([tagstring], args)

      | SignExtendHalfword (rd, rt) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd] ~xprs:[xrt; xxrt] ~rdefs ~uses ~useshigh () in
         ([tagstring], args)

      | StoreByte (addr, rt) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs =
           [get_rdef xrt; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:1 ~vtype:t_char ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreHalfWord (addr, rt) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs =
           [get_rdef xrt; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:2 ~vtype:t_short ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreWord (addr, rt) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs =
           [get_rdef xrt; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_int ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreWordFromFP (addr, ft) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xft = ft#to_expr floc in
         let xxft = rewrite_expr xft in
         let rdefs =
           [get_rdef xft; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxft) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_float ~xpr:xxft in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xft; xxft; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreDoublewordFromFP (addr, ft) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xft = ft#to_expr floc in
         let xxft = rewrite_expr xft in
         let rdefs =
           [get_rdef xft; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxft) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:8 ~vtype:t_double ~xpr:xxft in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xft; xxft; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreConditionalWord (addr, rt) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs =
           [get_rdef xrt; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size:4 ~vtype:t_int ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreWordLeft (addr, rt) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs =
           [get_rdef xrt; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let alignment = addr#get_address_alignment in
         let size =
           if system_info#is_little_endian then
             alignment + 1
           else
             4 - alignment in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size ~vtype:t_unknown ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | StoreWordRight (addr, rt) ->
         let xaddr = rewrite_expr (addr#to_address floc) in
         let vmem = addr#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs =
           [get_rdef xrt; get_rdef xaddr]
           @ (get_all_rdefs xaddr)
           @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let alignment = addr#get_address_alignment in
         let size =
           if system_info#is_little_endian then
             4 - alignment
           else
             alignment + 1 in
         let _ =
           floc#memrecorder#record_store
             ~addr:xaddr ~var:vmem ~size ~vtype:t_unknown ~xpr:xxrt in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrt; xxrt; xaddr]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | Subtract(rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XMinus, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh () in
         ([tagstring], args)

      | SubtractUnsigned (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XMinus, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh () in
         ([tagstring], args)

      | Syscall _ when floc#has_call_target ->
         let args = List.map snd floc#get_mips_call_arguments in
         let rdefs = List.concat (List.map get_all_rdefs args) in
         let regargs =
           match List.length(args) with
           | 0 -> []
           | 1 -> [MRa0]
           | 2 -> [MRa0; MRa1]
           | 3 -> [MRa0; MRa1; MRa2]
           | _ -> [MRa0; MRa1; MRa2; MRa3] in
         let regargs = List.map (fun r -> mips_register_op r RD) regargs in
         let regrdefs =
           List.map
             (fun (r: mips_operand_int) -> get_rdef (r#to_expr floc)) regargs in
         let vr0 = (mips_register_op MRv0 WR)#to_variable floc in
         let vr1 = (mips_register_op MRv1 WR)#to_variable floc in
         let syscallindex = floc#env#mk_mips_register_variable MRv0 in
         let syscallindex = rewrite_expr (XVar syscallindex) in
         let rdefs = (get_rdef syscallindex) :: rdefs in
         let returnval = floc#env#mk_return_value floc#cia in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[returnval]
             ~xprs:(syscallindex :: args)
             ~rdefs:(rdefs @ regrdefs)
             ~uses:[get_def_use vr0; get_def_use vr1]
             ~useshigh:[get_def_use_high vr0; get_def_use_high vr1]
             () in
         let tags = tagstring :: ["call"] in
         let args =
           args @ [ixd#index_call_target floc#get_call_target#get_target] in
         (tags, args)

      | Syscall _ ->
         let arg = floc#env#mk_mips_register_variable MRv0 in
         let argval = rewrite_expr (XVar arg) in
         let vr0 = (mips_register_op MRv0 WR)#to_variable floc in
         let vr1 = (mips_register_op MRv1 WR)#to_variable floc in
         let rdefs = [get_rdef argval] in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[argval]
             ~rdefs
             ~uses:[get_def_use vr0; get_def_use vr1]
             ~useshigh:[get_def_use_high vr0; get_def_use_high vr1]
             () in
         ([tagstring], args)

      | TrapIfEqual(cc, rs, rt) ->
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XEq, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data ~xprs:[xrs; xrt; result; rresult] ~rdefs () in
         ([tagstring], args)

      | TrapIfEqualImmediate (rs, imm) ->
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XEq, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let (tagstring, args) =
           mk_instrx_data ~xprs:[xrs; ximm; result; rresult] ~rdefs () in
         ([tagstring], args)

      | WordSwapBytesHalfwords (rd, rt) ->
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrt] @ (get_all_rdefs xxrt) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrt; xxrt]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | Xor (rd, rs, rt) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let xrt = rt#to_expr floc in
         let result = XOp (XBXor, [xrs; xrt]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrs; get_rdef xrt] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrd] in
         let useshigh = [get_def_use_high vrd] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; xrt; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | XorImmediate (rt, rs, imm) ->
         let vrt = rt#to_variable floc in
         let xrs = rs#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XBOr, [xrs; ximm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         let rdefs = [get_rdef xrs] @ (get_all_rdefs rresult) in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt]
             ~xprs:[xrs; ximm; result; rresult]
             ~rdefs
             ~uses
             ~useshigh
             () in
         ([tagstring], args)

      | _ -> ([],[]) in
    instrx_table#add key

  method write_xml_sp_offset
           ?(tag="isp") (node:xml_element_int) (o:int * interval_t) =
    node#setIntAttribute tag (self#index_sp_offset o)

  method write_xml_instr
           ?(tag="iopx")
           (node:xml_element_int)
           (instr:mips_assembly_instruction_int)
           (floc:floc_int)
           (restriction:block_restriction_t option) =
    try
      node#setIntAttribute tag (self#index_instr instr floc restriction)
    with
    | BCH_failure p ->
       raise (BCH_failure
                (LBLOCK [ STR "Error in writing xml instruction: " ;
                          floc#l#i#toPretty ; STR "  " ; instr#toPretty ;
                          STR ": " ; p ]))

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
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables;

  method toPretty =
    LBLOCK
      (List.map
         (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end

let mk_mips_opcode_dictionary = new mips_opcode_dictionary_t
