(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
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
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

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
open BCHByteUtilities
open BCHConstantDefinitions
open BCHCPURegisters
open BCHDoubleword
open BCHFloc   
open BCHFunctionInterface
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMConditionalExpr
open BCHARMDictionary
open BCHARMDisassemblyUtils
open BCHARMLoopStructure
open BCHARMOperand
open BCHARMOpcodeRecords
open BCHARMTypes

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
    let (tags, args) = sp_offset_table#retrieve index in
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
    let rewrite_expr x: xpr_t =
      try
        (*
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
          | XOp (op, l) -> XOp (op, List.map expand l)
          | _ -> x in *)
        let xpr =
          floc#inv#rewrite_expr x floc#env#get_variable_comparator in
        simplify_xpr xpr
      with IO.No_more_input ->
            begin
              pr_debug [STR "Error in rewriting expression: ";
                        x2p x;
                        STR ": No more input";
                        NL];
              raise IO.No_more_input
            end in
    let add_instr_condition
          (tags: string list)
          (args: int list)
          (x: xpr_t): (string list) * (int list) =
      let _ =
        if (List.length tags) = 0 then
          raise
            (BCH_failure
               (LBLOCK [STR "Empty tag list in add_instr_condition"])) in
      let xtag = (List.hd tags) ^ "x" in
      let tags = xtag :: ((List.tl tags) @ ["ic"]) in
      let args = args @ [xd#index_xpr x] in
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
      | XVar v ->
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

    let add_base_update
          (tags: string list)
          (args: int list)
          (v: variable_t)
          (x: xpr_t): (string list) * (int list) =
      let _ =
        if (List.length tags) = 0 then
          raise (BCH_failure
                   (LBLOCK [STR "Empty tag list in add_base_update"])) in
      let xtag = (List.hd tags) ^ "vx" in
      let tags = xtag :: ((List.tl tags) @ ["bu"]) in
      let args = args @ [xd#index_variable v; xd#index_xpr x] in
      (tags, args) in

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
      let flagrdefcount = List.length flagrdefs in
      let varstring = string_repeat "v" varcount in
      let xprstring = string_repeat "x" xprcount in
      let rdefstring = string_repeat "r" rdefcount in
      let defusestring = string_repeat "d" defusecount in
      let defusehighstring = string_repeat "h" defusehighcount in
      let flagrdefstring = string_repeat "f" flagrdefcount in
      let tagstring =
        "a:"
        ^ varstring
        ^ xprstring
        ^ rdefstring
        ^ defusestring
        ^ defusehighstring
        ^ flagrdefstring in
      let varargs = List.map xd#index_variable vars in
      let xprargs = List.map xd#index_xpr xprs in
      (tagstring, varargs @ xprargs @ rdefs @ uses @ useshigh @ flagrdefs) in

    let key =
      match instr#get_opcode with
      | Add (_, c, rd, rn, rm, _) ->
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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | AddCarry (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XPlus, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | Adr (_, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm = imm#to_expr floc in
         (["a:vx"], [xd#index_variable vrd; xd#index_xpr ximm])

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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | BitFieldClear (_, rd, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xrd = rd#to_expr floc in
         (["a:vx"], [xd#index_variable vrd; xd#index_xpr xrd])

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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | BitwiseBitClear (_, _, rd, rn, imm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rd#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XBAnd, [xrn; XOp (XBNot, [ximm])]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr ximm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | BitwiseExclusiveOr (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBXor, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | BitwiseNot (_, _, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBNot, [xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | BitwiseOr (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBOr, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | BitwiseOrNot (_, _, rd, rn, rm) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xrmn = XOp (XBNot, [xrm]) in
         let result = XOp (XBOr, [xrn; xrmn]) in
         let rresult = rewrite_expr result in
         (["a:vxxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr xrmn;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | Branch (_, tgt, _)
           when tgt#is_absolute_address && floc#has_call_target ->
         let args = List.map snd floc#get_arm_call_arguments in
         let xtag = "a:" ^ (string_repeat "x" (List.length args)) in
         ([xtag; "call"],
          (List.map xd#index_xpr args)
          @ [ixd#index_call_target floc#get_call_target#get_target])

      | Branch (c, tgt, _)
           when is_cond_conditional c
                && tgt#is_absolute_address
                && floc#has_test_expr ->
         let xtgt = tgt#to_expr floc in
         let txpr = floc#get_raw_test_expr in
         let fxpr = XOp (XLNot, [txpr]) in
         let tcond = floc#get_test_expr in
         let fcond = rewrite_expr (XOp (XLNot, [tcond])) in
         let csetter = floc#f#get_associated_cc_setter floc#cia in
         let instr =
           (!arm_assembly_instructions)#at_address
             (string_to_doubleword csetter) in
         let bytestr = instr#get_bytes_ashexstring in
         let rdefs = get_all_rdefs tcond in
         let (tagstring, args) =
           mk_instrx_data
             ~xprs:[txpr; fxpr; tcond; fcond; xtgt]
             ~rdefs:rdefs
             () in
         let (tags, args) = (tagstring :: ["TF"; csetter; bytestr], args) in
         (tags, args)

      | Branch (_, tgt, _) ->
         let xtgt = tgt#to_expr floc in
         (["a:x"], [xd#index_xpr xtgt])

      | BranchExchange (_, tgt) ->
         let xtgt = tgt#to_expr floc in
         (["a:x"], [xd#index_xpr xtgt])

      | BranchLink (_, tgt)
        | BranchLinkExchange (_, tgt)
           when floc#has_call_target
                && floc#get_call_target#is_signature_valid ->
         let args = List.map snd floc#get_arm_call_arguments in
         let xtag = "a:" ^ (string_repeat "x" (List.length args)) in
         ([xtag; "call"],
          (List.map xd#index_xpr args)
          @ [ixd#index_call_target floc#get_call_target#get_target])

      | BranchLink (_, tgt)
      | BranchLinkExchange (_, tgt) ->
         let xtgt = tgt#to_expr floc in
         let args =
           List.map (fun r -> arm_register_op r RD) [AR0; AR1; AR2; AR3] in
         let argxprs = List.map (fun a -> a#to_expr floc) args in
         let rargxprs = List.map rewrite_expr argxprs in
         (["a:xxxxx"],
          (xd#index_xpr xtgt) :: (List.map xd#index_xpr rargxprs))

      | ByteReverseWord(_, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let xrmm = rewrite_expr xrm in
         (["a:vxx"],
          [xd#index_variable vrd; xd#index_xpr xrm; xd#index_xpr xrmm])

      | ByteReversePackedHalfword (_, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let xrmm = rewrite_expr xrm in
         (["a:vxx"],
          [xd#index_variable vrd; xd#index_xpr xrm; xd#index_xpr xrmm])

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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | CompareBranchNonzero (rn, tgt) ->
         let xrn = rn#to_expr floc in
         let xtgt = tgt#to_expr floc in
         (["a:xx"], [xd#index_xpr xrn; xd#index_xpr xtgt])

      | CompareBranchZero (rn, tgt) ->
         let xrn = rn#to_expr floc in
         let xtgt = tgt#to_expr floc in
         (["a:xx"], [xd#index_xpr xrn; xd#index_xpr xtgt])

      | CompareNegative (_, rn, rm) ->
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         (["a:xx"], [xd#index_xpr xrn; xd#index_xpr xrm])

      | CountLeadingZeros (_, rd, rm) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let xxrm = rewrite_expr xrm in
         (["a:vxx"], [xd#index_variable vrd; xd#index_xpr xrm; xd#index_xpr xxrm])

      | IfThen (c, xyz) when instr#is_aggregate ->
         let finfo = floc#f in
         let ctxtiaddr = floc#l#ci in
         if finfo#has_associated_cc_setter ctxtiaddr then
           let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
           let testloc = ctxt_string_to_location faddr testiaddr in
           let testaddr = testloc#i in
           let testinstr = !arm_assembly_instructions#at_address testaddr in
           let dstop = instr#get_aggregate_dst in
           let (_, optpredicate) =
             arm_conditional_expr
               ~condopc:instr#get_opcode
               ~testopc:testinstr#get_opcode
               ~condloc:floc#l
               ~testloc:testloc in
           let (tags, args) =
             (match optpredicate with
              | Some p ->
                 let lhs = dstop#to_variable floc in
                 let rdefs = get_all_rdefs p in
                 let (tagstring, args) =
                   mk_instrx_data
                     ~vars:[lhs]
                     ~xprs:[p]
                     ~rdefs:rdefs
                     ~uses:[get_def_use lhs]
                     ~useshigh:[get_def_use_high lhs]
                     () in
                 ([tagstring], args)
              | _ ->
                 ([], [])) in
           let dependents =
             List.map (fun d -> d#to_hex_string) instr#get_dependents in
           let tags = tags @ ["subsumes"] @ dependents in
           (tags, args)
         else
           ([], [])

      | IfThen (c, xyz)  ->
         ([], [])

      | LoadMultipleDecrementAfter (_, _, base, rl, _) ->
         let reglhss = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let (memreads, _) =
           List.fold_left
             (fun (acc, off) reglhs ->
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
             (fun (acc, off) reglhs ->
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

      | LoadMultipleIncrementAfter (_, _, base, rl, _) ->
         let reglhss = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let (memreads, _) =
           List.fold_left
             (fun (acc, off) reglhs ->
               let memop = arm_reg_deref ~with_offset:off basereg RD in
               let memrhs = memop#to_expr floc in
               (acc @ [memrhs], off + 4)) ([], 0) reglhss in
         let xtag =
           "a:"
           ^ (string_repeat "v" regcount)
           ^ (string_repeat "x" regcount)
           ^ "x" in    (* base expression *)
         ([xtag],
          (List.map xd#index_variable reglhss)
          @ (List.map xd#index_xpr memreads)
          @ [xd#index_xpr (base#to_expr floc)])

      | LoadMultipleIncrementBefore (_, _, base, rl, _) ->
         let reglhss = rl#to_multiple_variable floc in
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let (memreads, _) =
           List.fold_left
             (fun (acc, off) reglhs ->
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

      | LoadRegister (c, rt, rn, rm, mem, _) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem] in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let xrmem = rewrite_expr xmem in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let xaddr = mem#to_updated_offset_address floc in
             add_base_update tags args vrn xaddr
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterByte (c, rt, rn, rm, mem, _) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         (* let xmem = XOp (XBAnd, [xmem; int_constant_expr 255]) in *)
         let xrmem = rewrite_expr xmem in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem] in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let xaddr = mem#to_updated_offset_address floc in
             add_base_update tags args vrn xaddr
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterDual (_, rt, rt2, _, _, mem, mem2) ->
         let vrt = rt#to_variable floc in
         let vrt2 = rt2#to_variable floc in
         let vmem = mem#to_variable floc in
         let vmem2 = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let xmem2 = mem2#to_expr floc in
         let xrmem2 = rewrite_expr xmem2 in
         (["a:vvvvxxxx"],
          [xd#index_variable vrt;
           xd#index_variable vrt2;
           xd#index_variable vmem;
           xd#index_variable vmem2;
           xd#index_xpr xmem;
           xd#index_xpr xrmem;
           xd#index_xpr xmem2;
           xd#index_xpr xrmem2])

      | LoadRegisterExclusive (_, rt, rn, _, mem) ->
         let vrt = rt#to_variable floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vvxx"],
          [xd#index_variable vrt;
           xd#index_variable vmem;
           xd#index_xpr xmem;
           xd#index_xpr xrmem])

      | LoadRegisterHalfword (_, rt, rn, _, mem, _) ->
         let vrt = rt#to_variable floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vvxx"],
          [xd#index_variable vrt;
           xd#index_variable vmem;
           xd#index_xpr xmem;
           xd#index_xpr xrmem])

      | LoadRegisterSignedByte (_, rt, rn, _, mem, _) ->
         let vrt = rt#to_variable floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vvxx"],
          [xd#index_variable vrt;
           xd#index_variable vmem;
           xd#index_xpr xmem;
           xd#index_xpr xrmem])

      | LoadRegisterSignedHalfword (c, rt, rn, rm, mem, _) ->
         let vrt = rt#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef_memvar vmem] in
         let uses = [get_def_use vrt] in
         let useshigh = [get_def_use_high vrt] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrt; vmem]
             ~xprs:[xrn; xrm; xmem; xrmem]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let xaddr = mem#to_updated_offset_address floc in
             add_base_update tags args vrn xaddr
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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | LogicalShiftRight (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XLsr, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | Move(_, c, rd, rm, _, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let result = rewrite_expr xrm in
         let rdefs = (get_rdef xrm) :: (get_all_rdefs result) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrm; result]
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
         if instr#is_subsumed then
           let subsumedby = instr#subsumed_by#to_hex_string in
           (tags @ ["subsumed"; subsumedby], args)
         else
           (tags, args)

      | MoveRegisterCoprocessor (_, _, _, dst, _, _, _) ->
         let vdst = dst#to_variable floc in
         (["a:v"], [xd#index_variable vdst])

      | MoveToCoprocessor (_, _, _, rt, _, _, _) ->
         let src = rt#to_expr floc in
         let rsrc = rewrite_expr src in
         (["a:xx"], [xd#index_xpr src; xd#index_xpr rsrc])

      | MoveTop (_, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm = imm#to_expr floc in
         let xrd = rd#to_expr floc in
         let ximm16 = XOp (XMult, [ximm; int_constant_expr e16]) in
         let xrdm16 = XOp (XMod, [xrd; int_constant_expr e16]) in
         let result = XOp (XPlus, [xrdm16; ximm16]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         (["a:vxxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr ximm;
           xd#index_xpr xrd;
           xd#index_xpr xrdm16;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | MoveTwoRegisterCoprocessor (_, _, _, rt, rt2, _) ->
         let v1 = rt#to_variable floc in
         let v2 = rt2#to_variable floc in
         (["a:vv"], [xd#index_variable v1; xd#index_variable v2])

      | Multiply(_, _, rd, rn, rm) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xprd = XOp (XMult, [xrn; xrm]) in
         let xrprd = rewrite_expr xprd in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr xprd;
           xd#index_xpr xrprd])

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
         let spresult = XOp (XPlus, [sprhs; int_constant_expr 4]) in
         let rspresult = rewrite_expr spresult in
         let lhsvars =
           List.map (fun op -> op#to_variable floc) rl#get_register_op_list in
         let rhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset RD)
             (List.init rl#get_register_count (fun i -> 4 * i)) in
         let rhsexprs = List.map (fun x -> x#to_expr floc) rhsops in
         let rrhsexprs = List.map rewrite_expr rhsexprs in
         let rdefs = List.map get_rdef (sprhs :: rhsexprs) in
         let uses = List.map get_def_use (splhs :: lhsvars) in
         let useshigh = List.map get_def_use_high (splhs :: lhsvars) in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(splhs :: lhsvars)
             ~xprs:(sprhs :: spresult :: rspresult :: rrhsexprs)
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | PreloadData (w, _, base, mem) ->
         let xbase = base#to_expr floc in
         let xmem = mem#to_expr floc in
         (["a:xx"], [xd#index_xpr xbase; xd#index_xpr xmem])

      | Push (c, sp, rl, _) ->
         let splhs = sp#to_variable floc in
         let sprhs = sp#to_expr floc in
         let rhsexprs =
           List.map (fun op -> op#to_expr floc) rl#get_register_op_list in
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
         let spresult = XOp (XMinus, [sprhs; int_constant_expr 4]) in
         let rspresult = rewrite_expr spresult in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:(splhs :: lhsvars)
             ~xprs:(sprhs :: spresult :: rspresult :: rrhsexprs)
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring ::["uc"], args) in
         (tags, args)

      | ReverseSubtract (_, _, dst, src1, src2, _) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XMinus, [rhs2; rhs1]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable lhs;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr result;
           xd#index_xpr rresult])

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

      | StoreMultipleDecrementBefore (_, _, base, rl, _, _) ->
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let rhss = rl#to_multiple_expr floc in
         let rrhss = List.map rewrite_expr rhss in
         let (memlhss, _) =
           List.fold_left
             (fun (acc, off) reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs = memop#to_variable floc in
               (acc @ [memlhs], off + 4))
             ([], -(4 * regcount)) rl#get_register_op_list in
         let xtag =
           "a:"
           ^ (string_repeat "v" regcount)
           ^ (string_repeat "x" regcount)
           ^ "x" in  (* base expression *)
         ([xtag],
          (List.map xd#index_variable memlhss)
          @ (List.map xd#index_xpr rrhss)
          @ [xd#index_xpr (base#to_expr floc)])

      | StoreMultipleIncrementAfter (_, _, base, rl, _, _) ->
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let rhss = rl#to_multiple_expr floc in
         let rrhss = List.map rewrite_expr rhss in
         let (memlhss, _) =
           List.fold_left
             (fun (acc, off) reg ->
               let memop = arm_reg_deref ~with_offset:off basereg WR in
               let memlhs = memop#to_variable floc in
               (acc @ [memlhs], off + 4)) ([], 0) rl#get_register_op_list in
         let xtag =
           "a:"
           ^ (string_repeat "v" regcount)
           ^ (string_repeat "x" regcount)
           ^ "x" in  (* base expression *)
         ([xtag],
          (List.map xd#index_variable memlhss)
          @ (List.map xd#index_xpr rrhss)
          @ [xd#index_xpr (base#to_expr floc)])

      | StoreMultipleIncrementBefore (_, _, base, rl, _, _) ->
         let basereg = base#get_register in
         let regcount = rl#get_register_count in
         let rhss = rl#to_multiple_expr floc in
         let rrhss = List.map rewrite_expr rhss in
         let (memlhss, _) =
           List.fold_left
             (fun (acc, off) reg ->
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
         let xrt = rt#to_expr floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef xrt; get_rdef xxrt] in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrn; xrm; xrt; xxrt]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | StoreRegisterByte (c, rt, rn, rm, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef xrt; get_rdef xxrt] in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrn; xrm; xrt; xxrt]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | StoreRegisterDual (_, rt, rt2, _, _, mem, mem2) ->
         let vmem = mem#to_variable floc in
         let vmem2 = mem2#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let xrt2 = rt2#to_expr floc in
         let xxrt2 = rewrite_expr xrt2 in
         (["a:vvxxxx"],
          [xd#index_variable vmem;
           xd#index_variable vmem2;
           xd#index_xpr xrt;
           xd#index_xpr xxrt;
           xd#index_xpr xrt2;
           xd#index_xpr xxrt2])

      | StoreRegisterExclusive (_, rd, rt, rn, mem) ->
         let vmem = mem#to_variable floc in
         let vrd = rd#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         (["a:vvxx"],
          [xd#index_variable vmem;
           xd#index_variable vrd;
           xd#index_xpr xrt;
           xd#index_xpr xxrt])

      | StoreRegisterHalfword (c, rt, rn, rm, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let rdefs = [get_rdef xrn; get_rdef xrm; get_rdef xrt; get_rdef xxrt] in
         let uses = [get_def_use vmem] in
         let useshigh = [get_def_use_high vmem] in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrn; xrm; xrt; xxrt]
             ~rdefs:rdefs
             ~uses:uses
             ~useshigh:useshigh
             () in
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | Subtract (_, c, rd, rn, rm, _, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XMinus, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let rdefs = [get_rdef xrn; get_rdef xrm] in
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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
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

      | TableBranchByte (_, _, rm, _) ->
         let xrm = rm#to_expr floc in
         (["a:x"], [xd#index_xpr xrm])

      | TableBranchHalfword (_, _, rm, _) ->
         let xrm = rm#to_expr floc in
         (["a:x"], [xd#index_xpr xrm])

      | Test (_, rn, rm) ->
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

      | UnsignedBitFieldExtract (_, rd, rn) ->
         let lhs = rd#to_variable floc in
         let rhs = rn#to_expr floc in
         let rrhs = rewrite_expr rhs in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr rhs; xd#index_xpr rrhs])

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
         let xrm = rm#to_expr floc in
         let result = XOp (XBAnd, [xrm; int_constant_expr 255]) in
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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
         (tags, args)

      | UnsignedExtendHalfword (c, rd, rm) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         (* let result = XOp (XBAnd, [xrm; int_constant_expr 65535]) in *)
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
         let (tags, args) =
           match c with
           | ACCAlways -> ([tagstring], args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition [tagstring] args tcond
           | _ -> (tagstring :: ["uc"], args) in
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

      | UnsignedMultiplyLong (_, _, rdlo, rdhi, rn, rm) ->
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

      | UnsignedSaturatingSubtract8 (_, rd, rn, rm) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         (["a:vxx"],
          [xd#index_variable vrd; xd#index_xpr xrn; xd#index_xpr xrm])

      | VCompare (_, _, _, op1, op2) ->
         let src1 = op1#to_expr floc in
         let src2 = op2#to_expr floc in
         let rsrc1 = rewrite_expr src1 in
         let rsrc2 = rewrite_expr src2 in
         (["a:xxxx"],
          [xd#index_xpr src1;
           xd#index_xpr src2;
           xd#index_xpr rsrc1;
           xd#index_xpr rsrc2])

      | VectorConvert (_, _, _, _, dst, src) ->
         let vdst = dst#to_variable floc in
         let src = src#to_expr floc in
         let rsrc = rewrite_expr src in
         (["a:vxx"],
          [xd#index_variable vdst; xd#index_xpr src; xd#index_xpr rsrc])

      | VectorDuplicate (_, _, _, _, _, src) ->
         let src = src#to_expr floc in
         let rsrc = rewrite_expr src in
         (["a:xx"], [xd#index_xpr src; xd#index_xpr rsrc])

      | VLoadRegister (_, vd, rn, mem) ->
         let vvd = vd#to_variable floc in
         let xmem = mem#to_expr floc in
         (["a:vx"], [xd#index_variable vvd; xd#index_xpr xmem])

      | VMoveToSystemRegister (_, _, src) ->
         let xsrc = src#to_expr floc in
         (["a:x"], [xd#index_xpr xsrc])

      | VStoreRegister (c, vd, rn, mem) ->
         let vmem = mem#to_variable floc in
         let xvd = vd#to_expr floc in
         (["a:vx"], [xd#index_variable vmem; xd#index_xpr xvd])

      | _ -> ([], []) in
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

