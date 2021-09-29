(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs LLC

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
          raise (BCH_failure
                   (LBLOCK [STR "Empty tag list in add_instr_condition"])) in
      let xtag = (List.hd tags) ^ "x" in
      let tags = xtag :: ((List.tl tags) @ ["ic"]) in
      let args = args @ [xd#index_xpr x] in
      (tags, args) in

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

    let key =
      match instr#get_opcode with
      | Add (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XPlus, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         (["a:vxxxx"], [xd#index_variable vrd;
                        xd#index_xpr xrn;
                        xd#index_xpr xrm;
                        xd#index_xpr result;
                        xd#index_xpr rresult])

      | Adr (_, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm = imm#to_expr floc in
         (["a:vx"], [xd#index_variable vrd; xd#index_xpr ximm])

      | ArithmeticShiftRight (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result =
           match xrm with
           | XConst (IntConst n) when n#toInt = 2 ->
              XOp (XDiv, [xrn; XConst (IntConst (mkNumerical 4))])
           | _ -> XOp (XShiftrt, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"], [xd#index_variable vrd;
                       xd#index_xpr xrn;
                       xd#index_xpr xrm;
                       xd#index_xpr result;
                       xd#index_xpr rresult])

      | BitFieldClear (_, rd, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xrd = rd#to_expr floc in
         (["a:vx"], [xd#index_variable vrd; xd#index_xpr xrd])

      | BitwiseAnd (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBAnd, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"], [xd#index_variable vrd;
                        xd#index_xpr xrn;
                        xd#index_xpr xrm;
                        xd#index_xpr result;
                        xd#index_xpr rresult])

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

      | Branch (c, tgt, _)
           when is_cond_conditional c
                && tgt#is_absolute_address
                && floc#has_test_expr ->
         let xtgt = tgt#to_expr floc in
         let tcond = rewrite_expr floc#get_test_expr in
         let fcond = rewrite_expr (XOp (XLNot, [tcond])) in
         (["a:xxx"; "TF"],
          [xd#index_xpr tcond; xd#index_xpr fcond; xd#index_xpr xtgt])

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

      | BranchLink (_, tgt) ->
         let xtgt = tgt#to_expr floc in
         (["a:x"], [xd#index_xpr xtgt])

      | BranchLinkExchange (_, tgt) ->
         let xtgt = tgt#to_expr floc in
         (["a:x"], [xd#index_xpr xtgt])

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

      | Compare (_, rn, rm, _) ->
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         (["a:xx"], [xd#index_xpr xrn; xd#index_xpr xrm])

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

      | LoadMultipleIncrementAfter (_, _, rn, rl, mem) ->
         let lhss = rl#to_multiple_variable floc in
         let xtag =
           "a:" ^ (string_repeat "v" rl#get_register_count) in
         ([xtag], List.map xd#index_variable lhss)

      | LoadRegister (c, rt, rn, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let tags = ["a:vxx"] in
         let args = [
             xd#index_variable vrt; xd#index_xpr xmem; xd#index_xpr xrmem] in
         let (tags, args) =
           match c with
           | ACCAlways -> (tags, args)
           | c when is_cond_conditional c && floc#has_test_expr ->
              let tcond = rewrite_expr floc#get_test_expr in
              add_instr_condition tags args tcond
           | _ -> (tags @ ["uc"], args) in
         let (tags, args) =
           if mem#is_offset_address_writeback then
             let vrn = rn#to_variable floc in
             let xaddr = mem#to_updated_offset_address floc in
             add_base_update tags args vrn xaddr
           else
             (tags, args) in
         (tags, args)

      | LoadRegisterByte (_, rt, rn, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"], [xd#index_variable vrt;
                      xd#index_xpr xmem;
                      xd#index_xpr xrmem])

      | LoadRegisterDual (_, rt, rt2, _, _, mem, mem2) ->
         let vrt = rt#to_variable floc in
         let vrt2 = rt2#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         let xmem2 = mem2#to_expr floc in
         let xrmem2 = rewrite_expr xmem2 in
         (["a:vvxxxx"],
          [xd#index_variable vrt;
           xd#index_variable vrt2;
           xd#index_xpr xmem;
           xd#index_xpr xrmem;
           xd#index_xpr xmem2;
           xd#index_xpr xrmem2])

      | LoadRegisterExclusive (_, rt, rn, mem) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"],
          [xd#index_variable vrt;
           xd#index_xpr xmem;
           xd#index_xpr xrmem])

      | LoadRegisterHalfword (_, rt, rn, _, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"], [xd#index_variable vrt;
                      xd#index_xpr xmem;
                      xd#index_xpr xrmem])

      | LoadRegisterSignedByte (_, rt, rn, _, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"],
          [xd#index_variable vrt;
           xd#index_xpr xmem;
           xd#index_xpr xrmem])

      | LoadRegisterSignedHalfword (_, rt, rn, _, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"],
          [xd#index_variable vrt;
           xd#index_xpr xmem;
           xd#index_xpr xrmem])

      | LogicalShiftLeft (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XShiftlt, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | LogicalShiftRight (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XShiftrt, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable vrd;
           xd#index_xpr xrn;
           xd#index_xpr xrm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | Move(_, c, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let tags = ["a:vx"] in
         let args = [xd#index_variable vrd; xd#index_xpr xrm] in
         (match c with
          | ACCAlways ->
             (tags, args)
          | c when is_cond_conditional c && floc#has_test_expr ->
             let tcond = rewrite_expr floc#get_test_expr in
             add_instr_condition tags args tcond
          | _ ->
             (["a:vx"; "uc"], [xd#index_variable vrd; xd#index_xpr xrm]))

      | MoveRegisterCoprocessor (_, _, _, dst, _, _, _) ->
         let vdst = dst#to_variable floc in
         (["a:v"], [xd#index_variable vdst])

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

      | MoveWide(_,rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm = imm#to_expr floc in
         let _ = ignore (get_string_reference floc ximm) in
         (["a:vx"], [xd#index_variable vrd; xd#index_xpr ximm])

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
         let lhsvars =
           List.map (fun op -> op#to_variable floc) rl#get_register_op_list in
         let rhsexprs =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset RD)
             (List.init rl#get_register_count (fun i -> 4 * i)) in
         let rhsexprs =
           List.map (fun x -> rewrite_expr (x#to_expr floc)) rhsexprs in
         let xtag =
           "a:"
           ^ (string_repeat "v" rl#get_register_count)
           ^ (string_repeat "x" rl#get_register_count) in
         let tags = [xtag] in
         let args =
           (List.map xd#index_variable lhsvars)
           @ (List.map xd#index_xpr rhsexprs) in
         (match c with
          | ACCAlways -> (tags, args)
          | c when is_cond_conditional c && floc#has_test_expr ->
             let tcond = rewrite_expr floc#get_test_expr in
             add_instr_condition tags args tcond
          | _ -> (tags @ ["uc"], args))

      | Push (_, sp, rl, _) ->
         let rhsexprs =
           List.map
             (fun op -> rewrite_expr (op#to_expr floc))
             rl#get_register_op_list in
         let regcount = List.length rhsexprs in
         let lhsops =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset WR)
             (List.init rl#get_register_count (fun i -> ((-4*regcount) + (4*i)))) in
         let lhsvars = List.map (fun v -> v#to_variable floc) lhsops in
         let xtag = "a:"
                    ^ (string_repeat "v" rl#get_register_count)
                    ^ (string_repeat "x" rl#get_register_count) in
         let tags = [xtag] in
         let args =
           (List.map xd#index_variable lhsvars)
           @ (List.map xd#index_xpr rhsexprs) in
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

      | SignedExtendByte (_, rd, rm) ->
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

      | StoreMultipleIncrementAfter (_, _, rn, rl, mem, _) ->
         let rhss = rl#to_multiple_expr floc in
         let xtag =
           "a:" ^ (string_repeat "x" rl#get_register_count) in
         ([xtag], List.map xd#index_xpr rhss)

      | StoreMultipleIncrementBefore (_, _, rn, rl, mem, _) ->
         let rhss = rl#to_multiple_expr floc in
         let xtag =
           "a:" ^ (string_repeat "x" rl#get_register_count) in
         ([xtag], List.map xd#index_xpr rhss)

      | StoreRegister (c, rt, rn, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         let tags = ["a:vxx"] in
         let args = [
             xd#index_variable vmem; xd#index_xpr xrt; xd#index_xpr xxrt] in
         (match c with
          | ACCAlways -> (tags, args)
          | c when is_cond_conditional c && floc#has_test_expr ->
             let tcond = rewrite_expr floc#get_test_expr in
             add_instr_condition tags args tcond
          | _ -> (tags @ ["uc"], args))

      | StoreRegisterByte (_, rt, rn, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         (["a:vxx"],
          [xd#index_variable vmem;
           xd#index_xpr xrt;
           xd#index_xpr xxrt])

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

      | StoreRegisterHalfword (_, rt, rn, _, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         (["a:vxx"],
          [xd#index_variable vmem;
           xd#index_xpr xrt;
           xd#index_xpr xxrt])

      | Subtract (_, _, dst, src1, src2, _) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XMinus, [rhs1; rhs2]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable lhs;
           xd#index_xpr rhs1;
           xd#index_xpr rhs2;
           xd#index_xpr result;
           xd#index_xpr rresult])

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

      | SubtractWide (_, rd, sp, imm) ->
         let lhs = rd#to_variable floc in
         let xsp = sp#to_expr floc in
         let ximm = imm#to_expr floc in
         let result = XOp (XMinus, [xsp; ximm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"],
          [xd#index_variable lhs;
           xd#index_xpr xsp;
           xd#index_xpr ximm;
           xd#index_xpr result;
           xd#index_xpr rresult])

      | TableBranchByte (_, _, rm, _) ->
         let xrm = rm#to_expr floc in
         (["a:x"], [xd#index_xpr xrm])

      | TableBranchHalfword (_, _, rm, _) ->
         let xrm = rm#to_expr floc in
         (["a:x"], [xd#index_xpr xrm])

      | SupervisorCall (_, _) ->
         let r7 = arm_register_op AR7 RD in
         let xr7 = r7#to_expr floc in
         (["a:x"], [xd#index_xpr xr7])

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

      | UnsignedExtendByte (_, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let result = xrm in
         let rresult = rewrite_expr result in
         (["a:vxxx"], [xd#index_variable vrd;
                       xd#index_xpr xrm;
                       xd#index_xpr result;
                       xd#index_xpr rresult])

      | UnsignedExtendHalfword (_, rd, rm) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         let result = xrm in
         let rresult = rewrite_expr result in
         (["a:vxxx"], [xd#index_variable vrd;
                       xd#index_xpr xrm;
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
      | VConvert (_, _, _, _, dst, src) ->
         let vdst = dst#to_variable floc in
         let src = src#to_expr floc in
         let rsrc = rewrite_expr src in
         (["a:vxx"],
          [xd#index_variable vdst; xd#index_xpr src; xd#index_xpr rsrc])

      | VLoadRegister (_, vd, rn, mem) ->
         let vvd = vd#to_variable floc in
         let xmem = mem#to_expr floc in
         (["a:vx"], [xd#index_variable vvd; xd#index_xpr xmem])

      | VMove (_, dst, src) ->
         let vdst = dst#to_variable floc in
         let src = src#to_expr floc in
         let rsrc = rewrite_expr src in
         (["a:vxx"],
          [xd#index_variable vdst; xd#index_xpr src; xd#index_xpr rsrc])

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
      
