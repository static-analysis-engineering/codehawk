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
open BCHApiParameter
open BCHBasicTypes
open BCHByteUtilities
open BCHConstantDefinitions
open BCHCPURegisters
open BCHDoubleword
open BCHFloc   
open BCHFunctionApi
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
          | _ -> x in
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
    let key =
      match instr#get_opcode with
      | Add (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XPlus, [xrn; xrm]) in
         let rresult = rewrite_expr result in
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

      | BitwiseOr (_, _, rd, rn, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrn = rn#to_expr floc in
         let xrm = rm#to_expr floc in
         let result = XOp (XBOr, [xrn; xrm]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"], [xd#index_variable vrd;
                        xd#index_xpr xrn;
                        xd#index_xpr xrm;
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

      | BranchLink (_, tgt) ->
         let xtgt = tgt#to_expr floc in
         (["a:x"], [xd#index_xpr xtgt])

      | BranchLinkExchange (_, tgt) ->
         let xtgt = tgt#to_expr floc in
         (["a:x"], [xd#index_xpr xtgt])

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

      | LoadMultipleIncrementAfter (_, _, rn, rl, mem) ->
         let lhss = rl#to_multiple_variable floc in
         let xtag =
           "a:" ^ (string_repeat "v" rl#get_register_count) in
         ([xtag], List.map xd#index_variable lhss)

      | LoadRegister (_, rt, rn, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"], [xd#index_variable vrt;
                      xd#index_xpr xmem;
                      xd#index_xpr xrmem])

      | LoadRegisterByte (_, rt, rn, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"], [xd#index_variable vrt;
                      xd#index_xpr xmem;
                      xd#index_xpr xrmem])

      | LoadRegisterHalfword (_, rt, rn, _, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"], [xd#index_variable vrt;
                      xd#index_xpr xmem;
                      xd#index_xpr xrmem])

      | LoadRegisterSignedHalfword (_, rt, rn, _, mem, _) ->
         let vrt = rt#to_variable floc in
         let xmem = mem#to_expr floc in
         let xrmem = rewrite_expr xmem in
         (["a:vxx"], [xd#index_variable vrt;
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

      | Move(_, _, rd, rm, _) ->
         let vrd = rd#to_variable floc in
         let xrm = rm#to_expr floc in
         (["a:vx"], [xd#index_variable vrd; xd#index_xpr xrm])

      | MoveTop (_, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm = imm#to_expr floc in
         let xrd = rd#to_expr floc in
         let ximm16 = XOp (XMult, [ximm; int_constant_expr e16]) in
         let xrdm16 = XOp (XMod, [xrd; int_constant_expr e16]) in
         let result = XOp (XPlus, [xrdm16; ximm16]) in
         let rresult = rewrite_expr result in
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
         (["a:vx"], [xd#index_variable vrd; xd#index_xpr ximm])

      | Pop (_, sp, rl, _) ->
         let lhsvars = List.map (fun op -> op#to_variable floc) rl#get_register_op_list in
         let rhsexprs =
           List.map (fun offset ->
               arm_sp_deref ~with_offset:offset RD)
             (List.init rl#get_register_count (fun i -> 4 * i)) in
         let rhsexprs = List.map (fun x -> x#to_expr floc) rhsexprs in
         let xtag = "a:"
                    ^ (string_repeat "v" rl#get_register_count)
                    ^ (string_repeat "x" rl#get_register_count) in
         let tags = [xtag] in
         let args =
           (List.map xd#index_variable lhsvars)
           @ (List.map xd#index_xpr rhsexprs) in
         (tags, args)

      | Push (_, sp, rl, _) ->
         let rhsexprs = List.map (fun op -> op#to_expr floc) rl#get_register_op_list in
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

      | StoreMultipleIncrementAfter (_, _, rn, rl, mem, _) ->
         let rhss = rl#to_multiple_expr floc in
         let xtag =
           "a:" ^ (string_repeat "x" rl#get_register_count) in
         ([xtag], List.map xd#index_xpr rhss)

      | StoreRegister (_, rt, rn, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         (["a:vxx"], [xd#index_variable vmem;
                      xd#index_xpr xrt;
                      xd#index_xpr xxrt])

      | StoreRegisterByte (_, rt, rn, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         (["a:vxx"], [xd#index_variable vmem;
                      xd#index_xpr xrt;
                      xd#index_xpr xxrt])

      | StoreRegisterHalfword (_, rt, rn, _, mem, _) ->
         let vmem = mem#to_variable floc in
         let xrt = rt#to_expr floc in
         let xxrt = rewrite_expr xrt in
         (["a:vxx"], [xd#index_variable vmem;
                      xd#index_xpr xrt;
                      xd#index_xpr xxrt])

      | Subtract (_, _, dst, src1, src2, _) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XMinus, [rhs1; rhs2]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"], [xd#index_variable lhs;
                        xd#index_xpr rhs1;
                        xd#index_xpr rhs2;
                        xd#index_xpr result;
                        xd#index_xpr rresult])

      | UnsignedBitFieldExtract (_, rd, rn) ->
         let lhs = rd#to_variable floc in
         let rhs = rn#to_expr floc in
         let rrhs = rewrite_expr rhs in
         (["a:vxx"],
          [xd#index_variable lhs; xd#index_xpr rhs; xd#index_xpr rrhs])

      | UnsignedExtendByte (_, rd, rm) ->
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
      
