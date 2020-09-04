(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma

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
open BCHFloc   
open BCHFunctionApi
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo

(* bchlibelf *)
open BCHELFHeader

(* bchlibmips32 *)
open BCHMIPSAssemblyInstructions
open BCHMIPSDisassemblyUtils
open BCHMIPSLoopStructure
open BCHMIPSOperand
open BCHMIPSDictionary
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
        let xpr = floc#inv#rewrite_expr (expand x) floc#env#get_variable_comparator in
        simplify_xpr (expand xpr)
      with IO.No_more_input ->
        begin
          pr_debug [ STR "Error in rewriting expression: " ; x2p x ;
                     STR ": No more input"; NL ];
          raise IO.No_more_input
        end in
    let get_condition_exprs thenxpr elsexpr =
      match restriction with
      | Some (BranchAssert false) -> (false_constant_expr,elsexpr)
      | Some (BranchAssert true) -> (thenxpr,false_constant_expr)
      | _ -> (thenxpr,elsexpr) in
    let key =
      match instr#get_opcode with
      | Add (dst,src,imm) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XPlus, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      | AddImmediate (dst,src,imm) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XPlus, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      | AddUpperImmediate (dst,src,imm) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
         let lhs = dst#to_variable floc in
         let result = XOp (XPlus, [ rhs2; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs; xd#index_xpr rhs1; xd#index_xpr rhs2;
                          xd#index_xpr result; xd#index_xpr rresult ])

      | AddImmediateUnsigned (dst,src,imm) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XPlus, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         let _ = ignore (get_string_reference floc rresult) in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      | AddUnsigned (dst,src1,src2) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XPlus, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      | And (dst,src,imm) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XBAnd, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      | AndImmediate (dst,src,imm) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XBAnd, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      | CountLeadingZeros (dst,src) ->
         let rhs = src#to_expr floc in
         let lhs = dst#to_variable floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ])

      | BranchEqual (src1,src2,tgt) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XEq, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxxx" ],[ xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ;
                          xd#index_xpr negresult ])

      | BranchEqualLikely (src1,src2,tgt) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XEq, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxxx" ],[ xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ;
                          xd#index_xpr negresult ])

      | BranchGEZero (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XGe, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchGEZeroLikely (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XGe, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchGEZeroLink (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XGe, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         ([ "a:xxx" ],[ xd#index_xpr rhs ; xd#index_xpr result ;
                        xd#index_xpr rresult ])

      | BranchGTZero (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XGt, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchGTZeroLikely (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XGt, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchLEZero (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XLe, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchLEZeroLikely (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XLe, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchLTZero (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XLt, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchLTZeroLikely (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XLt, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxx" ], [ xd#index_xpr rhs ; xd#index_xpr result ;
                          xd#index_xpr rresult ; xd#index_xpr negresult ])

      | BranchLTZeroLink (src,tgt) ->
         let rhs = src#to_expr floc in
         let result = XOp (XLt, [ rhs ; zero_constant_expr ]) in
         let rresult = rewrite_expr result in
         ([ "a:xxx" ],[ xd#index_xpr rhs ; xd#index_xpr result ;
                        xd#index_xpr rresult ])

      | BranchNotEqual (src1,src2,tgt) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XNe, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxxx" ],[ xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ;
                          xd#index_xpr negresult ])

      | BranchNotEqualLikely (src1,src2,tgt) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XNe, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         let negresult = rewrite_expr (XOp (XLNot, [ rresult ])) in
         let (rresult,negresult) = get_condition_exprs rresult negresult in
         ([ "a:xxxxx" ],[ xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ;
                          xd#index_xpr negresult ])

      | DivideWord (hi,lo,rs,rt) ->
         let lhshi = hi#to_variable floc in
         let lhslo = lo#to_variable floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = rt#to_expr floc in
         let resultlo = XOp (XDiv, [ rhs1; rhs2 ]) in
         let resulthi = XOp (XMod, [ rhs1; rhs2 ]) in
         let rresultlo = rewrite_expr resultlo in
         let rresulthi = rewrite_expr resulthi in
         ([ "a:vvxxxxxx" ],[ xd#index_variable lhslo; xd#index_variable lhshi;
                             xd#index_xpr rhs1; xd#index_xpr rhs2;
                             xd#index_xpr resultlo; xd#index_xpr resulthi;
                             xd#index_xpr rresultlo; xd#index_xpr rresulthi ])

      | ExtractBitField (dst,src,pos,size) ->
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                        xd#index_xpr rrhs ])

      | InsertBitField (dst,src,pos,size) ->
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                        xd#index_xpr rrhs ])

      | JumpLink _ | BranchLink _
           when floc#has_call_target
                && floc#get_call_target#is_signature_valid ->
         let args = List.map snd floc#get_mips_call_arguments in
         let xtag = "a:" ^ (string_repeat "x" (List.length args)) in
         if (List.length args) > 0 then 
           ([ xtag ], (List.map xd#index_xpr args)
                      @ [ ixd#index_call_target
                            floc#get_call_target#get_target ])
         else
           ([],[ ixd#index_call_target floc#get_call_target#get_target ])
                          
      | JumpLink _ | BranchLink _ when floc#has_call_target ->
         ([],[ ixd#index_call_target floc#get_call_target#get_target ])

      | JumpLink _ | BranchLink _ -> ([],[])

      | JumpLinkRegister _
           when floc#has_call_target
                  && floc#get_call_target#is_signature_valid ->
         let args = List.map snd floc#get_mips_call_arguments in
         let args = List.map rewrite_expr args in
         let xtag = "a:" ^ (string_repeat "x" (List.length args)) in
         if (List.length  args) > 0 then
           ([ xtag ], (List.map xd#index_xpr args)
                      @ [ ixd#index_call_target
                            floc#get_call_target#get_target ])
         else
           ([],[ ixd#index_call_target
                   floc#get_call_target#get_target ])

      | JumpLinkRegister (dst,tgt) ->
         let tgt = rewrite_expr (tgt#to_expr floc) in
         ([ "a:x" ],[ xd#index_xpr tgt ])

      | JumpRegister _
           when floc#has_call_target
                  && floc#get_call_target#is_signature_valid ->
         let args = List.map snd floc#get_mips_call_arguments in
         let xtag = "a:" ^ (string_repeat "x" (List.length args)) in
         if (List.length  args) > 0 then
           ([ xtag ], (List.map xd#index_xpr args)
                      @ [ ixd#index_call_target
                            floc#get_call_target#get_target ])
         else
           ([],[ ixd#index_call_target floc#get_call_target#get_target ])

      | JumpRegister tgt ->
         let rhs = rewrite_expr (tgt#to_expr floc) in
         let iaddr = floc#ia in
         let faddr = floc#fa in
         if  system_info#has_jump_table_target faddr iaddr then
           let (jt,jta,lb,ub) =
             system_info#get_jump_table_target faddr iaddr in
           let tgts = jt#get_indexed_targets jta lb ub in
           ([ "a:x" ; "table" ],
            (xd#index_xpr rhs) ::
              (List.concat
                 (List.map (fun (i,dw) -> [ i ; bd#index_address dw  ]) tgts)))
         else
           ([ "a:x" ],[ xd#index_xpr rhs ])

      | LoadByte (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in         
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                        xd#index_xpr addr ])

      | LoadByteUnsigned (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in         
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                        xd#index_xpr addr ])

      | LoadDoublewordToFP (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in         
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                        xd#index_xpr addr ])

      | LoadHalfWord (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                       xd#index_xpr addr ])

      | LoadHalfWordUnsigned (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in         
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                        xd#index_xpr addr ])

      | LoadImmediate (dst,imm) ->
         let rhs = imm#to_expr floc in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | LoadLinkedWord (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in
         let rhs = rewrite_expr (src#to_expr floc)  in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr addr ])

      | LoadUpperImmediate (dst,imm) ->
         let rhs = num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | LoadWord (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr addr ])

      | LoadWordFP (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                        xd#index_xpr addr ])

      | LoadWordLeft (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in         
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr addr ])

      | LoadWordRight (dst,src) ->
         let addr = rewrite_expr (src#to_address floc) in         
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr addr ])

      | MoveConditionalNotZero (dst,src,testxpr) ->
         let lhs = dst#to_variable floc in
         let rhs = rewrite_expr (src#to_expr floc) in
         let testxpr = rewrite_expr (testxpr#to_expr floc) in
         let cond = XOp (XNe, [ testxpr; zero_constant_expr ]) in
         let ccond = rewrite_expr cond in
         ([ "a:vxxx" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                         xd#index_xpr cond; xd#index_xpr ccond ])

      | MoveConditionalZero (dst,src,testxpr) ->
         let lhs = dst#to_variable floc in
         let rhs = rewrite_expr (src#to_expr floc) in
         let testxpr = rewrite_expr (testxpr#to_expr floc) in
         let cond = XOp (XEq, [ testxpr; zero_constant_expr ]) in
         let ccond = rewrite_expr cond in
         ([ "a:vxxx" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                         xd#index_xpr cond; xd#index_xpr ccond ])

      | MoveFromLo (rd,lo) ->
         let lhs = rd#to_variable floc in
         let rhs = rewrite_expr (lo#to_expr floc) in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | MoveFromHi (rd,hi) ->
         let lhs = rd#to_variable floc in
         let rhs = rewrite_expr (hi#to_expr floc) in
         ([ "a:vx" ],[ xd#index_variable lhs; xd#index_xpr rhs ])

      | MoveToLo (lo,rs) ->
         let lhs = lo#to_variable floc in
         let rhs = rewrite_expr (rs#to_expr floc) in
         ([ "a:vx" ],[ xd#index_variable lhs; xd#index_xpr rhs ])

      | MoveToHi (hi,rs) ->
         let lhs = hi#to_variable floc in
         let rhs = rewrite_expr (rs#to_expr floc) in
         ([ "a:vx" ],[ xd#index_variable lhs; xd#index_xpr rhs ])

      | Move (dst,src) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | MoveWordFromFP (dst,src) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | MoveWordFromHighHalfFP (dst,src) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | MoveWordToHighHalfFP (src,dst) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | MoveFromCoprocessor0 (dst,src,sel) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | MoveToCoprocessor0 (src,dst,sel) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         ([ "a:x" ],[ xd#index_xpr rhs ])

      | MoveFromHighCoprocessor0 (dst,src,sel) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         let lhs = dst#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])

      | MoveToHighCoprocessor0 (src,dst,_) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         ([ "a:x" ],[ xd#index_xpr rhs ])

      | MoveWordFromCoprocessor2 (dst,_,_) ->
         let lhs = dst#to_variable floc in
         ([ "a:v" ],[ xd#index_variable lhs ])

      | MoveWordToCoprocessor2 (src,_,_) ->
         let rhs = rewrite_expr (src#to_expr floc) in
         ( [ "a:x" ],[ xd#index_xpr rhs ])

      | MoveWordFromHighHalfCoprocessor2 (dst,_,_) ->
         let lhs = dst#to_variable floc in
         ([ "a:v" ],[ xd#index_variable lhs ])

      | MultiplyWord (hi,lo,rs,rt) ->
         let lhshi = hi#to_variable floc in
         let lhslo = lo#to_variable floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = rt#to_expr floc in
         let result = XOp (XMult, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vvxxxx" ],[ xd#index_variable lhshi ; xd#index_variable lhslo ;
                           xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                           xd#index_xpr result ; xd#index_xpr rresult ])

      | MultiplyUnsignedWord (hi,lo,rs,rt) ->
         let lhshi = hi#to_variable floc in
         let lhslo = lo#to_variable floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = rt#to_expr floc in
         let result = XOp (XMult, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vvxxxx" ],[ xd#index_variable lhshi ; xd#index_variable lhslo ;
                           xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                           xd#index_xpr result ; xd#index_xpr rresult ])

      | MultiplyAddWord (hi,lo,rs,rt) ->
         let lhshi = hi#to_variable floc in
         let lhslo = lo#to_variable floc in
         let rhshi = hi#to_expr floc in
         let rhslo = lo#to_expr floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = rt#to_expr floc in
         let result = XOp (XMult, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vvxxxxxx" ],[ xd#index_variable lhshi ; xd#index_variable lhslo ;
                             xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                             xd#index_xpr rhslo ; xd#index_xpr rhshi  ;
                             xd#index_xpr result ; xd#index_xpr rresult ])

      | MultiplyAddUnsignedWord (hi,lo,rs,rt) ->
         let lhshi = hi#to_variable floc in
         let lhslo = lo#to_variable floc in
         let rhshi = hi#to_expr floc in
         let rhslo = lo#to_expr floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = rt#to_expr floc in
         let result = XOp (XMult, [ rhs1; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vvxxxxxx" ],[ xd#index_variable lhshi; xd#index_variable lhslo;
                             xd#index_xpr rhs1; xd#index_xpr rhs2;
                             xd#index_xpr rhslo; xd#index_xpr rhshi;
                             xd#index_xpr result; xd#index_xpr rresult ])

      | Nor (dst,src1,src2) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XBNor, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])         

      | Or (dst,src1,src2) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XBOr, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])         

      | OrImmediate (dst,src,imm) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let result = XOp (XBOr, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      | Prefetch (addr,hint) ->
         let rhs = addr#to_expr floc in
         ([ "a:a" ],[ xd#index_xpr rhs ])

      | ReadHardwareRegister (dst,index) ->
         let lhs = dst#to_variable floc in
         ([ "a:v" ],[ xd#index_variable lhs ])

      | Return ->
         let rvar = floc#f#env#mk_mips_register_variable MRv0 in
         let result = rewrite_expr (XVar rvar) in
         ([ "a:x" ],[ xd#index_xpr result ])                  

      | SetLT (rd,rs,rt) ->
         let lhs = rd#to_variable floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = rt#to_expr floc in
         let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      | SetLTImmediate (rt,rs,imm) ->
         let lhs = rt#to_variable floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      | SetLTImmediateUnsigned (rt,rs,imm) ->
         let lhs = rt#to_variable floc in
         let rhs1 = rs#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      | SetLTUnsigned (dst,src1,src2) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      | ShiftLeftLogical (dst,src,imm) ->
         let rhs = src#to_expr floc in
         let lhs = dst#to_variable floc in
         (match imm#to_expr floc with
          | XConst (IntConst n) ->
             let m = get_multiplier n in
             let result = XOp (XMult, [ rhs ; m ]) in
             let rresult = rewrite_expr result in
             ([ "a:vxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                             xd#index_xpr result ; xd#index_xpr rresult ])
          | _ ->
             raise (BCH_failure
                      (LBLOCK [ STR "Unexpected operand for ShiftLeftLogical" ;
                                imm#toPretty ])))

      | ShiftLeftLogicalVariable (dst,src1,src2) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XShiftlt, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])         
         

      | ShiftRightArithmetic (dst,src,imm) ->
         let rhs = src#to_expr floc in
         let lhs = dst#to_variable floc in
         (match imm#to_expr floc with
          | XConst (IntConst n) ->
             let m = get_multiplier n in
             let result = XOp (XDiv, [ rhs ; m ]) in
             let rresult = rewrite_expr result in
             ([ "a:vxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                             xd#index_xpr result ; xd#index_xpr rresult ])
          | _ ->
             raise (BCH_failure
                      (LBLOCK [ STR "Unexpected operand for ShiftRightArithmetic: " ;
                                imm#toPretty ])))

      | ShiftRightArithmeticVariable (dst,src1,src2) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XShiftrt, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])         

      | ShiftRightLogical (dst,src,imm) ->
         let rhs = src#to_expr floc in
         let lhs = dst#to_variable floc in
         (match imm#to_expr floc with
          | XConst (IntConst n) ->
             let m = get_multiplier n in
             let result = XOp (XDiv, [ rhs ; m ]) in
             let rresult = rewrite_expr result in
             ([ "a:vxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                             xd#index_xpr result ; xd#index_xpr rresult ])
          | _ ->
             raise (BCH_failure
                      (LBLOCK [ STR "Unexpected operand for ShiftRightLogical: " ;
                                imm#toPretty ])))

      | ShiftRightLogicalVariable (dst,src1,src2) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XShiftrt, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      | SignExtendByte (dst,src) ->
         let rhs = src#to_expr floc in
         let lhs = dst#to_variable floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                        xd#index_xpr rrhs ])

      | SignExtendHalfword (dst,src) ->
         let rhs = src#to_expr floc in
         let lhs = dst#to_variable floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                        xd#index_xpr rrhs ])

      | StoreByte (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in         
         let rrhs = rewrite_expr rhs in
         ([ "a:vxxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ;
                         xd#index_xpr addr ])

      | StoreHalfWord (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in         
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in         
         let rrhs = rewrite_expr rhs in
         ([ "a:vxxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ;
                         xd#index_xpr addr ])

      | StoreWord (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in         
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in         
         let rrhs = rewrite_expr rhs in
         ([ "a:vxxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ;
                         xd#index_xpr addr ])

      | StoreWordFromFP (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in
         ([ "a:vxa" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                        xd#index_xpr addr ])

      | StoreDoublewordFromFP (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in
         ([ "a:vxa" ],[ xd#index_variable lhs; xd#index_xpr rhs;
                        xd#index_xpr addr ])

      | StoreConditionalWord (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in         
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in         
         let rrhs = rewrite_expr rhs in
         ([ "a:vxxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ;
                         xd#index_xpr addr ])         

      | StoreWordLeft (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in         
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in         
         let rrhs = rewrite_expr rhs in
         ([ "a:vxxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ;
                        xd#index_xpr addr ])

      | StoreWordRight (dst,src) ->
         let addr = rewrite_expr (dst#to_address floc) in
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in         
         let rrhs = rewrite_expr rhs in
         ([ "a:vxxa" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ;
                         xd#index_xpr addr ])

      | SubtractUnsigned (dst,src1,src2) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XMinus, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      | Syscall _ when floc#has_call_target ->
         let args = List.map snd floc#get_mips_call_arguments in
         let args = List.map rewrite_expr args in
         let xargs = List.map xd#index_xpr args in
         let xargs = xargs @ [ ixd#index_call_target floc#get_call_target#get_target ] in
         let xtag = "a:" ^ (string_repeat "x" ((List.length args) + 1)) in
         let syscallindex = floc#env#mk_mips_register_variable MRv0 in
         let syscallindex = rewrite_expr (XVar syscallindex) in
         ([ xtag ],[ xd#index_xpr syscallindex ] @ xargs)

      | Syscall _ ->
         let arg = floc#env#mk_mips_register_variable MRv0 in
         let argval = rewrite_expr (XVar arg) in
         ([ "a:x" ],[ xd#index_xpr argval ])

      | TrapIfEqualImmediate (src,imm) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let rrhs1 = rewrite_expr rhs1 in
         ([ "a:xxx" ],[ xd#index_xpr rhs1; xd#index_xpr rhs2; xd#index_xpr rrhs1 ])

      | WordSwapBytesHalfwords (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                        xd#index_xpr rrhs ])

      | Xor (dst,src1,src2) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XBXor, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])         

      | XorImmediate (dst,src,imm) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = imm#to_expr floc in
         let result = XOp (XBXor, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])


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
           begin t#write_xml tnode ; tnode end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables ;

  method toPretty =
    LBLOCK
      (List.map
         (fun t ->
           LBLOCK [ STR t#get_name ; STR ": " ; INT t#size ; NL ]) tables)
    
end

let mk_mips_opcode_dictionary = new mips_opcode_dictionary_t
