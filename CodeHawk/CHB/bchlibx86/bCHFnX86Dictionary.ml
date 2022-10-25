(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
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
open BCHFloc   
open BCHFunctionInterface
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO

(* bchlibx86 *)
open BCHAssemblyInstructions
open BCHDisassemblyUtils
open BCHConditionalJumpExpr
open BCHLibx86Types
open BCHOperand
open BCHX86Dictionary
open BCHX86OpcodeRecords


module B = Big_int_Z
module H = Hashtbl

let x2p = xpr_formatter#pr_expr

let bd = BCHDictionary.bdictionary
let ixd = BCHInterfaceDictionary.interface_dictionary

class x86_opcode_dictionary_t
        (faddr:doubleword_int)
        (vard:vardictionary_int):x86_opcode_dictionary_int =
object (self)

  val esp_offset_table = mk_index_table "sp-offset-table"
  val opx_table = mk_index_table "opx-table"
  val instrx_table = mk_index_table "instrx-table"  (* operands for instruction *)
  val xd = vard#xd

  val mutable tables = []

  initializer
    tables <- [
      esp_offset_table ;
      opx_table ;
      instrx_table
    ]

  method index_esp_offset (o:(int * interval_t)) =
    let (level,offset) = o in
    let key = ([],[ level ; xd#index_interval offset ]) in
    esp_offset_table#add key

  method get_esp_offset (index:int) =
    let (tags,args) = esp_offset_table#retrieve index in
    let a = a "esp-offset" args in
    (a 0, xd#get_interval (a 1))

  (* Legend for tags:
     "nop": instruction is no-op,
     "arg": source argument is an argument to call at given callsite,
     "save": saving a register to the stack,
     "a:" (prefix,arg-key) (if present should be first): 
          x: xpr; v: variable ; l: literal int ; s: string
   *) 

  method index_instr (instr:assembly_instruction_int) (floc:floc_int) =
    let rewrite_expr (x: xpr_t):xpr_t =
      floc#inv#rewrite_expr x floc#env#get_variable_comparator in
    let rewrite_test_expr (csetter: ctxt_iaddress_t) (x: xpr_t): xpr_t =
      let testloc = ctxt_string_to_location floc#fa csetter in
      let testfloc = get_floc testloc in
      let xpr =
        testfloc#inv#rewrite_expr x testfloc#env#get_variable_comparator in
      simplify_xpr xpr in
    let key =
      match instr#get_opcode with
      (* ------------------------------------------------------------- Add -- *)
      | Add (dst,src) | AddCarry (dst,src) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XPlus, [ rhs2 ; rhs1 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr result ; xd#index_xpr rresult ])

      (* --------------------------------------------- ConvertLongToDouble -- *)
      | ConvertLongToDouble (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ])

      (* ------------------------------------------------------- Decrement -- *)         
      | Decrement op ->
         let rhs = op#to_expr floc in
         let lhs = op#to_variable floc in
         let rhsx = XOp (XMinus, [ rhs ; int_constant_expr 1 ]) in
         let rrhsx = rewrite_expr rhsx in
         ([ "a:vxxx" ], [ xd#index_variable lhs ; xd#index_xpr rhs ;
                          xd#index_xpr rhsx ; xd#index_xpr rrhsx ])

      (* ----------------------------------------------------- Direct Call -- *)                  
      | DirectCall _ | IndirectCall _ when floc#has_call_target ->
         let args = floc#get_call_args in
         let xargs = List.map xd#index_xpr (List.map snd args) in
         let _ =
           List.iter (fun x -> ignore (get_string_reference floc x)) (List.map snd args) in
         let xtag = "a:" ^ (string_repeat "x" (List.length args)) in
         ([ xtag ],xargs @ [ixd#index_call_target floc#get_call_target#get_target ])

      | IndirectCall op ->
         let opx = op#to_expr floc in
         let ropx = rewrite_expr opx in
         let args = floc#get_call_args in
         let xargs = List.map xd#index_xpr (List.map snd args) in
         let _ =
           List.iter (fun x -> ignore (get_string_reference floc x)) (List.map snd args) in
         let xtag = "a:" ^ (string_repeat "x" ((List.length args) + 2)) in
         ([ xtag ; "u" ],[ xd#index_xpr opx ; xd#index_xpr ropx ] @ xargs)

      (* ----------------------------------------------------- Direct Jump -- *)

      | DirectJmp op when op#is_absolute_address ->
         ([],[ bd#index_address op#get_absolute_address ])

      (* ------------------------------------------------------- Increment -- *)                  
      | Increment op ->
         let rhs = op#to_expr floc in
         let lhs = op#to_variable floc in
         let rhsx = XOp (XPlus, [ rhs ; int_constant_expr 1 ]) in
         let rrhsx = rewrite_expr rhsx in
         ([ "a:vxxx" ], [ xd#index_variable lhs ; xd#index_xpr rhs ;
                          xd#index_xpr rhsx ; xd#index_xpr rrhsx ])

      (* ----------------------------------------------------- IndirectJmp -- *)

      | IndirectJmp op when floc#has_jump_target ->
         (match  floc#get_jump_target with
          | JumptableTarget (base,_,reg) ->
             let indexVar = floc#f#env#mk_register_variable reg in
             let vx = rewrite_expr  (XVar indexVar) in
             if floc#is_interval indexVar then
               let range = floc#get_interval indexVar in
               ([ "a:xxi" ],[ xd#index_xpr (op#to_expr  floc) ;
                              xd#index_xpr vx ;
                              xd#index_interval range ;
                              bd#index_register reg ;
                              bd#index_address base ])
             else
               ([ "a:xx" ],[ xd#index_xpr (op#to_expr floc) ;
                             xd#index_xpr vx ;
                             bd#index_register reg ;
                             bd#index_address base ])
          | _ ->
             let _ = chlog#add "other jump target"
                               (LBLOCK  [ floc#l#toPretty ; STR "; " ;
                                          x2p (op#to_expr floc) ]) in
             ([ "a:x" ],[ xd#index_xpr (op#to_expr floc) ]))

      | IndirectJmp op ->
         let tgtop = op#to_expr floc in
         ([ "a:x" ],[ xd#index_xpr tgtop ])

      (* ------------------------------------------------------------- Jcc -- *)
      | Jcc (_,op) | Jecxz op ->
         if op#is_absolute_address then
           if floc#has_test_expr then
             let tcond = floc#get_test_expr in
             let fcond = XOp (XLNot, [tcond]) in
             let csetter = floc#f#get_associated_cc_setter floc#cia in
             let tcond = rewrite_test_expr csetter tcond in
             let fcond = rewrite_test_expr csetter fcond in
             (["a:xx"], [xd#index_xpr tcond; xd#index_xpr fcond])
           else
             ([],[])
         else
           ([],[])

      (* ------------------------------------------------------------- Lea -- *)
      | Lea (dst,src) ->
         let lhs = dst#to_variable floc in       
         let rhs = src#to_address floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ])

      (* ------------------------------------------------------ LogicalAnd -- *)
      | LogicalAnd (dst,src) when src#is_zero ->
         let lhs = dst#to_variable floc in
         ([ "a:v" ],[ xd#index_variable lhs ])

      | LogicalAnd (dst,src)
           when dst#is_register && (dst#get_cpureg = Esp) && src#is_immediate_value
                && (match src#get_immediate_value#to_int with
                    | Some i -> i < 0 | _ -> false) ->
         (match src#get_immediate_value#to_int with
          | Some i -> ([ "stack-realign" ],[ (-i) ])
          | _ ->
             raise (BCH_failure (LBLOCK [ STR "Internal error in LogicalAnd" ])))

      | LogicalAnd (dst,src) when dst#is_register && dst#equal src ->
         let lhs = dst#to_variable floc in
         let rhs = dst#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ])         

      | LogicalAnd (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         let result = XOp (XBAnd, [ rhs2 ; rhs1 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      (* ------------------------------------------------------- LogicalOr -- *)
      | LogicalOr (dst,src) when
             src#is_immediate_value
             && (src#get_immediate_value#to_numerical#equal (mkNumerical (-1))) ->
         let lhs = dst#to_variable floc in
         ([ "a:v" ],[ xd#index_variable lhs ])

      | LogicalOr (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         let result = XOp (XBOr, [ rhs2 ; rhs1 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      (* ------------------------------------------------------------- Mov -- *)
      | Mov (_, dst,src)
        | Xchg (dst,src) when dst#equal src -> ([ "nop" ],[])
                                             
      | Mov (_, _, src) when src#is_function_argument ->
         let (callsite,argindex) = src#get_function_argument in
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:xx" ; "arg" ; callsite ],[ xd#index_xpr rhs ; xd#index_xpr rrhs ;
                                          argindex ])

      | Mov (_, dst,src) ->
         let lhs = dst#to_variable floc in         
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ])

      (* ------------------------------------------------------------ Movs -- *)
      | Movs(_,dst,src,srcptr,dstptr) ->
         let lhs = dst#to_variable floc in
         let lhssrcptr = srcptr#to_variable floc in
         let lhsdstptr = dstptr#to_variable floc in
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         let rhssrcptr = srcptr#to_expr floc in
         let rrhssrcptr = rewrite_expr rhssrcptr in
         let rhsdstptr = dstptr#to_expr floc in
         let rrhsdstptr = rewrite_expr rhsdstptr in
         ([ "a:vvvxxxxxx" ],[ xd#index_variable lhs ; xd#index_variable lhssrcptr ;
                              xd#index_variable lhsdstptr ;
                              xd#index_xpr rhs ; xd#index_xpr rrhs ;
                              xd#index_xpr rhssrcptr ; xd#index_xpr rrhssrcptr ;
                              xd#index_xpr rhsdstptr ; xd#index_xpr rrhsdstptr ])

      (* ----------------------------------------------------------- Movsx -- *)         
      | Movsx (_, dst, src) ->
         let lhs = dst#to_variable floc in
         let rhs = src#to_expr floc in         
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ])

      (* ----------------------------------------------------------- Movzx -- *)         
      | Movzx (_, dst, src) ->
         let lhs = dst#to_variable floc in         
         let rhs = src#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ; xd#index_xpr rrhs ])

      (* ------------------------------------------------------------- Not -- *)
      | OnesComplementNegate op ->
         let lhs = op#to_variable floc in
         let rhs = op#to_expr floc in
         let rhsx =  XOp (XBNot, [ rhs ]) in
         let rrhsx = rewrite_expr rhsx in
         ([ "a:vxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                         xd#index_xpr rhsx ; xd#index_xpr rrhsx ])                   
         
      (* ------------------------------------------------------------- Pop -- *)         
      | Pop (_,op) when op#is_register ->
         let lhs = op#to_variable floc in
         let rhs = (esp_deref RD)#to_expr floc in
         let rhs = floc#inv#rewrite_expr rhs floc#env#get_variable_comparator in
         let initVal = floc#env#mk_initial_register_value (CPURegister op#get_cpureg) in
         let rhsix = xd#index_xpr rhs in
         let initValix = xd#index_xpr (XVar initVal) in
         if rhsix = initValix then
           let tags = [ "a:v" ; "restore" ] in
           let args = [ xd#index_variable lhs ] in
           (tags,args)
         else
           let esp = floc#env#mk_cpu_register_variable Esp in
           let espx = XOp (XPlus, [ XVar esp ; int_constant_expr 4 ]) in
           let respx = rewrite_expr espx in
           let tags = [ "a:vxxx" ] in
           let args = [ xd#index_variable lhs ; rhsix ; xd#index_xpr espx ;
                        xd#index_xpr respx ] in
           (tags,args)

      | Pop (_,op) ->
         let lhs = op#to_variable floc in
         let rhs = (esp_deref RD)#to_expr floc in
         let esp = floc#env#mk_cpu_register_variable Esp in
         let espx = XOp (XPlus, [ XVar esp ; int_constant_expr 4 ]) in
         let respx = rewrite_expr espx in
         let tags = [ "a:vxxx" ] in
         let args = [ xd#index_variable lhs ; xd#index_xpr rhs ;
                      xd#index_xpr espx ; xd#index_xpr respx ] in
         (tags,args)

      (* ------------------------------------------------------------ Push -- *)
      | Push (_,op) when op#is_function_argument ->
         let (callsite,argindex) = op#get_function_argument in
         let rhs = op#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:xx"; "arg" ; callsite ],[ xd#index_xpr rhs ; xd#index_xpr rrhs ;
                                         argindex ])       

      | Push (_,op) when op#is_register ->
         let var = floc#env#mk_cpu_register_variable op#get_cpureg in
         if floc#has_initial_value var then
           let tags = [ "a:v" ; "save" ] in
           let args = [ xd#index_variable var ] in
           (tags,args)
         else
           let rhs = op#to_expr floc in
           let lhs_op = esp_deref ~with_offset:(-4) WR in
           let lhs = lhs_op#to_variable floc in
           let tags = [ "a:vx" ] in
           let args = [ xd#index_variable lhs ; xd#index_xpr rhs ] in
           (tags,args)

      | Push (_,op) ->
         let rhs = op#to_expr floc in
         let lhs_op = esp_deref ~with_offset:(-4) WR in
         let lhs = lhs_op#to_variable floc in
         let tags = [ "a:vx" ] in
         let args = [ xd#index_variable lhs ; xd#index_xpr rhs ] in
         (tags,args)

      (* ------------------------------------------------------------- Ret -- *)
      | Ret (Some numPopped) ->
         let eaxop = eax_r RD in
         let rhs = eaxop#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:xx" ],[ xd#index_xpr rhs ; xd#index_xpr rrhs ; numPopped ])

      | Ret None ->
         let eaxop = eax_r RD in
         let rhs = eaxop#to_expr floc in
         let rrhs = rewrite_expr rhs in
         ([ "a:xx" ],[ xd#index_xpr rhs ; xd#index_xpr rrhs ])
         
      (* ------------------------------------------------------------- Rcl -- *)
      | Rcl (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                        xd#index_xpr rhs2 ])
         
      (* ------------------------------------------------------------- Rcr -- *)
      | Rcr (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                        xd#index_xpr rhs2 ])
         
      (* ------------------------------------------------------------- Rol -- *)
      | Rol (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                        xd#index_xpr rhs2 ])

      (* ------------------------------------------------------------- Ror -- *)
      | Ror (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                        xd#index_xpr rhs2 ])

      (* ------------------------------------------------------------- Sar -- *)
      | Sar (dst,src) when src#is_immediate_value ->
         let lhs = dst#to_variable floc in
         let rhsexp = src#to_expr floc in
         let rhsbase = dst#to_expr floc in
         (match rhsexp with
          | XConst (IntConst n) when n#geq numerical_zero && n#lt (mkNumerical 32) ->
             let d = mkNumerical_big (B.power_int_positive_int 2 n#toInt) in
             let result = XOp (XDiv, [ rhsbase ; num_constant_expr d ]) in
             let rresult = rewrite_expr result in
             ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhsbase ;
                              xd#index_xpr rhsexp ; xd#index_xpr result ;
                              xd#index_xpr rresult ])
          | XConst (IntConst n) ->
             begin
               ch_error_log#add "shift righ exponent out of range"
                                (LBLOCK [ floc#l#toPretty ;  STR ": " ; n#toPretty ]) ;
               ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhsbase ;
                              xd#index_xpr rhsexp ])
             end
          | _ ->
             raise (BCH_failure (LBLOCK [ STR "Internal error in Sar" ])))

      (* ------------------------------------------------------------- Sbb -- *)
      | SubBorrow (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = dst#to_expr floc in
         let rhs2 = src#to_expr floc in
         let rhsexp = XOp (XMinus, [ rhs1 ; rhs2 ]) in
         let rhsexpb = XOp (XPlus, [ rhsexp ; one_constant_expr ]) in
         let rrhsexp = rewrite_expr rhsexp in
         let rrhsexpb = rewrite_expr rhsexpb in
         ([ "a:vxxxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                            xd#index_xpr rhs2 ; xd#index_xpr rhsexp ;
                            xd#index_xpr rrhsexp ; xd#index_xpr rhsexpb ;
                            xd#index_xpr rrhsexpb ])               

      (* ----------------------------------------------------------- Setcc -- *)
      | Setcc (_,op) when floc#f#has_associated_cc_setter floc#cia ->
         let testiaddr = floc#f#get_associated_cc_setter floc#cia in
         let testloc = ctxt_string_to_location faddr testiaddr in
         let testopc = ((!assembly_instructions)#at_address testloc#i)#get_opcode in
         let setopc = instr#get_opcode in
         let setloc = floc#l in
         let setexpr = conditional_set_expr ~setopc ~testopc ~setloc ~testloc in
         let lhs = op#to_variable floc in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr setexpr ])

      | Setcc (_,op) ->
         let lhs = op#to_variable floc in
         let rhs = XOp (XNumRange, [ zero_constant_expr ; one_constant_expr ]) in
         ([ "a:vx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ])
         
      (* ------------------------------------------------------------- Shl -- *)
      | Shl (dst, src) when src#is_immediate_value ->
         let lhs = dst#to_variable floc in
         let rhsexp = src#to_expr floc in
         let rhsbase = dst#to_expr floc in
         (match rhsexp with
          | XConst (IntConst n) when n#geq numerical_zero && n#lt (mkNumerical 32) ->
             let m = mkNumerical_big (B.power_int_positive_int 2 n#toInt) in
             let result = XOp (XMult, [ num_constant_expr m ; rhsbase ]) in
             let rresult = rewrite_expr result in
             ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhsbase ;
                              xd#index_xpr rhsexp ; xd#index_xpr result ;
                              xd#index_xpr rresult ])
          | XConst (IntConst n) ->
             begin
               ch_error_log#add "shift left exponent out of range"
                                (LBLOCK  [ floc#l#toPretty ; STR ": " ;  n#toPretty ]) ;
               ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhsbase ;
                              xd#index_xpr rhsexp ])
             end
          | _ ->
             raise (BCH_failure (LBLOCK [ STR "Internal error in Shl" ])))

      | Shl (dst, src) ->
         let lhs = dst#to_variable floc in
         let rhsexp = src#to_expr floc in
         let rhsbase = dst#to_expr floc in
         let result = XOp (XShiftlt, [rhsbase; rhsexp]) in
         let rresult = rewrite_expr result in
         (["a:vxxxx"], [
            xd#index_variable lhs;
            xd#index_xpr rhsbase;
            xd#index_xpr rhsexp;
            xd#index_xpr result;
            xd#index_xpr rresult])

      (* ------------------------------------------------------------ Shld -- *)
      | Shld (dst,src,shift) when shift#is_immediate_value ->
         let lhs = dst#to_variable floc in
         let rhs1 = dst#to_expr floc in
         let rrhs1 = rewrite_expr rhs1 in         
         let rhs2 = src#to_expr floc in
         let rrhs2 = rewrite_expr rhs2 in         
         let imm = shift#to_expr floc in
         ([ "a:vxxxxx"],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rrhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr rrhs2 ; xd#index_xpr imm ])

      (*  ------------------------------------------------------------ Shr -- *)
      | Shr (dst,src) when src#is_immediate_value ->
         let lhs = dst#to_variable floc in
         let rhsexp = src#to_expr floc in
         let rhsbase = dst#to_expr floc in
         (match rhsexp with
          | XConst (IntConst n) when n#geq numerical_zero && n#lt (mkNumerical 32) ->
             let result = XOp (XShiftrt, [ rhsbase ; num_constant_expr n ]) in
             let rresult = rewrite_expr result in
             ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhsbase ;
                              xd#index_xpr rhsexp ; xd#index_xpr result ;
                              xd#index_xpr rresult ])
          | XConst (IntConst n) ->
             begin
               ch_error_log#add "shift right operand out of range"
                                (LBLOCK [ floc#l#toPretty ; STR ": " ; n#toPretty ]) ;
               ([ "a:vxx" ],[ xd#index_variable lhs ; xd#index_xpr rhsbase ;
                              xd#index_xpr rhsexp ])
             end
          | _ ->
             raise (BCH_failure (LBLOCK [ STR "Internal error in Shr" ])))
                        

      (* ------------------------------------------------------------ Shrd -- *)
      | Shrd (dst,src,shift) when shift#is_immediate_value ->
         let lhs = dst#to_variable floc in
         let rhs1 = dst#to_expr floc in
         let rrhs1 = rewrite_expr rhs1 in         
         let rhs2 = src#to_expr floc in
         let rrhs2 = rewrite_expr rhs2 in         
         let imm = shift#to_expr floc in
         ([ "a:vxxxxx"],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rrhs1 ; xd#index_xpr rhs2 ;
                          xd#index_xpr rrhs2 ; xd#index_xpr imm ])
                 
      (* ------------------------------------------------------------ Stos -- *)
      | Stos (width,dst,src,opedi,opdf) ->
         let lhs = dst#to_variable floc in             (* (Edi)  *)
         let lhsedi = opedi#to_variable floc in        (* Edi *)
         let rhs = src#to_expr floc in                 (* AL, AX, or EAX *)
         let rrhs = rewrite_expr rhs in
         let rhsedi = opedi#to_expr floc in            (* Edi *)
         let rrhsedi = rewrite_expr rhsedi in
         let rhsdf = opdf#to_expr floc in              (* DFlag *)
         let rrhsdf = rewrite_expr rhsdf in
         ([ "a:vvxxxxxx" ],[ xd#index_variable lhs ; xd#index_variable lhsedi ;
                             xd#index_xpr rhs ; xd#index_xpr  rrhs ;
                             xd#index_xpr rhsedi ; xd#index_xpr rrhsedi ; 
                             xd#index_xpr rhsdf ;  xd#index_xpr rrhsdf ])         
         
      (* ------------------------------------------------------------- Sub -- *)         
      | Sub (dst,src) ->
         let lhs = dst#to_variable floc in                    
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         let result = XOp (XMinus, [ rhs2 ; rhs1 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ], [ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                           xd#index_xpr rhs2 ; xd#index_xpr result ; xd#index_xpr rresult ])

      (* -----------------------------------------------------------  Test -- *)
      | Test (op1,op2) ->
         let rhs1 = rewrite_expr (op1#to_expr floc) in
         let rhs2 = rewrite_expr (op2#to_expr floc) in
         ([ "a:xx" ],[ xd#index_xpr rhs1 ; xd#index_xpr rhs2 ])

      (* ---------------------------------------------------------- Negate -- *)
      | TwosComplementNegate op ->
         let lhs = op#to_variable floc in         
         let rhs = op#to_expr floc in
         let rhsx = XOp (XMinus, [ int_constant_expr 0 ; rhs ]) in
         let rrhsx = rewrite_expr rhsx in
         ([ "a:vxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs ;
                          xd#index_xpr rhsx ; xd#index_xpr rrhsx ])

      (* ------------------------------------------------------------ Xchg -- *)
      (* Note: one of the operands is always a register, so if the two 
         operands are equal both must be registers and there is no possibiliy
         of a memory access violation *)
      | Xchg (op1,op2) when op1#equal op2 -> ([ "nop" ],[])
                                           
      | Xchg (op1,op2) ->
         let rhs1 = op1#to_expr floc in
         let rhs2 = op2#to_expr floc in
         let lhs1 = op1#to_variable floc in
         let lhs2 = op2#to_variable floc in
         ([ "a:vvxx" ], [ xd#index_variable lhs1 ; xd#index_variable lhs2 ;
                          xd#index_xpr rhs1 ; xd#index_xpr rhs2 ])
         
      (* -------------------------------------------------------------- Xor -- *)
      | Xor (dst,src) when dst#equal src ->
         let lhs = dst#to_variable floc in
         ([ "a:v" ],[ xd#index_variable lhs ])

      | Xor (dst,src) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         let result = XOp (XBXor, [ rhs2 ; rhs1 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ],[ xd#index_variable lhs ; xd#index_xpr rhs1 ;
                          xd#index_xpr rhs2 ; xd#index_xpr result ;
                          xd#index_xpr rresult ])

      | Leave -> ([ "a:x" ], [ xd#index_xpr ((ebp_deref RD)#to_expr floc) ])

      | XAdd (dst,src) ->
         let rhs1 = src#to_expr floc in
         let rhs2 = dst#to_expr floc in
         let lhs1 = src#to_variable floc in
         let lhs2 = dst#to_variable floc in
         let result  = XOp (XPlus, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vvxxxx" ], [ xd#index_variable lhs1 ; xd#index_variable lhs2 ;
                xd#index_xpr rhs1 ; xd#index_xpr rhs2 ; xd#index_xpr result ;
                xd#index_xpr rresult ])

      | Mul (_,dst,src1,src2) ->
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let lhs = dst#to_variable floc in
         let result = XOp (XMult, [ rhs1 ; rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ], [ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                           xd#index_xpr result ; xd#index_xpr rresult ])

      | IMul (_,dst,src1,src2) ->
         let lhs = dst#to_variable floc in
         let rhs1 = src1#to_expr floc in
         let rhs2 = src2#to_expr floc in
         let result = XOp (XMult, [ rhs1 ;  rhs2 ]) in
         let rresult = rewrite_expr result in
         ([ "a:vxxxx" ], [ xd#index_variable lhs ; xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                           xd#index_xpr result ; xd#index_xpr rresult ])

      | Div (_,quot,rem,dividend,divisor) ->  (* need to distinguish between signed and unsigned *)
         let lhs1 = quot#to_variable floc in
         let lhs2 = rem#to_variable floc in
         let rhs1 = dividend#to_expr floc in
         let rhs2 = divisor#to_expr floc in
         let quot = XOp (XDiv, [ rhs1 ; rhs2 ]) in
         let rquot = rewrite_expr quot in
         let rem = XOp (XMod, [ rhs1 ; rhs2 ]) in
         let rrem = rewrite_expr rem in
         ([ "a:vvxxxxxx" ], [ xd#index_variable lhs1 ; xd#index_variable lhs2 ;
                xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                xd#index_xpr quot ; xd#index_xpr rquot ;
                xd#index_xpr rem ; xd#index_xpr rrem ])         

      | IDiv (_,quot,rem,dividend,divisor) -> (* need to distinguish between signed and unsigned *)
         let lhs1 = quot#to_variable floc in
         let lhs2 = rem#to_variable floc in
         let rhs1 = dividend#to_expr floc in
         let rhs2 = divisor#to_expr floc in
         let quot = XOp (XDiv, [ rhs1 ; rhs2 ]) in
         let rquot = rewrite_expr quot in
         let rem = XOp (XMod, [ rhs1 ; rhs2 ]) in
         let rrem = rewrite_expr rem in
         ([ "a:vvxxxxxx" ], [ xd#index_variable lhs1 ; xd#index_variable lhs2 ;
                xd#index_xpr rhs1 ; xd#index_xpr rhs2 ;
                xd#index_xpr quot ; xd#index_xpr rquot ;
                xd#index_xpr rem ; xd#index_xpr rrem ])
         
      | _ -> ([],[]) in
    instrx_table#add key

  method write_xml_esp_offset
           ?(tag="isp") (node:xml_element_int) (o:int * interval_t) =
    node#setIntAttribute tag (self#index_esp_offset o)

  method write_xml_instr
           ?(tag="iopx") (node:xml_element_int) (instr:assembly_instruction_int) (floc:floc_int) =
    try
      node#setIntAttribute tag (self#index_instr instr floc)
    with
    | BCH_failure p ->
       raise (BCH_failure (LBLOCK [ STR "Error in writing xml instruction: " ;
                                    floc#l#i#toPretty ; STR "  " ;  instr#toPretty ;
                                    STR ": " ; p ]))
       

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t -> let tnode = xmlElement t#get_name in
           begin t#write_xml tnode ; tnode end) tables)
    

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables ;

  method toPretty =
    LBLOCK (List.map (fun t ->
                LBLOCK [ STR t#get_name ; STR ": " ; INT t#size ; NL ]) tables)

end

let mk_x86_opcode_dictionary = new x86_opcode_dictionary_t

