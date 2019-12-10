(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHPretty

(* xprlib *)
open Xprt

(* bchlib *)
open BCHCPURegisters
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil


class get_pc_thunk_semantics_t
        (md5hash:string) (reg:cpureg_t) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__x86_get_pc_thunk_" ^ (cpureg_to_string reg)

  method get_annotation (floc:floc_int) =
    LBLOCK [ STR (cpureg_to_string reg) ; STR " := " ; floc#ia#toPretty ]

  method get_commands (floc:floc_int) =
    let (reglhs,reglhscmds) = get_reg_lhs reg floc in
    let instrlen = String.length floc#get_instruction_bytes in
    let refaddr = num_constant_expr (floc#ia#add_int instrlen)#to_numerical in
    let cmds = floc#get_assign_commands reglhs refaddr in
    reglhscmds @ cmds

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a,self#get_name)

  method get_description = "records the instruction pointer in register"

end
    

let thunk_functions = [
    new get_pc_thunk_semantics_t "01b2660bfccc528787dbd1910ebd6014" Eax 2 ; (*  __x86_get_pc_thunk_ax *)
    new get_pc_thunk_semantics_t "4b0f79ed52ddee49a395b2f505a67bf6" Ebx 2 ; (*  __x86_get_pc_thunk_bx *)
    new get_pc_thunk_semantics_t "caff9e88cc5e02718b4348dd56da751a" Ecx 2 ; (*  __x86_get_pc_thunk_cx *)
    new get_pc_thunk_semantics_t "36eb98d44bd8912a4212e9822a0b134d" Edx 2 ; (*  __x86_get_pc_thunk_dx *)
    new get_pc_thunk_semantics_t "e05fa5134fb6f41539578de453f9eb0d" Ebp 2 ; (*  __x86_get_pc_thunk_bp *)
    new get_pc_thunk_semantics_t "55d115c49cb2eded6a865e967cabadd8" Edi 2 ; (*  __x86_get_pc_thunk_di *)
    new get_pc_thunk_semantics_t "5fcec57dfdde48d2ecec7107a7e5ff10" Esi 2 ; (*  __x86_get_pc_thunk_si *)
  ]
