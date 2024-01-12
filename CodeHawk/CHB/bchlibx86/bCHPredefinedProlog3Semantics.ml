(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHMakeCallTargetInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil


(* Functions that are called at the beginning of many functions to set up
   exception handling pointers and dynamically allocate stack space

   __EH_prolog(fp)
   __EH_prolog3(size,eax:fp)
   __EH_prolog3_gs(size,eax:fp)
   __EH_prolog3_catch(size,eax:fp)
   __EH_prolog3_catch_gs(size,eax:fp)
   __EH_epilog3()

   __SEH_prolog()
   __SEH_epilog()

*)

(* ============================================================== __EH_prolog(fp)
   Example: V0c5:0x403210

  0x403210   [ 0 ]    push -0x1                 esp := esp - 4; var.0004 := -1
  0x403212   [ -4 ]   push eax                  save eax
  0x403213   [ -8 ]   mov eax, %fs:0x0          eax :=  ?  (tmpN)
  0x403219   [ -8 ]   push eax                  esp := esp - 4; var.0012 := eax
  0x40321a  [ -12 ]   mov eax, 0xc(esp,,1)      eax := arg.0000 = arg.0000_in
  0x40321e  [ -12 ]   mov %fs:0x0, esp          ? := esp = (esp_in - 12)
  0x403225  [ -12 ]   mov 0xc(esp,,1), ebp      arg.0000 := ebp = ebp_in
  0x403229  [ -12 ]   lea ebp, 0xc(esp,,1)      ebp := (esp + 12) = esp_in
  0x40322d  [ -12 ]   push eax                  esp := esp - 4; var.0016 := eax
  0x40322e  [ -16 ]   ret                       return

*)

class eh_prolog_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__EH_prolog"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_fppretty floc eaxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let _ = set_functionpointer self#get_name floc eaxv in
    let xm1 = int_constant_expr (-1) in
    let x4 = int_constant_expr 4 in
    let x16 = int_constant_expr 16 in
    let (esplhs,esplhscmds) = (esp_r WR)#to_lhs floc in
    let (ebplhs,ebplhscmds) = (ebp_r WR)#to_lhs floc in
    let eaxv = get_reg_value Eax floc in
    let ebpv = get_reg_value Ebp floc in
    let espv = get_reg_value Esp floc in
    let (loc0,lcmds0) = get_returnaddress_lhs floc in
    let (loc4,lcmds4) = get_var_lhs 4 floc in
    let (loc8,lcmds8) = get_var_lhs 8 floc in
    let cmds0 = floc#get_assign_commands loc0 ebpv in
    let cmds4 = floc#get_assign_commands loc4 xm1 in
    let cmds8 = floc#get_assign_commands loc8 eaxv in
    let cmdsebp = floc#get_assign_commands ebplhs (XOp (XMinus, [espv; x4])) in
    let cmdsesp = floc#get_assign_commands esplhs (XOp (XMinus, [espv; x16])) in
    let cmdsr = [ floc#get_abstract_cpu_registers_command [Eax]] in
    lcmds0
    @ lcmds4
    @ lcmds8
    @ esplhscmds
    @ ebplhscmds
    @ cmds0
    @ cmds4
    @ cmds8
    @ cmdsebp
    @ cmdsesp
    @ cmdsr

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "sets up exception handling frame"

end


(* ================================================================ seh_prolog
   example: V03be08
   md5hash: 2a95c18e8584a76aab19d604eb2a7e93

  0x4066a8   [ 0 ]    push fp:0x40979c          esp := esp - 4; var.0004 := 4233116
  0x4066ad   [ -4 ]   mov eax, %fs:0x0          eax :=  ?  (tmpN)
  0x4066b3   [ -4 ]   push eax                  esp := esp - 4; var.0008 := eax
  0x4066b4   [ -8 ]   mov eax, 0x10(esp,,1)     eax := arg.0008 = arg.0008_in
  0x4066b8   [ -8 ]   mov 0x10(esp,,1), ebp     arg.0008 := ebp = ebp_in
  0x4066bc   [ -8 ]   lea ebp, 0x10(esp,,1)     ebp := (esp + 16) = (esp_in + 8)
  0x4066c0   [ -8 ]   sub esp, eax              esp := ((esp_in - arg.0008_in) - 8)
  0x4066c2   [-8-s]   push ebx                  save ebx
  0x4066c3  [-12-s]   push esi                  save esi
  0x4066c4  [-16-s]   push edi                  save edi
  0x4066c5  [-20-s]   mov eax, -0x8(ebp)        eax := arg.0000 = arg.0000_in
  0x4066c8  [-20-s]   mov -0x18(ebp), esp       var.0016 := esp
                                                  = ((esp_in - arg.0008_in) - 20)
  0x4066cb  [-20-s]   push eax                  esp := esp - 4; ? := eax
  0x4066cc  [-24-s]   mov eax, -0x4(ebp)        eax := arg.0004 = arg.0004_in
  0x4066cf  [-24-s]   mov -0x4(ebp), 0xffffffff  arg.0004 := 4294967295
  0x4066d6  [-24-s]   mov -0x8(ebp), eax        arg.0000 := eax = arg.0004_in
  0x4066d9  [-24-s]   lea eax, -0x10(ebp)       eax := (ebp - 16) = (esp_in - 8)
  0x4066dc  [-24-s]   mov %fs:0x0, eax          ? := eax = (esp_in - 8)
  0x4066e2  [-24-s]   ret                       return

*)

let get_seh_prolog_chif (handler:doubleword_int) (floc:floc_int) =
  let ebp = floc#env#mk_cpu_register_variable Ebp in
  let ebxv = get_reg_value Ebx floc in
  let esiv = get_reg_value Esi floc in
  let ediv = get_reg_value Edi floc in
  let esp = floc#env#mk_cpu_register_variable Esp in
  try
    let args = floc#get_call_args in
    let scopetable = get_arg args 1 floc in
    let size = get_arg args 2 floc in
    let xhandler = num_constant_expr handler#to_numerical in
    let (esplhs,esplhscmds) = get_reg_lhs Esp floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let (ebplhs,ebplhscmds) = get_reg_lhs Ebp floc in
    match size with
    | XConst (IntConst num) ->
      let adj = num#toInt in
      let adj20 = int_constant_expr (adj + 24) in
      let xm1 = int_constant_expr (-1) in
      let x8 = int_constant_expr 8 in
      let x12 = int_constant_expr 12 in
      let (loca8,lcmdsa8) = get_arg_lhs 8 floc in
      let (loca4,lcmdsa4) = get_arg_lhs 4 floc in
      let (loc0,lcmds0) = get_returnaddress_lhs floc in
      let (loc4,lcmds4) = get_var_lhs 4 floc in
      let (loc8,lcmds8) = get_var_lhs 8 floc in
      let (loc16,lcmds16) = get_var_lhs 16 floc in
      let (_loc8s,lcmds8s) = get_allocavar_lhs 8 adj floc in
      let (loc12s,lcmds12s) = get_allocavar_lhs 12 adj floc in
      let (loc16s,lcmds16s) = get_allocavar_lhs 16 adj floc in
      let (loc20s,lcmds20s) = get_allocavar_lhs 20 adj floc in
      let cmdsa8 = floc#get_assign_commands loca8 (XVar ebp) in
      let cmdsa4 = floc#get_assign_commands loca4 xm1 in
      let cmds0 = floc#get_assign_commands loc0 scopetable in
      let cmds4 = floc#get_assign_commands loc4 xhandler in
      let cmds8 = [ABSTRACT_VARS [loc8] ] in  (* fs:0x0 *)
      let cmds16 =
        floc#get_assign_commands loc16 (XOp (XMinus, [XVar esp; adj20])) in
      let cmds12s = floc#get_assign_commands loc12s ebxv in
      let cmds16s = floc#get_assign_commands loc16s esiv in
      let cmds20s = floc#get_assign_commands loc20s ediv in
      let cmdsebp =
        floc#get_assign_commands ebplhs (XOp (XPlus, [XVar esp; x8])) in
      let cmdseax =
        floc#get_assign_commands eaxlhs (XOp (XMinus, [XVar esp; x12])) in
      let cmdsesp =
        floc#get_assign_commands esplhs (XOp (XMinus, [XVar esp; adj20])) in
      esplhscmds
      @ eaxlhscmds
      @ ebplhscmds
      @ lcmdsa8
      @ lcmdsa4
      @ lcmds0
      @ lcmds4
      @ lcmds8
      @ lcmds16
      @ lcmds8s
      @ lcmds12s
      @ lcmds16s
      @ lcmds20s
      @ cmdsa8
      @ cmdsa4
      @ cmds0
      @ cmds4
      @ cmds8
      @ cmds16
      @ cmds12s
      @ cmds16s
      @ cmds20s
      @ cmdsebp
      @ cmdseax
      @ cmdsesp
    | _ -> [ floc#get_abstract_cpu_registers_command [Eax; Esp; Ebp]]
  with
  | BCH_failure p ->
    begin
      ch_error_log#add ("seh_prolog_semantics") p;
      [floc#get_abstract_cpu_registers_command [Eax; Esp; Ebp]]
    end

class seh_prolog_semantics_t
        (md5hash:string)
        (handler:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__SEH_prolog__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [
        STR self#get_name; STR "(scopetable:"; xpr_to_dspretty floc arg1;
	STR ",size:"; xpr_to_pretty floc arg2; STR ")"]

  method! get_commands (floc:floc_int) =
    get_seh_prolog_chif handler floc

  method get_parametercount = 2

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "sets up exception handling"

end

(* ================================================================ seh_epilog
   example: V03be08
   md5hash: 308f40d5e2eb82b7a19ae1f143f87aa3

  0x4066e3   [ 0 ]  mov ecx, -0x10(ebp)  ecx :=  ?  (tmpN)
  0x4066e6   [ 0 ]  mov %fs:0x0, ecx     ? := ecx
  0x4066ed   [ 0 ]  pop ecx              ecx := arg.0000_in; esp := (esp_in + 4)
  0x4066ee   [ 4 ]  pop edi              edi := arg.0004_in; esp := (esp_in + 8)
  0x4066ef   [ 8 ]  pop esi              esi := arg.0008_in; esp := (esp_in + 12)
  0x4066f0   [ 12 ] pop ebx              ebx := arg.0012_in; esp := (esp_in + 16)
  0x4066f1   [ 16 ] leave                esp := ebp; ebp := (ebp_in)[0];
                                           esp := esp + 4
  0x4066f2  [  ?  ] push ecx             esp := esp - 4; (ebp_in)[0] := ecx
  0x4066f3  [  ?  ] ret                  return

*)
class seh_epilog_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__SEH_epilog__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let ebpv = get_reg_value Ebp floc in
    LBLOCK [
        STR self#get_name;
	STR " [ edi := "; xpr_to_pretty floc arg1;
	STR "; esi := "; xpr_to_pretty floc arg2;
	STR "; ebx := "; xpr_to_pretty floc arg3;
	STR "; esp := "; xpr_to_pretty floc ebpv; STR " ]"]

  method! get_commands (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let ebpv = get_reg_value Ebp floc in
    let (edilhs,edilhscmds) = get_reg_lhs Edi floc in
    let (esilhs,esilhscmds) = get_reg_lhs Esi floc in
    let (ebxlhs,ebxlhscmds) = get_reg_lhs Ebx floc in
    let (esplhs,esplhscmds) = get_reg_lhs Esp floc in
    let cmds1 = floc#get_assign_commands edilhs arg1 in
    let cmds2 = floc#get_assign_commands esilhs arg2 in
    let cmds3 = floc#get_assign_commands ebxlhs arg3 in
    let cmds4 = floc#get_assign_commands esplhs ebpv in
    let cmds5 = [floc#get_abstract_cpu_registers_command [Ecx; Ebp]] in
    edilhscmds
    @ esilhscmds
    @ ebxlhscmds
    @ esplhscmds
    @ cmds1
    @ cmds2
    @ cmds3
    @ cmds4
    @ cmds5

  method get_parametercount = 3

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "restores registers and stack pointer"

end


let get_ehprolog3_annotation
      (name:string) (cookie:doubleword_int) (floc:floc_int) =
  try
    let arg = get_arg floc#get_call_args 1 floc in
    let eaxv = get_reg_value Eax floc in
    LBLOCK [
        STR name; STR "(size:"; xpr_to_pretty floc arg;
	STR ",handler:"; xpr_to_fppretty floc eaxv;
	STR ") [ cookie:"; cookie#toPretty; STR "]"]
  with
  | _ -> LBLOCK [STR name; STR "(?,?)"]


let get_ehprolog3_chif ?(gs=false) ?(catch=false) (floc:floc_int) =
  let suffix = if gs && catch then
      "_catch_GS"
    else if gs then
      "_gs"
    else if catch then
      "_catch"
    else "" in
  let name = "__EH_prolog3" ^ suffix in
  try
    let env = floc#env in
    let eaxv = get_reg_value Eax floc in
    let _ = set_functionpointer name floc eaxv in
    let size = get_arg floc#get_call_args 1 floc in
    let ebp = env#mk_cpu_register_variable Ebp in
    let ebx = env#mk_cpu_register_variable Ebx in
    let esp = env#mk_cpu_register_variable Esp in
    let esi = env#mk_cpu_register_variable Esi in
    let edi = env#mk_cpu_register_variable Edi in
    match size with
    | XConst (IntConst num) ->
      let adj = num#toInt in
      let xm1 = int_constant_expr (-1) in
      let adj24 = int_constant_expr (adj + 28) in
      let (loca,lcmdsa) = get_arg_lhs 4 floc in
      let (esplhs,esplhscmds) = get_reg_lhs Esp floc in
      let (ebplhs,ebplhscmds) = get_reg_lhs Ebp floc in
      let (loc0,lcmds0) = get_returnaddress_lhs floc in
      let (loc4,lcmds4) = get_var_lhs 4 floc in   (* fp *)
      let (loc8,lcmds8) = get_var_lhs 8 floc in (* fs:0x0 *)
      let (loc12s,lcmds12s) = get_allocavar_lhs 12 adj floc in (* ebx *)
      let (loc16s,lcmds16s) = get_allocavar_lhs 16 adj floc in (* esi *)
      let (loc20s,lcmds20s) = get_allocavar_lhs 20 adj floc in (* edi *)
      let (loc24s,lcmds24s) = get_allocavar_lhs 24 adj floc in (* cookie *)
      let cmdsa = floc#get_assign_commands loca (XVar ebp) in
      let cmds0 = floc#get_assign_commands loc0 xm1 in
      let cmds4 = floc#get_assign_commands loc4 eaxv in
      let cmds8 = [ABSTRACT_VARS [loc8]] in
      let cmds12s = floc#get_assign_commands loc12s (XVar ebx) in
      let cmds16s = floc#get_assign_commands loc16s (XVar esi) in
      let cmds20s = floc#get_assign_commands loc20s (XVar edi) in
      let cmds24s = [ABSTRACT_VARS [loc24s]] in
      let cmdsebp = floc#get_assign_commands ebplhs (XVar esp) in (* esp_in + 4 *)
      let cmdsesp =
        floc#get_assign_commands esplhs (XOp (XMinus, [XVar esp; adj24])) in
      let catchgscmds = if catch && gs then
	  let (loc12,lcmds12) = get_var_lhs 12 floc in
	  let (loc16,lcmds16) = get_var_lhs 16 floc in
	  let cmds12 =
            floc#get_assign_commands loc12 (XOp (XMinus, [XVar esp; adj24])) in
	  let cmds16 = [ABSTRACT_VARS [loc16]] in
	  lcmds12 @ lcmds16 @ cmds12 @ cmds16
	else if gs then
	  let (loc12,lcmds12) = get_var_lhs 12 floc in
	  let cmds12 = [ABSTRACT_VARS [loc12]] in
	  lcmds12 @ cmds12
	else if catch then
	  let (loc12,lcmds12) = get_var_lhs 12 floc in
	  let cmds12 =
            floc#get_assign_commands loc12 (XOp (XMinus, [XVar esp; adj24])) in
	  lcmds12 @ cmds12
	else
	  [] in
      lcmdsa
      @ esplhscmds
      @ ebplhscmds
      @ lcmds0
      @ lcmds4
      @ lcmds8
      @	lcmds12s
      @ lcmds16s
      @ lcmds20s
      @ lcmds24s
      @ cmdsa
      @ cmds0
      @ cmds4
      @ cmds8
      @ cmds12s
      @ cmds16s
      @ cmds20s
      @ cmds24s
      @ cmdsebp
      @ catchgscmds
      @ cmdsesp
    | _ -> [floc#get_abstract_cpu_registers_command [Eax; Esp; Ebp]]
  with
  | BCH_failure p ->
    begin
      ch_error_log#add (name ^ " semantics") p;
      [floc#get_abstract_cpu_registers_command [Eax; Esp; Ebp]]
    end

(* __EH_prolog3 (arg1:size, eax:fp)

  0x4fc  [0]     push eax                  save eax
  0x4fd  [-4]    push %fs:0x0              esp := esp - 4; var.0008 :=  ?  (tmpN)
  0x504  [-8]    lea eax, 0xc(esp,,1)      eax := (esp + 12) = (esp_in + 4)
  0x508  [-8]    sub esp, 0xc(esp,,1)      esp := ((esp_in - arg.0004_in) - 8)
  0x50c  [-8-s]  push ebx                  save ebx
  0x50d  [-12-s] push esi                  save esi
  0x50e  [-16-s] push edi                  save edi
  0x50f  [-20-s] mov (eax), ebp            arg.0004 := ebp = ebp_in
  0x511  [-20-s] mov ebp, eax              ebp := eax = (esp_in + 4)
  0x513  [-20-s] mov eax, 0x4671f0         eax := gv_0x4671f0_in
  0x518  [-20-s] xor eax, ebp              eax := eax xor ebp
  0x51a  [-20-s] push eax                  esp := esp - 4; ? := eax
  0x51b  [-24-s] push -0x4(ebp)            esp := esp - 4; ? := arg.0000
  0x51e  [-28-s] mov -0x4(ebp), 0xffffffff  arg.0000 := 4294967295
  0x525  [-28-s] lea eax, -0xc(ebp)        eax := (ebp - 12) = (esp_in - 8)
  0x528  [-28-s] mov %fs:0x0, eax          ? := eax = (esp_in - 8)
  0x52e  [-28-s] ret                       return
*)

class eh_prolog3_semantics_t
        (md5hash:string)
        (cookie:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object(self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__EH_prolog3"

  method! get_annotation (floc:floc_int) =
    get_ehprolog3_annotation self#get_name cookie floc

  method! get_commands (floc:floc_int) = get_ehprolog3_chif floc

  method get_parametercount = 1

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "sets up exception handling and allocates stack memory"

end


(* =========================================== __EH_prolog3_gs(arg1:size, eax:fp)

  0xfd7    [ 0]    push eax                save eax
  0xfd8    [-4]    push %fs:0x0            esp := esp - 4; var.0008 :=  ?  (tmpN)
  0xfdf    [-8]    lea eax, 0xc(esp,,1)    eax := (esp + 12) = (esp_in + 4)
  0xfe3    [-8]    sub esp, 0xc(esp,,1)    esp := ((esp_in - arg.0004_in) - 8)
  0xfe7   [-8-s]   push ebx                save ebx
  0xfe8   [-12-s]  push esi                save esi
  0xfe9   [-16-s]  push edi                save edi
  0xfea   [-20-s]  mov (eax), ebp          arg.0004 := ebp = ebp_in
  0xfec   [-20-s]  mov ebp, eax            ebp := eax = (esp_in + 4)
  0xfee   [-20-s]  mov eax, 0x44eda8       eax := gv_0x44eda8 = gv_0x44eda8_in
  0xff3   [-20-s]  xor eax, ebp            eax := eax xor ebp
  0xff5   [-20-s]  push eax                esp := esp - 4; ? := eax
  0xff6   [-24-s]  mov -0x10(ebp), eax     var.0012 := eax
  0xff9   [-24-s]  push -0x4(ebp)          esp := esp - 4; ? := arg.0000
  0xffc   [-28-s]  mov -0x4(ebp), 0xffffffff  arg.0000 := 4294967295
  0x003   [-28-s]  lea eax, -0xc(ebp)      eax := (ebp - 12) = (esp_in - 8)
  0x006   [-28-s]  mov %fs:0x0, eax        ? := eax = (esp_in - 8)
  0x00c   [-28-s]  ret                     return
*)

class eh_prolog3_gs_semantics_t
        (md5hash:string)
        (cookie:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__EH_prolog3_GS"

  method! get_annotation (floc:floc_int) =
    get_ehprolog3_annotation self#get_name cookie floc

  method! get_commands (floc:floc_int) = get_ehprolog3_chif ~gs:true floc

  method get_parametercount = 1

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "sets up exception handling and allocates memory on the stack"

end


(* ========================================__EH_prolog3_catch(arg1:size, eax:fp)

  0x54    [0]     push eax                save eax
  0x55    [-4]    push %fs:0x0            esp := esp - 4; var.0008 :=  ?  (tmpN)
  0x5c    [-8]    lea eax, 0xc(esp,,1)    eax := (esp + 12) = (esp_in + 4)
  0x60    [-8]    sub esp, 0xc(esp,,1)    esp := ((esp_in - arg.0004_in) - 8)
  0x64   [-8-s]   push ebx                save ebx
  0x65   [-12-s]  push esi                save esi
  0x66   [-16-s]  push edi                save edi
  0x67   [-20-s]  mov (eax), ebp          arg.0004 := ebp = ebp_in
  0x69   [-20-s]  mov ebp, eax            ebp := eax = (esp_in + 4)
  0x6b   [-20-s]  mov eax, 0x4702a0       eax := gv_0x4702a0 = gv_0x4702a0_in
  0x70   [-20-s]  xor eax, ebp            eax := eax xor ebp
  0x72   [-20-s]  push eax                esp := esp - 4; ? := eax
  0x73   [-24-s]  mov -0x10(ebp), esp     var.0012 := esp
                                              = ((esp_in - arg.0004_in) - 24)
  0x76   [-24-s]  push -0x4(ebp)          esp := esp - 4; ? := arg.0000
  0x79   [-28-s]  mov -0x4(ebp), 0xffffffff  arg.0000 := 4294967295
  0x80   [-28-s]  lea eax, -0xc(ebp)      eax := (ebp - 12) = (esp_in - 8)
  0x83   [-28-s]  mov %fs:0x0, eax        ? := eax = (esp_in - 8)
  0x89   [-28-s]  ret                     return
*)

class eh_prolog3_catch_semantics_t
        (md5hash:string)
        (cookie:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__EH_prolog3_catch"

  method! get_annotation (floc:floc_int) =
    get_ehprolog3_annotation self#get_name cookie floc

  method! get_commands (floc:floc_int) = get_ehprolog3_chif ~catch:true floc

  method get_parametercount = 1

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "sets up exception handling and allocates memory on the stack"

end


(*  ================================== __EH_prolog3_catch_gs(arg1:size, eax:fp)

  0x8db    [0]    push eax                  save eax
  0x8dc    [-4]   push %fs:0x0              esp := esp - 4; var.0008 :=  ?  (tmpN)
  0x8e3    [-8]   lea eax, 0xc(esp,,1)      eax := (esp + 12) = (esp_in + 4)
  0x8e7    [-8]   sub esp, 0xc(esp,,1)      esp := esp - arg.0004
                                               = ((esp_in - arg.0004_in) - 8)
  0x8eb   [-8-s]  push ebx                  save ebx
  0x8ec   [-12-s] push esi                  save esi
  0x8ed   [-16-s] push edi                  save edi
  0x8ee   [-20-s] mov (eax), ebp            arg.0004 := ebp = ebp_in
  0x8f0   [-20-s] mov ebp, eax              ebp := eax = (esp_in + 4)
  0x8f2   [-20-s] mov eax, 0x469200         eax := gv_0x469200 = gv_0x469200_in
  0x8f7   [-20-s] xor eax, ebp              eax := eax xor ebp
  0x8f9   [-20-s] push eax                  esp := esp - 4; ? := eax
  0x8fa   [-24-s] mov -0x14(ebp), eax       var.0016 := eax
  0x8fd   [-24-s] mov -0x10(ebp), esp       var.0012 := esp
                                               = ((esp_in - arg.0004_in) - 24)
  0x900   [-24-s] push -0x4(ebp)            esp := esp - 4; ? := arg.0000
  0x903   [-28-s] mov -0x4(ebp), 0xffffffff  arg.0000 := 4294967295
  0x90a   [-28-s] lea eax, -0xc(ebp)        eax := (ebp - 12) = (esp_in - 8)
  0x90d   [-28-s] mov %fs:0x0, eax          ? := eax = (esp_in - 8)
  0x913   [-28-s] ret                       return
*)

class eh_prolog3_catch_gs_semantics_t
        (md5hash:string)
        (cookie:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__EH_prolog3_catch_GS"

  method! get_annotation (floc:floc_int) =
    get_ehprolog3_annotation self#get_name cookie floc

  method! get_commands (floc:floc_int) =
    get_ehprolog3_chif ~catch:true ~gs:true floc

  method get_parametercount = 1

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "sets up exectpion handling and allocates memory on the stack"

end


(* ================================================================ __EH_epilog3

  0xd4  mov ecx, -0xc(ebp)  ecx :=  ?  (tmpN)
  0xd7  mov %fs:0x0, ecx    ? := ecx
  0xde  pop ecx             ecx := arg.0000_in; esp := esp + 4 = (esp_in + 4)
  0xdf  pop edi             edi := arg.0004_in; esp := esp + 4 = (esp_in + 8)
  0xe0  pop edi             edi := arg.0008_in; esp := esp + 4 = (esp_in + 12)
  0xe1  pop esi             esi := arg.0012_in; esp := esp + 4 = (esp_in + 16)
  0xe2  pop ebx             ebx := arg.0016_in; esp := esp + 4 = (esp_in + 20)
  0xe3  mov esp, ebp        esp := ebp = ebp_in
  0xe5  pop ebp             ebp := (ebp_in)[0]_in; esp := esp + 4 = (ebp_in + 4)
  0xe6  push ecx            esp := esp - 4; (ebp_in)[0] := ecx
  0xe7  ret                 return
*)

class eh_epilog3_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__EH_epilog3__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let arg4 = get_arg args 4 floc in
    LBLOCK [
        STR self#get_name;
	STR "(rEdi:"; xpr_to_pretty floc arg2;
	STR "rEsi:"; xpr_to_pretty floc arg3;
	STR "rEbx:"; xpr_to_pretty floc arg4; STR ")"]

  method! get_commands (floc:floc_int) =
    try
      let args = floc#get_call_args in
      let arg2 = get_arg args 2 floc in
      let arg3 = get_arg args 3 floc in
      let arg4 = get_arg args 4 floc in
      let ebpv = get_reg_value Ebp floc in
      let (edilhs,edilhscmds) = get_reg_lhs Edi floc in
      let (esilhs,esilhscmds) = get_reg_lhs Esi floc in
      let (ebxlhs,ebxlhscmds) = get_reg_lhs Ebx floc in
      let (esplhs,esplhscmds) = get_reg_lhs Esp floc in
      let cmds2 = floc#get_assign_commands edilhs arg2 in
      let cmds3 = floc#get_assign_commands esilhs arg3 in
      let cmds4 = floc#get_assign_commands ebxlhs arg4 in
      let cmdsesp = floc#get_assign_commands esplhs ebpv in
      let cmdsr = [floc#get_abstract_cpu_registers_command [Ecx; Ebp]] in
      edilhscmds
      @ esilhscmds
      @ ebxlhscmds
      @ esplhscmds
      @ cmds2
      @ cmds3
      @ cmds4
      @ cmdsesp
      @ cmdsr
    with
    | BCH_failure p ->
      begin
	ch_error_log#add
          (self#get_name ^ " semantics")
	  (LBLOCK [STR self#get_name; STR " semantics: "; p]);
	[floc#get_abstract_cpu_registers_command [Ecx; Ebx; Esi; Edi; Esp; Ebp]]
      end

  method get_parametercount = 4

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "restores registers and stack pointer"

end


let eh3_functions = [
  new eh_prolog_semantics_t "b12eeb53f79c38640b7facb4b2e6c8f4" 10;
  new eh_epilog3_semantics_t "14048b5de5bd58c2d94888ebf3261e80" 11;
  new seh_epilog_semantics_t "308f40d5e2eb82b7a19ae1f143f87aa3" 9
]


let eh3_patterns = [
  (* EH_prolog3 *)
    { regex_s =
        Str.regexp
          ("5064ff35000000008d44240c2b64240c53565789288be8a1\\(........\\)"
           ^ "33c550ff75"
           ^ "fcc745fcffffffff8d45f464a300000000c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let cookie = todw (Str.matched_group 1 fnbytes) in
      let sem = new eh_prolog3_semantics_t fnhash cookie 17 in
      let msg = LBLOCK [STR " with security cookie "; cookie#toPretty] in
      sometemplate ~msg sem
  };

  (* EH_prolog3_GS *)
  { regex_s = Str.regexp
      ("5064ff35000000008d44240c2b64240c53565789288be8a1\\(........\\)33c5508945" ^
       "f0ff75fcc745fcffffffff8d45f464a300000000c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let cookie = todw (Str.matched_group 1 fnbytes) in
      let sem = new eh_prolog3_gs_semantics_t fnhash cookie 18 in
      let msg = LBLOCK [STR " with security cookie "; cookie#toPretty] in
      sometemplate ~msg sem
  };

  (* EH_prolog3_catch *)
  { regex_s = Str.regexp
      ("5064ff35000000008d44240c2b64240c53565789288be8a1\\(........\\)33c5508965" ^
       "f0ff75fcc745fcffffffff8d45f464a300000000c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let cookie = todw (Str.matched_group 1 fnbytes) in
      let sem = new eh_prolog3_catch_semantics_t fnhash cookie 18 in
      let msg = LBLOCK [STR " with security cookie "; cookie#toPretty] in
      sometemplate ~msg sem
  };

  (* EH_prolog3_catch_GS *)
  { regex_s = Str.regexp
      ("5064ff35000000008d44240c2b64240c53565789288be8a1\\(........\\)33c5508945" ^
       "ec8965f0ff75fcc745fcffffffff8d45f464a300000000c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let cookie = todw (Str.matched_group 1 fnbytes) in
      let sem = new eh_prolog3_catch_gs_semantics_t fnhash cookie 19 in
      let msg = LBLOCK [STR " with security cookie "; cookie#toPretty] in
      sometemplate ~msg sem
  };

  (* SEH_prolog *)
  { regex_s = Str.regexp
      ("68\\(........\\)64a100000000508b442410896c24108d6c24102be05356578b45f889" ^
       "65e8508b45fcc745fcffffffff8945f88d45f064a300000000c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let handler = todw (Str.matched_group 1 fnbytes) in
      let sem = new seh_prolog_semantics_t fnhash handler 19 in
      let msg = LBLOCK [STR " with handler "; handler#toPretty] in
      sometemplate ~msg sem
  };

]
