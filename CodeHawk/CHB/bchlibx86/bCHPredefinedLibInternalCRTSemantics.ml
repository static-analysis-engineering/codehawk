(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt

(* bchlib *)
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHSystemInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil

module H = Hashtbl
module FFU = BCHFileFormatUtil
module TR = CHTraceResult


(* Unsafe call to string_to_doubleword; may raise Invalid_argument. *)
let constant_string_to_doubleword (s: string) =
  TR.tget_ok (string_to_doubleword s)


let table = H.create 3

(* ============================================================== __addlocaleref
   example: V008:0x416625
*)
class addlocaleref_semantics_t
        (md5hash:string)
        (_gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__addlocaleref__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc arg; STR ")"]

  method get_parametercount = 1

end


(* =========================================================== __checkTOS_withFB
   example: V008:0x41cb78
*)
class checktoswithfb_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__checkTOS_withFB__"

  method! get_annotation (floc:floc_int) =
    let arg2 = get_arg floc#get_call_args 1 floc in
    LBLOCK [
        STR self#get_name; STR "(arg1:reserved,arg2:";
	xpr_to_pretty floc arg2; STR ")"]

  method get_parametercount = 2

end

let _ = H.add table "__checkTOS_withFB" (new checktoswithfb_semantics_t)


(* ========================================================== __convertTOStoQNaN
   example: V008: 0x41cb1c
*)
class converttostoqnan_semantics_t
        (md5hash:string)
        (_gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__convertTOStoQNaN__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc eaxv; STR ")"]

  method get_parametercount = 0

end


(* ========================================================= __crtCorExitProcess
   example: Vc13:0x408a6b
*)
class crtcorexitprocess_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__crtCorExitProcess__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "(exitCode:"; xpr_to_pretty floc arg; STR ")"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 1

  method! get_description = "shuts down the current unmanaged process"

end


(* ============================================================ __crtFlsGetValue
   example: Vc13:0x409735

  0x409735   [ 0 ]    push ebp             save ebp
  0x409736   [ -4 ]   mov ebp, esp         ebp := esp = (esp_in - 4)
  0x409738   [ -4 ]   mov eax, 0x41ec48    eax := gv_0x41ec48 = gv_0x41ec48_in
  0x40973d   [ -4 ]   xor eax, 0x419b30    eax := eax xor gv_0x419b30
  0x409743   [ -4 ]   push 0x8(ebp)        esp := esp - 4; var.0008 := arg.0004
  0x409746   [ -8 ]   jz 0x40974c          if ? then goto 0x40974c
--------------------------------------------------------------------------------
  0x409748   [ -8 ]   call* eax            *( eax )()
  0x40974a  [  ?  ]   pop ebp              ebp :=  ?  (tmpN); esp := esp + 4
  0x40974b  [  ?  ]   ret                  return
--------------------------------------------------------------------------------
  0x40974c   [ -8 ]   call* 0x40f090       TlsGetValue
                                              (dwTlsIndex:arg.0004_in) (adj 4)
  0x409752   [ -4 ]   pop ebp              restore ebp
  0x409753   [ 0 ]    ret                  return

*)
class crtflsgetvalue_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__crtFlsGetValue__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [
        STR self#get_name; STR "(dwTlsIndex:"; xpr_to_pretty floc arg; STR ")"]

  method get_parametercount = 1

  method! get_description = "retrieve Tls value or execute function"

end


(* ===================================================== __crtUnhandledException
   example: V008:0x413948
*)
class crtunhandledexception_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__crtUnhandledException__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [
        STR self#get_name; STR "(lpExceptionInfo:"; xpr_to_pretty floc arg;
	STR ")"]

  method get_parametercount = 1

end


(* ================================================================ fastcopy_I
   example: V2bd:0x10011c9e
   md5hash: b89d9fdf956ad1e6ede97f78381b98b0 (35 instrs)

  0x10011c9e   [ 0 ]    push ebp                  save ebp
  0x10011c9f   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x10011ca1   [ -4 ]   sub esp, 0x8              esp := esp - 8 = (esp_in - 12)
  0x10011ca4  [ -12 ]   mov -0x4(ebp), edi        var.0008 := edi = edi_in
  0x10011ca7  [ -12 ]   mov -0x8(ebp), esi        var.0012 := esi = esi_in
  0x10011caa  [ -12 ]   mov esi, 0xc(ebp)         esi := arg.0008 = arg.0008_in
  0x10011cad  [ -12 ]   mov edi, 0x8(ebp)         edi := arg.0004 = arg.0004_in
  0x10011cb0  [ -12 ]   mov ecx, 0x10(ebp)        ecx := arg.0012 = arg.0012_in
  0x10011cb3  [ -12 ]   shr ecx, 0x7              ecx := ecx / 128
                                                     = (arg.0012_in / 128)
  0x10011cb6  [ -12 ]   jmp 0x10011cbe            goto 0x10011cbe
--------------------------------------------------------------------------------
  0x10011cbe  [ -12 ]   movdqa %xmm0, (esi)       xmm(0) := ?
  0x10011cc2  [ -12 ]   movdqa %xmm1, 0x10(esi)   xmm(1) := ?
  0x10011cc7  [ -12 ]   movdqa %xmm2, 0x20(esi)   xmm(2) := ?
  0x10011ccc  [ -12 ]   movdqa %xmm3, 0x30(esi)   xmm(3) := ?
  0x10011cd1  [ -12 ]   movdqa (edi), %xmm0       ? := ?
  0x10011cd5  [ -12 ]   movdqa 0x10(edi), %xmm1   ? := ?
  0x10011cda  [ -12 ]   movdqa 0x20(edi), %xmm2   ? := ?
  0x10011cdf  [ -12 ]   movdqa 0x30(edi), %xmm3   ? := ?
  0x10011ce4  [ -12 ]   movdqa %xmm4, 0x40(esi)   xmm(4) := ?
  0x10011ce9  [ -12 ]   movdqa %xmm5, 0x50(esi)   xmm(5) := ?
  0x10011cee  [ -12 ]   movdqa %xmm6, 0x60(esi)   xmm(6) := ?
  0x10011cf3  [ -12 ]   movdqa %xmm7, 0x70(esi)   xmm(7) := ?
  0x10011cf8  [ -12 ]   movdqa 0x40(edi), %xmm4   ? := ?
  0x10011cfd  [ -12 ]   movdqa 0x50(edi), %xmm5   ? := ?
  0x10011d02  [ -12 ]   movdqa 0x60(edi), %xmm6   ? := ?
  0x10011d07  [ -12 ]   movdqa 0x70(edi), %xmm7   ? := ?
  0x10011d0c  [ -12 ]   lea esi, 0x80(esi)        esi := (esi + 128)
  0x10011d12  [ -12 ]   lea edi, 0x80(edi)        edi := (edi + 128)
  0x10011d18  [ -12 ]   dec ecx                   ecx := ecx - 1
  0x10011d19  [ -12 ]   jnz 0x10011cbe            if (ecx != 1) then
                                                      goto 0x10011cbe
--------------------------------------------------------------------------------
  0x10011d1b  [ -12 ]   mov esi, -0x8(ebp)        esi := var.0012 = esi_in
  0x10011d1e  [ -12 ]   mov edi, -0x4(ebp)        edi := var.0008 = edi_in
  0x10011d21  [ -12 ]   mov esp, ebp              esp := ebp = (esp_in - 4)
  0x10011d23   [ -4 ]   pop ebp                   restore ebp
  0x10011d24   [ 0 ]    ret                       return
*)
class fastcopy_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__fastcopy_I__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [
        STR self#get_name; STR "(dst:"; xpr_to_pretty floc arg1;
	STR ",src:"; xpr_to_pretty floc arg2;
	STR ",count:"; xpr_to_pretty floc arg3; STR ")"]

  method! get_commands (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let size = get_arg args 3 floc in
    let lhs = floc#get_lhs_from_address arg1 in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Ecx]] in
    cmds1 @ cmds2

  method get_parametercount = 3

  method! get_description = "fastcopy internal CRT function"

end

let _ = H.add table "fastcopy_I" (new fastcopy_semantics_t)


(* ================================================================ fastzero_I
   example: V2bd:0x10017a66
   md5hash: eec093ed846285d92d0134521623aa9b

  0x10017a66   [ 0 ]    push ebp                  save ebp
  0x10017a67   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x10017a69   [ -4 ]   sub esp, 0x4              esp := esp - 4 = (esp_in - 8)
  0x10017a6c   [ -8 ]   mov -0x4(ebp), edi        var.0008 := edi = edi_in
  0x10017a6f   [ -8 ]   mov edi, 0x8(ebp)         edi := arg.0004 = arg.0004_in
  0x10017a72   [ -8 ]   mov ecx, 0xc(ebp)         ecx := arg.0008 = arg.0008_in
  0x10017a75   [ -8 ]   shr ecx, 0x7              ecx := ecx / 128
                                                     = (arg.0008_in / 128)
  0x10017a78   [ -8 ]   pxordq %xmm0, %xmm0       packed op:xor (abstract xmm(0))
  0x10017a7c   [ -8 ]   jmp 0x10017a86            goto 0x10017a86
--------------------------------------------------------------------------------
  0x10017a86   [ -8 ]   movdqa (edi), %xmm0       ? := ?
  0x10017a8a   [ -8 ]   movdqa 0x10(edi), %xmm0   ? := ?
  0x10017a8f   [ -8 ]   movdqa 0x20(edi), %xmm0   ? := ?
  0x10017a94   [ -8 ]   movdqa 0x30(edi), %xmm0   ? := ?
  0x10017a99   [ -8 ]   movdqa 0x40(edi), %xmm0   ? := ?
  0x10017a9e   [ -8 ]   movdqa 0x50(edi), %xmm0   ? := ?
  0x10017aa3   [ -8 ]   movdqa 0x60(edi), %xmm0   ? := ?
  0x10017aa8   [ -8 ]   movdqa 0x70(edi), %xmm0   ? := ?
  0x10017aad   [ -8 ]   lea edi, 0x80(edi)        edi := (edi + 128)
  0x10017ab3   [ -8 ]   dec ecx                   ecx := ecx - 1
  0x10017ab4   [ -8 ]   jnz 0x10017a86            if (ecx != 1) then
                                                     goto 0x10017a86
--------------------------------------------------------------------------------
  0x10017ab6   [ -8 ]   mov edi, -0x4(ebp)        edi := var.0008 = edi_in
  0x10017ab9   [ -8 ]   mov esp, ebp              esp := ebp = (esp_in - 4)
  0x10017abb   [ -4 ]   pop ebp                   restore ebp
  0x10017abc   [ 0 ]    ret                       return

*)
class fastzero_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__fastzero_I__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [
        STR self#get_name; STR "(dst:"; xpr_to_pretty floc arg1;
	STR ",count:"; xpr_to_pretty floc arg2; STR ")"]

  method! get_commands (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let size = get_arg args 2 floc in
    let lhs = floc#get_lhs_from_address arg1 in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Ecx]] in
    cmds1 @ cmds2

  method get_parametercount = 2

  method! get_description = "fastcopy_I internal crt function"

end

let _ = H.add table "fastzero_I" (new fastzero_semantics_t)


(* =============================================================== __fload_withFB
   example: V008:0x41cb35
*)
class floadwithfb_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__fload_withFB__"

  method! get_annotation (floc:floc_int) =
    let edxv = get_reg_value Edx floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc edxv; STR ")"]

  method get_parametercount = 0

end

let _ = H.add table "__fload_withFB" (new floadwithfb_semantics_t)


class getrterrmsg_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__GET_RTERRMSG__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc arg; STR ")"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx]]

  method get_parametercount = 1

  method! get_description =
    "retrieves an error message based on an error code"

end


class getprintfcountoutput_semantics_t
        (md5hash:string)
        (_securitycookie:doubleword_int)
        (_gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__get_printf_count_output__"

  method get_parametercount = 0

end


(* ========================================================= __initp_misc_winsig
   example: V007:0x44bccd

  0x44bccd   [ 0 ]    mov edi, edi          nop
  0x44bccf   [ 0 ]    push ebp              save ebp
  0x44bcd0   [ -4 ]   mov ebp, esp          ebp := esp = (esp_in - 4)
  0x44bcd2   [ -4 ]   mov eax, 0x8(ebp)     eax := arg.0004 = arg.0004_in
  0x44bcd5   [ -4 ]   mov 0x473148, eax     gv_0x473148 := eax = arg.0004_in
  0x44bcda   [ -4 ]   mov 0x47314c, eax     gv_0x47314c := eax = arg.0004_in
  0x44bcdf   [ -4 ]   mov 0x473150, eax     gv_0x473150 := eax = arg.0004_in
  0x44bce4   [ -4 ]   mov 0x473154, eax     gv_0x473154 := eax = arg.0004_in
  0x44bce9   [ -4 ]   pop ebp               restore ebp
  0x44bcea   [ 0 ]    ret                   return
*)
class initpmiscwinsig_semantics_t
        (md5hash:string)
        (gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__initp_misc_winsig__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc arg; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs, lhscmds) = get_reg_lhs Eax floc in
    let arg = get_arg floc#get_call_args 1 floc in
    let cmds1 =
      List.concat
        (List.map (fun offset ->
             let v =
               TR.tget_ok
                 (floc#env#mk_global_variable (gv#add_int offset)#to_numerical) in
             floc#get_assign_commands v arg)
           [0; 4; 8; 16]) in
    let cmds2 = floc#get_assign_commands lhs arg in
    List.concat [lhscmds; cmds1; cmds2]

  method get_parametercount = 1

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

end


class lcgrandom_semantics_t
        (md5hash:string)
        (gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__LCGrandom__"

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = (absolute_op gv 4 WR)#to_lhs floc in
    let cmds1 = floc#get_assign_commands lhs random_constant_expr in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax]] in
    List.concat [lhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "Linear Congruence Generator of pseudo random numbers"

end


class lcidfromhexstring_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__LcidFromHexString__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "(s:"; xpr_to_strpretty floc arg; STR ")"]

  method get_parametercount = 1

end

let _ = H.add table "_LcidFromHexString" (new lcidfromhexstring_semantics_t)


(* ===================================================================== MD5Init
   example: V030:0x806cd1

  0x806cd1  mov eax, 0x4(esp,,1)      eax := arg.0004 = arg.0004_in
  0x806cd5  and 0x14(eax), 0x0        (arg.0004_in)[20] := 0
  0x806cd9  and 0x10(eax), 0x0        (arg.0004_in)[16] := 0
  0x806cdd  mov (eax), 0x67452301     (arg.0004_in)[0] := 1732584193
  0x806ce3  mov 0x4(eax), 0xefcdab89  (arg.0004_in)[4] := 4023233417
  0x806cea  mov 0x8(eax), 0x98badcfe  (arg.0004_in)[8] := 2562383102
  0x806cf1  mov 0xc(eax), 0x10325476  (arg.0004_in)[12] := 271733878
  0x806cf8  ret                       return
*)
class md5init_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__MD5Init__"

  method !get_annotation (floc:floc_int) =
    let arg1 = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc arg1; STR ")"]

  method! get_commands (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    let vals =
      [ (0, "0x67452301");
	(4, "0xefcdab89");
	(8, "0x98badcfe");
	(12, "0x10325476");
	(16, "0x0");
	(20, "0x0")] in
    List.concat (List.map (fun (offset, c) ->
      let lhs = get_x_deref_lhs arg offset floc in
      let cv =
        num_constant_expr (constant_string_to_doubleword c)#to_numerical in
      floc#get_assign_commands lhs cv) vals)

  method get_parametercount = 1

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "initializes a vector with the MD5 initialization constants"

end

let _ = H.add table "MD5Init" (new md5init_semantics_t)


(* =================================================================== __mtold12
   example: V008:0x423c84
*)
class mtold12_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__mtold12__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1;
	STR ","; xpr_to_pretty floc arg2;
	STR ","; xpr_to_pretty floc arg3; STR ")"]

  method! get_commands (floc:floc_int) =
    let arg3 = get_arg floc#get_call_args 3 floc in
    let lhs = get_x_deref_lhs arg3 0 floc in
    let size = int_constant_expr 12 in
    let serhs = floc#f#env#mk_side_effect_value floc#cia "arg3" in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar serhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 3

end

let _ = H.add table "__mtold12" (new mtold12_semantics_t)


(* ================================================================== NLG_Notify
   example: Vc13:0x40d035

  0x40d035  push ebx                  save ebx
  0x40d036  push ecx                  save ecx
  0x40d037  mov ebx, 0x419e30         ebx := 4300336
  0x40d03c  mov ecx, 0xc(esp,,1)      ecx := arg.0004 = arg.0004_in
--------------------------------------------------------------------------------
  0x40d040  mov 0x8(ebx), ecx         gv_0x419e38 := ecx = arg.0004_in
  0x40d043  mov 0x4(ebx), eax         gv_0x419e34 := eax = eax_in
  0x40d046  mov 0xc(ebx), ebp         gv_0x419e3c := ebp = ebp_in
  0x40d049  push ebp                  save ebp
  0x40d04a  push ecx                  esp := esp - 4; var.0016 := ecx
  0x40d04b  push eax                  save eax
  0x40d04c  pop eax                   restore eax
  0x40d04d  pop ecx                   ecx := arg.0004_in; (esp_in - 12)
  0x40d04e  pop ebp                   restore ebp
  0x40d04f  pop ecx                   restore ecx
  0x40d050  pop ebx                   restore ebx
  0x40d051  ret 4                     return (increment stackpointer by 4)
*)
class nlgnotify_semantics_t
        (md5hash:string)
        (gv:doubleword_int)
        (rhs1:patternrhs_t)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__NLG_Notify__"

  method! get_annotation (floc:floc_int) =
    let arg1 = get_patternrhs_value rhs1 floc in
    let eaxv = get_reg_value Eax floc in
    let ebpv = get_reg_value Ebp floc in
    LBLOCK [
        STR self#get_name; STR "(fld1:"; xpr_to_pretty floc arg1;
	STR ",fld2:"; xpr_to_pretty floc eaxv;
	STR ",fld3:"; xpr_to_pretty floc ebpv; STR ")"]

  method! get_commands (floc:floc_int) =
    let env = floc#f#env in
    let arg1 = get_patternrhs_value rhs1 floc in
    let eaxv = get_reg_value Eax floc in
    let ebpv = get_reg_value Ebp floc in
    let gv1 = TR.tget_ok (env#mk_global_variable (gv#add_int 4)#to_numerical) in
    let gv2 = TR.tget_ok (env#mk_global_variable (gv#add_int 8)#to_numerical) in
    let gv3 = TR.tget_ok (env#mk_global_variable (gv#add_int 12)#to_numerical) in
    let cmds1 = floc#get_assign_commands gv1 arg1 in
    let cmds2 = floc#get_assign_commands gv2 eaxv in
    let cmds3 = floc#get_assign_commands gv3 ebpv in
    let cmds4 = get_adjustment_commands 4 floc in
    List.concat [cmds1; cmds2; cmds3; cmds4]

  method get_parametercount = 1

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "sets info for setjmp/longjmp"

end


(* ================================================================== __positive
   example: V007: 0x450c12
 *)
class positive_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__positive__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc arg; STR ")"]

  method get_parametercount = 1

  method! get_description =
    "checks whether a floating point number is positive"

end

let _ = H.add table "positive" (new positive_semantics_t)


(* ========================================================== __removelocaleref
   example: V008: 0x416814
 *)
class removelocaleref_semantics_t
        (md5hash:string)
        (_gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__removelocaleref__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK  [STR self#get_name; STR "("; xpr_to_pretty floc arg; STR ")"]

  method! get_commands (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let cmds1 = floc#get_assign_commands lhs arg in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Ecx; Edx]] in
    List.concat [lhscmds; cmds1; cmds2 ]

  method get_parametercount = 1

end


(* ============================================================== sbh_find_block
   example: V2bd:0x1001211a

  0x1001211a   [ 0 ]    mov edi, edi          nop
  0x1001211c   [ 0 ]    push ebp              save ebp
  0x1001211d   [ -4 ]   mov ebp, esp          ebp := esp = (esp_in - 4)
  0x1001211f   [ -4 ]   mov ecx, 0x10026fb0   ecx := gv_0x10026fb0
                                                 = gv_0x10026fb0_in
  0x10012125   [ -4 ]   mov eax, 0x10026fb4   eax := gv_0x10026fb4
                                                 = gv_0x10026fb4_in
  0x1001212a   [ -4 ]   imul ecx, ecx, 0x14   ecx := ecx * 20
                                                 = (gv_0x10026fb0_in * 20)
  0x1001212d   [ -4 ]   add ecx, eax          ecx := ecx + eax
                                                 = (ecx + gv_0x10026fb4_in)
  0x1001212f   [ -4 ]   jmp 0x10012142        goto 0x10012142
--------------------------------------------------------------------------------
  0x10012131   [ -4 ]   mov edx, 0x8(ebp)     edx := arg.0004 = arg.0004_in
  0x10012134   [ -4 ]   sub edx, 0xc(eax)     edx := edx -  ?  (tmpN)
                                                 = (arg.0004_in - tmpN)
  0x10012137   [ -4 ]   cmp edx, 0x100000     cmp edx, 0x100000
  0x1001213d   [ -4 ]   jc 0x10012148         if (edx < 1048576) then
                                                 goto 0x10012148
--------------------------------------------------------------------------------
  0x1001213f   [ -4 ]   add eax, 0x14         eax := eax + 20
--------------------------------------------------------------------------------
  0x10012142   [ -4 ]   cmp eax, ecx          cmp eax, ecx
  0x10012144   [ -4 ]   jc 0x10012131         if (eax < ecx) then
                                                  goto 0x10012131
--------------------------------------------------------------------------------
  0x10012146   [ -4 ]   xor eax, eax          eax := 0
--------------------------------------------------------------------------------
  0x10012148   [ -4 ]   pop ebp               restore ebp
  0x10012149   [ 0 ]    ret                   return
   -----------------------------------------------------------------------------
   example: V304:0x403b55

  0x403b55  mov eax, 0x486efc      eax := gv_0x486efc = gv_0x486efc_in
  0x403b5a  lea ecx, (eax,eax,4)   ecx := (gv_0x486efc_in + (4 * gv_0x486efc_in))
  0x403b5d  mov eax, 0x486f00      eax := gv_0x486f00 = gv_0x486f00_in
  0x403b62  lea ecx, (eax,ecx,4)   ecx := (gv_0x486f00_in + (20 * gv_0x486efc_in))
  0x403b65  jmp 0x403b79           goto 0x403b79
--------------------------------------------------------------------------------
  0x403b67  mov edx, 0x4(esp,,1)   edx := arg.0004 = arg.0004_in
  0x403b6b  sub edx, 0xc(eax)      edx := edx -  ?  (tmpN) = (arg.0004_in - tmpN)
  0x403b6e  cmp edx, 0x100000      cmp edx, 0x100000
  0x403b74  jc 0x403b7f            if (edx < 1048576) then goto 0x403b7f
--------------------------------------------------------------------------------
  0x403b76  add eax, 0x14          eax := eax + 20
--------------------------------------------------------------------------------
  0x403b79  cmp eax, ecx      cmp eax, ecx
  0x403b7b  jc 0x403b67       if (eax < (gv_0x486f00_in + (20 * gv_0x486efc_in)))
                                       then goto 0x403b67
--------------------------------------------------------------------------------
  0x403b7d  xor eax, eax      eax := 0
--------------------------------------------------------------------------------
  0x403b7f  ret               return

*)

class sbhfindblock_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__sbh_find_block__"

  method! get_annotation (floc:floc_int) =
    let arg1 = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc arg1; STR ")"]

  method get_parametercount = 1

  method! get_description = "sbh_find_block internal CRT function"

end


(* ============================================================ sbh_resize_block
   example: V2bd:0x10012618
   md5hash: 293320db45cefa03202b79e448bc1181 (256 instrs)
*)
class sbhresizeblock_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__sbh_resize_block__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1;
	STR ", "; xpr_to_pretty floc arg2;
	STR ", "; xpr_to_pretty floc arg3; STR ")"]

  method get_parametercount = 3

  method! get_description = "sbh_resize_block internal CRT function"

end

let _ = H.add table "sbh_resize_block" (new sbhresizeblock_semantics_t)


(* ================================================================= setSBCS *)
class setsbcs_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__setSBCS__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [
        STR self#get_name; STR "(lpThreadMbcInfo:"; xpr_to_pretty floc arg;
	STR ")"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 1

  method! get_description = "sets single byte character set"

end


(* ================================================================ siglookup *)

class siglookup_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__siglookup__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1; STR ",";
	xpr_to_pretty floc arg2; STR ")"]

  method get_parametercount = 2

end

(* ======================================================== _TestDefaultCountry
   example: V008:4200e8
 *)
class testdefaultcountry_semantics_t
        (md5hash:string)
        (_gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__TestDefaultCountry__"

  method! get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc arg; STR ")"]

  method get_parametercount = 1

end


(* ================================================================ vec_memzero
   example: V2bd:0x10017abd

  0x10017abd   [ 0 ]    push ebp                  save ebp
  0x10017abe   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x10017ac0   [ -4 ]   sub esp, 0x10             esp := esp - 16 = (esp_in - 20)
  0x10017ac3  [ -20 ]   mov -0x4(ebp), edi        var.0008 := edi = edi_in
  0x10017ac6  [ -20 ]   mov eax, 0x8(ebp)         eax := arg.0004 = arg.0004_in
  0x10017ac9  [ -20 ]   cdq                       convert long to double
  0x10017aca  [ -20 ]   mov edi, eax              edi := eax = arg.0004_in
  0x10017acc  [ -20 ]   xor edi, edx              edi := edi xor edx
  0x10017ace  [ -20 ]   sub edi, edx              edi := edi - edx
  0x10017ad0  [ -20 ]   and edi, 0xf              edi := edi & 15
  0x10017ad3  [ -20 ]   xor edi, edx              edi := edi xor edx
  0x10017ad5  [ -20 ]   sub edi, edx              edi := edi - edx
  0x10017ad7  [ -20 ]   test edi, edi             test edi, edi
  0x10017ad9  [ -20 ]   jnz 0x10017b17            if (edi != 0) then
                                                     goto 0x10017b17
--------------------------------------------------------------------------------
  0x10017adb  [ -20 ]   mov ecx, 0x10(ebp)        ecx := arg.0012 = arg.0012_in
  0x10017ade  [ -20 ]   mov edx, ecx              edx := ecx = arg.0012_in
  0x10017ae0  [ -20 ]   and edx, 0x7f             edx := edx & 127
  0x10017ae3  [ -20 ]   mov -0xc(ebp), edx        var.0016 := edx
  0x10017ae6  [ -20 ]   cmp ecx, edx              cmp ecx, edx
  0x10017ae8  [ -20 ]   jz 0x10017afc             if (arg.0012_in = edx) then
                                                     goto 0x10017afc
--------------------------------------------------------------------------------
  0x10017aea  [ -20 ]   sub ecx, edx              ecx := ecx - edx
                                                     = (arg.0012_in - edx)
  0x10017aec  [ -20 ]   push ecx                  [0x10017a66 : arg_2 = ecx ]
  0x10017aed  [ -24 ]   push eax                  [0x10017a66 : arg_1 = eax ]
  0x10017aee  [ -28 ]   call 0x10017a66           0x10017a66(
                                                     arg_1:arg.0004_in,
                                                     arg_2:var.0024,
                                                     reg_ebp:&var.0004,
                                                     reg_edi:0)
  0x10017af3  [ -28 ]   add esp, 0x8              esp := esp + 8 = (esp_in - 20)
  0x10017af6  [ -20 ]   mov eax, 0x8(ebp)         eax := arg.0004 = arg.0004_in
  0x10017af9  [ -20 ]   mov edx, -0xc(ebp)        edx := var.0016
--------------------------------------------------------------------------------
  0x10017afc  [ -20 ]   test edx, edx             test edx, edx
  0x10017afe  [ -20 ]   jz 0x10017b45             if (edx = 0) then goto 0x10017b45
--------------------------------------------------------------------------------
  0x10017b00  [ -20 ]   add eax, 0x10(ebp)        eax := eax + arg.0012
                                                     = (arg.0004_in + arg.0012_in)
  0x10017b03  [ -20 ]   sub eax, edx              eax := eax - edx
                                                     = ((arg.0004_in + arg.0012_in)
                                                       - edx)
  0x10017b05  [ -20 ]   mov -0x8(ebp), eax        var.0012 := eax
  0x10017b08  [ -20 ]   xor eax, eax              eax := 0
  0x10017b0a  [ -20 ]   mov edi, -0x8(ebp)        edi := var.0012
  0x10017b0d  [ -20 ]   mov ecx, -0xc(ebp)        ecx := var.0016
  0x10017b10  [ -20 ]   rep stos                  (Edi): ?; Ecx: ecx (width: 1)
  0x10017b12  [ -20 ]   mov eax, 0x8(ebp)         eax := arg.0004 = arg.0004_in
  0x10017b15  [ -20 ]   jmp 0x10017b45            goto 0x10017b45
--------------------------------------------------------------------------------
  0x10017b17  [ -20 ]   neg edi                   edi := 0 - edi
  0x10017b19  [ -20 ]   add edi, 0x10             edi := edi + 16
  0x10017b1c  [ -20 ]   mov -0x10(ebp), edi       var.0020 := edi
  0x10017b1f  [ -20 ]   xor eax, eax              eax := 0
  0x10017b21  [ -20 ]   mov edi, 0x8(ebp)         edi := arg.0004 = arg.0004_in
  0x10017b24  [ -20 ]   mov ecx, -0x10(ebp)       ecx := var.0020
  0x10017b27  [ -20 ]   rep stos                  (Edi): (arg.0004_in)[0];
                                                     Ecx: ecx (width: 1)
  0x10017b29  [ -20 ]   mov eax, -0x10(ebp)       eax := var.0020
  0x10017b2c  [ -20 ]   mov ecx, 0x8(ebp)         ecx := arg.0004 = arg.0004_in
  0x10017b2f  [ -20 ]   mov edx, 0x10(ebp)        edx := arg.0012 = arg.0012_in
  0x10017b32  [ -20 ]   add ecx, eax              ecx := ecx + eax
                                                     = (arg.0004_in + eax)
  0x10017b34  [ -20 ]   sub edx, eax              edx := edx - eax
                                                     = (arg.0012_in - eax)
  0x10017b36  [ -20 ]   push edx                  [0x10017abd : arg_3 = edx ]
  0x10017b37  [ -24 ]   push 0x0                  [0x10017abd : ?arg_2 = 0 ]
  0x10017b39  [ -28 ]   push ecx                  [0x10017abd : arg_1 = ecx ]
  0x10017b3a  [ -32 ]   call 0x10017abd           0x10017abd(
                                                     arg_1:var.0032,
                                                     arg_3:var.0024,
                                                     reg_ebp:&var.0004,
                                                     reg_edi:edi)
  0x10017b3f  [ -32 ]   add esp, 0xc              esp := esp + 12 = (esp_in - 20)
  0x10017b42  [ -20 ]   mov eax, 0x8(ebp)         eax := arg.0004 = arg.0004_in
--------------------------------------------------------------------------------
  0x10017b45  [ -20 ]   mov edi, -0x4(ebp)        edi := var.0008 = edi_in
  0x10017b48  [ -20 ]   mov esp, ebp              esp := ebp = (esp_in - 4)
  0x10017b4a   [ -4 ]   pop ebp                   restore ebp
  0x10017b4b   [ 0 ]    ret                       return
*)

class vecmemzero_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__VEC_memzero__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [ STR self#get_name; STR "(dst:"; xpr_to_pretty floc arg1;
	     STR ",c:_,count:"; xpr_to_pretty floc arg3; STR ")" ]

  method! get_commands (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let size = get_arg args 3 floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let lhs = floc#get_lhs_from_address arg1 in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = floc#get_assign_commands eaxlhs arg1 in
    let cmds3 = [floc#get_abstract_cpu_registers_command [Ecx; Edx]] in
    eaxlhscmds @ cmds1 @ cmds2 @ cmds3

  method get_parametercount = 3

  method! get_description = "vec_memzero internal crt function"

end

(* ================================================================== VEC_memcpy
   example: V2bd:0x10011d25

 *)
class vecmemcpy_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__VEC_memcpy__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [
        STR self#get_name; STR "(dst:"; xpr_to_pretty floc arg1;
	STR ",src:"; xpr_to_pretty floc arg2;
	STR ",count:"; xpr_to_pretty floc arg3; STR ")"]

  method! get_commands (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let size = get_arg args 3 floc in
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let selhs = floc#get_lhs_from_address arg1 in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands selhs ~size (XVar rhs) in
    let cmds2 = floc#get_assign_commands lhs arg1 in
    let cmds3 = [floc#get_abstract_cpu_registers_command [Ecx; Edx]] in
    List.concat [lhscmds; cmds1; cmds2; cmds3]

  method get_parametercount = 3

  method! get_description = "VEC_memcpy internal CRT function"

end


let internalcrt_functions =
  H.fold (fun k v a -> a @ (get_fnhashes k v)) table []


let findblock_matcher instrs _faddr fnbytes fnhash =
  let base = todw (Str.matched_group 1 fnbytes) in
  let lpMem = todw (Str.matched_group 2 fnbytes) in
  let sem = new sbhfindblock_semantics_t fnhash instrs in
  let msg =
    LBLOCK [
        STR " with base "; base#toPretty; STR " and lpMem "; lpMem#toPretty] in
  sometemplate ~msg sem


let internalcrt_patterns = [

  (* __addlocaleref (V008:0x416625) *)
  { regex_s = Str.regexp
      ("558bec8b550833c9535641578bc1f00fc1028b727885f674068bc1f00fc1068bb28000" ^
       "000085f674068bc1f00fc1068b727c85f674068bc1f00fc1068bb28800000085f67406" ^
       "8bc1f00fc1066a068d721c5b817ef8\\(........\\)740c8b3e85ff74068bc1f00fc1" ^
       "07837ef400740d8b7efc85ff74068bc1f00fc10783c6104b75d28b829c00000005b000" ^
       "0000f00fc108415f5e5b5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new addlocaleref_semantics_t fnhash gv 67 in
      let msg = LBLOCK [STR " with reference location "; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* __convertTOStoQNaN (V008:0x41cb1c) *)
  { regex_s = Str.regexp
      ("a9000008007406b807000000c3dc05\\(........\\)b801000000c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new converttostoqnan_semantics_t fnhash gv 7 in
      let msg = LBLOCK [STR " with global variable gv_"; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* __crtCorExitProcess (Vc13:0x408a6b) *)
  { regex_s = Str.regexp
      ("558bec518d45fc5068\\(........\\)6a00ff15\\(........\\)85c0741768" ^
       "\\(........\\)ff75fcff15\\(........\\)85c07405ff7508ffd0c9c3$");

    regex_f = fun faddr fnbytes fnhash ->
      let get_string = FFU.get_string_reference in
      let lpmname = todw (Str.matched_group 1 fnbytes) in
      let lppname = todw (Str.matched_group 3 fnbytes) in
      match (get_string lpmname, get_string lppname) with
      | (Some "mscoree.dll",Some "CorExitProcess") ->
	if (is_named_dll_call faddr 15 "GetModuleHandleExW") &&
	  (is_named_dll_call faddr 33 "GetProcAddress") then
	  let sem = new crtcorexitprocess_semantics_t fnhash 19 in
	  sometemplate sem
	else
	  None
      | (Some mname, Some pname) ->
	begin
	  chlog#add
            "mismatched library function"
	    (LBLOCK [
                 faddr#toPretty; STR ": ";
		 STR "__crtCorExitProcess with different dll and/or function: ";
		 STR mname; STR ":"; STR pname]);
	  None
	end
      | _ ->
	begin
	  chlog#add
            "unmatched library function"
	    (LBLOCK [
                 faddr#toPretty; STR ": ";
		 STR "__crtCorExitProcess without dll and/or function name"]);
	  None
	end
  };


  (* __crtFlsGetValue (Vc13:0x409735) *)
  { regex_s = Str.regexp
      ("558beca1\\(........\\)3305\\(........\\)ff75087404ffd05dc3ff15" ^
       "\\(........\\)5dc3$");

    regex_f = fun faddr fnbytes fnhash ->
      let fploc = todw (Str.matched_group 1 fnbytes) in
      let sec = todw (Str.matched_group 2 fnbytes) in
      if is_named_dll_call faddr 23 "TlsGetValue" then
	let _ = system_info#add_esp_adjustment faddr (faddr#add_int 19) 4 in
	let sem = new crtflsgetvalue_semantics_t fnhash 12 in
	let msg =
          LBLOCK [
              STR " with fp location "; fploc#toPretty;
	      STR " and security cookie "; sec#toPretty] in
	sometemplate ~msg sem
      else
	None
  };

  (* __crtUnhandledException (V008:0x413948) *)
  { regex_s = Str.regexp
      ("558bec6a00ff1570504200ff7508ff156c5042005dc3$");

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_dll_call faddr 5 "SetUnhandledExceptionFilter" &&
	is_named_dll_call faddr 14 "UnhandledExceptionFilter" then
	let sem = new crtunhandledexception_semantics_t fnhash 8 in
	sometemplate sem
      else
	None
  };

  (* __get_printf_count_output (V007:0x44e9c7) *)
  { regex_s = Str.regexp
      ("a1\\(........\\)83c80133c93905\\(........\\)0f94c18bc1c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let secc = todw (Str.matched_group 1 fnbytes) in
      let gv = todw (Str.matched_group 2 fnbytes) in
      let sem = new getprintfcountoutput_semantics_t fnhash secc gv 7 in
      let msg =
        LBLOCK [
            STR " with security cookie "; secc#toPretty;
	    STR " and global variable gv_"; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* __get_printf_count_output (V008:0x41d97b) *)
  { regex_s = Str.regexp
      ("8b0d\\(........\\)33c083c901390d\\(........\\)0f94c0c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let secc = todw (Str.matched_group 1 fnbytes) in
      let gv = todw (Str.matched_group 2 fnbytes) in
      let sem = new getprintfcountoutput_semantics_t fnhash secc gv 7 in
      let msg =
        LBLOCK [
            STR " with security cookie "; secc#toPretty;
	    STR " and global variable gv_"; gv#toPretty] in
      sometemplate ~msg sem
  };


  (* __GET_RTERRMSG
     example: Vc13:0x408d96

  0x408d96  push ebp                  save ebp
  0x408d97  mov ebp, esp              ebp := esp = (esp_in - 4)
  0x408d99  mov ecx, 0x8(ebp)         ecx := arg.0004 = arg.0004_in
  0x408d9c  xor eax, eax              eax := 0
--------------------------------------------------------------------------------
  0x408d9e  cmp ecx, 0x4151e8(,eax,8)  cmp ecx, 0x4151e8(,eax,8)
  0x408da5  jz 0x408db1               if (arg.0004_in = gv_0x4151e8[eax:8]) then
                                        goto 0x408db1
--------------------------------------------------------------------------------
  0x408da7  inc eax                   eax := eax + 1
  0x408da8  cmp eax, 0x17             cmp eax, 0x17
  0x408dab  jc 0x408d9e               if (eax < 23) then goto 0x408d9e
--------------------------------------------------------------------------------
  0x408dad  xor eax, eax              eax := 0
  0x408daf  pop ebp                   restore ebp
  0x408db0  ret                       return
--------------------------------------------------------------------------------
  0x408db1  mov eax, 0x4151ec(,eax,8)  eax := gv_0x4151ec[eax:8]
  0x408db8  pop ebp                   restore ebp
  0x408db9  ret                       return

  *)
  { regex_s = Str.regexp
      ("558bec8b4d0833c03b0cc5\\(........\\)740a4083f8\\(..\\)72f133c05dc38b04" ^
       "c5\\(........\\)5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let base1 = todw (Str.matched_group 1 fnbytes) in
      let count = toimm2 (Str.matched_group 2 fnbytes) in
      let base2 = todw (Str.matched_group 3 fnbytes) in
      if (base1#add_int 4)#equal base2 then
	let sem = new getrterrmsg_semantics_t fnhash 15 in
	let msg =
          LBLOCK [
              STR " with message base "; base1#toPretty;
	      STR " and message count "; INT count] in
	sometemplate ~msg sem
      else
	None
  };

 (* __initp_misc_winsig (V007:44bccd) *)
  { regex_s = Str.regexp
      ("8bff558bec8b4508a3\\(........\\)a3\\(........\\)a3\\(........\\)a3" ^
       "\\(........\\)5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv1 = todw (Str.matched_group 1 fnbytes) in
      let gv2 = todw (Str.matched_group 2 fnbytes) in
      let gv3 = todw (Str.matched_group 3 fnbytes) in
      let gv4 = todw (Str.matched_group 4 fnbytes) in
      if gv2#equal (gv1#add_int 4) &&
	(gv3#equal (gv1#add_int 8)) &&
	(gv4#equal (gv1#add_int 12)) then
	let sem = new initpmiscwinsig_semantics_t fnhash gv1 10 in
	let msg = LBLOCK [STR " with base location "; gv1#toPretty] in
	sometemplate ~msg sem
      else
	None
  };

  { regex_s = Str.regexp
      ("558bec8b4508a3\\(........\\)a3\\(........\\)a3\\(........\\)a3" ^
       "\\(........\\)5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv1 = todw (Str.matched_group 1 fnbytes) in
      let gv2 = todw (Str.matched_group 2 fnbytes) in
      let gv3 = todw (Str.matched_group 3 fnbytes) in
      let gv4 = todw (Str.matched_group 4 fnbytes) in
      if gv2#equal (gv1#add_int 4) &&
	(gv3#equal (gv1#add_int 8)) &&
	(gv4#equal (gv1#add_int 12)) then
	let sem = new initpmiscwinsig_semantics_t fnhash gv1 9 in
	let msg = LBLOCK [STR " with base location "; gv1#toPretty] in
	sometemplate ~msg sem
      else
	None
  };


  (* Linear Congruential Generator of pseudo random numbers: LCGrandom
     example: V022:0x802ec9

  0x802e9c  mov eax, dbv:0x807f20[0x0]  eax := gv_0x807f20 = gv_0x807f20_in
  0x802ea1  imul eax, eax, 0x343fd      eax := eax * 214013
                                           = (gv_0x807f20_in * 214013)
  0x802ea7  add eax, 0x269ec3           eax := eax + 2531011
  0x802eac  mov 0x807f20, eax           gv_0x807f20 := eax
  0x802eb1  mov eax, dbv:0x807f20[0x2]  eax := gv_0x807f22 = gv_0x807f22_in
  0x802eb7  ret                         return
  *)
  { regex_s =
      Str.regexp
        ("a1\\(........\\)69c0fd43030005c39e2600a3\\(........\\)"
         ^ "66a1\\(........\\)c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let gv1 = todw (Str.matched_group 2 fnbytes) in
      let gv2 = todw (Str.matched_group 3 fnbytes) in
      if gv#equal gv1 && (gv#add_int 2)#equal gv2 then
	let sem = new lcgrandom_semantics_t fnhash gv 6 in
	let msg = LBLOCK [STR " with seed location "; gv#toPretty] in
	sometemplate ~msg sem
      else
	None
  };

  (* NLG_Notify (Vc13:0x40d035) *)
  { regex_s = Str.regexp
      ("5351bb\\(........\\)8b4c240c894b08894304896b0c55515058595d595bc20400$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new nlgnotify_semantics_t fnhash gv (PArgument 1) 16 in
      let msg = LBLOCK [STR " with base address "; gv#toPretty]  in
      sometemplate ~msg sem
  };

  (* NLG_Notify1 (V007:0x45181c) *)
  { regex_s = Str.regexp
      ("5351bb\\(........\\)eb0b894b08894304896b0c55515058595d595bc20400$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new nlgnotify_semantics_t fnhash gv (PRegister Ecx) 16 in
      let msg = LBLOCK [STR " with base address "; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* __removelocaleref (V008:0x416814) *)
  { regex_s = Str.regexp
      ("558bec8b550885d20f848e000000535683ceff578bc6f00fc1028b4a7885c974068bc6" ^
       "f00fc1018b8a8000000085c974068bc6f00fc1018b4a7c85c974068bc6f00fc1018b8a" ^
       "8800000085c974068bc6f00fc1016a068d4a1c5b8179f8\\(........\\)740c8b3985" ^
       "ff74068bc6f00fc1078379f400740d8b79fc85ff74068bc6f00fc10783c1104b75d28b" ^
       "8a9c00000081c1b0000000f00fc1314e5f5e5b8bc25dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new removelocaleref_semantics_t fnhash gv 69 in
      let msg = LBLOCK [STR " with reference address "; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* sbh_find_block (V007:0x447a0e) *)
  { regex_s = Str.regexp
      ("8bff558bec8b0d\\(........\\)a1\\(........\\)6bc91403c8eb118b55082b500c81" ^
       "fa00001000720983c0143bc172eb33c05dc3$");
    regex_f = findblock_matcher 18
  };

  (* sbh_find_block (V00bcd1 : 0x40afd1) *)
  { regex_s = Str.regexp
      ("a1\\(........\\)8d0c80a1\\(........\\)8d0c88eb128b5424042b500c81fa000010" ^
       "00720983c0143bc172ea33c0c3$");
    regex_f = findblock_matcher 14
  };

  (* sbh_find_block (V098864:0x455a45 *)
  { regex_s = Str.regexp
      ("8b0d\\(........\\)a1\\(........\\)6bc91403c8eb128b5424042b500c81fa000010" ^
       "00720983c0143bc172ea33c0c3$");
    regex_f = findblock_matcher 14
  };

  (* sbh_find_block (Vfc160a:0x10001957) *)
  { regex_s = Str.regexp
      ("a1\\(........\\)8d0c80a1\\(........\\)8d0c883bc173148b5424042b500c81fa00" ^
       "001000720783c014ebe833c0c3$");
    regex_f = findblock_matcher 14
  };

  (* setSBCS (Vc13:0x40a412) *)
  { regex_s = Str.regexp
      ("558bec538b5d085657680101000033ff8d73185756e8\\(........\\)33c00fb7c8897b" ^
       "04897b0889bb1c0200008bc1c1e1100bc18d7b0cabababbf\\(........\\)83c40c2bfb" ^
       "b9010100008a04378806464975f78d8b19010000ba000100008a04398801414a75f75f5e" ^
       "5b5dc3$");

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 2 fnbytes) in
      if is_named_dll_call faddr 21 "memset" then
	let sem = new setsbcs_semantics_t fnhash 45 in
	let msg = LBLOCK [STR " with base address "; gv#toPretty] in
	sometemplate ~msg sem
      else
	None
  };

  (* _siglookup (Vc13:0x40b135) *)
  { regex_s = Str.regexp
      ("558bec8b4d0c8b15\\(........\\)568b7508397104740f8bc26bc00c03450c83c10c3b" ^
       "c872ec6bd20c03550c3bca730939710475048bc1eb0233c05e5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new siglookup_semantics_t fnhash 26 in
      let msg = LBLOCK [STR " with size in global variable "; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* _siglookup (V007:0x44bceb) *)
  { regex_s = Str.regexp
      ("8bff558bec8b45088b0d\\(........\\)56395004740f8bf16bf60c03750883c00c3bc6" ^
       "72ec6bc90c034d085e3bc17305395004740233c05dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new siglookup_semantics_t fnhash 26 in
      let msg = LBLOCK [STR " with size in global variable "; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* siglookup (V008:0x41c710) *)
  { regex_s = Str.regexp
      ("558bec8b550c8b0d\\(........\\)568b7508397204740d6bc10c83c20c03450c3bd0" ^
       "72ee6bc90c034d0c3bd1730939720475048bc2eb0233c05e5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new siglookup_semantics_t fnhash 25 in
      let msg = LBLOCK [STR " with size in global variable "; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* _TestDefaultCountry (V008:0x4200e8) *)
  { regex_s = Str.regexp
      ("558bec8b4d0833c0663b88\\(........\\)740d83c00283f81472ef33c0405dc333c0" ^
       "5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new testdefaultcountry_semantics_t fnhash gv 16 in
      let msg = LBLOCK [STR " with global variable gv_"; gv#toPretty] in
      sometemplate ~msg sem
  };

  (* VEC_memcpy *)
  { regex_s = Str.regexp
      ("558bec83ec1c897df48975f8895dfc8b5d0c8bc3998bc88b450833ca2bca83e10f33ca2b" ^
       "ca998bf833fa2bfa83e70f33fa2bfa8bd10bd7754a8b75108bce83e17f894de83bf17413" ^
       "2bf1565350e8\\(........\\)83c40c8b45088b4de885c974778b5d108b550c03d32bd1" ^
       "8955ec03d82bd9895df08b75ec8b7df08b4de8f3a48b4508eb533bcf7535f7d983c11089" ^
       "4de48b750c8b7d088b4de4f3a48b4d08034de48b550c0355e48b45102b45e4505251e84c" ^
       "ffffff83c40c8b4508eb1a8b750c8b7d088b4d108bd1c1e902f3a58bca83e103f3a48b45" ^
       "088b5dfc8b75f88b7df48be55dc3$");

    regex_f =
      fun faddr _fnbytes fnhash ->
      let loc =
        make_location { loc_faddr = faddr; loc_iaddr = faddr#add_int 77 } in
      let cfloc = get_floc loc in
      if cfloc#has_call_target
         && cfloc#get_call_target#is_app_call
         && (let tgtaddr = cfloc#get_call_target#get_app_address in
             (functions_data#get_function tgtaddr)#get_function_name =
               "__fastcopy_I__") then
	let sem = new vecmemcpy_semantics_t fnhash 94 in
	let msg = STR "" in
	sometemplate ~msg sem
      else
        None
  };

  (* VEC_memzero *)
  { regex_s = Str.regexp
      ("558bec83ec10897dfc8b4508998bf833fa2bfa83e70f33fa2bfa85ff753c8b4d108bd183" ^
       "e27f8955f43bca74122bca5150e8\\(........\\)83c4088b45088b55f485d274450345" ^
       "102bc28945f833c08b7df88b4df4f3aa8b4508eb2ef7df83c710897df033c08b7d088b4d" ^
       "f0f3aa8b45f08b4d088b551003c82bd0526a0051e87effffff83c40c8b45088b7dfc8be5" ^
       "5dc3$");

    regex_f =
      fun faddr _fnbytes fnhash ->
      let loc = make_location { loc_faddr = faddr; loc_iaddr = faddr#add_int 49 } in
      let cfloc = get_floc loc in
      if cfloc#has_call_target
         && cfloc#get_call_target#is_app_call
         && (let tgtaddr = cfloc#get_call_target#get_app_address in
             (functions_data#get_function tgtaddr)#get_function_name =
               "__fastzero_I__") then
        let sem = new vecmemzero_semantics_t fnhash 60 in
	sometemplate sem
      else
        None
  }
]
