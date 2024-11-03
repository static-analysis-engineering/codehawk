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
open CHNumerical
open CHPretty

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHFunctionData
open BCHLibTypes
open BCHMakeCallTargetInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHPredefinedUtil

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory
module TR = CHTraceResult

(* -------------------------------------------------------------------------------
   System::AStrCmp
   System::_CLenToPasStr
   System::Copy (s)
   System::EXP
   System::FillChar (s)
   System::Get8087CW
   System::initExnHandling (made up)
   System::InitImports
   System::initTIBInfo (made up)
   System::IntfAddRef
   System::IntfCopy
   System::LStrAddRef
   System::LStrCmp
   System::LStrLen
   System::LStrPos
   System::LStrToPChar
   System::Move (s)
   System::PStrCmp
   System::PStrNCpy
   System::RegisterModule
   System::RegisterModule_wrapper
   System::ROUND
   System::Set8087CW
   System::SetElem
   System::SetEq
   System::SetRange
   System::SetSub
   System::SetUnion
   System::StartExe
   System::TRUNC
   System::ValLong
   System::UpCase (s)
   System::WStrToPWChar
   System::WStrCmp
   System::WStrLen

   System::Sysinit:InitExe

   System::delphi_unknown1   (made up)
 * --------------------------------------------------------------------------- *)

let table = H.create 11


let load_rtl_functions () =
  List.iter
    (fun m -> add_libfun table ["System"] m)
    ["Copy"; "FillChar"; "Move"; "UpCase"]


let mk_target ?(pkgs=[ "System" ]) (a:doubleword_int) (name:string) =
  mk_static_pck_stub_target a "RTL" pkgs name


(* ============================================================= System::AStrCmp
   example: V01a:0x402cd4
   md5hash: 185e45d24958ad6c5099b5c25a309299

  0x402cd4   [ 0 ]    push ebx                  save ebx
  0x402cd5   [ -4 ]   push esi                  save esi
  0x402cd6   [ -8 ]   push ecx                  save ecx
  0x402cd7  [ -12 ]   mov esi, ecx              esi := ecx = ecx_in
  0x402cd9  [ -12 ]   shr esi, 0x2              esi := esi / 4 = (ecx_in / 4)
  0x402cdc  [ -12 ]   jz 0x402d04               if ? then goto 0x402d04
--------------------------------------------------------------------------------
  0x402cde  [ -12 ]   mov ecx, (eax)            ecx :=  ?  (tmpN)
  0x402ce0  [ -12 ]   mov ebx, (edx)            ebx :=  ?  (tmpN)
  0x402ce2  [ -12 ]   cmp ecx, ebx              cmp ecx, ebx
  0x402ce4  [ -12 ]   jnz 0x402d2b              if (ecx != ebx) then goto 0x402d2b
--------------------------------------------------------------------------------
  0x402ce6  [ -12 ]   dec esi                   esi := esi - 1
  0x402ce7  [ -12 ]   jz 0x402cfe               if (esi = 1) then goto 0x402cfe
--------------------------------------------------------------------------------
  0x402ce9  [ -12 ]   mov ecx, 0x4(eax)         ecx :=  ?  (tmpN)
  0x402cec  [ -12 ]   mov ebx, 0x4(edx)         ebx :=  ?  (tmpN)
  0x402cef  [ -12 ]   cmp ecx, ebx              cmp ecx, ebx
  0x402cf1  [ -12 ]   jnz 0x402d2b              if (ecx != ebx) then goto 0x402d2b
--------------------------------------------------------------------------------
  0x402cf3  [ -12 ]   add eax, 0x8              eax := eax + 8
  0x402cf6  [ -12 ]   add edx, 0x8              edx := edx + 8
  0x402cf9  [ -12 ]   dec esi                   esi := esi - 1
  0x402cfa  [ -12 ]   jnz 0x402cde              if (esi != 1) then goto 0x402cde
--------------------------------------------------------------------------------
  0x402cfc  [ -12 ]   jmp 0x402d04              goto 0x402d04
--------------------------------------------------------------------------------
  0x402cfe  [ -12 ]   add eax, 0x4              eax := eax + 4
  0x402d01  [ -12 ]   add edx, 0x4              edx := edx + 4
--------------------------------------------------------------------------------
  0x402d04  [ -12 ]   pop esi                   esi := ecx_in ; esp := esp + 4 = (esp_in - 8)
  0x402d05   [ -8 ]   and esi, 0x3              esi := esi & 3
  0x402d08   [ -8 ]   jz 0x402d40               if ? then goto 0x402d40
--------------------------------------------------------------------------------
  0x402d0a   [ -8 ]   mov cl, (eax)             cl :=  ?  (tmpN)
  0x402d0c   [ -8 ]   cmp cl, (edx)             cmp cl, (edx)
  0x402d0e   [ -8 ]   jnz 0x402d40              if (cl != Unknown) then goto 0x402d40
--------------------------------------------------------------------------------
  0x402d10   [ -8 ]   dec esi                   esi := esi - 1
  0x402d11   [ -8 ]   jz 0x402d26               if (esi = 1) then goto 0x402d26
--------------------------------------------------------------------------------
  0x402d13   [ -8 ]   mov cl, 0x1(eax)          cl :=  ?  (tmpN)
  0x402d16   [ -8 ]   cmp cl, 0x1(edx)          cmp cl, 0x1(edx)
  0x402d19   [ -8 ]   jnz 0x402d40              if (cl != Unknown) then goto 0x402d40
--------------------------------------------------------------------------------
  0x402d1b   [ -8 ]   dec esi                   esi := esi - 1
  0x402d1c   [ -8 ]   jz 0x402d26               if (esi = 1) then goto 0x402d26
--------------------------------------------------------------------------------
  0x402d1e   [ -8 ]   mov cl, 0x2(eax)          cl :=  ?  (tmpN)
  0x402d21   [ -8 ]   cmp cl, 0x2(edx)          cmp cl, 0x2(edx)
  0x402d24   [ -8 ]   jnz 0x402d40              if (cl != Unknown) then goto 0x402d40
--------------------------------------------------------------------------------
  0x402d26   [ -8 ]   xor eax, eax              eax := 0
  0x402d28   [ -8 ]   pop esi                   restore esi
  0x402d29   [ -4 ]   pop ebx                   restore ebx
  0x402d2a   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x402d2b  [ -12 ]   pop esi                   esi := ecx_in ; esp := esp + 4 = (esp_in - 8)
  0x402d2c   [ -8 ]   cmp cl, bl                cmp cl, bl
  0x402d2e   [ -8 ]   jnz 0x402d40              if (cl != bl) then goto 0x402d40
--------------------------------------------------------------------------------
  0x402d30   [ -8 ]   cmp ch, bh                cmp ch, bh
  0x402d32   [ -8 ]   jnz 0x402d40              if (ch != bh) then goto 0x402d40
--------------------------------------------------------------------------------
  0x402d34   [ -8 ]   shr ecx, 0x10             ecx := ecx / 65536
  0x402d37   [ -8 ]   shr ebx, 0x10             ebx := ebx / 65536
  0x402d3a   [ -8 ]   cmp cl, bl                cmp cl, bl
  0x402d3c   [ -8 ]   jnz 0x402d40              if (cl != bl) then goto 0x402d40
--------------------------------------------------------------------------------
  0x402d3e   [ -8 ]   cmp ch, bh                cmp ch, bh
--------------------------------------------------------------------------------
  0x402d40   [ -8 ]   pop esi                   restore esi
  0x402d41   [ -4 ]   pop ebx                   restore ebx
  0x402d42   [ 0 ]    ret                       return
*)
class rtl_system_astrcmp_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::AStrCmp__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    LBLOCK [
        STR self#get_name; STR "(reg_eax:"; xpr_to_pretty floc eaxv;
	STR ",reg_edx:"; xpr_to_pretty floc edxv;
	STR ",reg_ecx:"; xpr_to_pretty floc ecxv; STR ")"]

  method! get_commands (floc:floc_int) =
    [ floc#get_abstract_cpu_registers_command [ Eax; Ecx; Edx ] ]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "AStrCmp"

  method! get_description = "Delphi RTL function System::AStrCmp"

end

let _ = H.add table "System::AStrCmp" (new rtl_system_astrcmp_semantics_t)


(* ======================================================== System::_CLenToPasStr
   example: V1da:0x420fd0
   md5hash: 7a05fc3f003bcbede77d6c3015447139

  0x402fd0   [ 0 ]    push ebx                  save ebx
  0x402fd1   [ -4 ]   push eax                  save eax
  0x402fd2   [ -8 ]   cmp ecx, 0xff             cmp ecx, 0xff
  0x402fd8   [ -8 ]   jbe 0x402fdf              if (ecx_in <= 255) then goto 0x402fdf
--------------------------------------------------------------------------------
  0x402fda   [ -8 ]   mov ecx, 0xff             ecx := 255
--------------------------------------------------------------------------------
  0x402fdf   [ -8 ]   mov bl, (edx)             bl :=  ?  (tmpN)
  0x402fe1   [ -8 ]   inc edx                   edx := edx + 1
  0x402fe2   [ -8 ]   test bl, bl               test bl, bl
  0x402fe4   [ -8 ]   jz 0x402fec               if (bl = 0) then goto 0x402fec
--------------------------------------------------------------------------------
  0x402fe6   [ -8 ]   inc eax                   eax := eax + 1
  0x402fe7   [ -8 ]   mov (eax), bl             ? := bl
  0x402fe9   [ -8 ]   dec ecx                   ecx := ecx - 1
  0x402fea   [ -8 ]   jnz 0x402fdf              if (ecx != 1) then goto 0x402fdf
--------------------------------------------------------------------------------
  0x402fec   [ -8 ]   pop edx                   edx := eax_in; esp := esp + 4 = (esp_in - 4)
  0x402fed   [ -4 ]   sub eax, edx              eax := eax - edx = (eax - eax_in)
  0x402fef   [ -4 ]   mov (edx), al             (eax_in)[0] := al
  0x402ff1   [ -4 ]   pop ebx                   restore ebx
  0x402ff2   [ 0 ]    ret                       return
*)
class rtl_system_clentopasstr_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::_CLenToPasStr__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    LBLOCK [
        STR self#get_name; STR "(Dest:"; xpr_to_pretty floc eaxv;
	STR ",Source:"; xpr_to_pretty floc edxv;
	STR ",Count:"; xpr_to_pretty floc ecxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_deref_lhs Eax 0 floc in
    let rhs = floc#env#mk_side_effect_value floc#cia "Dest" in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Edx; Ecx]] in
    List.concat [lhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "_CLenToPasStr"

  method! get_description = "Delphi RTL function System::_CLenToPasStr"

end

let _ =
  H.add table "System::_CLenToPasStr" (new rtl_system_clentopasstr_semantics_t)


(* ========================================================== System::_CToPasStr
   example: V1da: 0x402fc4

  0x402fc4   [ 0 ]    mov ecx, 0xff      ecx := 255
  0x402fc9   [ 0 ]    call 0x402fd0      0x402fd0(reg_eax:eax_in, reg_ebx:ebx_in)
  0x402fce   [ 0 ]    ret                return
*)
class rtl_system_ctopasstr_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::_CToPasStr__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(Dest:"; xpr_to_pretty floc eaxv;
	STR ",Source:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_deref_lhs Eax 0 floc in
    let rhs = floc#env#mk_side_effect_value floc#cia "Dest" in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Edx; Ecx]] in
    List.concat [lhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "_CToPasStr"

  method! get_description = "Delphi RTL function System::_CToPasStr"

end


(* ============================================================== System::EXP
   example: V01a:0x402ae8
   md5hash: 6854a056ae0804a99ba6a3a9eb7d7b67

  0x402ae8   [ 0 ]    fldl2e                    fldl2e
  0x402aea   [ 0 ]    fmulp %st(1), %st(0)      fmulp %st(1), %st(0)
  0x402aec   [ 0 ]    fld %st(0)                fld %st(0)
  0x402aee   [ 0 ]    frndint                   frndint
  0x402af0   [ 0 ]    fsub %st(1), %st(0)       fsub %st(1), %st(0)
  0x402af2   [ 0 ]    fxch %st(1)               fxch %st(1)
  0x402af4   [ 0 ]    f2xm1                     f2xm1
  0x402af6   [ 0 ]    fld1                      fld1
  0x402af8   [ 0 ]    faddp %st(1), %st(0)      faddp %st(1), %st(0)
  0x402afa   [ 0 ]    fnstcw bp                 bp := FPU control word
  0x402afc   [ 0 ]    fstp %st(1)               st(1) := ST(0) (10 bytes)
  0x402afe   [ 0 ]    ret                       return
*)
class rtl_system_exp_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::EXP__"

  method! get_annotation (_floc:floc_int) =
    LBLOCK [ STR "ST(0) = "; STR self#get_name; STR "()" ]

  method! get_commands (_floc:floc_int) = []

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "EXP"

  method! get_description = "Delphi RTL function System::EXP"

end

let _ = H.add table "System::EXP" (new rtl_system_exp_semantics_t)


(* =========================================================== System::Get8087CW
   example: V01a:0x402ae0
   md5hash: 4419e9eee8a3958c8f13aa2d92620a39

  0x402ae0   [ 0 ]    push 0x0           esp := esp - 4 ; var.0004 := 0
  0x402ae2   [ -4 ]   fnstcw (esp,,1)    var.0004 := FPU control word
  0x402ae5   [ -4 ]   pop eax            eax := var.0004 ; esp := esp + 4 = esp_in
  0x402ae6   [ 0 ]    ret                return
*)
class rtl_system_get8087cw_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::Get8087CW__"

  method! get_annotation (_floc:floc_int) =
    LBLOCK [STR self#get_name; STR "()"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds = floc#get_assign_commands lhs (XVar rhs) in
    List.concat [lhscmds; cmds]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "Get8087CW"

  method! get_description = "Delphi RTL function Get8087CW"

end

let _ = H.add table "System::Get8087CW" (new rtl_system_get8087cw_semantics_t)


(* ============================================================== System::InitImports
   example: V1da:0x404034
   md5hash: 983a85c93a0722b0964f271fe4094cfd

  0x404034   [ 0 ]    push ebx                  save ebx
  0x404035   [ -4 ]   xor ebx, ebx              ebx := 0
  0x404037   [ -4 ]   push edi                  save edi
  0x404038   [ -8 ]   push esi                  save esi
  0x404039  [ -12 ]   mov edi, (eax,ebx,1)      edi := (eax_in)[0] = (eax_in)[0]_in
  0x40403c  [ -12 ]   lea esi, 0x4(eax,ebx,1)   esi := ((eax + ebx) + 4) = (eax_in + 4)
--------------------------------------------------------------------------------
  0x404040  [ -12 ]   mov eax, 0x4(esi)         eax :=  ?  (tmpN)
  0x404043  [ -12 ]   mov edx, (esi)            edx :=  ?  (tmpN)
  0x404045  [ -12 ]   mov eax, (eax,ebx,1)      eax :=  ?  (tmpN)
  0x404048  [ -12 ]   add eax, 0x8(esi)         eax := eax +  ?  (tmpN)
  0x40404b  [ -12 ]   mov (edx,ebx,1), eax      ? := eax
  0x40404e  [ -12 ]   add esi, 0xc              esi := esi + 12
  0x404051  [ -12 ]   dec edi                   edi := edi - 1
  0x404052  [ -12 ]   jnz 0x404040              if (edi != 1) then goto 0x404040
--------------------------------------------------------------------------------
  0x404054  [ -12 ]   pop esi                   restore esi
  0x404055   [ -8 ]   pop edi                   restore edi
  0x404056   [ -4 ]   pop ebx                   restore ebx
  0x404057   [ 0 ]    ret                       return
*)
class rtl_system_initimports_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::InitImports__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name; STR "(Addr:"; xpr_to_dspretty floc eaxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_deref_lhs Eax 0 floc in
    let rhs = floc#env#mk_side_effect_value floc#cia "Addr" in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Edx]] in
    List.concat [lhscmds; cmds1; cmds2 ]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "InitImports"

  method! get_description = "Delphi Rtl function System::InitImports"

end

let _ = H.add table "System::InitImports" (new rtl_system_initimports_semantics_t)


(* ============================================================== System::IntfAddRef
   example: V01a:0x405b84
   md5hash: 9de067dd7ba0341cf026d6a88bd2de5c

  0x405b84   [ 0 ]    test eax, eax             test eax, eax
  0x405b86   [ 0 ]    jz 0x405b8e               if (eax_in = 0) then goto 0x405b8e
--------------------------------------------------------------------------------
  0x405b88   [ 0 ]    push eax                  push eax
  0x405b89   [ -4 ]   mov eax, (eax)            eax := (eax_in)[0] = (eax_in)[0]_in
  0x405b8b   [ -4 ]   call* 0x4(eax)            *( ((eax_in)[0]_in)[4]_in )()
--------------------------------------------------------------------------------
  0x405b8e  [  ?  ]   ret                       return
*)
class rtl_system_intfaddref_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::IntfAddRef__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc eaxv; STR ")"]

  method! get_commands (_floc:floc_int) = []

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "IntfAddRef"

  method! get_description = "Delphi RTL system function System::IntfAddRef"

end

let _ = H.add table "System::IntfAddRef" (new rtl_system_intfaddref_semantics_t)


(* ============================================================= System::IntfCopy
   example: V01a:0x405b28
   md5hash: e97ccd25e34e32a714d3d1ee73d31b4c
*)
class rtl_system_intfcopy_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::IntfCopy__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(dst:"; xpr_to_pretty floc eaxv;
	STR ",src:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]] in
    List.concat [lhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "IntfCopy"

  method! get_description = "Delphi RTL function System::IntfCopy"

end

let _ = H.add table "System::IntfCopy" (new rtl_system_intfcopy_semantics_t)


(* ============================================================== System::IsClass
   example: V1da:0x403674

  0x403674   [ 0 ]    push ebx           save ebx
  0x403675   [ -4 ]   push esi           save esi
  0x403676   [ -8 ]   mov esi, edx       esi := edx = edx_in
  0x403678   [ -8 ]   mov ebx, eax       ebx := eax = eax_in
  0x40367a   [ -8 ]   test ebx, ebx      test ebx, ebx
  0x40367c   [ -8 ]   jz 0x40368b        if (eax_in = 0) then goto 0x40368b
--------------------------------------------------------------------------------
  0x40367e   [ -8 ]   mov edx, esi       edx := esi = edx_in
  0x403680   [ -8 ]   mov eax, (ebx)     eax := (eax_in)[0] = (eax_in)[0]_in
  0x403682   [ -8 ]   call 0x403714      __System::TObject::InheritsFrom__(
                                             this:(eax_in)[0]_in,AClass:edx_in)
  0x403687   [ -8 ]   test al, al        test al, al
  0x403689   [ -8 ]   jnz 0x403690       if (al != 0) then goto 0x403690
--------------------------------------------------------------------------------
  0x40368b   [ -8 ]   xor eax, eax       eax := 0
  0x40368d   [ -8 ]   pop esi            restore esi
  0x40368e   [ -4 ]   pop ebx            restore ebx
  0x40368f   [ 0 ]    ret                return
--------------------------------------------------------------------------------
  0x403690   [ -8 ]   mov al, 0x1        al := 1
  0x403692   [ -8 ]   pop esi            restore esi
  0x403693   [ -4 ]   pop ebx            restore ebx
  0x403694   [ 0 ]    ret                return
*)
class rtl_system_isclasssemantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::IsClass__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(Obj:"; xpr_to_pretty floc eaxv;
	STR ",AClass:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    List.concat [lhscmds; cmds1]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =  mk_target a "IsClass"

  method! get_description = "Delphi Rtl function System::IsClass"

end


(* ========================================================== System::LStrAddRef
   example: V1da:0x40479c
   md5hash: e2e4a17e3d634dee00cf9744452c6233

  0x40479c   [ 0 ]    test eax, eax             test eax, eax
  0x40479e   [ 0 ]    jz 0x4047aa               if (eax_in = 0) then goto 0x4047aa
--------------------------------------------------------------------------------
  0x4047a0   [ 0 ]    mov edx, -0x8(eax)        edx :=  ?  (tmpN)
  0x4047a3   [ 0 ]    inc edx                   edx := edx + 1
  0x4047a4   [ 0 ]    jle 0x4047aa              if ? then goto 0x4047aa
--------------------------------------------------------------------------------
  0x4047a6   [ 0 ]    lock                      lock
  0x4047a7   [ 0 ]    inc -0x8(eax)             ? :=  ?  (tmpN) + 1
--------------------------------------------------------------------------------
  0x4047aa   [ 0 ]    ret                       return
*)
class rtl_system_lstraddref_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::LStrAddRef__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name; STR "(Str:"; xpr_to_pretty floc eaxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxderefval = get_reg_derefvalue Eax (-8) floc in
    let (lhs,lhscmds) = get_reg_deref_lhs Eax (-8) floc in
    let one = int_constant_expr 1 in
    let cmds1 =
      floc#get_assign_commands lhs (XOp (XPlus, [eaxderefval; one])) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Edx]] in
    List.concat [lhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "LStrAddRef"

  method! get_description = "Delphi Rtl function System::LStrAddRef"

end

let _ = H.add table "System::LStrAddRef" (new rtl_system_lstraddref_semantics_t)


(* ============================================================= System::LStrCmp
   example: V01a:0x4045c4
   md5hash: 23bf95961be3ce25595b58665e1a6c77
*)
class rtl_system_lstrcmp_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::LStrCmp__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(s1:"; xpr_to_strpretty floc eaxv;
	STR ",s2:"; xpr_to_strpretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands eaxlhs (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Edx; Ecx]] in
    List.concat [eaxlhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "LStrCmp"

  method! get_description = "Delphi RTL system function System::LStrCmp"

end

let _ = H.add table "System::LStrCmp" (new rtl_system_lstrcmp_semantics_t)


(* ============================================================== System::LStrPos
   example: V01a:0x4047bc
   md5hash: ec79e63dcb8db41e93ceb2a005c196c4
*)
class rtl_system_lstrpos_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::LStrPos__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(s1:"; xpr_to_strpretty floc eaxv;
	STR ",s2:"; xpr_to_strpretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands eaxlhs (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Ecx; Edx]] in
    List.concat [eaxlhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "LStrPos"

  method! get_description = "Delphi RTL system function System::LStrPos"

end

let _ = H.add table "System::LStrPos" (new rtl_system_lstrpos_semantics_t)


(* ============================================================== System::PStrCmp
   example: V01a:0x402c50
   md5hash: 4ca3ef6fccd4199e35265b3f8508458f

  0x402c50   [ 0 ]    push ebx                  save ebx
  0x402c51   [ -4 ]   push esi                  save esi
  0x402c52   [ -8 ]   push edi                  save edi
  0x402c53  [ -12 ]   mov esi, eax              esi := eax = eax_in
  0x402c55  [ -12 ]   mov edi, edx              edi := edx = edx_in
  0x402c57  [ -12 ]   xor eax, eax              eax := 0
  0x402c59  [ -12 ]   xor edx, edx              edx := 0
  0x402c5b  [ -12 ]   mov al, (esi)             al := (eax_in)[0] = (eax_in)[0]_in
  0x402c5d  [ -12 ]   mov dl, (edi)             dl := (edx_in)[0] = (edx_in)[0]_in
  0x402c5f  [ -12 ]   inc esi                   esi := esi + 1 = (eax_in + 1)
  0x402c60  [ -12 ]   inc edi                   edi := edi + 1 = (edx_in + 1)
  0x402c61  [ -12 ]   sub eax, edx              eax := eax - edx
  0x402c63  [ -12 ]   ja 0x402c67               if ? then goto 0x402c67
--------------------------------------------------------------------------------
  0x402c65  [ -12 ]   add edx, eax              edx := edx + eax
--------------------------------------------------------------------------------
  0x402c67  [ -12 ]   push edx                  esp := esp - 4; var.0016 := edx
  0x402c68  [ -16 ]   shr edx, 0x2              edx := edx / 4
  0x402c6b  [ -16 ]   jz 0x402c93               if ? then goto 0x402c93
--------------------------------------------------------------------------------
  0x402c6d  [ -16 ]   mov ecx, (esi)            ecx :=  ?  (tmpN)
  0x402c6f  [ -16 ]   mov ebx, (edi)            ebx :=  ?  (tmpN)
  0x402c71  [ -16 ]   cmp ecx, ebx              cmp ecx, ebx
  0x402c73  [ -16 ]   jnz 0x402cb9              if (ecx != ebx) then goto 0x402cb9
--------------------------------------------------------------------------------
  0x402c75  [ -16 ]   dec edx                   edx := edx - 1
  0x402c76  [ -16 ]   jz 0x402c8d               if (edx = 1) then goto 0x402c8d
--------------------------------------------------------------------------------
  0x402c78  [ -16 ]   mov ecx, 0x4(esi)         ecx :=  ?  (tmpN)
  0x402c7b  [ -16 ]   mov ebx, 0x4(edi)         ebx :=  ?  (tmpN)
  0x402c7e  [ -16 ]   cmp ecx, ebx              cmp ecx, ebx
  0x402c80  [ -16 ]   jnz 0x402cb9              if (ecx != ebx) then goto 0x402cb9
--------------------------------------------------------------------------------
  0x402c82  [ -16 ]   add esi, 0x8              esi := esi + 8
  0x402c85  [ -16 ]   add edi, 0x8              edi := edi + 8
  0x402c88  [ -16 ]   dec edx                   edx := edx - 1
  0x402c89  [ -16 ]   jnz 0x402c6d              if (edx != 1) then goto 0x402c6d
--------------------------------------------------------------------------------
  0x402c8b  [ -16 ]   jmp 0x402c93              goto 0x402c93
--------------------------------------------------------------------------------
  0x402c8d  [ -16 ]   add esi, 0x4              esi := esi + 4
  0x402c90  [ -16 ]   add edi, 0x4              edi := edi + 4
--------------------------------------------------------------------------------
  0x402c93  [ -16 ]   pop edx                   edx := var.0016; esp := (esp_in - 12)
  0x402c94  [ -12 ]   and edx, 0x3              edx := edx & 3
  0x402c97  [ -12 ]   jz 0x402cb5               if ? then goto 0x402cb5
--------------------------------------------------------------------------------
  0x402c99  [ -12 ]   mov cl, (esi)             cl :=  ?  (tmpN)
  0x402c9b  [ -12 ]   cmp cl, (edi)             cmp cl, (edi)
  0x402c9d  [ -12 ]   jnz 0x402cce              if (cl != Unknown) then goto 0x402cce
--------------------------------------------------------------------------------
  0x402c9f  [ -12 ]   dec edx                   edx := edx - 1
  0x402ca0  [ -12 ]   jz 0x402cb5               if (edx = 1) then goto 0x402cb5
--------------------------------------------------------------------------------
  0x402ca2  [ -12 ]   mov cl, 0x1(esi)          cl :=  ?  (tmpN)
  0x402ca5  [ -12 ]   cmp cl, 0x1(edi)          cmp cl, 0x1(edi)
  0x402ca8  [ -12 ]   jnz 0x402cce              if (cl != Unknown) then goto 0x402cce
--------------------------------------------------------------------------------
  0x402caa  [ -12 ]   dec edx                   edx := edx - 1
  0x402cab  [ -12 ]   jz 0x402cb5               if (edx = 1) then goto 0x402cb5
--------------------------------------------------------------------------------
  0x402cad  [ -12 ]   mov cl, 0x2(esi)          cl :=  ?  (tmpN)
  0x402cb0  [ -12 ]   cmp cl, 0x2(edi)          cmp cl, 0x2(edi)
  0x402cb3  [ -12 ]   jnz 0x402cce              if (cl != Unknown) then goto 0x402cce
--------------------------------------------------------------------------------
  0x402cb5  [ -12 ]   add eax, eax              eax := eax + eax
  0x402cb7  [ -12 ]   jmp 0x402cce              goto 0x402cce
--------------------------------------------------------------------------------
  0x402cb9  [ -16 ]   pop edx                   edx := var.0016; esp := (esp_in - 12)
  0x402cba  [ -12 ]   cmp cl, bl                cmp cl, bl
  0x402cbc  [ -12 ]   jnz 0x402cce              if (cl != bl) then goto 0x402cce
--------------------------------------------------------------------------------
  0x402cbe  [ -12 ]   cmp ch, bh                cmp ch, bh
  0x402cc0  [ -12 ]   jnz 0x402cce              if (ch != bh) then goto 0x402cce
--------------------------------------------------------------------------------
  0x402cc2  [ -12 ]   shr ecx, 0x10             ecx := ecx / 65536
  0x402cc5  [ -12 ]   shr ebx, 0x10             ebx := ebx / 65536
  0x402cc8  [ -12 ]   cmp cl, bl                cmp cl, bl
  0x402cca  [ -12 ]   jnz 0x402cce              if (cl != bl) then goto 0x402cce
--------------------------------------------------------------------------------
  0x402ccc  [ -12 ]   cmp ch, bh                cmp ch, bh
--------------------------------------------------------------------------------
  0x402cce  [ -12 ]   pop edi                   restore edi
  0x402ccf   [ -8 ]   pop esi                   restore esi
  0x402cd0   [ -4 ]   pop ebx                   restore ebx
  0x402cd1   [ 0 ]    ret                       return
*)
class rtl_system_pstrcmp_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::PStrCmp__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(reg_eax:"; xpr_to_pretty floc eaxv;
	STR ",reg_edx:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "PStrCmp"

  method! get_description = "Delphi RTL function System::PStrCmp"

end

let _ = H.add table "System::PStrCmp" (new rtl_system_pstrcmp_semantics_t)


(* ============================================================== System::PStrNCpy
   example V1da:0x402dc0

  0x402dc0   [ 0 ]    push ebx           save ebx
  0x402dc1   [ -4 ]   mov bl, (edx)      bl := (edx_in)[0] = (edx_in)[0]_in
  0x402dc3   [ -4 ]   cmp cl, bl         cmp cl, bl
  0x402dc5   [ -4 ]   jbe 0x402dc9       if (cl <= (edx_in)[0]_in) then goto 0x402dc9
--------------------------------------------------------------------------------
  0x402dc7   [ -4 ]   mov ecx, ebx       ecx := ebx
--------------------------------------------------------------------------------
  0x402dc9   [ -4 ]   mov (eax), cl      (eax_in)[0] := cl
  0x402dcb   [ -4 ]   inc edx            edx := edx + 1 = (edx_in + 1)
  0x402dcc   [ -4 ]   inc eax            eax := eax + 1 = (eax_in + 1)
  0x402dcd   [ -4 ]   and ecx, 0xff      ecx := ecx & 255
  0x402dd3   [ -4 ]   xchg eax, edx      tmp := edx; edx := eax; eax := tmp
  0x402dd4   [ -4 ]   call 0x402c58      __System::Move__(Source:(edx_in + 1),
                                                 Dest:(eax_in + 1),Count:ecx)
  0x402dd9   [ -4 ]   pop ebx            restore ebx
  0x402dda   [ 0 ]    ret                return
*)
class rtl_system_pstrncpy_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::PStrNCpy__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    LBLOCK [
        STR self#get_name; STR "(Dest:"; xpr_to_pretty floc eaxv;
	STR ",Source:"; xpr_to_strpretty floc edxv;
	STR ",Count:"; xpr_to_pretty floc ecxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_deref_lhs Eax 0 floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let (edxlhs,edxlhscmds) = get_reg_lhs Edx floc in
    let one = int_constant_expr 1 in
    let rhs = floc#env#mk_side_effect_value floc#cia "Dest" in
    let size = get_reg_value Ecx floc in
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Ecx]] in
    let cmds3 = floc#get_assign_commands eaxlhs (XOp (XPlus, [eaxv; one])) in
    let cmds4 = floc#get_assign_commands edxlhs (XOp (XPlus, [edxv; one])) in
    List.concat [lhscmds; eaxlhscmds; edxlhscmds; cmds1; cmds2; cmds3; cmds4]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "PStrNCpy"

  method! get_description = "Delphi RTL function System::PStrNCpy"

end


(* ============================================================== System::ROUND
   example: V01a:0x402b00
   md5hash: d69492e88a5718b71d5b34099ad3d8f5

  0x402b00   [ 0 ]    sub esp, 0x8     esp := esp - 8 = (esp_in - 8)
  0x402b03   [ -8 ]   fistp (esp,,1)   var.0008 := ST(0) (8 bytes)
  0x402b06   [ -8 ]   wait             wait
  0x402b07   [ -8 ]   pop eax          eax := var.0008; esp := esp + 4 = (esp_in - 4)
  0x402b08   [ -4 ]   pop edx          edx := var.0004; esp := esp + 4 = esp_in
  0x402b09   [ 0 ]    ret              return
*)
class rtl_system_round_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::ROUND__"

  method! get_annotation (_floc:floc_int) =
    LBLOCK [STR "(eax,edx) := "; STR self#get_name; STR "()"]

  method! get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let (edxlhs,edxlhscmds) = get_reg_lhs Edx floc in
    let rhs1 = get_return_value (self#get_name ^ "_low") floc in
    let rhs2 = get_return_value (self#get_name ^ "_high") floc in
    let cmds1 = floc#get_assign_commands eaxlhs (XVar rhs1) in
    let cmds2 = floc#get_assign_commands edxlhs (XVar rhs2) in
    List.concat [eaxlhscmds; edxlhscmds; cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "ROUND"

  method! get_description = "Delphi RTL function System::ROUND"

end

let _ = H.add table "System::ROUND" (new rtl_system_round_semantics_t)


(* =========================================================== System::Set8087CW
   example: V01a:0x402ad0

   __fastcall System::Set8087CW(unsigned short)

  0x402ad0   [ 0 ]    mov 0x4a6020, eax         gv_0x4a6020 := eax = eax_in
  0x402ad6   [ 0 ]    fnclex                    fnclex
  0x402ad8   [ 0 ]    fldcw 0x4a6020            FPU control word := gv_0x4a6020
  0x402ade   [ 0 ]    ret                       return
*)
class rtl_system_set8087cw_semantics_t
  (md5hash:string) (gv:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::Set8087CW__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc eaxv;
	STR ",gv:"; gv#toPretty; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let vgv = TR.tget_ok (floc#env#mk_global_variable gv#to_numerical) in
    floc#get_assign_commands vgv eaxv

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "Set8087CW"

  method! get_description = "Delphi RTL function Set8087CW"

end


(* ============================================================= System::SetElem
   example: V01a:0x402e68
   md5hash: d504a9f352a457dc0d87511db895f1a6

  0x402e68   [ 0 ]    push ebx              save ebx
  0x402e69   [ -4 ]   push edi              save edi
  0x402e6a   [ -8 ]   mov edi, eax          edi := eax = eax_in
  0x402e6c   [ -8 ]   xor ebx, ebx          ebx := 0
  0x402e6e   [ -8 ]   mov bl, cl            bl := cl
  0x402e70   [ -8 ]   mov ecx, ebx          ecx := ebx
  0x402e72   [ -8 ]   xor eax, eax          eax := 0
  0x402e74   [ -8 ]   rep stos              (Edi): (eax_in)[0]; Ecx: ecx (width: 1)
  0x402e76   [ -8 ]   sub edi, ebx          edi := edi - ebx
  0x402e78   [ -8 ]   inc eax               eax := eax + 1 = 1
  0x402e79   [ -8 ]   mov cl, dl            cl := dl
  0x402e7b   [ -8 ]   rol al, cl            rol al, cl
  0x402e7d   [ -8 ]   shr ecx, 0x3          ecx := ecx / 8
  0x402e80   [ -8 ]   cmp ecx, ebx          cmp ecx, ebx
  0x402e82   [ -8 ]   jnc 0x402e87          if (ecx >= ebx) then goto 0x402e87
----------------------------------------------------------------------------
  0x402e84   [ -8 ]   or (ecx,edi,1), al    ? :=  ?  (tmpN) | al
----------------------------------------------------------------------------
  0x402e87   [ -8 ]   pop edi               restore edi
  0x402e88   [ -4 ]   pop ebx               restore ebx
  0x402e89   [ 0 ]    ret                   return
*)
class rtl_system_setelem_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::SetElem__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(A:"; xpr_to_pretty floc eaxv;
	STR ",reg_ecx:"; xpr_to_pretty floc ecxv;
	STR ",reg_edx:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let size = get_reg_value Ecx floc in
    let lhs = floc#get_lhs_from_address eaxv in
    let rhs = floc#env#mk_side_effect_value floc#cia "A" in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]] in
    List.concat [ cmds1; cmds2 ]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "SetElem"

  method! get_description = "Delphi RTL function System::SetElem"

end

let _ = H.add table "System::SetElem" (new rtl_system_setelem_semantics_t)


(* ============================================================== System::SetEq
   example: V01a: 0x402ee4
   md5hash: b1ed2ec21524c71591df3025a7749ad9

  0x402ee4   [ 0 ]    push esi        save esi
  0x402ee5   [ -4 ]   push edi        save edi
  0x402ee6   [ -8 ]   mov esi, eax    esi := eax = eax_in
  0x402ee8   [ -8 ]   mov edi, edx    edi := edx = edx_in
  0x402eea   [ -8 ]   and ecx, 0xff   ecx := ecx & 255
  0x402ef0   [ -8 ]   repe cmps       (Edi):(edx_in)[0]_in;
                                         (Edi): (eax_in)[0]_in; Ecx: ecx (width: 1)
  0x402ef2   [ -8 ]   pop edi         restore edi
  0x402ef3   [ -4 ]   pop esi         restore esi
  0x402ef4   [ 0 ]    ret             return
*)
class rtl_system_seteq_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::SetEq__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    LBLOCK [
        STR self#get_name; STR "A1:"; xpr_to_pretty floc eaxv;
	STR ",A2:"; xpr_to_pretty floc edxv;
	STR ",Count:"; xpr_to_pretty floc ecxv]

  method! get_commands (_floc:floc_int) = []

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "SetEq"

  method! get_description = "Delphi RTL function System::SetEq"

end

let _ = H.add table "System::SetEq" (new rtl_system_seteq_semantics_t)


(* ============================================================== System::SetRange
   example: V01a:0x402e8c
   md5hash: 3bd32b5d959220e1bef2573d50bd3834

  0x402e8c   [ 0 ]    push ebx                  save ebx
  0x402e8d   [ -4 ]   push esi                  save esi
  0x402e8e   [ -8 ]   push edi                  save edi
  0x402e8f  [ -12 ]   xor ebx, ebx              ebx := 0
  0x402e91  [ -12 ]   mov bl, ah                bl := ah
  0x402e93  [ -12 ]   movzx esi, al             esi := al
  0x402e96  [ -12 ]   movzx edx, dl             edx := dl
  0x402e99  [ -12 ]   mov edi, ecx              edi := ecx = ecx_in
  0x402e9b  [ -12 ]   mov ecx, ebx              ecx := ebx
  0x402e9d  [ -12 ]   xor eax, eax              eax := 0
  0x402e9f  [ -12 ]   rep stos                  (Edi): (ecx_in)[0]; Ecx: ecx (width: 1)
  0x402ea1  [ -12 ]   sub edi, ebx              edi := edi - ebx
  0x402ea3  [ -12 ]   shl ebx, 0x3              ebx := ebx * 8
  0x402ea6  [ -12 ]   cmp edx, ebx              cmp edx, ebx
  0x402ea8  [ -12 ]   jc 0x402ead               if (edx < ebx) then goto 0x402ead
--------------------------------------------------------------------------------
  0x402eaa  [ -12 ]   lea edx, -0x1(ebx)        edx := (ebx - 1)
--------------------------------------------------------------------------------
  0x402ead  [ -12 ]   cmp esi, edx              cmp esi, edx
  0x402eaf  [ -12 ]   ja 0x402ede               if (esi > edx) then goto 0x402ede
--------------------------------------------------------------------------------
  0x402eb1  [ -12 ]   dec eax                   eax := eax - 1 = -1
  0x402eb2  [ -12 ]   mov ecx, esi              ecx := esi
  0x402eb4  [ -12 ]   and cl, 0x7               cl := cl & 7
  0x402eb7  [ -12 ]   shl al, cl                al := al << cl
  0x402eb9  [ -12 ]   shr esi, 0x3              esi := esi / 8
  0x402ebc  [ -12 ]   mov cl, dl                cl := dl
  0x402ebe  [ -12 ]   not cl                    not cl
  0x402ec0  [ -12 ]   and cl, 0x7               cl := cl & 7
  0x402ec3  [ -12 ]   shr ah, cl                ah := ah >> cl
  0x402ec5  [ -12 ]   shr edx, 0x3              edx := edx / 8
  0x402ec8  [ -12 ]   add edi, esi              edi := edi + esi
  0x402eca  [ -12 ]   mov ecx, edx              ecx := edx
  0x402ecc  [ -12 ]   sub ecx, esi              ecx := ecx - esi
  0x402ece  [ -12 ]   jnz 0x402ed6              if (esi != ecx_val@_0x402ecc_@_0x402ece) then goto 0x402ed6
--------------------------------------------------------------------------------
  0x402ed0  [ -12 ]   and al, ah                al := al & ah
  0x402ed2  [ -12 ]   mov (edi), al             ? := al
  0x402ed4  [ -12 ]   jmp 0x402ede              goto 0x402ede
--------------------------------------------------------------------------------
  0x402ed6  [ -12 ]   stosb                     ? := al
  0x402ed7  [ -12 ]   dec ecx                   ecx := ecx - 1
  0x402ed8  [ -12 ]   mov al, -0x1              al := -1
  0x402eda  [ -12 ]   rep stos                  (Edi): ?; Ecx: ecx (width: 1)
  0x402edc  [ -12 ]   mov (edi), ah             ? := ah
--------------------------------------------------------------------------------
  0x402ede  [ -12 ]   pop edi                   restore edi
  0x402edf   [ -8 ]   pop esi                   restore esi
  0x402ee0   [ -4 ]   pop ebx                   restore ebx
  0x402ee1   [ 0 ]    ret                       return
*)
class rtl_system_setrange_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::SetRange__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in   (* TODO: separate out Ah,Al *)
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(A:"; xpr_to_pretty floc ecxv;
	STR ",reg_eax:"; xpr_to_pretty floc eaxv;
	STR ",reg_edx:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let ecxv = get_reg_value Ecx floc in
    let lhs = floc#get_lhs_from_address ecxv in
    let rhs = floc#env#mk_side_effect_value floc#cia "A" in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]] in
    List.concat [cmds1; cmds2 ]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "SetRange"

  method! get_description = "Delphi RTL function System::SetRange"

end

let _ = H.add table "System::SetRange" (new rtl_system_setrange_semantics_t)


(* ============================================================== System::SetSub
   example: V01a:0x402f04
   md5hash: 000b732597e71a2121a1d0d4fb3f4c7b

  0x402f04   [ 0 ]    mov ch, (edx)             ch :=  ?  (tmpN)
  0x402f06   [ 0 ]    not ch                    not ch
  0x402f08   [ 0 ]    inc edx                   edx := edx + 1
  0x402f09   [ 0 ]    and (eax), ch             ? :=  ?  (tmpN) & ch
  0x402f0b   [ 0 ]    inc eax                   eax := eax + 1
  0x402f0c   [ 0 ]    dec cl                    cl := cl - 1
  0x402f0e   [ 0 ]    jnz fp:0x402f04           if (cl != 1) then goto 0x402f04
--------------------------------------------------------------------------------
  0x402f10   [ 0 ]    ret                       return
*)
class rtl_system_setsub_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::SetSub__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(dst:"; xpr_to_pretty floc eaxv;
	STR ",src:"; xpr_to_pretty floc edxv;
	STR ",count:"; xpr_to_pretty floc ecxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let size = get_reg_value Ecx floc in
    let lhs = floc#get_lhs_from_address eaxv in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "SetSub"

  method! get_description = "Delphi RTL function System::SetSub"

end

let _ = H.add table "System::SetSub" (new rtl_system_setsub_semantics_t)


(* ============================================================ System::SetUnion
   example: V01a:0x402ef8
   md5hash: d4e3bccc7b882275fbe7b0aa0b368941

  0x402ef8   [ 0 ]    mov ch, (edx)             ch :=  ?  (tmpN)
  0x402efa   [ 0 ]    inc edx                   edx := edx + 1
  0x402efb   [ 0 ]    or (eax), ch              ? :=  ?  (tmpN) | ch
  0x402efd   [ 0 ]    inc eax                   eax := eax + 1
  0x402efe   [ 0 ]    dec cl                    cl := cl - 1
  0x402f00   [ 0 ]    jnz fp:0x402ef8           if (cl != 1) then goto 0x402ef8
--------------------------------------------------------------------------------
  0x402f02   [ 0 ]    ret                       return
*)
class rtl_system_setunion_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::SetUnion__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(dst:"; xpr_to_pretty floc eaxv;
	STR ",src:"; xpr_to_pretty floc edxv;
	STR ",count:"; xpr_to_pretty floc ecxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let size = get_reg_value Ecx floc in
    let lhs = floc#get_lhs_from_address eaxv in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "SetUnion"

  method! get_description = "Delphi RTL function System::SetUnion"

end

let _ = H.add table "System::SetUnion" (new rtl_system_setunion_semantics_t)


(* ============================================================== System::LStrLen
   example: V8af:0x403f28
   md5hash: 3f3d245fd827b42ff75949bd77c119a9

  0x28  test eax, eax             test eax, eax
  0x2a  jz 0x403f2f               if (eax_in = 0) then goto 0x403f2f
--------------------------------------------------------------------------------
  0x2c  mov eax, -0x4(eax)        eax :=  eax_in[-4]
--------------------------------------------------------------------------------
  0x2f  ret                       return

*)
class rtl_system_strlen_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::LStrLen__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    match eaxv with
    | XConst (IntConst n) when n#is_zero -> LBLOCK [STR "__fnop__"]
    | _ ->
      let eaxv = get_reg_value Eax floc in
      LBLOCK [
          STR self#get_name; STR "(str:"; xpr_to_strpretty floc eaxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    match eaxv with
    | XConst (IntConst n) when n#is_zero -> []
    | _ ->
      let zero = floc#env#request_num_constant numerical_zero in
      let eax = floc#env#mk_cpu_register_variable Eax in
      let eaxzero = ASSERT (EQ (eax,zero)) in
      let eaxnzero = ASSERT (NEQ (eax, zero)) in
      let eaxderefv = get_reg_derefvalue Eax (-4) floc in
      let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
      let cmds1 = floc#get_assign_commands eaxlhs eaxderefv in
      [BRANCH [
           LF.mkCode [eaxzero]; LF.mkCode (eaxnzero :: (eaxlhscmds @ cmds1))]]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "Delphi RTL function System::LStrLen"

end

let _ = H.add table "System::StrLen" (new rtl_system_strlen_semantics_t)


(* ========================================================= System::LStrToPChar
   example: V01a:0x404678

  0x404678   [ 0 ]    test eax, eax             test eax, eax
  0x40467a   [ 0 ]    jz 0x40467e               if (eax_in = 0) then goto 0x40467e
--------------------------------------------------------------------------------
  0x40467c   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x40467e   [ 0 ]    mov eax,db:0x40467d[0x0]  eax := 4212349
  0x404683   [ 0 ]    ret                       return

  --------------------------------------------------------- System::WStrToPWChar
   example: V1da:0x404b28

  0x404b28   [ 0 ]    test eax, eax          test eax, eax
  0x404b2a   [ 0 ]    jz 0x404b30            if (eax_in = 0) then goto 0x404b30
-------------------------------------------------------------------------------
  0x404b2c   [ 0 ]    ret                    return
--------------------------------------------------------------------------------
  0x404b30   [ 0 ]    mov eax,ca:0x404b2e    eax := 4213550
  0x404b35   [ 0 ]    ret                    return
*)
class rtl_system_strtopchar_semantics_t
  (md5hash:string) (name:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::" ^ name ^ "__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [ STR self#get_name; STR "("; xpr_to_strpretty floc eaxv; STR ")" ]

  method! get_commands (_floc:floc_int) = []

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "Delphi function checks that string argument is not null"

end

(* ===================================================== System::initExnHandling
   example: V1da:0x403f38
*)
class rtl_system_initexnhandling_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::initExnHandling__"  (* made up *)

  method! get_annotation (_floc:floc_int) =
    LBLOCK [STR self#get_name; STR "()"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "initExnHandling"

  method! get_description =
    "Delphi RTL function to initialize exception handling"

end



(* ========================================================= System::initTIBInfo
   example: V1da:0x403e80

  0x403e80   [ 0 ]    xor edx, edx              edx := 0
  0x403e82   [ 0 ]    lea eax, -0xc(ebp)        eax := (ebp - 12) = (ebp_in - 12)
  0x403e85   [ 0 ]    mov ecx, %fs:(edx)        ecx :=  ?  (tmpN)
  0x403e88   [ 0 ]    mov %fs:(edx), eax        ? := eax = (ebp_in - 12)
  0x403e8b   [ 0 ]    mov (eax), ecx            ? := ecx
  0x403e8d   [ 0 ]    mov 0x4(eax),fp:0x403de0  ? := 4210144
  0x403e94   [ 0 ]    mov 0x8(eax), ebp         ? := ebp = ebp_in
  0x403e97   [ 0 ]    mov 0x47c638, eax         gv_0x47c638 := eax = (ebp_in - 12)
  0x403e9c   [ 0 ]    ret                       return
*)
class rtl_system_inittibinfo_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::initTIBInfo__"   (* made up *)

  method! get_annotation (floc:floc_int) =
    let ebpv = get_reg_value Ebp floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc ebpv; STR ")"]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_deref_lhs Ebp (-12) floc in
    let rhs = floc#env#mk_special_variable "fs:0x0" in
    let cmds1 = floc#get_assign_commands lhs (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Eax; Ecx; Edx ] ] in
    List.concat [ lhscmds; cmds1; cmds2 ]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "initTIBInfo"

  method! get_description = "Delphi RTL function System::initTIBInfo"

end


(* ============================================================== delphi_unknown1
   example V4a6371:0x300022d4

  0x300022d4   [ 0 ]    mov eax, 0x300295b0  eax := gv_0x300295b0 = gv_0x300295b0_in
  0x300022d9   [ 0 ]    test eax, eax        test eax, eax
  0x300022db   [ 0 ]    jz 0x300022ec        if (gv_0x300295b0_in = 0) then
                                                   goto 0x300022ec
--------------------------------------------------------------------------------
  0x300022dd   [ 0 ]    mov edx, (eax)       edx := (gv_0x300295b0_in)[0]_in
  0x300022df   [ 0 ]    xor ecx, ecx         ecx := 0
  0x300022e1   [ 0 ]    mov eax, 0x4(eax)    eax := (gv_0x300295b0_in)[4]_in
  0x300022e4   [ 0 ]    xchg edx, ecx        tmp := ecx; ecx := edx; edx := tmp
  0x300022e6   [ 0 ]    call* 0x3002503c     *( gv_0x3002503c_in )()
--------------------------------------------------------------------------------
  0x300022ec  [  ?  ]   ret                  return
*)
class rtl_system_delphiunknown1_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::delphi_unknown1__"   (* made up *)

  method! get_annotation (_floc:floc_int) =
    LBLOCK [STR self#get_name; STR "()"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "delphi_unknown1"

  method! get_description =
    "Delphi RTL function to initialize exception handling?"

end



(* ============================================================== System::StartExe
   example: V1da:0x403fa8

  0x403fa8   [ 0 ]    mov 0x47c014,fp:0x4011fc  gv_0x47c014 := 4198908
  0x403fb2   [ 0 ]    mov 0x47c018,fp:0x401204  gv_0x47c018 := 4198916
  0x403fbc   [ 0 ]    mov 0x47c63c, eax         gv_0x47c63c := eax = eax_in
  0x403fc1   [ 0 ]    xor eax, eax              eax := 0
  0x403fc3   [ 0 ]    mov 0x47c640, eax         gv_0x47c640 := eax = 0
  0x403fc8   [ 0 ]    mov 0x47c644, edx         gv_0x47c644 := edx = edx_in
  0x403fce   [ 0 ]    mov eax, 0x4(edx)         eax := (edx_in)[4] = (edx_in)[4]_in
  0x403fd1   [ 0 ]    mov 0x47c02c, eax         gv_0x47c02c := eax = (edx_in)[4]_in
  0x403fd6   [ 0 ]    call 0x403e80             __System::initTIBInfo__(ebp_in)
  0x403fdb   [ 0 ]    mov 0x47c034, 0x0         gv_0x47c034 := 0
  0x403fe2   [ 0 ]    call 0x403f38             __System::initExnHandling__()
  0x403fe7   [ 0 ]    ret                       return

   ------------------------------------------------------------------------------
   example: V4a6371:0x300022f0

  0x300022f0   [ 0 ]    mov 0x30029010,fp:0x300010fc  gv_0x30029010 := 805310716
  0x300022fa   [ 0 ]    mov 0x30029014,ca:0x3000110c  gv_0x30029014 := 805310732
  0x30002304   [ 0 ]    mov 0x300295b0, eax           gv_0x300295b0 := eax = eax_in
  0x30002309   [ 0 ]    xor eax, eax                  eax := 0
  0x3000230b   [ 0 ]    mov 0x300295b4, eax           gv_0x300295b4 := eax = 0
  0x30002310   [ 0 ]    mov 0x300295b8, edx           gv_0x300295b8 := edx = edx_in
  0x30002316   [ 0 ]    mov eax, 0x4(edx)             eax := (edx_in)[4] = (edx_in)[4]_in
  0x30002319   [ 0 ]    mov 0x30029020, eax           gv_0x30029020 := eax = (edx_in)[4]_in
  0x3000231e   [ 0 ]    mov 0x30029028, 0x0           gv_0x30029028 := 0
  0x30002325   [ 0 ]    call 0x300022d4               0x300022d4()
  0x3000232a   [ 0 ]    ret                           return

*)
class rtl_system_startexe_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::StartExe__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(pPackageInfoTable:"; xpr_to_pretty floc eaxv;
	STR ",pTLibModule:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (_floc:floc_int) = []

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "StartExe"

  method! get_description = "Delphi RTL system function System::StartExe"

end


(* ============================================================== System::TRUNC
   example: V01a:0x402b0c
   md5hash: 4e4ee118240f2366fc39b5ca67f65c5f

  0x402b0c   [ 0 ]    sub esp, 0xc           esp := esp - 12 = (esp_in - 12)
  0x402b0f  [ -12 ]   fnstcw (esp,,1)        var.0012 := FPU control word
  0x402b12  [ -12 ]   fnstcw 0x2(esp,,1)     var.0010 := FPU control word
  0x402b16  [ -12 ]   wait                   wait
  0x402b17  [ -12 ]   or 0x2(esp,,1), 0xf00  var.0010 := var.0010 | 3840
  0x402b1e  [ -12 ]   fldcw 0x2(esp,,1)      FPU control word := var.0010
  0x402b22  [ -12 ]   fistp 0x4(esp,,1)      var.0008 := ST(0) (8 bytes)
  0x402b26  [ -12 ]   wait                   wait
  0x402b27  [ -12 ]   fldcw (esp,,1)         FPU control word := var.0012
  0x402b2a  [ -12 ]   pop ecx                ecx := var.0012; esp := (esp_in - 8)
  0x402b2b   [ -8 ]   pop eax                eax := var.0008; esp := (esp_in - 4)
  0x402b2c   [ -4 ]   pop edx                edx := var.0004; esp := esp_in
  0x402b2d   [ 0 ]    ret                    return
*)
class rtl_system_trunc_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::TRUNC__"

  method! get_annotation (_floc:floc_int) =
    LBLOCK [STR "(ecx,eax,edx) := "; STR self#get_name; STR "()"]

  method! get_commands (floc:floc_int) =
    let (ecxlhs,ecxlhscmds) = get_reg_lhs Ecx floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let (edxlhs,edxlhscmds) = get_reg_lhs Edx floc in
    let rhs1 = get_return_value (self#get_name ^ "_low") floc in
    let rhs2 = get_return_value (self#get_name ^ "_med") floc in
    let rhs3 = get_return_value (self#get_name ^ "_high") floc in
    let cmds1 = floc#get_assign_commands ecxlhs (XVar rhs1) in
    let cmds2 = floc#get_assign_commands eaxlhs (XVar rhs2) in
    let cmds3 = floc#get_assign_commands edxlhs (XVar rhs3) in
    List.concat [ecxlhscmds; eaxlhscmds; edxlhscmds; cmds1; cmds2; cmds3]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "TRUNC"

  method! get_description = "Delphi RTL function System::TRUNC"

end

let _ = H.add table "System::TRUNC" (new rtl_system_trunc_semantics_t)



(* ============================================================= System::ValLong
   example: V01a:0x402d64
   md5hash: 53624ad4bcd014d5276ab05b392555a0

  0x402d64   [ 0 ]    push ebx                  save ebx
  0x402d65   [ -4 ]   push esi                  save esi
  0x402d66   [ -8 ]   push edi                  save edi
  0x402d67  [ -12 ]   mov esi, eax              esi := eax = eax_in
  0x402d69  [ -12 ]   push eax                  save eax
  0x402d6a  [ -16 ]   test eax, eax             test eax, eax
  0x402d6c  [ -16 ]   jz 0x402dda               if (eax_in = 0) then goto 0x402dda
--------------------------------------------------------------------------------
  0x402d6e  [ -16 ]   xor eax, eax              eax := 0
  0x402d70  [ -16 ]   xor ebx, ebx              ebx := 0
  0x402d72  [ -16 ]   mov edi, 0xccccccc        edi := 214748364
--------------------------------------------------------------------------------
  0x402d77  [ -16 ]   mov bl, (esi)             bl :=  ?  (tmpN)
  0x402d79  [ -16 ]   inc esi                   esi := esi + 1
  0x402d7a  [ -16 ]   cmp bl, 0x20              cmp bl, 0x20
  0x402d7d  [ -16 ]   jz 0x402d77               if (bl = 32) then goto 0x402d77
--------------------------------------------------------------------------------
  0x402d7f  [ -16 ]   mov ch, 0x0               ch := 0
  0x402d81  [ -16 ]   cmp bl, 0x2d              cmp bl, 0x2d
  0x402d84  [ -16 ]   jz 0x402de8               if (bl = 45) then goto 0x402de8
--------------------------------------------------------------------------------
  0x402d86  [ -16 ]   cmp bl, 0x2b              cmp bl, 0x2b
  0x402d89  [ -16 ]   jz 0x402dea               if (bl = 43) then goto 0x402dea
--------------------------------------------------------------------------------
  0x402d8b  [ -16 ]   cmp bl, 0x24              cmp bl, 0x24
  0x402d8e  [ -16 ]   jz 0x402def               if (bl = 36) then goto 0x402def
--------------------------------------------------------------------------------
  0x402d90  [ -16 ]   cmp bl, 0x78              cmp bl, 0x78
  0x402d93  [ -16 ]   jz 0x402def               if (bl = 120) then goto 0x402def
--------------------------------------------------------------------------------
  0x402d95  [ -16 ]   cmp bl, 0x58              cmp bl, 0x58
  0x402d98  [ -16 ]   jz 0x402def               if (bl = 88) then goto 0x402def
--------------------------------------------------------------------------------
  0x402d9a  [ -16 ]   cmp bl, 0x30              cmp bl, 0x30
  0x402d9d  [ -16 ]   jnz 0x402db2              if (bl != 48) then goto 0x402db2
--------------------------------------------------------------------------------
  0x402d9f  [ -16 ]   mov bl, (esi)             bl :=  ?  (tmpN)
  0x402da1  [ -16 ]   inc esi                   esi := esi + 1
  0x402da2  [ -16 ]   cmp bl, 0x78              cmp bl, 0x78
  0x402da5  [ -16 ]   jz 0x402def               if (bl = 120) then goto 0x402def
--------------------------------------------------------------------------------
  0x402da7  [ -16 ]   cmp bl, 0x58              cmp bl, 0x58
  0x402daa  [ -16 ]   jz 0x402def               if (bl = 88) then goto 0x402def
--------------------------------------------------------------------------------
  0x402dac  [ -16 ]   test bl, bl               test bl, bl
  0x402dae  [ -16 ]   jz 0x402dd0               if (bl = 0) then goto 0x402dd0
--------------------------------------------------------------------------------
  0x402db0  [ -16 ]   jmp 0x402db6              goto 0x402db6
--------------------------------------------------------------------------------
  0x402db2  [ -16 ]   test bl, bl               test bl, bl
  0x402db4  [ -16 ]   jz 0x402de3               if (bl = 0) then goto 0x402de3
--------------------------------------------------------------------------------
  0x402db6  [ -16 ]   sub bl, 0x30              bl := bl - 48
  0x402db9  [ -16 ]   cmp bl, 0x9               cmp bl, 0x9
  0x402dbc  [ -16 ]   ja 0x402de3               if (bl > 9) then goto 0x402de3
--------------------------------------------------------------------------------
  0x402dbe  [ -16 ]   cmp eax, edi              cmp eax, edi
  0x402dc0  [ -16 ]   ja 0x402de3               if (eax > 214748364) then
                                                   goto 0x402de3
--------------------------------------------------------------------------------
  0x402dc2  [ -16 ]   lea eax, (eax,eax,4)      eax := (eax + (4 * eax))
  0x402dc5  [ -16 ]   add eax, eax              eax := eax + eax
  0x402dc7  [ -16 ]   add eax, ebx              eax := eax + ebx
  0x402dc9  [ -16 ]   mov bl, (esi)             bl :=  ?  (tmpN)
  0x402dcb  [ -16 ]   inc esi                   esi := esi + 1
  0x402dcc  [ -16 ]   test bl, bl               test bl, bl
  0x402dce  [ -16 ]   jnz 0x402db6              if (bl != 0) then goto 0x402db6
--------------------------------------------------------------------------------
  0x402dd0  [ -16 ]   dec ch                    ch := ch - 1
  0x402dd2  [ -16 ]   jz 0x402ddd               if (ch = 1) then goto 0x402ddd
--------------------------------------------------------------------------------
  0x402dd4  [ -16 ]   test eax, eax             test eax, eax
  0x402dd6  [ -16 ]   jge 0x402e2c              if (eax >= 0) then goto 0x402e2c
--------------------------------------------------------------------------------
  0x402dd8  [ -16 ]   jmp 0x402de3              goto 0x402de3
--------------------------------------------------------------------------------
  0x402dda  [ -16 ]   inc esi                   esi := esi + 1
  0x402ddb  [ -16 ]   jmp 0x402de3              goto 0x402de3
--------------------------------------------------------------------------------
  0x402ddd  [ -16 ]   neg eax                   eax := 0 - eax
  0x402ddf  [ -16 ]   jle 0x402e2c              if ? then goto 0x402e2c
--------------------------------------------------------------------------------
  0x402de1  [ -16 ]   js 0x402e2c               if ? then goto 0x402e2c
--------------------------------------------------------------------------------
  0x402de3  [ -16 ]   pop ebx                   ebx := eax_in; esp := esp + 4 = (esp_in - 12)
  0x402de4  [ -12 ]   sub esi, ebx              esi := esi - ebx = (esi - eax_in)
  0x402de6  [ -12 ]   jmp 0x402e2f              goto 0x402e2f
--------------------------------------------------------------------------------
  0x402de8  [ -16 ]   inc ch                    ch := ch + 1 = 1
--------------------------------------------------------------------------------
  0x402dea  [ -16 ]   mov bl, (esi)             bl :=  ?  (tmpN)
  0x402dec  [ -16 ]   inc esi                   esi := esi + 1
  0x402ded  [ -16 ]   jmp 0x402d8b              goto 0x402d8b
--------------------------------------------------------------------------------
  0x402def  [ -16 ]   mov edi, 0xfffffff        edi := 268435455
  0x402df4  [ -16 ]   mov bl, (esi)             bl :=  ?  (tmpN)
  0x402df6  [ -16 ]   inc esi                   esi := esi + 1
  0x402df7  [ -16 ]   test bl, bl               test bl, bl
  0x402df9  [ -16 ]   jz 0x402dda               if (bl = 0) then goto 0x402dda
--------------------------------------------------------------------------------
  0x402dfb  [ -16 ]   cmp bl, 0x61              cmp bl, 0x61
  0x402dfe  [ -16 ]   jc 0x402e03               if (bl < 97) then goto 0x402e03
--------------------------------------------------------------------------------
  0x402e00  [ -16 ]   sub bl, 0x20              bl := bl - 32
--------------------------------------------------------------------------------
  0x402e03  [ -16 ]   sub bl, 0x30              bl := bl - 48
  0x402e06  [ -16 ]   cmp bl, 0x9               cmp bl, 0x9
  0x402e09  [ -16 ]   jbe 0x402e16              if (bl <= 9) then goto 0x402e16
--------------------------------------------------------------------------------
  0x402e0b  [ -16 ]   sub bl, 0x11              bl := bl - 17
  0x402e0e  [ -16 ]   cmp bl, 0x5               cmp bl, 0x5
  0x402e11  [ -16 ]   ja 0x402de3               if (bl > 5) then goto 0x402de3
--------------------------------------------------------------------------------
  0x402e13  [ -16 ]   add bl, 0xa               bl := bl + 10
--------------------------------------------------------------------------------
  0x402e16  [ -16 ]   cmp eax, edi              cmp eax, edi
  0x402e18  [ -16 ]   ja 0x402de3               if (eax > 268435455) then
                                                   goto 0x402de3
--------------------------------------------------------------------------------
  0x402e1a  [ -16 ]   shl eax, 0x4              eax := eax * 16
  0x402e1d  [ -16 ]   add eax, ebx              eax := eax + ebx
  0x402e1f  [ -16 ]   mov bl, (esi)             bl :=  ?  (tmpN)
  0x402e21  [ -16 ]   inc esi                   esi := esi + 1
  0x402e22  [ -16 ]   test bl, bl               test bl, bl
  0x402e24  [ -16 ]   jnz 0x402dfb              if (bl != 0) then goto 0x402dfb
--------------------------------------------------------------------------------
  0x402e26  [ -16 ]   dec ch                    ch := ch - 1
  0x402e28  [ -16 ]   jnz 0x402e2c              if (ch != 1) then goto 0x402e2c
--------------------------------------------------------------------------------
  0x402e2a  [ -16 ]   neg eax                   eax := 0 - eax
--------------------------------------------------------------------------------
  0x402e2c  [ -16 ]   pop ecx                   ecx := eax_in; esp := esp + 4 = (esp_in - 12)
  0x402e2d  [ -12 ]   xor esi, esi              esi := 0
--------------------------------------------------------------------------------
  0x402e2f  [ -12 ]   mov (edx), esi            (edx_in)[0] := esi
  0x402e31  [ -12 ]   pop edi                   restore edi
  0x402e32   [ -8 ]   pop esi                   restore esi
  0x402e33   [ -4 ]   pop ebx                   restore ebx
  0x402e34   [ 0 ]    ret                       return

*)
class rtl_system_vallong_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::ValLong__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(str:"; xpr_to_pretty floc eaxv;
	STR ",lpVal:"; xpr_to_pretty floc edxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let edxv = get_reg_value Edx floc in
    let lhs = floc#get_lhs_from_address edxv in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let size = int_constant_expr 4 in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Edx; Ecx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "ValLong"

  method! get_description = "Delphi RTL function System::ValLong"

end

let _ = H.add table "System::ValLong" (new rtl_system_vallong_semantics_t)


(* ============================================================= System::WStrCmp
   example: V01a:0x404a58
   md5hash: 5bf4432a4b3e10f024087649e3a041bc
*)
class rtl_system_wstrcmp_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::WStrCmp__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(s1:"; xpr_to_strpretty floc eaxv;
	STR ",s2:"; xpr_to_strpretty floc edxv; STR ")"]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "WStrCmp"

  method! get_description = "Delphi RTL system function System::WStrCmp"

end

let _ = H.add table "System::WStrCmp" (new rtl_system_wstrcmp_semantics_t)

(* ====================================================== System::RegisterModule
   example: V1da:0x405990

  0x405990   [ 0 ]    mov edx, 0x478034     edx := gv_0x478034 = gv_0x478034_in
  0x405996   [ 0 ]    mov (eax), edx        (eax_in)[0] := edx = gv_0x478034_in
  0x405998   [ 0 ]    mov 0x478034, eax     gv_0x478034 := eax = eax_in
  0x40599d   [ 0 ]    ret                   return
*)
class rtl_system_registermodule_semantics_t
  (md5hash:string) (gv:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::RegisterModule__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc eaxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let (eaxdlhs,eaxdlhscmds) = get_reg_deref_lhs Eax 0 floc in
    let gval = get_gv_value gv floc in
    let gvar = TR.tget_ok (floc#env#mk_global_variable gv#to_numerical) in
    let cmds1 = floc#get_assign_commands eaxdlhs gval in
    let cmds2 = floc#get_assign_commands gvar eaxv in
    let cmds3 = [floc#get_abstract_cpu_registers_command [Edx]] in
    List.concat [eaxdlhscmds; cmds1; cmds2; cmds3]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "Delphi RTL system function System::RegisterModule"

end

(* ===================================================== System::wRegisterModule
   example: V1da:0x406194

  0x406194   [ 0 ]    mov eax, 0x4780a4         eax := 4685988
  0x406199   [ 0 ]    call 0x405990             0x405990(reg_eax:ds:0x4780a4)
  0x40619e   [ 0 ]    ret                       return
*)
class rtl_system_wregistermodule_semantics_t
        (md5hash:string)
        (ptlibmodule:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::RegisterModule_wrapper__"

  method! get_annotation (_floc:floc_int) =
    LBLOCK [STR "__System::RegisterModule("; ptlibmodule#toPretty; STR ")"]

  method! get_commands (_floc:floc_int) = []

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_target a "RegisterModule_wrapper"

  method! get_description = "RTL system function that wraps RegisterModule"

end


(* ============================================================= System::WStrLen
   example: V01a:0x404a04
   md5hash: ff41d3d352405142c298ae47b896cc85

  0x404a04   [ 0 ]    test eax, eax         test eax, eax
  0x404a06   [ 0 ]    jz 0x404a0d           if (eax_in = 0) then goto 0x404a0d
--------------------------------------------------------------------------------
  0x404a08   [ 0 ]    mov eax, -0x4(eax)    eax :=  (eax_in)[-4]
  0x404a0b   [ 0 ]    shr eax, 0x1          eax := eax / 2
--------------------------------------------------------------------------------
  0x404a0d   [ 0 ]    ret                   return
*)
class rtl_system_wstrlen_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::WStrLen__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let eaxderefvalue = get_reg_derefvalue Eax (-4) floc in
    let rhs = XOp (XDiv, [ eaxderefvalue; int_constant_expr 2 ]) in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_strpretty floc eaxv; STR ")";
	STR " [ eax := "; xpr_to_pretty floc rhs; STR " ]"]

  method! get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds = floc#get_assign_commands eaxlhs (XVar rhs) in
    List.concat [eaxlhscmds; cmds]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_target a "WStrLen"

  method! get_description = "Delphi RTL system function System::WStrLen"

end

let _ = H.add table "System::WStrLen" (new rtl_system_wstrlen_semantics_t)


(* ==================================================== System::Sysinit::InitExe
   example: V1da:0x4061a0

  0x4061a0   [ 0 ]    push ebx             save ebx
  0x4061a1   [ -4 ]   mov ebx, eax         ebx := eax = eax_in
  0x4061a3   [ -4 ]   xor eax, eax         eax := 0
  0x4061a5   [ -4 ]   mov 0x47809c, eax    gv_0x47809c := eax = 0
  0x4061aa   [ -4 ]   push 0x0             [GetModuleHandleA: lpModuleName = 0]
  0x4061ac   [ -8 ]   call 0x4060dc        GetModuleHandleA(lpModuleName:0) (adj 4)
  0x4061b1   [ -4 ]   mov 0x47c664, eax    gv_0x47c664 := GetModuleHandleA_rtn_0x4061ac
  0x4061b6   [ -4 ]   mov eax, 0x47c664    eax := GetModuleHandleA_rtn_0x4061ac
  0x4061bb   [ -4 ]   mov 0x4780a8, eax    gv_0x4780a8 := GetModuleHandleA_rtn_0x4061ac
  0x4061c0   [ -4 ]   xor eax, eax         eax := 0
  0x4061c2   [ -4 ]   mov 0x4780ac, eax    gv_0x4780ac := eax = 0
  0x4061c7   [ -4 ]   xor eax, eax         eax := 0
  0x4061c9   [ -4 ]   mov 0x4780b0, eax    gv_0x4780b0 := eax = 0
  0x4061ce   [ -4 ]   call 0x406194        0x406194()
  0x4061d3   [ -4 ]   mov edx, 0x4780a4    edx := 4685988
  0x4061d8   [ -4 ]   mov eax, ebx         eax := ebx = eax_in
  0x4061da   [ -4 ]   call 0x403fa8        0x403fa8(reg_eax:eax_in, reg_edx:ds:0x4780a4)
  0x4061df   [ -4 ]   pop ebx              restore ebx
  0x4061e0   [ 0 ]    ret                  return
*)
class rtl_system_sysinit_initexe_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::Sysinit::InitExe__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name; STR "("; xpr_to_pretty floc eaxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let _ = set_delphi_exception_handler_table floc eaxv in
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_target a ~pkgs:["System"; "Sysinit"] "InitExe"

  method! get_description = "Delphi RTL function System::Sysinit::InitExe"

end


(* ============================================================== set_handler
   example: V1da:0x470008

  0x470008   [ 0 ]    push ebp            save ebp
  0x470009   [ -4 ]   mov ebp, esp        ebp := esp = (esp_in - 4)
  0x47000b   [ -4 ]   xor eax, eax        eax := 0
  0x47000d   [ -4 ]   push ebp            esp := esp - 4; var.0008 := ebp
  0x47000e   [ -8 ]   push ca:0x47002d    esp := esp - 4; var.0012 := 4653101
  0x470013  [ -12 ]   push (eax)          esp := esp - 4; var.0016 :=  ?  (tmpN)
  0x470016  [ -16 ]   mov (eax), esp      ? := esp = (esp_in - 16)
  0x470019  [ -16 ]   inc 0x47d9f8        gv_0x47d9f8 := (gv_0x47d9f8_in + 1)
  0x47001f  [ -16 ]   xor eax, eax        eax := 0
  0x470021  [ -16 ]   pop edx             edx := var.0016; esp := (esp_in - 12)
  0x470022  [ -12 ]   pop ecx             ecx := 4653101; esp := (esp_in - 8)
  0x470023   [ -8 ]   pop ecx             ecx := (esp_in - 4); esp := (esp_in - 4)
  0x470024   [ -4 ]   mov (eax), edx      ? := edx
  0x470027   [ -4 ]   push ca:0x470034    esp := esp - 4; var.0008 := 4653108
--------------------------------------------------------------------------------
  0x47002c   [ -8 ]   ret                 esp := esp + 4; goto 0x470034
--------------------------------------------------------------------------------
  0x470034   [ -4 ]   pop ebp             restore ebp
  0x470035   [ 0 ]    ret                 return
*)

class rtl_system_sethandler_semantics_t
  (md5hash:string) (gv:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__set_handler_" ^ gv#to_hex_string ^ "__"

  method! get_annotation (_floc:floc_int) =
    LBLOCK [STR self#get_name; STR "()"]

  method! get_commands (_floc:floc_int) = []

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) = mk_app_target a

  method! get_description = "Delphi set exception handler"

end

let delphi_rtl_functions () =
  H.fold (fun k v a -> a @ (get_fnhashes k v)) table []


let delphi_rtl_patterns = [

  (* set exception handler (V1da:0x470008) *)
  { regex_s = Str.regexp
      ("558bec33c05568\\(........\\)64ff30648920ff05\\(........\\)33c05a5959" ^
       "64891068\\(........\\)c35dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let fp1 = todw (Str.matched_group 1 fnbytes) in
      let fp2 = todw (Str.matched_group 3 fnbytes) in
      let gv = todw (Str.matched_group 2 fnbytes) in
      let sem = new rtl_system_sethandler_semantics_t fnhash gv 17 in
      let msg =
        LBLOCK [STR " with handlers "; fp1#toPretty; STR " and "; fp2#toPretty] in
      sometemplate ~msg sem
  };

  (* Set8087CW(unsigned short) (V01a:0x402ad0) *)
  { regex_s = Str.regexp "66a3\\(........\\)dbe2d92d\\(........\\)c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let gv1 = todw (Str.matched_group 1 fnbytes) in
      let gv2 = todw (Str.matched_group 2 fnbytes) in
      if gv1#equal gv2 then
	let sem = new rtl_system_set8087cw_semantics_t fnhash gv1 4 in
	let msg = LBLOCK [STR " with source gv_"; gv1#toPretty] in
	sometemplate ~msg sem
      else
	None
  };

  (* System::_CToPasStr (V1da:0x402fc4) *)
  { regex_s = Str.regexp "b9ff000000e8\\(........\\)c3$";

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_lib_call faddr 5 "_CLenToPasStr" then
	let sem = new rtl_system_ctopasstr_semantics_t fnhash 3 in
	sometemplate sem
      else None
  };

  (* System::IsClass  (V1da: 0x403674) *)
  { regex_s = Str.regexp
      ("53568bf28bd885db740d8bd68b03e8\\(........\\)84c0750533c05e5bc3b0015e5bc3$");

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_lib_call faddr 14 "InheritsFrom" then
	let sem = new rtl_system_isclasssemantics_t fnhash 19 in
	sometemplate sem
      else None
  };

  (* LStrToPChar(s: void (V01a:0x404678) *)
  { regex_s = Str.regexp "85c07402c3b8\\(........\\)c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new rtl_system_strtopchar_semantics_t fnhash "LStrToPChar" 5 in
      let msg = LBLOCK [ STR " with nullstr at "; gv#toPretty ] in
      sometemplate ~msg sem
  };

  (* WStrToPWChar (V1da:0x404b28) *)
  { regex_s = Str.regexp "85c07404c3b8\\(........\\)c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new rtl_system_strtopchar_semantics_t fnhash "WStrToPWChar" 5 in
      let msg = LBLOCK [ STR " with nullstr at "; gv#toPretty ] in
      sometemplate ~msg sem
  };

  (* System::PStrNCpy (V1da:0x402dc0) *)
  { regex_s = Str.regexp
      ("538a1a3acb76028bcb8808424081e1ff00000092e8\\(........\\)5bc3$");

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_lib_call faddr 20 "Move" then
	let sem = new rtl_system_pstrncpy_semantics_t fnhash 13 in
	sometemplate sem
      else None
  };

  (* System::RegisterModule (V1da:0x405990) *)
  { regex_s = Str.regexp "8b15\\(........\\)8910a3\\(........\\)c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let gv1 = todw (Str.matched_group 1 fnbytes) in
      let gv2 = todw (Str.matched_group 2 fnbytes) in
      if gv1#equal gv2 then
	let sem = new rtl_system_registermodule_semantics_t fnhash gv1 4 in
	let msg = LBLOCK [ STR " with location "; gv1#toPretty ] in
	sometemplate ~msg sem
      else None
  };

  (* System::RegisterModule_wrapper (V1da:0x406194) *)
  { regex_s = Str.regexp "b8\\(........\\)e8\\(........\\)c3$";

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      if is_named_inlined_call faddr 5 "__System::RegisterModule__" then
	let sem = new rtl_system_wregistermodule_semantics_t fnhash gv 3 in
	let msg = LBLOCK [ STR " with pTLibModule "; gv#toPretty ] in
	sometemplate ~msg sem
      else None
  };

  (* System::StartExe (V1da:0x403fa8) *)
  { regex_s = Str.regexp
      ("c705\\(........\\)\\(........\\)c705\\(........\\)\\(........\\)a3" ^
       "\\(........\\)33c0a3\\(........\\)8915\\(........\\)8b4204a3\\(........\\)" ^
       "e8\\(........\\)c605\\(........\\)00e8\\(........\\)c3$");

    regex_f = fun faddr fnbytes fnhash ->
      let dgv1 = todw (Str.matched_group 1 fnbytes) in
      let dgv2 = todw (Str.matched_group 3 fnbytes) in
      let dgv3 = todw (Str.matched_group 5 fnbytes) in
      let dgv4 = todw (Str.matched_group 6 fnbytes) in
      let dgv5 = todw (Str.matched_group 7 fnbytes) in
      let dgv6 = todw (Str.matched_group 8 fnbytes) in
      let dgv7 = todw (Str.matched_group 10 fnbytes) in
      let src1 = todw (Str.matched_group 2 fnbytes) in
      let src2 = todw (Str.matched_group 4 fnbytes) in
      let _ = functions_data#add_function src1 in
      let _ = functions_data#add_function src2 in
      if (is_named_lib_call faddr 46 "initTIBInfo") &&
	(is_named_lib_call faddr 58 "initExnHandling") then
	let sem = new rtl_system_startexe_semantics_t fnhash 12 in
	let msg = LBLOCK [
	  STR " with global variables set ";
	  pretty_print_list [ dgv1; dgv2; dgv3; dgv4; dgv5; dgv6; dgv7 ]
	    (fun g -> g#toPretty) "[" ", " "]" ] in
	sometemplate ~msg sem
      else None
  };

  (* System::delphi_unknown1 (V4a6371:0x300022d4) *)
  { regex_s = Str.regexp
      ("a1\\(........\\)85c0740f8b1033c98b400487caff15\\(........\\)c3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv1 = todw (Str.matched_group 1 fnbytes) in
      let gv2 = todw (Str.matched_group 2 fnbytes) in
      let sem = new rtl_system_delphiunknown1_semantics_t fnhash 9 in
      let msg =
        LBLOCK [
            STR " with global variables "; gv1#toPretty; STR " and ";
	    gv2#toPretty] in
      sometemplate ~msg sem
  };

  (* System::StartExe1 (V4a6371:0x300022f0) *)
  { regex_s = Str.regexp
      ("c705\\(........\\)\\(........\\)c705\\(........\\)\\(........\\)a3" ^
       "\\(........\\)33c0a3\\(........\\)8915\\(........\\)8b4204a3\\(........\\)" ^
       "c605\\(........\\)00e8\\(........\\)c3$");

    regex_f = fun faddr fnbytes fnhash ->
      let dgv1 = todw (Str.matched_group 1 fnbytes) in
      let dgv2 = todw (Str.matched_group 3 fnbytes) in
      let dgv3 = todw (Str.matched_group 5 fnbytes) in
      let dgv4 = todw (Str.matched_group 6 fnbytes) in
      let dgv5 = todw (Str.matched_group 7 fnbytes) in
      let dgv6 = todw (Str.matched_group 8 fnbytes) in
      let dgv7 = todw (Str.matched_group 9 fnbytes) in
      let src1 = todw (Str.matched_group 2 fnbytes) in
      let src2 = todw (Str.matched_group 4 fnbytes) in
      let _ = functions_data#add_function src1 in
      let _ = functions_data#add_function src2 in
      if (is_named_lib_call faddr 53 "delphi_unknown1") then
	let sem = new rtl_system_startexe_semantics_t fnhash 11 in
	let msg = LBLOCK [
	  STR " with global variables set ";
	  pretty_print_list [ dgv1; dgv2; dgv3; dgv4; dgv5; dgv6; dgv7 ]
	    (fun g -> g#toPretty) "[" ", " "]" ] in
	sometemplate ~msg sem
      else None
  };


  (* System::initTIBInfo (V1da:0x403e80) *)
  { regex_s = Str.regexp
      "31d28d45f4648b0a6489028908c74004\\(........\\)896808a3\\(........\\)c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let fp = todw (Str.matched_group 1 fnbytes) in
      let gv = todw (Str.matched_group 2 fnbytes) in
      let _ = functions_data#add_function fp in
      let sem = new rtl_system_inittibinfo_semantics_t fnhash 9 in
      let msg = LBLOCK [ STR " with global variable "; gv#toPretty ] in
      sometemplate ~msg sem
  };

  (* System::initExnHandling (V1da:0x403f38) *)
  { regex_s = Str.regexp
      ("558bec83c4f8535657bf\\(........\\)8b470885c074548b3033db8b40048945fc33c0" ^
       "5568\\(........\\)64ff306489203bf37e1a8b45fc8b04d88945f843895f0c837df800" ^
       "7403ff55f83bf37fe633c05a5959648910eb145f5e5b59595dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let fp = todw (Str.matched_group 2 fnbytes) in
      let _ = functions_data#add_function fp in
      let sem = new rtl_system_initexnhandling_semantics_t fnhash 44 in
      let msg = LBLOCK [ STR " with base "; gv#toPretty ] in
      sometemplate ~msg sem
  };

  (* System::initExnHandling (V01a:0403e00) *)
  { regex_s = Str.regexp
      ("558bec535657a1\\(........\\)85c0744b8b3033db8b780433d25568\\(........\\)" ^
       "64ff326489223bf37e148b04df43891d\\(........\\)85c07402ffd03bf37fec33c05a" ^
       "5959648910eb145f5e5b5dc3$");

    regex_f = fun _faddr fnbytes fnhash ->
      let gv1 = todw (Str.matched_group 1 fnbytes) in
      let fp = todw (Str.matched_group 2 fnbytes) in
      let gv2 = todw (Str.matched_group 3 fnbytes) in
      let _ = functions_data#add_function fp in
      let sem = new rtl_system_initexnhandling_semantics_t fnhash 37 in
      let msg = LBLOCK [ STR " with bases "; gv1#toPretty; STR " and ";
			 gv2#toPretty ] in
      sometemplate ~msg sem
  };


  (* System::Sysinit::InitExe (V1da:0x4061a0) *)
  { regex_s = Str.regexp
      ("538bd833c0a3\\(........\\)6a00e8\\(........\\)a3\\(........\\)a1" ^
       "\\(........\\)a3\\(........\\)33c0a3\\(........\\)33c0a3" ^
       "\\(........\\)e8\\(........\\)ba\\(........\\)8bc3e8\\(........\\)" ^
       "5bc3$");

    regex_f = fun faddr fnbytes fnhash ->
              (* let tlsindex = todw (Str.matched_group 1 fnbytes) in *)
      let gv1 = todw (Str.matched_group 3 fnbytes) in
      let gv2 = todw (Str.matched_group 4 fnbytes) in
      let gv3 = todw (Str.matched_group 5 fnbytes) in
      let gv4 = todw (Str.matched_group 6 fnbytes) in
      let gv5 = todw (Str.matched_group 8 fnbytes) in
      if is_named_dll_call faddr 12 "GetModuleHandleA" &&
	(is_named_lib_call faddr 46 "RegisterModule_wrapper") &&
	(is_named_lib_call faddr 58 "StartExe") then
	let sem = new rtl_system_sysinit_initexe_semantics_t fnhash 19 in
	let msg = LBLOCK [ STR " with globals ";
			   pretty_print_list [ gv1; gv2; gv3; gv4; gv5 ]
			     (fun g -> g#toPretty) "[" ", " "]" ] in
	sometemplate ~msg sem
      else
	None
  }
]
