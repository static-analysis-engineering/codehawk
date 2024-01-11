(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
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
open CHPretty

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHPredefinedUtil

module H = Hashtbl

let table = H.create 7

(* The functions in this file seem to be part of the Microsoft C/C++ Exchange
   Development Kit (EDK) library; they provide compiler support for 64 bit
   arithmetic operations. Most operations have 4 32-bit arguments that constitute
   the two 64-bit arguments and return the result in Edx_Eax.

   --alldiv__(A,B,C,D)
   __alldvrm__(A,B,C,D)
   __allmul__(A,B,C,D)
   __allrem__(A,B,C,D)
   __allshl__
   __aulldiv___(A,B,C,D)
   __aulldvrm__(A,B,C,D)
   __aullshr__(eax,edx,ecx)

*)

(* ================================================================ __alldiv__
   example: V03be08:0x4048c0
   md5hash: 650b1c3a88bc03163222fbfd32e81d04

  0x4048c0   [ 0 ]    push edi                  save edi
  0x4048c1   [ -4 ]   push esi                  save esi
  0x4048c2   [ -8 ]   push ebx                  save ebx
  0x4048c3  [ -12 ]   xor edi, edi              edi := 0
  0x4048c5  [ -12 ]   mov eax, 0x14(esp,,1)     eax := arg.0008 = arg.0008_in
  0x4048c9  [ -12 ]   or eax, eax               eax := eax | eax
  0x4048cb  [ -12 ]   jge 0x4048e1              if ? then goto 0x4048e1
--------------------------------------------------------------------------------
  0x4048cd  [ -12 ]   inc edi                   edi := edi + 1 = 1
  0x4048ce  [ -12 ]   mov edx, 0x10(esp,,1)     edx := arg.0004 = arg.0004_in
  0x4048d2  [ -12 ]   neg eax                   eax := 0 - eax
  0x4048d4  [ -12 ]   neg edx                   edx := 0 - edx = (0 - arg.0004_in)
  0x4048d6  [ -12 ]   sbb eax, 0x0              eax := eax - (0 - (0 or 1))
  0x4048d9  [ -12 ]   mov 0x14(esp,,1), eax     arg.0008 := eax
  0x4048dd  [ -12 ]   mov 0x10(esp,,1), edx     arg.0004 := edx = (0 - arg.0004_in)
--------------------------------------------------------------------------------
  0x4048e1  [ -12 ]   mov eax, 0x1c(esp,,1)     eax := arg.0016 = arg.0016_in
  0x4048e5  [ -12 ]   or eax, eax               eax := eax | eax
  0x4048e7  [ -12 ]   jge 0x4048fd              if ? then goto 0x4048fd
--------------------------------------------------------------------------------
  0x4048e9  [ -12 ]   inc edi                   edi := edi + 1
  0x4048ea  [ -12 ]   mov edx, 0x18(esp,,1)     edx := arg.0012 = arg.0012_in
  0x4048ee  [ -12 ]   neg eax                   eax := 0 - eax
  0x4048f0  [ -12 ]   neg edx                   edx := 0 - edx = (0 - arg.0012_in)
  0x4048f2  [ -12 ]   sbb eax, 0x0              eax := eax - (0 - (0 or 1))
  0x4048f5  [ -12 ]   mov 0x1c(esp,,1), eax     arg.0016 := eax
  0x4048f9  [ -12 ]   mov 0x18(esp,,1), edx     arg.0012 := edx = (0 - arg.0012_in)
--------------------------------------------------------------------------------
  0x4048fd  [ -12 ]   or eax, eax               eax := eax | eax
  0x4048ff  [ -12 ]   jnz 0x404919              if (eax_val@_0x4048fd_@_0x4048ff != 0) then goto 0x404919
--------------------------------------------------------------------------------
  0x404901  [ -12 ]   mov ecx, 0x18(esp,,1)     ecx := arg.0012
  0x404905  [ -12 ]   mov eax, 0x14(esp,,1)     eax := arg.0008
  0x404909  [ -12 ]   xor edx, edx              edx := 0
  0x40490b  [ -12 ]   div ecx                   (eax,edx) = eax / ecx (unsigned)
  0x40490d  [ -12 ]   mov ebx, eax              ebx := eax
  0x40490f  [ -12 ]   mov eax, 0x10(esp,,1)     eax := arg.0004
  0x404913  [ -12 ]   div ecx                   (eax,edx) = edx_eax / ecx (unsigned)
  0x404915  [ -12 ]   mov edx, ebx              edx := ebx
  0x404917  [ -12 ]   jmp 0x40495a              goto 0x40495a
--------------------------------------------------------------------------------
  0x404919  [ -12 ]   mov ebx, eax              ebx := eax
  0x40491b  [ -12 ]   mov ecx, 0x18(esp,,1)     ecx := arg.0012
  0x40491f  [ -12 ]   mov edx, 0x14(esp,,1)     edx := arg.0008
  0x404923  [ -12 ]   mov eax, 0x10(esp,,1)     eax := arg.0004
--------------------------------------------------------------------------------
  0x404927  [ -12 ]   shr ebx, 0x1              ebx := ebx / 2
  0x404929  [ -12 ]   rcr ecx, 0x1              ecx := rotate_right(CF,ecx) by 1
  0x40492b  [ -12 ]   shr edx, 0x1              edx := edx / 2
  0x40492d  [ -12 ]   rcr eax, 0x1              eax := rotate_right(CF,eax) by 1
  0x40492f  [ -12 ]   or ebx, ebx               ebx := ebx | ebx
  0x404931  [ -12 ]   jnz 0x404927              if (ebx_val@_0x40492f_@_0x404931 != 0) then goto 0x404927
--------------------------------------------------------------------------------
  0x404933  [ -12 ]   div ecx                   (eax,edx) = edx_eax / ecx (unsigned)
  0x404935  [ -12 ]   mov esi, eax              esi := eax
  0x404937  [ -12 ]   mul 0x1c(esp,,1)          edx_eax := eax * arg.0016 (unsigned)
  0x40493b  [ -12 ]   mov ecx, eax              ecx := eax
  0x40493d  [ -12 ]   mov eax, 0x18(esp,,1)     eax := arg.0012
  0x404941  [ -12 ]   mul esi                   edx_eax := eax * esi (unsigned)
  0x404943  [ -12 ]   add edx, ecx              edx := edx + ecx
  0x404945  [ -12 ]   jc 0x404955               if ? then goto 0x404955
--------------------------------------------------------------------------------
  0x404947  [ -12 ]   cmp edx, 0x14(esp,,1)     cmp edx, 0x14(esp,,1)
  0x40494b  [ -12 ]   ja 0x404955               if (edx > arg.0008) then goto 0x404955
--------------------------------------------------------------------------------
  0x40494d  [ -12 ]   jc 0x404956               if ? then goto 0x404956
--------------------------------------------------------------------------------
  0x40494f  [ -12 ]   cmp eax, 0x10(esp,,1)     cmp eax, 0x10(esp,,1)
  0x404953  [ -12 ]   jbe 0x404956              if (eax <= arg.0004) then goto 0x404956
--------------------------------------------------------------------------------
  0x404955  [ -12 ]   dec esi                   esi := esi - 1
--------------------------------------------------------------------------------
  0x404956  [ -12 ]   xor edx, edx              edx := 0
  0x404958  [ -12 ]   mov eax, esi              eax := esi
--------------------------------------------------------------------------------
  0x40495a  [ -12 ]   dec edi                   edi := edi - 1
  0x40495b  [ -12 ]   jnz 0x404964              if (edi != 1) then goto 0x404964
--------------------------------------------------------------------------------
  0x40495d  [ -12 ]   neg edx                   edx := 0 - edx
  0x40495f  [ -12 ]   neg eax                   eax := 0 - eax
  0x404961  [ -12 ]   sbb edx, 0x0              edx := edx - (0 - (0 or 1))
--------------------------------------------------------------------------------
  0x404964  [ -12 ]   pop ebx                   restore ebx
  0x404965   [ -8 ]   pop esi                   restore esi
  0x404966   [ -4 ]   pop edi                   restore edi
  0x404967   [ 0 ]    ret 16                    return (increment stackpointer by 16)
 *)
class alldiv_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object(self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__alldiv__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let arg4 = get_arg args 4 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1;
	STR ","; xpr_to_pretty floc arg2;
	STR ","; xpr_to_pretty floc arg3;
	STR ","; xpr_to_pretty floc arg4; STR ") (adj 16)"]

  method! get_commands (floc:floc_int) =
    let cmds1 = get_adjustment_commands 16 floc in
    let cmds2 =
      [floc#get_abstract_cpu_registers_command [Eax; Ebx; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 4

  method! get_description = "64 bit division"

end

let _ = H.add table "alldiv" (new alldiv_semantics_t)


(* ========================================================= __alldvrm__(A,B,C,D)
   example: Vb4b:0x409be0

  0x409be0   [ 0 ]    push edi                  save edi
  0x409be1   [ -4 ]   push esi                  save esi
  0x409be2   [ -8 ]   push ebp                  save ebp
  0x409be3  [ -12 ]   xor edi, edi              edi := 0
  0x409be5  [ -12 ]   xor ebp, ebp              ebp := 0
  0x409be7  [ -12 ]   mov eax, 0x14(esp,,1)     eax := arg.0008 = arg.0008_in
  0x409beb  [ -12 ]   or eax, eax               eax := eax | eax
  0x409bed  [ -12 ]   jge 0x409c04              if ? then goto 0x409c04
--------------------------------------------------------------------------------
  0x409bef  [ -12 ]   inc edi                   edi := edi + 1 = 1
  0x409bf0  [ -12 ]   inc ebp                   ebp := ebp + 1 = 1
  0x409bf1  [ -12 ]   mov edx, 0x10(esp,,1)     edx := arg.0004 = arg.0004_in
  0x409bf5  [ -12 ]   neg eax                   eax := 0 - eax
  0x409bf7  [ -12 ]   neg edx                   edx := 0 - edx = (0 - arg.0004_in)
  0x409bf9  [ -12 ]   sbb eax, 0x0              eax := eax - (0 - (0 or 1))
  0x409bfc  [ -12 ]   mov 0x14(esp,,1), eax     arg.0008 := eax
  0x409c00  [ -12 ]   mov 0x10(esp,,1), edx     arg.0004 := edx = (0 - arg.0004_in)
--------------------------------------------------------------------------------
  0x409c04  [ -12 ]   mov eax, 0x1c(esp,,1)     eax := arg.0016 = arg.0016_in
  0x409c08  [ -12 ]   or eax, eax               eax := eax | eax
  0x409c0a  [ -12 ]   jge 0x409c20              if ? then goto 0x409c20
--------------------------------------------------------------------------------
  0x409c0c  [ -12 ]   inc edi                   edi := edi + 1
  0x409c0d  [ -12 ]   mov edx, 0x18(esp,,1)     edx := arg.0012 = arg.0012_in
  0x409c11  [ -12 ]   neg eax                   eax := 0 - eax
  0x409c13  [ -12 ]   neg edx                   edx := 0 - edx = (0 - arg.0012_in)
  0x409c15  [ -12 ]   sbb eax, 0x0              eax := eax - (0 - (0 or 1))
  0x409c18  [ -12 ]   mov 0x1c(esp,,1), eax     arg.0016 := eax
  0x409c1c  [ -12 ]   mov 0x18(esp,,1), edx     arg.0012 := edx = (0 - arg.0012_in)
--------------------------------------------------------------------------------
  0x409c20  [ -12 ]   or eax, eax               eax := eax | eax
  0x409c22  [ -12 ]   jnz 0x409c4c              if (eax != 0) then goto 0x409c4c
--------------------------------------------------------------------------------
  0x409c24  [ -12 ]   mov ecx, 0x18(esp,,1)     ecx := arg.0012
  0x409c28  [ -12 ]   mov eax, 0x14(esp,,1)     eax := arg.0008
  0x409c2c  [ -12 ]   xor edx, edx              edx := 0
  0x409c2e  [ -12 ]   div ecx                   (eax,edx) = eax / ecx (unsigned)
  0x409c30  [ -12 ]   mov ebx, eax              ebx := eax
  0x409c32  [ -12 ]   mov eax, 0x10(esp,,1)     eax := arg.0004
  0x409c36  [ -12 ]   div ecx                   (eax,edx) = edx_eax / ecx (unsigned)
  0x409c38  [ -12 ]   mov esi, eax              esi := eax
  0x409c3a  [ -12 ]   mov eax, ebx              eax := ebx
  0x409c3c  [ -12 ]   mul 0x18(esp,,1)          edx_eax := eax * arg.0012 (unsigned)
  0x409c40  [ -12 ]   mov ecx, eax              ecx := eax
  0x409c42  [ -12 ]   mov eax, esi              eax := esi
  0x409c44  [ -12 ]   mul 0x18(esp,,1)          edx_eax := eax * arg.0012 (unsigned)
  0x409c48  [ -12 ]   add edx, ecx              edx := edx + ecx
  0x409c4a  [ -12 ]   jmp 0x409c93              goto 0x409c93
--------------------------------------------------------------------------------
  0x409c4c  [ -12 ]   mov ebx, eax              ebx := eax
  0x409c4e  [ -12 ]   mov ecx, 0x18(esp,,1)     ecx := arg.0012
  0x409c52  [ -12 ]   mov edx, 0x14(esp,,1)     edx := arg.0008
  0x409c56  [ -12 ]   mov eax, 0x10(esp,,1)     eax := arg.0004
--------------------------------------------------------------------------------
  0x409c5a  [ -12 ]   shr ebx, 0x1              ebx := ebx / 2
  0x409c5c  [ -12 ]   rcr ecx, 0x1              ecx := rotate_right(CF,ecx) by 1
  0x409c5e  [ -12 ]   shr edx, 0x1              edx := edx / 2
  0x409c60  [ -12 ]   rcr eax, 0x1              eax := rotate_right(CF,eax) by 1
  0x409c62  [ -12 ]   or ebx, ebx               ebx := ebx | ebx
  0x409c64  [ -12 ]   jnz 0x409c5a              if (ebx != 0) then goto 0x409c5a
--------------------------------------------------------------------------------
  0x409c66  [ -12 ]   div ecx                   (eax,edx) = edx_eax / ecx (unsigned)
  0x409c68  [ -12 ]   mov esi, eax              esi := eax
  0x409c6a  [ -12 ]   mul 0x1c(esp,,1)          edx_eax := eax * arg.0016 (unsigned)
  0x409c6e  [ -12 ]   mov ecx, eax              ecx := eax
  0x409c70  [ -12 ]   mov eax, 0x18(esp,,1)     eax := arg.0012
  0x409c74  [ -12 ]   mul esi                   edx_eax := eax * esi (unsigned)
  0x409c76  [ -12 ]   add edx, ecx              edx := edx + ecx
  0x409c78  [ -12 ]   jc 0x409c88               if ? then goto 0x409c88
--------------------------------------------------------------------------------
  0x409c7a  [ -12 ]   cmp edx, 0x14(esp,,1)     cmp edx, 0x14(esp,,1)
  0x409c7e  [ -12 ]   ja 0x409c88               if (edx > arg.0008) then goto 0x409c88
--------------------------------------------------------------------------------
  0x409c80  [ -12 ]   jc 0x409c91               if ? then goto 0x409c91
--------------------------------------------------------------------------------
  0x409c82  [ -12 ]   cmp eax, 0x10(esp,,1)     cmp eax, 0x10(esp,,1)
  0x409c86  [ -12 ]   jbe 0x409c91              if (eax <= arg.0004) then goto 0x409c91
--------------------------------------------------------------------------------
  0x409c88  [ -12 ]   dec esi                   esi := esi - 1
  0x409c89  [ -12 ]   sub eax, 0x18(esp,,1)     eax := eax - arg.0012
  0x409c8d  [ -12 ]   sbb edx, 0x1c(esp,,1)     edx := edx - (arg.0016 - (0 or 1))
--------------------------------------------------------------------------------
  0x409c91  [ -12 ]   xor ebx, ebx              ebx := 0
--------------------------------------------------------------------------------
  0x409c93  [ -12 ]   sub eax, 0x10(esp,,1)     eax := eax - arg.0004
  0x409c97  [ -12 ]   sbb edx, 0x14(esp,,1)     edx := edx - (arg.0008 - (0 or 1))
  0x409c9b  [ -12 ]   dec ebp                   ebp := ebp - 1
  0x409c9c  [ -12 ]   jns 0x409ca5              if (ebp > 0) then goto 0x409ca5
--------------------------------------------------------------------------------
  0x409c9e  [ -12 ]   neg edx                   edx := 0 - edx
  0x409ca0  [ -12 ]   neg eax                   eax := 0 - eax
  0x409ca2  [ -12 ]   sbb edx, 0x0              edx := edx - (0 - (0 or 1))
--------------------------------------------------------------------------------
  0x409ca5  [ -12 ]   mov ecx, edx              ecx := edx
  0x409ca7  [ -12 ]   mov edx, ebx              edx := ebx
  0x409ca9  [ -12 ]   mov ebx, ecx              ebx := ecx
  0x409cab  [ -12 ]   mov ecx, eax              ecx := eax
  0x409cad  [ -12 ]   mov eax, esi              eax := esi
  0x409caf  [ -12 ]   dec edi                   edi := edi - 1
  0x409cb0  [ -12 ]   jnz 0x409cb9              if (edi != 1) then goto 0x409cb9
--------------------------------------------------------------------------------
  0x409cb2  [ -12 ]   neg edx                   edx := 0 - edx
  0x409cb4  [ -12 ]   neg eax                   eax := 0 - eax
  0x409cb6  [ -12 ]   sbb edx, 0x0              edx := edx - (0 - (0 or 1))
--------------------------------------------------------------------------------
  0x409cb9  [ -12 ]   pop ebp                   restore ebp
  0x409cba   [ -8 ]   pop esi                   restore esi
  0x409cbb   [ -4 ]   pop edi                   restore edi
  0x409cbc   [ 0 ]    ret 16                    return (increment stackpointer by 16)

*)

class alldvrm_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__alldvrm__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let arg4 = get_arg args 4 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1;
	STR ","; xpr_to_pretty floc arg2;
	STR ","; xpr_to_pretty floc arg3;
	STR ","; xpr_to_pretty floc arg4; STR ") (adj 16)"]

  method! get_commands (floc:floc_int) =
    let cmds1 = get_adjustment_commands 16 floc in
    let cmds2 =
      [floc#get_abstract_cpu_registers_command [Eax; Ebx; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 4

  method! get_description = "64 bit division and remainder"

end

let _ = H.add table "alldvrm" (new alldvrm_semantics_t)

(* =========================================================== __allmul__(A,B,C,D)
   example: V02c:0x40db20

  0x40db20  [ 0 ]    mov eax, 0x8(esp,,1)   eax := arg.0008 = arg.0008_in
  0x40db24  [ 0 ]    mov ecx, 0x10(esp,,1)  ecx := arg.0016 = arg.0016_in
  0x40db28  [ 0 ]    or ecx, eax            ecx := ecx | eax
  0x40db2a  [ 0 ]    mov ecx, 0xc(esp,,1)   ecx := arg.0012 = arg.0012_in
  0x40db2e  [ 0 ]    jnz 0x40db39           if ((arg.0016_in != 0) or (arg.0008_in != 0))
                                              then goto 0x40db39
--------------------------------------------------------------------------------
  0x40db30  [ 0 ]    mov eax, 0x4(esp,,1)   eax := arg.0004 = arg.0004_in
  0x40db34  [ 0 ]    mul ecx                edx_eax := eax * ecx =
                                                (arg.0004_in * arg.0012_in) (unsigned)
  0x40db36  [ 0 ]    ret 16                 return (increment stackpointer by 16)
--------------------------------------------------------------------------------
  0x40db39  [ 0 ]    push ebx               save ebx
  0x40db3a  [ -4 ]   mul ecx                edx_eax := eax * ecx =
                                                (arg.0008_in * arg.0012_in) (unsigned)
  0x40db3c  [ -4 ]   mov ebx, eax           ebx := eax
  0x40db3e  [ -4 ]   mov eax, 0x8(esp,,1)   eax := arg.0004 = arg.0004_in
  0x40db42  [ -4 ]   mul 0x14(esp,,1)       edx_eax := eax * arg.0016 =
                                                (arg.0004_in * arg.0016_in) (unsigned)
  0x40db46  [ -4 ]   add ebx, eax           ebx := ebx + eax
  0x40db48  [ -4 ]   mov eax, 0x8(esp,,1)   eax := arg.0004 = arg.0004_in
  0x40db4c  [ -4 ]   mul ecx                edx_eax := eax * ecx =
                                                (arg.0004_in * arg.0012_in) (unsigned)
  0x40db4e  [ -4 ]   add edx, ebx           edx := edx + ebx
  0x40db50  [ -4 ]   pop ebx                restore ebx
  0x40db51  [ 0 ]    ret 16                 return (increment stackpointer by 16)

*)
class allmul_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__allmul__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let arg4 = get_arg args 4 floc in
    LBLOCK [
        STR "__allmul("; xpr_to_pretty floc arg1;
	STR ","; xpr_to_pretty floc arg2;
	STR ","; xpr_to_pretty floc arg3;
	STR ","; xpr_to_pretty floc arg4; STR ") (adj 16)"]

  method! get_commands (floc:floc_int) =
    let cmds1 = get_adjustment_commands 16 floc in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ebx; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 4

  method! get_description = "64 bit multiplication"

end

let _ = H.add table "allmul" (new allmul_semantics_t)


(* ============================================================== __allrem__
   example: V03be08:0x4094e0
   md5hash: 1661afbabd6431a8181f385f68edb67e

  0x4094e0   [ 0 ]    push ebx                  save ebx
  0x4094e1   [ -4 ]   push edi                  save edi
  0x4094e2   [ -8 ]   xor edi, edi              edi := 0
  0x4094e4   [ -8 ]   mov eax, 0x10(esp,,1)     eax := arg.0008 = arg.0008_in
  0x4094e8   [ -8 ]   or eax, eax               eax := eax | eax
  0x4094ea   [ -8 ]   jge 0x409500              if ? then goto 0x409500
--------------------------------------------------------------------------------
  0x4094ec   [ -8 ]   inc edi                   edi := edi + 1 = 1
  0x4094ed   [ -8 ]   mov edx, 0xc(esp,,1)      edx := arg.0004 = arg.0004_in
  0x4094f1   [ -8 ]   neg eax                   eax := 0 - eax
  0x4094f3   [ -8 ]   neg edx                   edx := 0 - edx = (0 - arg.0004_in)
  0x4094f5   [ -8 ]   sbb eax, 0x0              eax := eax - (0 - (0 or 1))
  0x4094f8   [ -8 ]   mov 0x10(esp,,1), eax     arg.0008 := eax
  0x4094fc   [ -8 ]   mov 0xc(esp,,1), edx      arg.0004 := edx = (0 - arg.0004_in)
--------------------------------------------------------------------------------
  0x409500   [ -8 ]   mov eax, 0x18(esp,,1)     eax := arg.0016 = arg.0016_in
  0x409504   [ -8 ]   or eax, eax               eax := eax | eax
  0x409506   [ -8 ]   jge 0x40951b              if ? then goto 0x40951b
--------------------------------------------------------------------------------
  0x409508   [ -8 ]   mov edx, 0x14(esp,,1)     edx := arg.0012 = arg.0012_in
  0x40950c   [ -8 ]   neg eax                   eax := 0 - eax
  0x40950e   [ -8 ]   neg edx                   edx := 0 - edx = (0 - arg.0012_in)
  0x409510   [ -8 ]   sbb eax, 0x0              eax := eax - (0 - (0 or 1))
  0x409513   [ -8 ]   mov 0x18(esp,,1), eax     arg.0016 := eax
  0x409517   [ -8 ]   mov 0x14(esp,,1), edx     arg.0012 := edx = (0 - arg.0012_in)
--------------------------------------------------------------------------------
  0x40951b   [ -8 ]   or eax, eax               eax := eax | eax
  0x40951d   [ -8 ]   jnz 0x40953a              if (eax_val@_0x40951b_@_0x40951d != 0) then goto 0x40953a
--------------------------------------------------------------------------------
  0x40951f   [ -8 ]   mov ecx, 0x14(esp,,1)     ecx := arg.0012
  0x409523   [ -8 ]   mov eax, 0x10(esp,,1)     eax := arg.0008
  0x409527   [ -8 ]   xor edx, edx              edx := 0
  0x409529   [ -8 ]   div ecx                   (eax,edx) = eax / ecx (unsigned)
  0x40952b   [ -8 ]   mov eax, 0xc(esp,,1)      eax := arg.0004
  0x40952f   [ -8 ]   div ecx                   (eax,edx) = edx_eax / ecx (unsigned)
  0x409531   [ -8 ]   mov eax, edx              eax := edx
  0x409533   [ -8 ]   xor edx, edx              edx := 0
  0x409535   [ -8 ]   dec edi                   edi := edi - 1
  0x409536   [ -8 ]   jns 0x409586              if (edi > 0) then goto 0x409586
--------------------------------------------------------------------------------
  0x409538   [ -8 ]   jmp 0x40958d              goto 0x40958d
--------------------------------------------------------------------------------
  0x40953a   [ -8 ]   mov ebx, eax              ebx := eax
  0x40953c   [ -8 ]   mov ecx, 0x14(esp,,1)     ecx := arg.0012
  0x409540   [ -8 ]   mov edx, 0x10(esp,,1)     edx := arg.0008
  0x409544   [ -8 ]   mov eax, 0xc(esp,,1)      eax := arg.0004
--------------------------------------------------------------------------------
  0x409548   [ -8 ]   shr ebx, 0x1              ebx := ebx / 2
  0x40954a   [ -8 ]   rcr ecx, 0x1              ecx := rotate_right(CF,ecx) by 1
  0x40954c   [ -8 ]   shr edx, 0x1              edx := edx / 2
  0x40954e   [ -8 ]   rcr eax, 0x1              eax := rotate_right(CF,eax) by 1
  0x409550   [ -8 ]   or ebx, ebx               ebx := ebx | ebx
  0x409552   [ -8 ]   jnz 0x409548              if (ebx_val@_0x409550_@_0x409552 != 0) then goto 0x409548
--------------------------------------------------------------------------------
  0x409554   [ -8 ]   div ecx                   (eax,edx) = edx_eax / ecx (unsigned)
  0x409556   [ -8 ]   mov ecx, eax              ecx := eax
  0x409558   [ -8 ]   mul 0x18(esp,,1)          edx_eax := eax * arg.0016 (unsigned)
  0x40955c   [ -8 ]   xchg eax, ecx             tmp := ecx; ecx := eax; eax := tmp
  0x40955d   [ -8 ]   mul 0x14(esp,,1)          edx_eax := eax * arg.0012 (unsigned)
  0x409561   [ -8 ]   add edx, ecx              edx := edx + ecx
  0x409563   [ -8 ]   jc 0x409573               if ? then goto 0x409573
--------------------------------------------------------------------------------
  0x409565   [ -8 ]   cmp edx, 0x10(esp,,1)     cmp edx, 0x10(esp,,1)
  0x409569   [ -8 ]   ja 0x409573               if (edx > arg.0008) then goto 0x409573
--------------------------------------------------------------------------------
  0x40956b   [ -8 ]   jc 0x40957b               if ? then goto 0x40957b
--------------------------------------------------------------------------------
  0x40956d   [ -8 ]   cmp eax, 0xc(esp,,1)      cmp eax, 0xc(esp,,1)
  0x409571   [ -8 ]   jbe 0x40957b              if (eax <= arg.0004) then goto 0x40957b
--------------------------------------------------------------------------------
  0x409573   [ -8 ]   sub eax, 0x14(esp,,1)     eax := eax - arg.0012
  0x409577   [ -8 ]   sbb edx, 0x18(esp,,1)     edx := edx - (arg.0016 - (0 or 1))
--------------------------------------------------------------------------------
  0x40957b   [ -8 ]   sub eax, 0xc(esp,,1)      eax := eax - arg.0004
  0x40957f   [ -8 ]   sbb edx, 0x10(esp,,1)     edx := edx - (arg.0008 - (0 or 1))
  0x409583   [ -8 ]   dec edi                   edi := edi - 1
  0x409584   [ -8 ]   jns 0x40958d              if (edi > 0) then goto 0x40958d
--------------------------------------------------------------------------------
  0x409586   [ -8 ]   neg edx                   edx := 0 - edx
  0x409588   [ -8 ]   neg eax                   eax := 0 - eax
  0x40958a   [ -8 ]   sbb edx, 0x0              edx := edx - (0 - (0 or 1))
--------------------------------------------------------------------------------
  0x40958d   [ -8 ]   pop edi                   restore edi
  0x40958e   [ -4 ]   pop ebx                   restore ebx
  0x40958f   [ 0 ]    ret 16                    return (increment stackpointer by 16)
*)
class allrem_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__allrem__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let arg4 = get_arg args 4 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1;
	STR ","; xpr_to_pretty floc arg2;
	STR ","; xpr_to_pretty floc arg3;
	STR ","; xpr_to_pretty floc arg4; STR ") (adj 16)"]

  method! get_commands (floc:floc_int) =
    let cmds1 = get_adjustment_commands 16 floc in
    let cmds2 =
      [floc#get_abstract_cpu_registers_command [Eax; Ebx; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 4

  method! get_description = "64 bit remainder"

end

let _ = H.add table "allrem" (new allrem_semantics_t)



(* ========================================================= __allshl(eax,edx,cl)
   example: putty:0x44bd80
   md5hash: 86aee56a335d8d457990da457cbb4642

  0x44bd80   [ 0 ]    cmp cl, 0x40              cmp cl, 0x40
  0x44bd83   [ 0 ]    jnc 0x44bd9a              if (cl >= 64) then goto 0x44bd9a
--------------------------------------------------------------------------------
  0x44bd85   [ 0 ]    cmp cl, 0x20              cmp cl, 0x20
  0x44bd88   [ 0 ]    jnc 0x44bd90              if (cl >= 32) then goto 0x44bd90
--------------------------------------------------------------------------------
  0x44bd8a   [ 0 ]    shld edx, eax, cl         shld edx, eax, cl
  0x44bd8d   [ 0 ]    shl eax, cl               eax := eax << cl
  0x44bd8f   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x44bd90   [ 0 ]    mov edx, eax              edx := eax = eax_in
  0x44bd92   [ 0 ]    xor eax, eax              eax := 0
  0x44bd94   [ 0 ]    and cl, 0x1f              cl := cl & 31
  0x44bd97   [ 0 ]    shl edx, cl               edx := edx << cl
  0x44bd99   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x44bd9a   [ 0 ]    xor eax, eax              eax := 0
  0x44bd9c   [ 0 ]    xor edx, edx              edx := 0
  0x44bd9e   [ 0 ]    ret                       return
*)
class allshl_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__allshl__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(eax:"; xpr_to_pretty floc eaxv;
	STR ",edx:"; xpr_to_pretty floc edxv;
	STR ",ecx:"; xpr_to_pretty floc ecxv; STR ")"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 0

  method! get_description = "64 bit left shift"

end

let _ = H.add table "allshl" (new allshl_semantics_t)


(* =============================================================== allshr ==
   example: V102:0x41d000
   md5hash: 238b0ab55789e99faaf18e055db162b0

  0x41d000   [ 0 ]    cmp cl, 0x40              cmp cl, 0x40
  0x41d003   [ 0 ]    jnc 0x41d01b              if (cl >= 64) then goto 0x41d01b
--------------------------------------------------------------------------------
  0x41d005   [ 0 ]    cmp cl, 0x20              cmp cl, 0x20
  0x41d008   [ 0 ]    jnc 0x41d010              if (cl >= 32) then goto 0x41d010
--------------------------------------------------------------------------------
  0x41d00a   [ 0 ]    shrd eax, edx, cl         shrd eax, edx, cl
  0x41d00d   [ 0 ]    sar edx, cl               edx := edx >> cl
  0x41d00f   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x41d010   [ 0 ]    mov eax, edx              eax := edx = edx_in
  0x41d012   [ 0 ]    sar edx, 0x1f             edx := edx / 2147483648
  0x41d015   [ 0 ]    and cl, 0x1f              cl := cl & 31
  0x41d018   [ 0 ]    sar eax, cl               eax := eax >> cl
  0x41d01a   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x41d01b   [ 0 ]    sar edx, 0x1f             edx := edx / 2147483648
  0x41d01e   [ 0 ]    mov eax, edx              eax := edx
  0x41d020   [ 0 ]    ret                       return
*)
class allshr_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__allshr__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [
        STR self#get_name; STR "(eax:"; xpr_to_pretty floc eaxv;
	STR ",edx:"; xpr_to_pretty floc edxv;
	STR ",ecx:"; xpr_to_pretty floc ecxv; STR ")"]

  method! get_commands (floc:floc_int) =
    [floc#get_abstract_cpu_registers_command [Eax; Ecx; Edx]]

  method get_parametercount = 0

  method! get_description = "64 bit right shift"

end

let _ = H.add table "allshr" (new allshr_semantics_t)


(* ========================================================= __aulldiv__(A,B,C,D)
   example: V02c:0x40b7f0

  0x40b7f0  [ 0 ]       push ebx                  save ebx
  0x40b7f1  [ -4 ]      push esi                  save esi
  0x40b7f2  [ -8 ]      mov eax, 0x18(esp,,1)     eax := arg.0016 = arg.0016_in
  0x40b7f6  [ -8 ]      or eax, eax               eax := eax | eax
  0x40b7f8  [ -8 ]      jnz 0x40b812              if (arg.0016_in != 0) then goto 0x40b812
--------------------------------------------------------------------------------
  0x40b7fa  [ -8 ]      mov ecx, 0x14(esp,,1)     ecx := arg.0012 = arg.0012_in
  0x40b7fe  [ -8 ]      mov eax, 0x10(esp,,1)     eax := arg.0008 = arg.0008_in
  0x40b802  [ -8 ]      xor edx, edx              edx := 0
  0x40b804  [ -8 ]      div ecx                   (eax,edx) = eax / ecx =
                                                     (arg.0008_in / arg.0012_in) (unsigned)
  0x40b806  [ -8 ]      mov ebx, eax              ebx := eax
  0x40b808  [ -8 ]      mov eax, 0xc(esp,,1)      eax := arg.0004 = arg.0004_in
  0x40b80c  [ -8 ]      div ecx                   (eax,edx) = edx_eax / ecx =
                                                     (edx_eax / arg.0012_in) (unsigned)
  0x40b80e  [ -8 ]      mov edx, ebx              edx := ebx
  0x40b810  [ -8 ]      jmp 0x40b853              goto 0x40b853
--------------------------------------------------------------------------------
  0x40b812  [ -8 ]      mov ecx, eax              ecx := eax
  0x40b814  [ -8 ]      mov ebx, 0x14(esp,,1)     ebx := arg.0012 = arg.0012_in
  0x40b818  [ -8 ]      mov edx, 0x10(esp,,1)     edx := arg.0008 = arg.0008_in
  0x40b81c  [ -8 ]      mov eax, 0xc(esp,,1)      eax := arg.0004 = arg.0004_in
--------------------------------------------------------------------------------
  0x40b820  [ -8 ]      shr ecx, 0x1              ecx := ecx / 2
  0x40b822  [ -8 ]      rcr ebx, 0x1              ebx := rotate_right(CF,ebx) by 1
  0x40b824  [ -8 ]      shr edx, 0x1              edx := edx / 2
  0x40b826  [ -8 ]      rcr eax, 0x1              eax := rotate_right(CF,eax) by 1
  0x40b828  [ -8 ]      or ecx, ecx               ecx := ecx | ecx
  0x40b82a  [ -8 ]      jnz 0x40b820              if (ecx != 0) then goto 0x40b820
--------------------------------------------------------------------------------
  0x40b82c  [ -8 ]      div ebx                   (eax,edx) = edx_eax / ebx (unsigned)
  0x40b82e  [ -8 ]      mov esi, eax              esi := eax
  0x40b830  [ -8 ]      mul 0x18(esp,,1)          edx_eax := eax * arg.0016 =
                                                     (eax * arg.0016_in) (unsigned)
  0x40b834  [ -8 ]      mov ecx, eax              ecx := eax
  0x40b836  [ -8 ]      mov eax, 0x14(esp,,1)     eax := arg.0012 = arg.0012_in
  0x40b83a  [ -8 ]      mul esi                   edx_eax := eax * esi =
                                                     (arg.0012_in * esi) (unsigned)
  0x40b83c  [ -8 ]      add edx, ecx              edx := edx + ecx
  0x40b83e  [ -8 ]      jc 0x40b84e               if ? then goto 0x40b84e
--------------------------------------------------------------------------------
  0x40b840  [ -8 ]      cmp edx, 0x10(esp,,1)     cmp edx, 0x10(esp,,1)
  0x40b844  [ -8 ]      ja 0x40b84e               if (edx > arg.0008_in) then goto 0x40b84e
--------------------------------------------------------------------------------
  0x40b846  [ -8 ]      jc 0x40b84f               if ? then goto 0x40b84f
--------------------------------------------------------------------------------
  0x40b848  [ -8 ]      cmp eax, 0xc(esp,,1)      cmp eax, 0xc(esp,,1)
  0x40b84c  [ -8 ]      jbe 0x40b84f              if (eax <= arg.0004_in) then goto 0x40b84f
--------------------------------------------------------------------------------
  0x40b84e  [ -8 ]      dec esi                   esi := esi - 1
--------------------------------------------------------------------------------
  0x40b84f  [ -8 ]      xor edx, edx              edx := 0
  0x40b851  [ -8 ]      mov eax, esi              eax := esi
--------------------------------------------------------------------------------
  0x40b853  [ -8 ]      pop esi                   restore esi
  0x40b854  [ -4 ]      pop ebx                   restore ebx
  0x40b855  [ 0 ]       ret 16                    return (increment stackpointer by 16)

*)

class aulldiv_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__aulldiv__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let arg4 = get_arg args 4 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1;
	STR ","; xpr_to_pretty floc arg2;
	STR ","; xpr_to_pretty floc arg3;
	STR ","; xpr_to_pretty floc arg4; STR ") (adj 16)"]

  method! get_commands (floc:floc_int) =
    let cmds1 = get_adjustment_commands 16 floc in
    let cmds2 =
      [floc#get_abstract_cpu_registers_command [Eax; Ebx; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 4

  method! get_description = "64 bit unsigned divide"

end

let _ = H.add table "aulldiv" (new aulldiv_semantics_t)


(* ======================================================= __aulldvrm__(A,B,C,D)
   Example: V0c3

  0x43c9e0   [ 0 ]    push esi                  save esi
  0x43c9e1   [ -4 ]   mov eax, 0x14(esp,,1)     eax := arg.0016 = arg.0016_in
  0x43c9e5   [ -4 ]   or eax, eax               eax := eax | eax
  0x43c9e7   [ -4 ]   jnz 0x43ca11              if (arg.0016_in != 0) then goto 0x43ca11
--------------------------------------------------------------------------------
  0x43c9e9   [ -4 ]   mov ecx, 0x10(esp,,1)     ecx := arg.0012 = arg.0012_in
  0x43c9ed   [ -4 ]   mov eax, 0xc(esp,,1)      eax := arg.0008 = arg.0008_in
  0x43c9f1   [ -4 ]   xor edx, edx              edx := 0
  0x43c9f3   [ -4 ]   div ecx                   (eax,edx) = eax / ecx =
                                                    (arg.0008_in / arg.0012_in) (unsigned)
  0x43c9f5   [ -4 ]   mov ebx, eax              ebx := eax
  0x43c9f7   [ -4 ]   mov eax, 0x8(esp,,1)      eax := arg.0004 = arg.0004_in
  0x43c9fb   [ -4 ]   div ecx                   (eax,edx) = edx_eax / ecx =
                                                    (edx_eax / arg.0012_in) (unsigned)
  0x43c9fd   [ -4 ]   mov esi, eax              esi := eax
  0x43c9ff   [ -4 ]   mov eax, ebx              eax := ebx
  0x43ca01   [ -4 ]   mul 0x10(esp,,1)          edx_eax := eax * arg.0012 =
                                                    (eax * arg.0012_in) (unsigned)
  0x43ca05   [ -4 ]   mov ecx, eax              ecx := eax
  0x43ca07   [ -4 ]   mov eax, esi              eax := esi
  0x43ca09   [ -4 ]   mul 0x10(esp,,1)          edx_eax := eax * arg.0012 =
                                                    (eax * arg.0012_in) (unsigned)
  0x43ca0d   [ -4 ]   add edx, ecx              edx := edx + ecx
  0x43ca0f   [ -4 ]   jmp 0x43ca58              goto 0x43ca58
--------------------------------------------------------------------------------
  0x43ca11   [ -4 ]   mov ecx, eax              ecx := eax
  0x43ca13   [ -4 ]   mov ebx, 0x10(esp,,1)     ebx := arg.0012 = arg.0012_in
  0x43ca17   [ -4 ]   mov edx, 0xc(esp,,1)      edx := arg.0008 = arg.0008_in
  0x43ca1b   [ -4 ]   mov eax, 0x8(esp,,1)      eax := arg.0004 = arg.0004_in
--------------------------------------------------------------------------------
  0x43ca1f   [ -4 ]   shr ecx, 0x1              ecx := ecx / 2
  0x43ca21   [ -4 ]   rcr ebx, 0x1              ebx := rotate_right(CF,ebx) by 1
  0x43ca23   [ -4 ]   shr edx, 0x1              edx := edx / 2
  0x43ca25   [ -4 ]   rcr eax, 0x1              eax := rotate_right(CF,eax) by 1
  0x43ca27   [ -4 ]   or ecx, ecx               ecx := ecx | ecx
  0x43ca29   [ -4 ]   jnz 0x43ca1f              if (ecx != 0) then goto 0x43ca1f
--------------------------------------------------------------------------------
  0x43ca2b   [ -4 ]   div ebx                   (eax,edx) = edx_eax / ebx (unsigned)
  0x43ca2d   [ -4 ]   mov esi, eax              esi := eax
  0x43ca2f   [ -4 ]   mul 0x14(esp,,1)          edx_eax := eax * arg.0016 =
                                                    (eax * arg.0016_in) (unsigned)
  0x43ca33   [ -4 ]   mov ecx, eax              ecx := eax
  0x43ca35   [ -4 ]   mov eax, 0x10(esp,,1)     eax := arg.0012 = arg.0012_in
  0x43ca39   [ -4 ]   mul esi                   edx_eax := eax * esi =
                                                    (arg.0012_in * esi) (unsigned)
  0x43ca3b   [ -4 ]   add edx, ecx              edx := edx + ecx
  0x43ca3d   [ -4 ]   jc 0x43ca4d               if ? then goto 0x43ca4d
--------------------------------------------------------------------------------
  0x43ca3f   [ -4 ]   cmp edx, 0xc(esp,,1)      cmp edx, 0xc(esp,,1)
  0x43ca43   [ -4 ]   ja 0x43ca4d               if (edx > arg.0008_in) then goto 0x43ca4d
--------------------------------------------------------------------------------
  0x43ca45   [ -4 ]   jc 0x43ca56               if ? then goto 0x43ca56
--------------------------------------------------------------------------------
  0x43ca47   [ -4 ]   cmp eax, 0x8(esp,,1)      cmp eax, 0x8(esp,,1)
  0x43ca4b   [ -4 ]   jbe 0x43ca56              if (eax <= arg.0004_in) then goto 0x43ca56
--------------------------------------------------------------------------------
  0x43ca4d   [ -4 ]   dec esi                   esi := esi - 1
  0x43ca4e   [ -4 ]   sub eax, 0x10(esp,,1)     eax := eax - arg.0012 = (eax - arg.0012_in)
  0x43ca52   [ -4 ]   sbb edx, 0x14(esp,,1)     edx := edx - (arg.0016 - (0 or 1))
--------------------------------------------------------------------------------
  0x43ca56   [ -4 ]   xor ebx, ebx              ebx := 0
--------------------------------------------------------------------------------
  0x43ca58   [ -4 ]   sub eax, 0x8(esp,,1)      eax := eax - arg.0004 = (eax - arg.0004_in)
  0x43ca5c   [ -4 ]   sbb edx, 0xc(esp,,1)      edx := edx - (arg.0008 - (0 or 1))
  0x43ca60   [ -4 ]   neg edx                   edx := 0 - edx
  0x43ca62   [ -4 ]   neg eax                   eax := 0 - eax
  0x43ca64   [ -4 ]   sbb edx, 0x0              edx := edx - (0 - (0 or 1))
  0x43ca67   [ -4 ]   mov ecx, edx              ecx := edx
  0x43ca69   [ -4 ]   mov edx, ebx              edx := ebx
  0x43ca6b   [ -4 ]   mov ebx, ecx              ebx := ecx
  0x43ca6d   [ -4 ]   mov ecx, eax              ecx := eax
  0x43ca6f   [ -4 ]   mov eax, esi              eax := esi
  0x43ca71   [ -4 ]   pop esi                   restore esi
  0x43ca72   [ 0 ]    ret 16                    return (increment stackpointer by 16)

*)

class aulldvrm_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__aulldvrm__"

  method! get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    let arg4 = get_arg args 4 floc in
    LBLOCK [
        STR self#get_name; STR "("; xpr_to_pretty floc arg1;
	STR ","; xpr_to_pretty floc arg2;
	STR ","; xpr_to_pretty floc arg3;
	STR ","; xpr_to_pretty floc arg4; STR ") (adj 16)"]

  method! get_commands (floc:floc_int) =
    let cmds1 = get_adjustment_commands 16 floc in
    let cmds2 =
      [floc#get_abstract_cpu_registers_command [Eax; Ebx; Ecx; Edx]] in
    List.concat [cmds1; cmds2]

  method get_parametercount = 4

  method! get_description = "64 bit unsigned divide and remainder"

end

let _ = H.add table "aulldvrm" (new aulldvrm_semantics_t)


(* ==================================================== __aullshr__(eax,edx,cl)
   example: Vb4b:0x409cc0

  0x409cc0   [ 0 ]    cmp cl, 0x40           cmp cl, 0x40
  0x409cc3   [ 0 ]    jnc 0x409cda           if (cl >= 64) then goto 0x409cda
--------------------------------------------------------------------------------
  0x409cc5   [ 0 ]    cmp cl, 0x20           cmp cl, 0x20
  0x409cc8   [ 0 ]    jnc 0x409cd0           if (cl >= 32) then goto 0x409cd0
--------------------------------------------------------------------------------
  0x409cca   [ 0 ]    shrd eax, edx, cl      shrd eax, edx, cl
  0x409ccd   [ 0 ]    shr edx, cl            edx := edx >> cl
  0x409ccf   [ 0 ]    ret                    return
--------------------------------------------------------------------------------
  0x409cd0   [ 0 ]    mov eax, edx           eax := edx = edx_in
  0x409cd2   [ 0 ]    xor edx, edx           edx := 0
  0x409cd4   [ 0 ]    and cl, 0x1f           cl := cl & 31
  0x409cd7   [ 0 ]    shr eax, cl            eax := eax >> cl
  0x409cd9   [ 0 ]    ret                    return
--------------------------------------------------------------------------------
  0x409cda   [ 0 ]    xor eax, eax           eax := 0
  0x409cdc   [ 0 ]    xor edx, edx           edx := 0
  0x409cde   [ 0 ]    ret                    return

*)

class aullshr_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__aullshr__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [ STR self#get_name; STR "(eax:"; xpr_to_pretty floc eaxv;
	     STR ",edx:"; xpr_to_pretty floc edxv;
	     STR ",ecx:"; xpr_to_pretty floc ecxv; STR ")" ]

  method! get_commands (floc:floc_int) =
    [ floc#get_abstract_cpu_registers_command [ Eax; Ecx; Edx ] ]

  method get_parametercount = 0

  method! get_description = "unsigned 64 bit right shift"

end

let _ = H.add table "aullshr" (new aullshr_semantics_t)


let edk64_functions = H.fold (fun k v a -> a @ (get_fnhashes k v)) table []
