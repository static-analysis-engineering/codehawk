(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open BCHLibTypes
open BCHMakeCallTargetInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHPredefinedUtil
open BCHVariableType

module H = Hashtbl

let table = H.create 11

let load_wcs_functions () =
  List.iter (fun m -> add_dllfun table "msvcrt.dll" m)
    [ "wcscat" ; "wcschr" ; "wcscpy" ; "wcscspn" ; "wcslen" ; "wcsnlen" ; "wcsncat" ; 
      "wcsncmp"; "wcspbrk" ; "wcsstr"; "wcscmp"; "wcsncpy" ; "wcsrchr" ; "wcsspn" ]

(* ============================================================= wcsnicmp_ascii
   example: V3fc:0x40a5c6
   md5hash: 80cd08aa5a259f87cfacbc0f14dde29e

  0x40a5c6   [ 0 ]    push ebp                  save ebp
  0x40a5c7   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x40a5c9   [ -4 ]   push esi                  save esi
  0x40a5ca   [ -8 ]   mov esi, 0x10(ebp)        esi := arg.0012 = arg.0012_in
  0x40a5cd   [ -8 ]   xor eax, eax              eax := 0 
  0x40a5cf   [ -8 ]   test esi, esi             test esi, esi
  0x40a5d1   [ -8 ]   jz 0x40a631               if (arg.0012_in = 0) then goto 0x40a631
--------------------------------------------------------------------------------
  0x40a5d3   [ -8 ]   mov ecx, 0xc(ebp)         ecx := arg.0008 = arg.0008_in
  0x40a5d6   [ -8 ]   push ebx                  save ebx
  0x40a5d7  [ -12 ]   push edi                  save edi
  0x40a5d8  [ -16 ]   mov edi, 0x8(ebp)         edi := arg.0004 = arg.0004_in
  0x40a5db  [ -16 ]   push 0x41                 esp := esp - 4 ; var.0020 := 65
  0x40a5dd  [ -20 ]   pop ebx                   ebx := 65 ; esp := esp + 4 = (esp_in - 16)
  0x40a5de  [ -16 ]   push 0x5a                 esp := esp - 4 ; var.0020 := 90
  0x40a5e0  [ -20 ]   pop edx                   edx := 90 ; esp := esp + 4 = (esp_in - 16)
  0x40a5e1  [ -16 ]   sub edi, ecx              edi := edi - ecx = (arg.0004_in - arg.0008_in)
  0x40a5e3  [ -16 ]   mov 0x10(ebp), edx        arg.0012 := edx = 90
  0x40a5e6  [ -16 ]   jmp 0x40a5eb              goto 0x40a5eb
--------------------------------------------------------------------------------
  0x40a5e8  [ -16 ]   push 0x5a                 esp := esp - 4 ; var.0020 := 90
  0x40a5ea  [ -20 ]   pop edx                   edx := 90 ; esp := esp + 4 = (esp_in - 16)
--------------------------------------------------------------------------------
  0x40a5eb  [ -16 ]   movzx eax, (edi,ecx,1)    eax :=  ?  (tmpN)
  0x40a5ef  [ -16 ]   cmp ax, bx                cmp ax, bx
  0x40a5f2  [ -16 ]   jc 0x40a601               if (ax < bx) then goto 0x40a601
--------------------------------------------------------------------------------
  0x40a5f4  [ -16 ]   cmp ax, dx                cmp ax, dx
  0x40a5f7  [ -16 ]   ja 0x40a601               if (ax > dx) then goto 0x40a601
--------------------------------------------------------------------------------
  0x40a5f9  [ -16 ]   add eax, 0x20             eax := eax + 32
  0x40a5fc  [ -16 ]   movzx edx, ax             edx := ax
  0x40a5ff  [ -16 ]   jmp 0x40a603              goto 0x40a603
--------------------------------------------------------------------------------
  0x40a601  [ -16 ]   mov edx, eax              edx := eax
--------------------------------------------------------------------------------
  0x40a603  [ -16 ]   movzx eax, (ecx)          eax :=  ?  (tmpN)
  0x40a606  [ -16 ]   cmp ax, bx                cmp ax, bx
  0x40a609  [ -16 ]   jc 0x40a617               if (ax < bx) then goto 0x40a617
--------------------------------------------------------------------------------
  0x40a60b  [ -16 ]   cmp ax, 0x10(ebp)         cmp ax, 0x10(ebp)
  0x40a60f  [ -16 ]   ja 0x40a617               if (ax > 90) then goto 0x40a617
--------------------------------------------------------------------------------
  0x40a611  [ -16 ]   add eax, 0x20             eax := eax + 32
  0x40a614  [ -16 ]   movzx eax, ax             eax := ax
--------------------------------------------------------------------------------
  0x40a617  [ -16 ]   add ecx, 0x2              ecx := ecx + 2
  0x40a61a  [ -16 ]   dec esi                   esi := esi - 1
  0x40a61b  [ -16 ]   jz 0x40a627               if (esi = 1) then goto 0x40a627
--------------------------------------------------------------------------------
  0x40a61d  [ -16 ]   test dx, dx               test dx, dx
  0x40a620  [ -16 ]   jz 0x40a627               if (dx = 0) then goto 0x40a627
--------------------------------------------------------------------------------
  0x40a622  [ -16 ]   cmp dx, ax                cmp dx, ax
  0x40a625  [ -16 ]   jz 0x40a5e8               if (dx = ax) then goto 0x40a5e8
--------------------------------------------------------------------------------
  0x40a627  [ -16 ]   movzx ecx, ax             ecx := ax
  0x40a62a  [ -16 ]   movzx eax, dx             eax := dx
  0x40a62d  [ -16 ]   pop edi                   restore edi
  0x40a62e  [ -12 ]   sub eax, ecx              eax := eax - ecx
  0x40a630  [ -12 ]   pop ebx                   restore ebx
--------------------------------------------------------------------------------
  0x40a631   [ -8 ]   pop esi                   restore esi
  0x40a632   [ -4 ]   pop ebp                   restore ebp
  0x40a633   [ 0 ]    ret                       return
*)
class wcsnicmp_ascii_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wcsnicmp_ascii__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [ STR self#get_name ; STR "(str1:" ; xpr_to_strpretty floc arg1 ;
	     STR ",str2:" ; xpr_to_strpretty floc arg2 ;
	     STR ",count:" ; xpr_to_pretty floc arg3 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands eaxlhs ~vtype:t_int (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    eaxlhscmds @ cmds1 @ cmds2

  method get_parametercount = 3

  method get_call_target (a:doubleword_int) =
    mk_static_dll_stub_target a "msvcrt.dll" "_wcsnicmp"

  method get_description = "compares two string"

end

let _ = H.add table "wcsnicmp_ascii" (new wcsnicmp_ascii_semantics_t)

let libwcs_functions () = H.fold (fun k v a -> a @ (get_fnhashes k v)) table []

