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
open BCHVariableType

(* bchlibx86 *)
open BCHLibx86Types
open BCHPredefinedUtil

module H = Hashtbl

let table = H.create 17

let load_str_functions () =
  begin
    List.iter (fun m -> add_dllfun table "msvcrt.dll" m)
      [ "strcat" ; "strchr" ; "strcmp" ; "strcpy" ; "strcspn" ; "strlen" ;
	"strncat" ; "strncmp" ; "_strncnt" ; "strncpy" ; "strnlen" ; "strpbrk" ;
	"strrchr" ; "strstr" ; "strspn" ] ;
    List.iter (fun m -> add_dllfun table "kernel32.dll" m)
      [ "lstrcpyn" ]
  end

(* ============================================================= ascii_stricmp
   example: V03be08:0x40b1e0
   md5hash: b7d09b2b5fe193689c79b65e5c675823

  0x40b1e0   [ 0 ]    push ebp                  save ebp
  0x40b1e1   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x40b1e3   [ -4 ]   push edi                  save edi
  0x40b1e4   [ -8 ]   push esi                  save esi
  0x40b1e5  [ -12 ]   push ebx                  save ebx
  0x40b1e6  [ -16 ]   mov esi, 0xc(ebp)         esi := arg.0008 = arg.0008_in
  0x40b1e9  [ -16 ]   mov edi, 0x8(ebp)         edi := arg.0004 = arg.0004_in
  0x40b1ec  [ -16 ]   mov al, -0x1              al := -1
  0x40b1ee  [ -16 ]   mov edi, edi              nop
--------------------------------------------------------------------------------
  0x40b1f0  [ -16 ]   or al, al                 al := al | al
  0x40b1f2  [ -16 ]   jz 0x40b226               if (al_val@_0x40b1f0_@_0x40b1f2 = 0) then goto 0x40b226
--------------------------------------------------------------------------------
  0x40b1f4  [ -16 ]   mov al, (esi)             al :=  ?  (tmpN)
  0x40b1f6  [ -16 ]   add esi, 0x1              esi := esi + 1
  0x40b1f9  [ -16 ]   mov ah, (edi)             ah :=  ?  (tmpN)
  0x40b1fb  [ -16 ]   add edi, 0x1              edi := edi + 1
  0x40b1fe  [ -16 ]   cmp ah, al                cmp ah, al
  0x40b200  [ -16 ]   jz 0x40b1f0               if (ah = al) then goto 0x40b1f0
--------------------------------------------------------------------------------
  0x40b202  [ -16 ]   sub al, 0x41              al := al - 65
  0x40b204  [ -16 ]   cmp al, 0x1a              cmp al, 0x1a
  0x40b206  [ -16 ]   sbb cl, cl                cl := 0 or -1
  0x40b208  [ -16 ]   and cl, 0x20              cl := cl & 32
  0x40b20b  [ -16 ]   add al, cl                al := al + cl
  0x40b20d  [ -16 ]   add al, 0x41              al := al + 65
  0x40b20f  [ -16 ]   xchg al, ah               tmp := ah; ah := al; al := tmp
  0x40b211  [ -16 ]   sub al, 0x41              al := al - 65
  0x40b213  [ -16 ]   cmp al, 0x1a              cmp al, 0x1a
  0x40b215  [ -16 ]   sbb cl, cl                cl := 0 or -1
  0x40b217  [ -16 ]   and cl, 0x20              cl := cl & 32
  0x40b21a  [ -16 ]   add al, cl                al := al + cl
  0x40b21c  [ -16 ]   add al, 0x41              al := al + 65
  0x40b21e  [ -16 ]   cmp al, ah                cmp al, ah
  0x40b220  [ -16 ]   jz 0x40b1f0               if (al = ah) then goto 0x40b1f0
--------------------------------------------------------------------------------
  0x40b222  [ -16 ]   sbb al, al                al := 0 or -1
  0x40b224  [ -16 ]   sbb al, -0x1              al := al - (-1 - (0 or 1))
--------------------------------------------------------------------------------
  0x40b226  [ -16 ]   movsx eax, al             eax := al
  0x40b229  [ -16 ]   pop ebx                   restore ebx
  0x40b22a  [ -12 ]   pop esi                   restore esi
  0x40b22b   [ -8 ]   pop edi                   restore edi
  0x40b22c   [ -4 ]   leave                     esp := ebp ; ebp := var.0004 ; esp := esp + 4 
  0x40b22d   [ 0 ]    ret                       return
*)
class ascii_stricmp_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__ascii_stricmp__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(s1:" ; xpr_to_strpretty floc arg1 ;
	     STR ",s2:" ; xpr_to_strpretty floc arg2 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands lhs ~vtype:t_char (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    List.concat [ lhscmds ; cmds1 ; cmds2 ]

  method get_parametercount = 2 

  method get_call_target (a:doubleword_int) =
    mk_static_dll_stub_target a "msvcrt.dll" "_stricmp"

  method get_description = "stricmp library function"

end

let _ = H.add table "ascii_stricmp" (new ascii_stricmp_semantics_t)

(* ============================================================= ascii_strnicmp
   example: V02c:04081a0
   md5hash: 20b7f8fee14db3a23a80237e8274ddaf

  0x4081a0   [ 0 ]    push ebp              save ebp
  0x4081a1   [ -4 ]   mov ebp, esp          ebp := esp = (esp_in - 4)
  0x4081a3   [ -4 ]   push edi              save edi
  0x4081a4   [ -8 ]   push esi              save esi
  0x4081a5  [ -12 ]   push ebx              save ebx
  0x4081a6  [ -16 ]   mov ecx, 0x10(ebp)    ecx := arg.0012 = arg.0012_in
  0x4081a9  [ -16 ]   or ecx, ecx           ecx := ecx | ecx
  0x4081ab  [ -16 ]   jz 0x4081fa           if (arg.0012_in = 0) then goto 0x4081fa
--------------------------------------------------------------------------------
  0x4081ad  [ -16 ]   mov esi, 0x8(ebp)     esi := arg.0004 = arg.0004_in
  0x4081b0  [ -16 ]   mov edi, 0xc(ebp)     edi := arg.0008 = arg.0008_in
  0x4081b3  [ -16 ]   mov bh, 0x41          bh := 65
  0x4081b5  [ -16 ]   mov bl, 0x5a          bl := 90
  0x4081b7  [ -16 ]   mov dh, 0x20          dh := 32
  0x4081b9  [ -16 ]   lea ecx, (ecx)        ecx := ecx
--------------------------------------------------------------------------------
  0x4081bc  [ -16 ]   mov ah, (esi)         ah :=  ?  (tmpN)
  0x4081be  [ -16 ]   or ah, ah             ah := ah | ah
  0x4081c0  [ -16 ]   mov al, (edi)         al :=  ?  (tmpN)
  0x4081c2  [ -16 ]   jz 0x4081eb           if (ah = 0) then goto 0x4081eb
--------------------------------------------------------------------------------
  0x4081c4  [ -16 ]   or al, al             al := al | al
  0x4081c6  [ -16 ]   jz 0x4081eb           if (al = 0) then goto 0x4081eb
--------------------------------------------------------------------------------
  0x4081c8  [ -16 ]   add esi, 0x1          esi := esi + 1
  0x4081cb  [ -16 ]   add edi, 0x1          edi := edi + 1
  0x4081ce  [ -16 ]   cmp ah, bh            cmp ah, bh
  0x4081d0  [ -16 ]   jc 0x4081d8           if (ah < 65) then goto 0x4081d8
--------------------------------------------------------------------------------
  0x4081d2  [ -16 ]   cmp ah, bl            cmp ah, bl
  0x4081d4  [ -16 ]   ja 0x4081d8           if (ah > 90) then goto 0x4081d8
--------------------------------------------------------------------------------
  0x4081d6  [ -16 ]   add ah, dh            ah := ah + dh = (ah + 32)
--------------------------------------------------------------------------------
  0x4081d8  [ -16 ]   cmp al, bh            cmp al, bh
  0x4081da  [ -16 ]   jc 0x4081e2           if (al < 65) then goto 0x4081e2
--------------------------------------------------------------------------------
  0x4081dc  [ -16 ]   cmp al, bl            cmp al, bl
  0x4081de  [ -16 ]   ja 0x4081e2           if (al > 90) then goto 0x4081e2
--------------------------------------------------------------------------------
  0x4081e0  [ -16 ]   add al, dh            al := al + dh = (al + 32)
--------------------------------------------------------------------------------
  0x4081e2  [ -16 ]   cmp ah, al            cmp ah, al
  0x4081e4  [ -16 ]   jnz 0x4081f1          if (ah != al) then goto 0x4081f1
--------------------------------------------------------------------------------
  0x4081e6  [ -16 ]   sub ecx, 0x1          ecx := ecx - 1
  0x4081e9  [ -16 ]   jnz 0x4081bc          if (1 != ecx) then goto 0x4081bc
--------------------------------------------------------------------------------
  0x4081eb  [ -16 ]   xor ecx, ecx          ecx := 0 
  0x4081ed  [ -16 ]   cmp ah, al            cmp ah, al
  0x4081ef  [ -16 ]   jz 0x4081fa           if (ah = al) then goto 0x4081fa
--------------------------------------------------------------------------------
  0x4081f1  [ -16 ]   mov ecx, 0xffffffff   ecx := 4294967295
  0x4081f6  [ -16 ]   jc 0x4081fa           if ? then goto 0x4081fa
--------------------------------------------------------------------------------
  0x4081f8  [ -16 ]   neg ecx               ecx := 0 - ecx = -4294967295
--------------------------------------------------------------------------------
  0x4081fa  [ -16 ]   mov eax, ecx          eax := ecx
  0x4081fc  [ -16 ]   pop ebx               restore ebx
  0x4081fd  [ -12 ]   pop esi               restore esi
  0x4081fe   [ -8 ]   pop edi               restore edi
  0x4081ff   [ -4 ]   leave                 esp := ebp ; ebp := var.0004 ; esp := esp + 4 
  0x408200   [ 0 ]    ret                   return
*)

class ascii_strnicmp_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__ascii_strnicmp__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [ STR self#get_name ; STR "(s1:" ; xpr_to_strpretty floc arg1 ;
	     STR ",s2:" ; xpr_to_strpretty floc arg2 ;
	     STR ",count:" ; xpr_to_pretty floc arg3 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands lhs ~vtype:t_int (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    List.concat [ lhscmds ; cmds1 ; cmds2 ]

  method get_parametercount = 3 

  method get_call_target (a:doubleword_int) =
    mk_static_dll_stub_target a "msvcrt.dll" "_strnicmp"

  method get_description = "compares two strings"

end

let _ = H.add table "ascii_strnicmp" (new ascii_strnicmp_semantics_t)

	       
let libstr_functions () = H.fold (fun k v a -> a @ (get_fnhashes k v)) table []
