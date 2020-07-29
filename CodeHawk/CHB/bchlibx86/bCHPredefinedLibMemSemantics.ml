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
open XprTypes

(* bchlib *)
open BCHFloc
open BCHFunctionData
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHMakeCallTargetInfo
open BCHSystemInfo
open BCHVariableType

(* bchlibx86 *)
open BCHFunctionHashes
open BCHLibx86Types
open BCHLocation
open BCHPredefinedUtil

module H = Hashtbl
(*
  memcmp()
  memcpy()
  memmove_r()
  memset()
  wmemset()
*)

let table = H.create 11

let load_mem_functions () =
  List.iter (fun m -> add_dllfun table "pe-vs-static" m) 
            [ "memchr0" ; "memchr"; "memcmp" ; "memcpy" ; "memmove" ;
              "memset" ; "memset0"; "wmemset" ]



(* ================================================================== memcpy_r
   example: V9da:0x401030
   md5hash: c0605f9b9904b351841d7a5c2b26d44e

  0x401030   [ 0 ]    push esi                  save esi
  0x401031   [ -4 ]   mov esi, 0x8(esp,,1)      esi := arg.0004 = arg.0004_in
  0x401035   [ -4 ]   jmp 0x40103e              goto 0x40103e
--------------------------------------------------------------------------------
  0x401037   [ -4 ]   mov al, (edx)             al :=  ?  (tmpN)
  0x401039   [ -4 ]   inc edx                   edx := edx + 1
  0x40103a   [ -4 ]   mov (ecx), al             ? := al
  0x40103c   [ -4 ]   dec esi                   esi := esi - 1
  0x40103d   [ -4 ]   inc ecx                   ecx := ecx + 1
--------------------------------------------------------------------------------
  0x40103e   [ -4 ]   test esi, esi             test esi, esi
  0x401040   [ -4 ]   ja 0x401037               if (esi != 0) then goto 0x401037
--------------------------------------------------------------------------------
  0x401042   [ -4 ]   pop esi                   restore esi
  0x401043   [ 0 ]    ret 4                     return (increment stackpointer by 4)
*)
class memcpy_r_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__memcpy_r__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let count = get_arg args 1 floc in
    let dst = get_reg_value Ecx floc in
    let src = get_reg_value Edx floc in
    LBLOCK [ STR self#get_name ; STR "(dst:" ; xpr_to_pretty floc dst ;
	     STR ",src:" ; xpr_to_pretty floc src ; 
	     STR ",count:" ; xpr_to_pretty floc count ; STR ")" ]

  method get_commands (floc:floc_int) =
    let size = get_arg floc#get_call_args 1 floc in
    let dst = get_reg_value Ecx floc in
    let dst = floc#get_lhs_from_address dst in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands dst ~size (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    let adjcmds = get_adjustment_commands 4 floc in
    cmds1 @ cmds2 @ adjcmds

  method get_parametercount = 1

  method get_description = "unsafe memcpy function with register arguments"

end

(* ================================================================== reverse memcpy
   example: V0ca:0x4013a0
   md5hash: 8ce12f8c2bdb67498161f289bd03f797

  0x4013a0   [ 0 ]    push esi               save esi
  0x4013a1   [ -4 ]   push edi               save edi
  0x4013a2   [ -8 ]   mov edi, 0xc(esp,,1)   edi := arg.0004 = arg.0004_in
  0x4013a6   [ -8 ]   or ecx, -0x1           ecx := -1 
  0x4013a9   [ -8 ]   xor eax, eax           eax := 0 
  0x4013ab   [ -8 ]   repne scas             (Edi): (arg.0004_in)[0]_in; Ecx: -1 (width: 1)
  0x4013ad   [ -8 ]   not ecx                not ecx
  0x4013af   [ -8 ]   sub edi, ecx           edi := edi - ecx = (arg.0004_in - ecx)
  0x4013b1   [ -8 ]   mov eax, ecx           eax := ecx
  0x4013b3   [ -8 ]   mov esi, edi           esi := edi
  0x4013b5   [ -8 ]   mov edi, 0x10(esp,,1)  edi := arg.0008 = arg.0008_in
  0x4013b9   [ -8 ]   shr ecx, 0x2           ecx := ecx / 4
  0x4013bc   [ -8 ]   rep movs               (Esi):  ? ; (Edi): (arg.0008_in)[0]; 
                                               Ecx: ecx (width: 4)
  0x4013be   [ -8 ]   mov ecx, eax           ecx := eax
  0x4013c0   [ -8 ]   and ecx, 0x3           ecx := ecx & 3
  0x4013c3   [ -8 ]   rep movs               (Esi):  ? ; (Edi): ?; Ecx: ecx (width: 1)
  0x4013c5   [ -8 ]   pop edi                restore edi
  0x4013c6   [ -4 ]   pop esi                restore esi
  0x4013c7   [ 0 ]    ret                    return
*)
class rev_memcpy_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__rev_memcpy__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(src:" ; xpr_to_strpretty floc arg1 ;
	     STR ",dst:" ; xpr_to_strpretty floc arg2 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let arg2 = get_arg floc#get_call_args 2 floc in
    let dst = floc#get_lhs_from_address arg2 in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands dst (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Eax ; Ecx  ] ] in
    List.concat [ cmds1 ; cmds2 ]

  method get_parametercount = 2

  method get_description = "reverse memcpy"

end

(* ================================================================ memset0_r
   example: V9da:0x401024
   md5hash: 57804a0ab693214de412354cc6d41ac9

  0x401024   [ 0 ]    jmp 0x40102b              goto 0x40102b
--------------------------------------------------------------------------------
  0x401026   [ 0 ]    mov (ecx), 0x0            ? := 0
  0x401029   [ 0 ]    dec edx                   edx := edx - 1
  0x40102a   [ 0 ]    inc ecx                   ecx := ecx + 1
--------------------------------------------------------------------------------
  0x40102b   [ 0 ]    test edx, edx             test edx, edx
  0x40102d   [ 0 ]    ja 0x401026               if (edx != 0) then goto 0x401026
--------------------------------------------------------------------------------
  0x40102f   [ 0 ]    ret                       return
*)
class memset0_r_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__memset0_r__"

  method get_annotation (floc:floc_int) =
    let ecxv = get_reg_value Ecx floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [ STR self#get_name ; STR "(dst:" ; xpr_to_pretty floc ecxv ;
	     STR ",c:0,count:" ; xpr_to_pretty floc edxv ; STR ")" ]

  method get_commands (floc:floc_int) =
    let ecxv = get_reg_value Ecx floc in
    let size = get_reg_value Edx floc in
    let dst = floc#get_lhs_from_address ecxv in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands dst ~size (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    List.concat [ cmds1 ; cmds2 ]

  method get_parametercount = 0

  method get_description = "unsafe memset 0 with ecx as destination and edx as count"

end

(* ================================================================ wmemset()
   Example: V943:0x43377d
   md5hash: e2c6bb53696a0828cd2e131b803fc6f6

  0x43377d   [ 0 ]    mov edi, edi           nop
  0x43377f   [ 0 ]    push ebp               save ebp
  0x433780   [ -4 ]   mov ebp, esp           ebp := esp = (esp_in - 4)
  0x433782   [ -4 ]   mov ecx, 0x10(ebp)     ecx := arg.0012 = arg.0012_in
  0x433785   [ -4 ]   test ecx, ecx          test ecx, ecx
  0x433787   [ -4 ]   jz 0x4337a4            if (arg.0012_in = 0) then goto 0x4337a4
--------------------------------------------------------------------------------
  0x433789   [ -4 ]   mov eax, 0xc(ebp)      eax := arg.0008 = arg.0008_in
  0x43378c   [ -4 ]   movzx edx, ax          edx := ax
  0x43378f   [ -4 ]   mov eax, edx           eax := edx
  0x433791   [ -4 ]   shl edx, 0x10          edx := edx * 65536
  0x433794   [ -4 ]   push edi               save edi
  0x433795   [ -8 ]   mov edi, 0x8(ebp)      edi := arg.0004 = arg.0004_in
  0x433798   [ -8 ]   or eax, edx            eax := eax | edx
  0x43379a   [ -8 ]   shr ecx, 0x1           ecx := ecx / 2 = (arg.0012_in / 2)
  0x43379c   [ -8 ]   rep stos               (Edi): (arg.0004_in)[0]; Ecx: ecx (width: 4)
  0x43379e   [ -8 ]   adc ecx, ecx           ecx := ecx + ecx + (0 or 1)
  0x4337a0   [ -8 ]   rep stos               (Edi): ?; Ecx: ecx (width: 2)
  0x4337a3   [ -8 ]   pop edi                restore edi
--------------------------------------------------------------------------------
  0x4337a4   [ -4 ]   mov eax, 0x8(ebp)      eax := arg.0004 = arg.0004_in
  0x4337a7   [ -4 ]   pop ebp                restore ebp
  0x4337a8   [ 0 ]    ret                    return

  ============================================================================
   example: V0a29ae: 0x4087b0
   md5hash:

  0x4087b0   [ 0 ]    push ebp               save ebp
  0x4087b1   [ -4 ]   mov ebp, esp           ebp := esp = (esp_in - 4)
  0x4087b3   [ -4 ]   mov ecx, 0x10(ebp)     ecx := arg.0012 = arg.0012_in
  0x4087b6   [ -4 ]   test ecx, ecx          test ecx, ecx
  0x4087b8   [ -4 ]   jz 0x4087d5            if (arg.0012_in = 0) then goto 0x4087d5
--------------------------------------------------------------------------------
  0x4087ba   [ -4 ]   mov eax, 0xc(ebp)      eax := arg.0008 = arg.0008_in
  0x4087bd   [ -4 ]   movzx edx, ax          edx := ax
  0x4087c0   [ -4 ]   mov eax, edx           eax := edx
  0x4087c2   [ -4 ]   shl edx, 0x10          edx := edx * 65536
  0x4087c5   [ -4 ]   push edi               save edi
  0x4087c6   [ -8 ]   mov edi, 0x8(ebp)      edi := arg.0004 = arg.0004_in
  0x4087c9   [ -8 ]   or eax, edx            eax := eax | edx
  0x4087cb   [ -8 ]   shr ecx, 0x1           ecx := ecx / 2 = (arg.0012_in / 2)
  0x4087cd   [ -8 ]   rep stos               (Edi): (arg.0004_in)[0]; Ecx: ecx (width: 4)
  0x4087cf   [ -8 ]   adc ecx, ecx           ecx := ecx + ecx + (0 or 1)
  0x4087d1   [ -8 ]   rep stos               (Edi): ?; Ecx: ecx (width: 2)
  0x4087d4   [ -8 ]   pop edi                restore edi
--------------------------------------------------------------------------------
  0x4087d5   [ -4 ]   mov eax, 0x8(ebp)      eax := arg.0004 = arg.0004_in
  0x4087d8   [ -4 ]   pop ebp                restore ebp
  0x4087d9   [ 0 ]    ret                    return

*)

class wmemset_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wmemset__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [ STR self#get_name ; STR "(dst:" ; xpr_to_pretty floc arg1 ;
	     STR ",c:" ; xpr_to_pretty floc arg2 ;
	     STR ",count:" ; xpr_to_pretty floc arg3 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let size = get_arg args 3 floc in
    let size = XOp (XMult, [ int_constant_expr 2 ; size ]) in
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let dst = floc#get_lhs_from_address arg1 in
    let rhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let cmds1 = floc#get_assign_commands dst ~size ~vtype:t_wchar (XVar rhs) in
    let cmds2 = floc#get_assign_commands lhs arg1 in
    let cmds3 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    List.concat [ lhscmds ; cmds1 ; cmds2 ; cmds3 ]

    method get_parametercount = 3

    method get_call_target (a:doubleword_int) =
      mk_static_dll_stub_target a "msvcrt.dll" "wmemset"

    method get_description = "wmemset library function"

end

let _ = H.add table "wmemset" (new wmemset_semantics_t)


let libmem_functions () = 
  (H.fold (fun k v a -> a @ (get_fnhashes k v)) table []) @

  [ new memcpy_r_semantics_t "c0605f9b9904b351841d7a5c2b26d44e" 12 ;
    new memset0_r_semantics_t "57804a0ab693214de412354cc6d41ac9" 7 ;
    new rev_memcpy_semantics_t "8ce12f8c2bdb67498161f289bd03f797" 19 
  ]

let memcpyvec_matcher faddr fnbytes fnhash =
  let dll = "msvcrt.dll" in
  let name = "memcpy" in
  if function_summary_library#has_dll_function dll name then
    let checkpoint = todw (Str.matched_group 1 fnbytes) in
    let jmpoff = todwoff (Str.matched_group 2 fnbytes) in
    let vecaddr = (faddr#add_int 71)#add_int jmpoff in
    let loc = make_location { loc_faddr = faddr ; loc_iaddr = vecaddr#add_int 77 } in
    let cfloc = get_floc loc in
    if cfloc#has_call_target
       && cfloc#get_call_target#is_app_call
       && (let tgtaddr = cfloc#get_call_target#get_app_address in
           (functions_data#get_function tgtaddr)#get_function_name =
             "__fastcopy_I__") then
      let sem = (mk_dllfun_semantics dll name) fnhash 263 in
      let msg = LBLOCK [ STR " with checkpoint " ; checkpoint#toPretty ] in
      sometemplate ~msg sem
    else
      None
  else
    None

let memsetvec_matcher faddr fnbytes fnhash =
  let dll = "msvcrt.dll" in
  let fname = "memset" in
  if function_summary_library#has_dll_function dll fname then
    let jmpoff = todwoff (Str.matched_group 1 fnbytes) in
    let vecaddr = (faddr#add_int 44)#add_int jmpoff in
    let loc = make_location { loc_faddr = faddr ; loc_iaddr = vecaddr#add_int 49 } in    
    let cfloc = get_floc loc in
    if cfloc#has_call_target
       && cfloc#get_call_target#is_app_call
       && (let tgtaddr = cfloc#get_call_target#get_app_address in
           (functions_data#get_function tgtaddr)#get_function_name =
             "__fastzero_I__") then
      let sem = (mk_dllfun_semantics dll fname) fnhash 107 in
      sometemplate sem
    else
      None
  else
    None


let libmem_patterns = [

  (* memcpy using VEC (V2bd:0x1000cb70) *)
  { regex_s = Str.regexp 
      ("558bec57568b750c8b4d108b7d088bc18bd103c63bfe76083bf80f82a401000081f90001" ^
       "0000721f833d\\(........\\)007416575683e70f83e60f3bfe5e5f75085e5f5de9" ^
       "\\(........\\)f7c7030000007515c1e90283e20383f908722af3a5ff2495\\(........\\)8b" ^
       "c7ba0300000083e904720c83e00303c8ff2485\\(........\\)ff248d\\(........\\)" ^
       "ff248d\\(........\\)8b448ee489448fe48b448ee889448fe88b448eec89448fec8b" ^
       "448ef089448ff08b448e" ^
       "f489448ff48b448ef889448ff88b448efc89448ffc8d048d0000000003f003f8ff2495" ^
       "\\(........\\)8b45085e5fc9c38a0688078b45085e5fc9c38a0688078a4601884701" ^
       "8b45085e5f" ^
       "c9c38a0688078a46018847018a46028847028b45085e5fc9c38d7431fc8d7c39fcf7c703" ^
       "0000007524c1e90283e20383f908720dfdf3a5fcff2495\\(........\\)f7d9ff248d" ^
       "\\(........\\)" ^
       "8bc7ba0300000083f904720c83e0032bc8ff2485\\(........\\)ff248d" ^
       "\\(........\\)8b448e1c89" ^
       "448f1c8b448e1889448f188b448e1489448f148b448e1089448f108b448e0c89448f0c8b" ^
       "448e0889448f088b448e0489448f048d048d0000000003f003f8ff2495\\(........\\)" ^
       "8b4508" ^
       "5e5fc9c38a46038847038b45085e5fc9c38a46038847038a46028847028b45085e5fc9c3" ^
       "8a46038847038a46028847028a46018847018b45085e5fc9c3558bec83ec1c897df48975" ^
       "f8895dfc8b5d0c8bc3998bc88b450833ca2bca83e10f33ca2bca998bf833fa2bfa83e70f" ^
       "33fa2bfa8bd10bd7754a8b75108bce83e17f894de83bf174132bf1565350e8" ^
       "\\(........\\)83c40c8b45088b4de885c974778b5d108b550c03d32bd18955ec03d82b" ^
       "d9895df08b75ec8b7df08b4de8f3a48b4508eb533bcf7535f7d983c110894de48b750c8b" ^
       "7d088b4de4f3a48b4d08034de48b550c0355e48b45102b45e4505251e84cffffff83c40c" ^
       "8b4508eb1a8b750c8b7d088b4d108bd1c1e902f3a58bca83e103f3a48b45088b5dfc8b75" ^
       "f88b7df48be55dc3$") ;

    regex_f = memcpyvec_matcher
  } ;

  (* memcpy using VEC (V2bd:0x100109a0) *)
  { regex_s = Str.regexp 
      ("558bec57568b750c8b4d108b7d088bc18bd103c63bfe76083bf80f82a401000081f90001" ^
       "0000721f833d\\(........\\)007416575683e70f83e60f3bfe5e5f75085e5f5de9" ^
       "\\(........\\)f7c7030000007515c1e90283e20383f908722af3a5ff2495\\(........\\)8b" ^
       "c7ba0300000083e904720c83e00303c8ff2485280a0110ff248d240b0110ff248da80a01" ^
       "108b448ee489448fe48b448ee889448fe88b448eec89448fec8b448ef089448ff08b448e" ^
       "f489448ff48b448ef889448ff88b448efc89448ffc8d048d0000000003f003f8ff249514" ^
       "0b01108b45085e5fc9c38a0688078b45085e5fc9c38a0688078a46018847018b45085e5f" ^
       "c9c38a0688078a46018847018a46028847028b45085e5fc9c38d7431fc8d7c39fcf7c703" ^
       "0000007524c1e90283e20383f908720dfdf3a5fcff2495b00c0110f7d9ff248d600c0110" ^
       "8bc7ba0300000083f904720c83e0032bc8ff2485b40b0110ff248db00c01108b448e1c89" ^
       "448f1c8b448e1889448f188b448e1489448f148b448e1089448f108b448e0c89448f0c8b" ^
       "448e0889448f088b448e0489448f048d048d0000000003f003f8ff2495b00c01108b4508" ^
       "5e5fc9c38a46038847038b45085e5fc9c38a46038847038a46028847028b45085e5fc9c3" ^
       "8a46038847038a46028847028a46018847018b45085e5fc9c3558bec83ec1c897df48975" ^
       "f8895dfc8b5d0c8bc3998bc88b450833ca2bca83e10f33ca2bca998bf833fa2bfa83e70f" ^
       "33fa2bfa8bd10bd7754a8b75108bce83e17f894de83bf174132bf1565350e8" ^
       "\\(........\\)83c40c8b45088b4de885c974778b5d108b550c03d32bd18955ec03d82b" ^
       "d9895df08b75ec8b7df08b4de8f3a48b4508eb533bcf7535f7d983c110894de48b750c8b" ^
       "7d088b4de4f3a48b4d08034de48b550c0355e48b45102b45e4505251e84cffffff83c40c" ^
       "8b4508eb1a8b750c8b7d088b4d108bd1c1e902f3a58bca83e103f3a48b45088b5dfc8b75" ^
       "f88b7df48be55dc3$") ;

    regex_f = memcpyvec_matcher
  } ;

  (* memset using VEC (V2bd:0x1000fe10) *)
  { regex_s = Str.regexp
      ("8b54240c8b4c240485d2746933c08a44240884c0751681fa00010000720e833dcc6f0210" ^
       "007405e9\\(........\\)578bf983fa047231f7d983e103740c2bd1880783c70183e901" ^
       "75f68bc8c1e00803c18bc8c1e01003c18bca83e203c1e9027406f3ab85d2740a880783c7" ^
       "0183ea0175f68b4424085fc38b442404c3558bec83ec10897dfc8b4508998bf833fa2bfa" ^
       "83e70f33fa2bfa85ff753c8b4d108bd183e27f8955f43bca74122bca5150e873ffffff83" ^
       "c4088b45088b55f485d274450345102bc28945f833c08b7df88b4df4f3aa8b4508eb2ef7" ^
       "df83c710897df033c08b7d088b4df0f3aa8b45f08b4d088b551003c82bd0526a0051e87e" ^
       "ffffff83c40c8b45088b7dfc8be55dc3$") ;

    regex_f = memsetvec_matcher
  }

]

