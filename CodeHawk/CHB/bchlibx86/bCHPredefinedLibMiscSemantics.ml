(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open BCHFloc
open BCHFunctionInterface
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHVariableType

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil

module H = Hashtbl

let table = H.create 11

let load_misc_functions () =
  List.iter (fun m -> add_dllfun table "msvcrt.dll" m)
    [ "_initterm" ; "_unlock" ]

(* =========================================================== controlfp_call
   example: Va2d:0x401910
   md5hash: c3180896d5a80dddc933dbb003f27d1e

  0x401910   [ 0 ]    push 0x30000              [_controlfp : mask = 196608 ]
  0x401915   [ -4 ]   push 0x10000              [_controlfp : new = 65536 ]
  0x40191a   [ -8 ]   call 0x401936             _controlfp(new:65536, mask:196608)
  0x40191f   [ -8 ]   pop ecx                   ecx := 65536 ; esp := esp + 4 = (esp_in - 4)
  0x401920   [ -4 ]   pop ecx                   ecx := 196608 ; esp := esp + 4 = esp_in
  0x401921   [ 0 ]    ret                       return
*)

class controlfp_call_semantics_t 
  (md5hash:string) (arg1:doubleword_int) (arg2:doubleword_int) (instrs:int) =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__controlfp_call__"

  method get_annotation (floc:floc_int) =
    LBLOCK [ STR self#get_name ; STR "(new:" ; arg1#toPretty ; 
	     STR ",mask:" ; arg2#toPretty ; STR ")" ]

  method get_commands (floc:floc_int) =
    [ floc#get_abstract_cpu_registers_command [ Eax ; Ecx ; Edx ] ]

  method get_parametercount = 0

end

(* =========================================================== CPtoLCID
   example: V007:0x445132
*)
class cptolcid_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__CPtoLCID__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR ")" ]

  method get_parametercount = 0

end

let _ = H.add table "CPtoLCID" (new cptolcid_semantics_t)

(* =========================================================== CPtoLocaLName
   example: V494:0x40aeac

  0x40aeac   [ 0 ]    push ebp                  save ebp
  0x40aead   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x40aeaf   [ -4 ]   mov eax, 0x8(ebp)         eax := arg.0004 = arg.0004_in
  0x40aeb2   [ -4 ]   sub eax, 0x3a4            eax := eax - 932 = (arg.0004_in - 932)
  0x40aeb7   [ -4 ]   jz 0x40aedf               if (arg.0004_in = 1864) then goto 0x40aedf
--------------------------------------------------------------------------------
  0x40aeb9   [ -4 ]   sub eax, 0x4              eax := eax - 4 = (arg.0004_in - 936)
  0x40aebc   [ -4 ]   jz 0x40aed8               if (arg.0004_in = 940) then goto 0x40aed8
--------------------------------------------------------------------------------
  0x40aebe   [ -4 ]   sub eax, 0xd              eax := eax - 13 = (arg.0004_in - 949)
  0x40aec1   [ -4 ]   jz 0x40aed1               if (arg.0004_in = 962) then goto 0x40aed1
--------------------------------------------------------------------------------
  0x40aec3   [ -4 ]   dec eax                   eax := eax - 1 = (arg.0004_in - 950)
  0x40aec4   [ -4 ]   jz 0x40aeca               if (arg.0004_in = 951) then goto 0x40aeca
--------------------------------------------------------------------------------
  0x40aec6   [ -4 ]   xor eax, eax              eax := 0 
  0x40aec8   [ -4 ]   pop ebp                   restore ebp
  0x40aec9   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x40aeca   [ -4 ]   mov eax, 0x4119dc         eax := 4266500
  0x40aecf   [ -4 ]   pop ebp                   restore ebp
  0x40aed0   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x40aed1   [ -4 ]   mov eax, 0x4119d8         eax := 4266488
  0x40aed6   [ -4 ]   pop ebp                   restore ebp
  0x40aed7   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x40aed8   [ -4 ]   mov eax, 0x4119d4         eax := 4266476
  0x40aedd   [ -4 ]   pop ebp                   restore ebp
  0x40aede   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x40aedf   [ -4 ]   mov eax, 0x4119d0         eax := 4266464
  0x40aee4   [ -4 ]   pop ebp                   restore ebp
  0x40aee5   [ 0 ]    ret                       return
*)
class cptolocalname_semantics_t (md5hash:string)
  (gv1:doubleword_int) (gv2:doubleword_int) (gv3:doubleword_int) (gv4:doubleword_int)
  (instrs:int) =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__CPtoLocalName__"

  method get_annotation (floc:floc_int) =
    let arg1 = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(cp:" ; xpr_to_pretty floc arg1 ; STR ")" ;
	     STR " (from: [gv_" ; gv1#toPretty ; STR ",gv_" ; gv2#toPretty ;
	     STR ",gv_" ; gv3#toPretty ; STR ",gv_" ; gv4#toPretty ; STR "])" ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value self#get_name floc in
    let cmds = floc#get_assign_commands lhs ~vtype:(t_ptrto t_wchar) (XVar rhs) in
    lhscmds @ cmds

  method get_parametercount = 1

  method get_description = "get local name from code page"

end

(* =========================================================== CxxThrowException
   example: V03be08:0x403e38

  0x403e38   [ 0 ]    push ebp              save ebp
  0x403e39   [ -4 ]   mov ebp, esp          ebp := esp = (esp_in - 4)
  0x403e3b   [ -4 ]   sub esp, 0x20         esp := esp - 32 = (esp_in - 36)
  0x403e3e  [ -36 ]   mov eax, 0x8(ebp)     eax := arg.0004 = arg.0004_in
  0x403e41  [ -36 ]   push esi              save esi
  0x403e42  [ -40 ]   push edi              save edi
  0x403e43  [ -44 ]   push 0x8              esp := esp - 4 ; var.0048 := 8
  0x403e45  [ -48 ]   pop ecx               ecx := 8 ; esp := esp + 4 = (esp_in - 44)
  0x403e46  [ -44 ]   mov esi, 0x4179f4     esi := 4291060
  0x403e4b  [ -44 ]   lea edi, -0x20(ebp)   edi := (ebp - 32) = (esp_in - 36)
  0x403e4e  [ -44 ]   rep movs              (Esi): gv_0x4179f4_in; 
                                               (Edi): var.0036; Ecx: 8 (width: 4)
  0x403e50  [ -44 ]   mov -0x8(ebp), eax    var.0012 := eax = arg.0004_in
  0x403e53  [ -44 ]   mov eax, 0xc(ebp)     eax := arg.0008 = arg.0008_in
  0x403e56  [ -44 ]   mov -0x4(ebp), eax    var.0008 := eax = arg.0008_in
  0x403e59  [ -44 ]   lea eax, -0xc(ebp)    eax := (ebp - 12) = (esp_in - 16)
  0x403e5c  [ -44 ]   push eax              [RaiseException : lpArguments = eax ]
  0x403e5d  [ -48 ]   push -0x10(ebp)       [RaiseException : nNumberOfArguments = var.0020 ]
  0x403e60  [ -52 ]   push -0x1c(ebp)       [RaiseException : dwExceptionFlags = var.0032 ]
  0x403e63  [ -56 ]   push -0x20(ebp)       [RaiseException : dwExceptionCode = var.0036 ]
  0x403e66  [ -60 ]   call* 0x416094        RaiseException(dwExceptionCode:var.0060, 
                                                  dwExceptionFlags:var.0056, 
                                                  nNumberOfArguments:var.0052, 
                                                  lpArguments:&var.0016) (adj 16)

*)
class cxxthrowexception_semantics_t 
  (md5hash:string) 
  (faddr:doubleword_int) 
  (base:doubleword_int) 
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__CxxThrowException__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let excode = (absolute_op base 4 RD)#to_expr floc in
    let exflags = (absolute_op (base#add_int 4) 4 RD)#to_expr floc in
    let nArgs = (absolute_op (base#add_int 16) 4 RD)#to_expr floc in
    let dArg1 = (absolute_op (base#add_int 20) 4 RD)#to_expr floc in
    let dArg2 = get_arg args 1 floc in
    let dArg3 = get_arg args 2 floc in
    LBLOCK [
        STR "RaiseException(dwExceptionCode:"; xpr_to_pretty floc excode;
	STR ",dwExceptionFlags:"; xpr_to_pretty floc exflags;
	STR ",nNumberArgs:"; xpr_to_pretty floc nArgs;
	STR ",dArg1:"; xpr_to_pretty floc dArg1;
	STR ",dArg2:"; xpr_to_pretty floc dArg2;
	STR ",dArg3:"; xpr_to_pretty floc dArg3; STR ")"]

  method get_commands (floc:floc_int) =
    let tgtloc =
      make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 46 } in
    let tgtfloc = get_floc tgtloc in
    get_wrapped_call_commands floc tgtfloc

  method get_parametercount = 2

  method get_call_target (a:doubleword_int) =
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 6 } in
    let tgtfloc = get_floc tgtloc in
    let wtgt = tgtfloc#get_call_target#get_target in
    let fintf = default_function_interface ~returntype:t_void self#get_name [] in
    mk_wrapped_target a fintf wtgt []

  method get_description = "wraps CxxThrowException"

end

(* =========================================================== FindPESection
   example: V494:0x40b7b0
   md5hash: 3306fea76897df3c506584532e5a8ea8

  0x40b7b0   [ 0 ]    push ebp              save ebp
  0x40b7b1   [ -4 ]   mov ebp, esp          ebp := esp = (esp_in - 4)
  0x40b7b3   [ -4 ]   mov eax, 0x8(ebp)     eax := arg.0004 = arg.0004_in
  0x40b7b6   [ -4 ]   push ebx              save ebx
  0x40b7b7   [ -8 ]   mov ecx, 0x3c(eax)    ecx := (arg.0004_in)[60] = (arg.0004_in)[60]_in
  0x40b7ba   [ -8 ]   add ecx, eax          ecx := ecx + eax = ((arg.0004_in)[60]_in + arg.0004_in)
  0x40b7bc   [ -8 ]   push esi              save esi
  0x40b7bd  [ -12 ]   movzx eax, 0x14(ecx)  eax := (arg.0004_in)[20][(arg.0004_in)[60]_in:1]
  0x40b7c1  [ -12 ]   movzx ebx, 0x6(ecx)   ebx := (arg.0004_in)[6][(arg.0004_in)[60]_in:1]
  0x40b7c5  [ -12 ]   add eax, 0x18         eax := eax + 24
  0x40b7c8  [ -12 ]   xor edx, edx          edx := 0 
  0x40b7ca  [ -12 ]   add eax, ecx          eax := eax + ecx = (eax + (arg.0004_in + (arg.0004_in)[60]_in))
  0x40b7cc  [ -12 ]   push edi              save edi
  0x40b7cd  [ -16 ]   test ebx, ebx         test ebx, ebx
  0x40b7cf  [ -16 ]   jz 0x40b7ec           if (ebx = 0) then goto 0x40b7ec
--------------------------------------------------------------------------------
  0x40b7d1  [ -16 ]   mov edi, 0xc(ebp)     edi := arg.0008 = arg.0008_in
--------------------------------------------------------------------------------
  0x40b7d4  [ -16 ]   mov esi, 0xc(eax)     esi :=  ?  (tmpN)
  0x40b7d7  [ -16 ]   cmp edi, esi          cmp edi, esi
  0x40b7d9  [ -16 ]   jc 0x40b7e4           if (arg.0008_in < esi) then goto 0x40b7e4
--------------------------------------------------------------------------------
  0x40b7db  [ -16 ]   mov ecx, 0x8(eax)     ecx :=  ?  (tmpN)
  0x40b7de  [ -16 ]   add ecx, esi          ecx := ecx + esi
  0x40b7e0  [ -16 ]   cmp edi, ecx          cmp edi, ecx
  0x40b7e2  [ -16 ]   jc 0x40b7ee           if (arg.0008_in < ecx) then goto 0x40b7ee
--------------------------------------------------------------------------------
  0x40b7e4  [ -16 ]   inc edx               edx := edx + 1
  0x40b7e5  [ -16 ]   add eax, 0x28         eax := eax + 40
  0x40b7e8  [ -16 ]   cmp edx, ebx          cmp edx, ebx
  0x40b7ea  [ -16 ]   jc 0x40b7d4           if (edx < ebx) then goto 0x40b7d4
--------------------------------------------------------------------------------
  0x40b7ec  [ -16 ]   xor eax, eax          eax := 0 
--------------------------------------------------------------------------------
  0x40b7ee  [ -16 ]   pop edi               restore edi
  0x40b7ef  [ -12 ]   pop esi               restore esi
  0x40b7f0   [ -8 ]   pop ebx               restore ebx
  0x40b7f1   [ -4 ]   pop ebp               restore ebp
  0x40b7f2   [ 0 ]    ret                   return
*)
class findpesection_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__FindPESection__"

  method get_annotation (floc:floc_int) =
    let arg1 = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg1 ; STR ")" ]

  method get_parametercount = 1

end

let _ = H.add table "FindPESection" (new findpesection_semantics_t)
    

(* =========================================================== GetPrimaryLen
   example: Vc416ff:0x46f864
   md5hash: e542c4d73d3653aa7aad8247b36b6a8a

  0x46f964   [ 0 ]    xor eax, eax              eax := 0 
--------------------------------------------------------------------------------
  0x46f966   [ 0 ]    mov cl, (edx)             cl :=  ?  (tmpN)
  0x46f968   [ 0 ]    inc edx                   edx := edx + 1
  0x46f969   [ 0 ]    cmp cl, 0x41              cmp cl, 0x41
  0x46f96c   [ 0 ]    jl 0x46f973               if (cl < 65) then goto 0x46f973
--------------------------------------------------------------------------------
  0x46f96e   [ 0 ]    cmp cl, 0x5a              cmp cl, 0x5a
  0x46f971   [ 0 ]    jle 0x46f97b              if (cl <= 90) then goto 0x46f97b
--------------------------------------------------------------------------------
  0x46f973   [ 0 ]    sub cl, 0x61              cl := cl - 97
  0x46f976   [ 0 ]    cmp cl, 0x19              cmp cl, 0x19
  0x46f979   [ 0 ]    ja 0x46f97e               if (cl > 25) then goto 0x46f97e
--------------------------------------------------------------------------------
  0x46f97b   [ 0 ]    inc eax                   eax := eax + 1
  0x46f97c   [ 0 ]    jmp 0x46f966              goto 0x46f966
--------------------------------------------------------------------------------
  0x46f97e   [ 0 ]    ret                       return
*)

class getprimarylen_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__GetPrimaryLen__"

  method get_annotation (floc:floc_int) =
    let edxv = get_reg_value Edx floc in
    LBLOCK [ STR self#get_name ; STR "("  ; xpr_to_pretty floc edxv ; STR ")" ]

  method get_parametercount = 0 

  method get_description = "get length of primary language"

end

let _ = H.add table "GetPrimaryLen" (new getprimarylen_semantics_t)

(* =============================================================== _abstract_cw
   example: nginx:0x589dd7
*)
class abstract_cw_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__abstract_cw__"

  method get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg ; STR ")" ]

  method get_parametercount = 1

end

(* =============================================================== _abstract_sw
   example: nginx:0x58a087
*)
class abstract_sw_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__abstract_sw__"

  method get_parametercount = 0

end

let _ = H.add table "_abstract_sw" (new abstract_sw_semantics_t)

(* =============================================================== __hw_cw__
   example: V2bd:0x1001c18d
   md5hash: 32dd72fd7de15972185c1ea6fae115c0
*)
class hw_cw_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__hw_cw__"

  method get_annotation (floc:floc_int) =
    let ebxv = get_reg_value Ebx floc in
    LBLOCK [ STR self#get_name ; STR "(ebx:" ; xpr_to_pretty floc ebxv ; STR ")" ]

  method get_parametercount = 0 

end

let _ = H.add table "hw_cw" (new hw_cw_semantics_t)

(* ================================================================ ___hw_cw_sse2__
   example: V2bd:0x1001c21b
   md5hash: d0bcda2758e75868d3b0d31fd10b6836
*)
class hw_cw_sse2_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__hw_cw_sse2__"

  method get_annotation (floc:floc_int) =
    let edxv = get_reg_value Edx floc in
    LBLOCK [ STR self#get_name ; STR "(edx:" ; xpr_to_pretty floc edxv ; STR ")" ]

  method get_parametercount = 0 

end

let _ = H.add table "hw_cw_sse2" (new hw_cw_sse2_semantics_t)

 
(* ========================================================= heapalloc_call
   example: V9da:0x401000

  0x401000   [ 0 ]    push ecx          [HeapAlloc : dwBytes = ecx ]
  0x401001   [ -4 ]   push 0x8          [HeapAlloc : dwFlags = 8 ]
  0x401003   [ -8 ]   push 0x404408     [HeapAlloc : hHeap = gv_0x404408 ]
  0x401009  [ -12 ]   call* 0x403000    HeapAlloc(hHeap:gv_0x404408_in, 
                                         dwFlags:HEAP_ZERO_MEMORY, dwBytes:ecx_in) (adj 12)
  0x40100f   [ 0 ]    ret               return
*)
class heapalloc_call_semantics_t 
  (md5hash:string) (hheap:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__heapalloc_call__"

  method get_annotation (floc:floc_int) =
    let ecxv = get_reg_value Ecx floc in
    LBLOCK [ STR "HeapAlloc(hHeap:gv_" ; hheap#toPretty ; 
	     STR ",dwFlags:HEAP_ZERO_MEMORY, dwBytes:" ; xpr_to_pretty floc ecxv ]

  method get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let rhs = get_return_value "HeapAlloc" floc in
    let cmds1 = floc#get_assign_commands eaxlhs ~vtype:(t_ptrto t_void) (XVar rhs) in
    eaxlhscmds @ cmds1

  method get_parametercount = 0

  method get_description = "wraps a call to HeapAlloc"

end
    
(* __ValidateImageBase
   example: Vc13:0x40ad80
*)
class validateimagebase_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__ValidateImageBase__"

  method get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg ; STR ")" ]

  method get_parametercount = 1

end

let _ = H.add table "ValidateImageBase" (new validateimagebase_semantics_t)


(* ========================================================= virtualallocex_call
   example: Vc6c:0x402b69

  0x402b69   [ 0 ]    push 0x40                 [VirtualAllocEx : flProtect = 64 ]
  0x402b6b   [ -4 ]   push 0x1000               [VirtualAllocEx : flAllocationType = 4096 ]
  0x402b70   [ -8 ]   push 0x10(esp,,1)         [VirtualAllocEx : dwSize = arg.0008 ]
  0x402b74  [ -12 ]   push 0x0                  [VirtualAllocEx : lpAddress = 0 ]
  0x402b76  [ -16 ]   push 0x14(esp,,1)         [VirtualAllocEx : hProcess = arg.0004 ]
  0x402b7a  [ -20 ]   call* cav:0x401038        VirtualAllocEx(hProcess:arg.0004_in, 
                                                  lpAddress:0, 
                                                  dwSize:arg.0008_in, 
                                                  flAllocationType:MEM_COMMIT, 
                                                  flProtect:PAGE_EXECUTE_READWRITE) (adj 20)
  0x402b80   [ 0 ]    ret                       return
*)
class virtualallocex_call_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__virtualallocex_call__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR "VirtualAllocEx(hProcess:" ; xpr_to_pretty floc arg1 ;
	     STR ",lpAddress:0,dwSize:" ; xpr_to_pretty floc arg2 ;
	     STR ",flAllocationType:MEM_COMMIT,flProtect:PAGE_EXECUTE_READWRITE)" ]

  method get_parametercount = 2

end

(* =================================================================== __wchartodigit
   example: V098864: 0x45f357
   md5hash: bd5768aaebfb148a078e98a4277f9691
*)
class wchartodigit_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wchartodigit__"

  method get_annotation (floc:floc_int) =
    let arg1 = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg1 ; STR ")" ]

  method get_parametercount = 1 

  method get_description = "__wchartodigit internal library function"

end

let _ = H.add table "__wchartodigit" (new wchartodigit_semantics_t)

(* =================================================================== __xchg_arg2__
   example: V2bd:0x1001c9de
   md5hash: c1ed954e2d9e4415774047545d03d0fa

  0x1001c9de [ 0 ]  pop eax             eax := arg.0000_in ; esp := esp + 4 = (esp_in + 4)
  0x1001c9df [ 4 ]  pop ecx             ecx := arg.0004_in ; esp := esp + 4 = (esp_in + 8)
  0x1001c9e0 [ 8 ]  xchg (esp,,1), eax  eax := arg.0008; arg.0008 := arg.0000
  0x1001c9e3 [ 8 ] jmp* eax             return 8

*)
class xchg_arg2_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__xchg_arg2__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(c:" ; xpr_to_pretty floc arg1 ;
	     STR "(r:" ; xpr_to_pretty floc arg2 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let (ecxlhs,ecxlhscmds) = get_reg_lhs Ecx floc in
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let cmds1 = floc#get_assign_commands eaxlhs arg2 in
    let cmds2 = floc#get_assign_commands ecxlhs arg1 in
    let cmds3 = get_adjustment_commands 8 floc in
    List.concat [ eaxlhscmds ; ecxlhscmds ; cmds1 ; cmds2 ; cmds3 ]

  method get_parametercount = 2

  method get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method get_description = "return second argument"

end
    

let libmisc_functions () = 
  (H.fold (fun k v a -> a @ (get_fnhashes k v)) table []) @

    [ new xchg_arg2_semantics_t "c1ed954e2d9e4415774047545d03d0fa" 4 ]


let libmisc_patterns = [

  (* CPtoLocalName (V494:0x40aeac) *)
  { regex_s = Str.regexp 
      ("558bec8b45082da4030000742683e804741a83e80d740e48740433c05dc3a1" ^
       "\\(........\\)5dc3a1\\(........\\)5dc3a1\\(........\\)5dc3a1" ^
       "\\(........\\)5dc3$") ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let gv1 = todw (Str.matched_group 1 fnbytes) in
      let gv2 = todw (Str.matched_group 2 fnbytes) in
      let gv3 = todw (Str.matched_group 3 fnbytes) in
      let gv4 = todw (Str.matched_group 4 fnbytes) in
      let sem = new cptolocalname_semantics_t fnhash gv1 gv2 gv3 gv4 26 in
      let msg = LBLOCK [ STR " with sources " ;
			 pretty_print_list [ gv1 ; gv2 ; gv3 ; gv4 ]
			   (fun gv -> gv#toPretty) "[" "," "]" ] in
      sometemplate ~msg sem
  } ;

  (* CxxThrowException *)
  { regex_s = Str.regexp
      ("558bec83ec208b450856576a0859be\\(........\\)8d7de0f3a58945f88b450c8945fc" ^
       "8d45f450ff75f0ff75e4ff75e0ff15\\(........\\)$") ;

    regex_f = fun faddr fnbytes fnhash ->
      let base = todw (Str.matched_group 1 fnbytes) in
      if is_named_dll_call faddr 46 "RaiseException" then
	let sem = new cxxthrowexception_semantics_t fnhash faddr base 20 in
	let msg = LBLOCK [ STR " with base " ; base#toPretty ] in
	sometemplate ~msg sem
      else None
  } ;

  (* controlfp call *)
  { regex_s = Str.regexp 
      "68\\(........\\)68\\(........\\)e8\\(........\\)5959c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let arg1 = todw (Str.matched_group 1 fnbytes) in
      let arg2 = todw (Str.matched_group 2 fnbytes) in
      if is_named_dll_call faddr 10 "_controlfp" then
	let sem = new controlfp_call_semantics_t fnhash arg1 arg2 6 in
	let msg = LBLOCK [ STR " with arguments " ; arg1#toPretty ; STR " and " ; 
			   arg2#toPretty ] in
	sometemplate ~msg sem
      else None
  } ;

 (* _unlock (Vc13:0x409e4e) 
  0x409e4e  push ebp               save ebp
  0x409e4f  mov ebp, esp           ebp := esp = (esp_in - 4)
  0x409e51  mov eax, 0x8(ebp)      eax := arg.0004 = arg.0004_in
  0x409e54  push 0x419120(,eax,8)  [LeaveCriticalSection : 
                                       lpCriticalSection = gv_0x419120[arg.0004_in:8] ]
  0x409e5b  call* 0x40f0a4         LeaveCriticalSection(lpCriticalSection:var.0008) (adj 4)
  0x409e61  pop ebp                restore ebp
  0x409e62  ret                    return

 *)
  { regex_s = Str.regexp
      "558bec8b4508ff34c5\\(........\\)ff15\\(........\\)5dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      if is_named_dll_call faddr 13 "LeaveCriticalSection" then
	let sem = mk_dllfun_semantics "msvcrt.dll" "_unlock" fnhash 7 in
	let msg = LBLOCK [ STR " with base address " ; gv#toPretty ] in
	sometemplate ~msg sem
      else
	None
  } ;

  (* virtualallocex wrapper *)
  { regex_s = Str.regexp 
      "6a406800100000ff7424106a00ff742414ff15\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      if is_named_dll_call faddr 17 "VirtualAllocEx" then
	let sem = new virtualallocex_call_semantics_t fnhash 7 in
	sometemplate sem
      else None
  } ;

  (* heapalloc wrapper *)
  { regex_s = Str.regexp "516a08ff35\\(........\\)ff1500304000c3" ;

    regex_f = fun faddr fnbytes fnhash ->
      let hheap = todw (Str.matched_group 1 fnbytes) in
      if is_named_dll_call faddr 9 "HeapAlloc" then
	let sem = new heapalloc_call_semantics_t fnhash hheap 5 in
	sometemplate sem
      else None
  } ;
]
