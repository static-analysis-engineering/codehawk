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
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHPredefinedUtil

(* =========================================================== geterrnofromoserr
   example: V2fa:0x48e93c

  0x48e93c   [ 0 ]    mov eax, 0x4(esp,,1)      eax := arg.0004 = arg.0004_in
  0x48e940   [ 0 ]    xor ecx, ecx              ecx := 0 
--------------------------------------------------------------------------------
  0x48e942   [ 0 ]    cmp eax, 0x4d8680(,ecx,8)  cmp eax, 0x4d8680(,ecx,8)
  0x48e949   [ 0 ]    jz 0x48e95d               if (arg.0004_in = gv_0x4d8680[ecx:8])
                                                  then goto 0x48e95d
--------------------------------------------------------------------------------
  0x48e94b   [ 0 ]    inc ecx                   ecx := ecx + 1
  0x48e94c   [ 0 ]    cmp ecx, 0x2d             cmp ecx, 0x2d
  0x48e94f   [ 0 ]    jc 0x48e942               if (ecx < 45) then goto 0x48e942
--------------------------------------------------------------------------------
  0x48e951   [ 0 ]    lea ecx, -0x13(eax)       ecx := (eax - 19) = (arg.0004_in - 19)
  0x48e954   [ 0 ]    cmp ecx, 0x11             cmp ecx, 0x11
  0x48e957   [ 0 ]    ja 0x48e965               if ((arg.0004_in - 19) > 17) 
                                                  then goto 0x48e965
--------------------------------------------------------------------------------
  0x48e959   [ 0 ]    push 0xd                  esp := esp - 4 ; var.0004 := 13
  0x48e95b   [ -4 ]   pop eax                   eax := 13 ; esp := esp + 4 = esp_in
  0x48e95c   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x48e95d   [ 0 ]    mov eax, 0x4d8684(,ecx,8)  eax := gv_0x4d8684[ecx:8]
  0x48e964   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x48e965   [ 0 ]    add eax, -0xbc            eax := eax + -188 = (arg.0004_in - 188)
  0x48e96a   [ 0 ]    push 0xe                  esp := esp - 4 ; var.0004 := 14
  0x48e96c   [ -4 ]   pop ecx                   ecx := 14 ; esp := esp + 4 = esp_in
  0x48e96d   [ 0 ]    cmp ecx, eax              cmp ecx, eax
  0x48e96f   [ 0 ]    sbb eax, eax              eax := 0 or -1
  0x48e971   [ 0 ]    and eax, ecx              eax := eax & ecx
  0x48e973   [ 0 ]    add eax, 0x8              eax := eax + 8
  0x48e976   [ 0 ]    ret                       return

  example: V2bd: 0x1000ec99

*)

class geterrnofromoserr_semantics_t
  (md5hash:string) (base1:doubleword_int) 
  (base2:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__get_errno_from_oserr__"

  method get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg ; STR ")" ]

  method get_parametercount = 1

  method get_description = "retrieves errno from os"

end


let errno_matcher instrs faddr fnbytes fnhash =
  let base1 = todw (Str.matched_group 1 fnbytes) in
  let base2 = todw (Str.matched_group 2 fnbytes) in
  let sem = new geterrnofromoserr_semantics_t fnhash base1 base2 instrs in
  let msg = LBLOCK [ STR " with bases " ; base1#toPretty ; STR " and " ; base2#toPretty ] in
  sometemplate ~msg sem

let errno_patterns = [
  
  { regex_s = Str.regexp 
      ("8b44240433c93b04cd\\(........\\)74124183f92d72f18d48ed83f911770c6a0d58c3" ^
       "8b04cd\\(........\\)c30544ffffff6a0e593bc81bc023c183c008c3$") ;
    
    regex_f = (errno_matcher 23)
  } ;

  { regex_s = Str.regexp 
      ("8bff558bec8b450833c93b04cd\\(........\\)74134183f92d72f18d48ed83f911770e" ^
       "6a0d585dc38b04cd\\(........\\)5dc30544ffffff6a0e593bc81bc023c183c0085dc3$") ;
    
    regex_f = (errno_matcher 29)
  } ;

  (* V494:0x40b76e *)
  { regex_s = Str.regexp 
      ("558bec8b4d0833c03b0cc5\\(........\\)74274083f82d72f18d41ed83f81177056a0d" ^
       "585dc38d8144ffffff6a0e593bc81bc023c183c0085dc38b04c5\\(........\\)5dc3$") ;
    
    regex_f = (errno_matcher 28)
  }
]
      
