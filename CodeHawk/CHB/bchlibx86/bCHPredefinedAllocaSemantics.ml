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
open CHPretty

(* bchlib *)
open BCHLibTypes
open BCHMakeCallTargetInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil

module H = Hashtbl

let table = H.create 3

(* ======================================================== __alloca__(eax:size)
   hash    : 11e41922ff27869c267f0226b448d937
   instrs  : 19
   examples: V4b4:0x40dc40

  0x40    [ 0 ]       push ecx                  save ecx
  0x41    [ -4 ]      lea ecx, 0x4(esp,,1)      ecx := (esp + 4) = esp_in
  0x45    [ -4 ]      sub ecx, eax              ecx := ecx - eax = (esp_in - eax_in)
  0x47    [ -4 ]      sbb eax, eax              eax := 0 or -1
  0x49    [ -4 ]      not eax                   not eax
  0x4b    [ -4 ]      and ecx, eax              ecx := ecx & eax
  0x4d    [ -4 ]      mov eax, esp              eax := esp = (esp_in - 4)
  0x4f    [ -4 ]      and eax, 0xfffff000       eax := eax & 4294963200
--------------------------------------------------------------------------------
  0x54    [ -4 ]      cmp ecx, eax              cmp ecx, eax
  0x56    [ -4 ]      jc 0x40dc62               if (ecx < eax) then goto 0x40dc62
--------------------------------------------------------------------------------
  0x58    [ -4 ]      mov eax, ecx              eax := ecx
  0x5a    [ -4 ]      pop ecx                   restore ecx
  0x5b    [ 0 ]       xchg eax, esp             tmp := esp; esp := eax; eax := tmp
  0x5c   [  ?  ]      mov eax, (eax)            eax := arg.0000 = arg.0000_in
  0x5e   [  ?  ]      mov (esp,,1), eax         ? := eax = arg.0000_in
  0x61   [  ?  ]      ret                       return
--------------------------------------------------------------------------------
  0x62    [ -4 ]      sub eax, 0x1000           eax := eax - 4096
  0x67    [ -4 ]      test (eax), eax           test (eax), eax
  0x69    [ -4 ]      jmp 0x40dc54              goto 0x40dc54


   =============================================== ======= __alloca__(eax:size)
   hash   : d9fd5da9ba4d793a57eec03378c22267
   instrs : 17
   example: V225:0x402390

  0x90    [ 0 ]       push ecx                  save ecx
  0x91    [ -4 ]      cmp eax, 0x1000           cmp eax, 0x1000
  0x96    [ -4 ]      lea ecx, 0x8(esp,,1)      ecx := (esp + 8) = (esp_in + 4)
  0x9a    [ -4 ]      jc 0x4023b0               if (eax_in < 4096) then goto 0xb0
--------------------------------------------------------------------------------
  0x9c    [ -4 ]      sub ecx, 0x1000           ecx := ecx - 4096
  0xa2    [ -4 ]      sub eax, 0x1000           eax := eax - 4096
  0xa7    [ -4 ]      test (ecx), eax           test (ecx), eax
  0xa9    [ -4 ]      cmp eax, 0x1000           cmp eax, 0x1000
  0xae    [ -4 ]      jnc 0x40239c              if (eax >= 4096) then goto 0x9c
--------------------------------------------------------------------------------
  0xb0    [ -4 ]      sub ecx, eax              ecx := ecx - eax
  0xb2    [ -4 ]      mov eax, esp              eax := esp = (esp_in - 4)
  0xb4    [ -4 ]      test (ecx), eax           test (ecx), eax
  0xb6    [ -4 ]      mov esp, ecx              esp := ecx = ((esp_in - eax_in) + 4)
  0xb8   [  ?  ]      mov ecx, (eax)            ecx := var.0004 = ecx_in
  0xba   [  ?  ]      mov eax, 0x4(eax)         eax := arg.0000 = arg.0000_in
  0xbd   [  ?  ]      push eax                  esp := esp - 4 ; ? := eax
  0xbe   [  ?  ]      ret                       return


   ======================================================= __alloca__(eax:size)
   hash   : ea9e1808f313809c4630d7c5daab76d4
   instrs : 17
   example: V944:0x403c30

  0x30    [ 0 ]       push ecx                  save ecx
  0x31    [ -4 ]      lea ecx, 0x8(esp,,1)      ecx := (esp + 8) = (esp_in + 4)
  0x35    [ -4 ]      cmp eax, 0x1000           cmp eax, 0x1000
  0x3a    [ -4 ]      jc 0x403c51               if (eax_in < 4096) then goto 0x51
--------------------------------------------------------------------------------
  0x3c    [ -4 ]      sub ecx, 0x1000           ecx := ecx - 4096
  0x42    [ -4 ]      or (ecx), 0x0             ? :=  ?  (tmpN) | 0
  0x45    [ -4 ]      sub eax, 0x1000           eax := eax - 4096
  0x4a    [ -4 ]      cmp eax, 0x1000           cmp eax, 0x1000
  0x4f    [ -4 ]      ja 0x403c3c               if (eax > 4096) then goto 0x3c
--------------------------------------------------------------------------------
  0x51    [ -4 ]      sub ecx, eax              ecx := ecx - eax
  0x53    [ -4 ]      or (ecx), 0x0             ? :=  ?  (tmpN) | 0
  0x56    [ -4 ]      mov eax, esp              eax := esp = (esp_in - 4)
  0x58    [ -4 ]      mov esp, ecx              esp := ecx = ((esp_in - eax_in) + 4)
  0x5a   [  ?  ]      mov ecx, (eax)            ecx := var.0004 = ecx_in
  0x5c   [  ?  ]      mov eax, 0x4(eax)         eax := arg.0000 = arg.0000_in
  0x5f   [  ?  ]      push eax                  esp := esp - 4 ; ? := eax
  0x60   [  ?  ]      ret                       return

*)

class alloca_semantics_t
        (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  (* semantics is modeled by increasing the stack size by the value of eax;
     no alignment is performed
  *)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__alloca__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [STR self#get_name ; STR "("; xpr_to_pretty floc eaxv; STR ")"]

  method! get_commands (floc:floc_int) =
    let env = floc#f#env in
    let (esplhs,esplhscmds) = (esp_r WR)#to_lhs floc in
    let esp = env#mk_cpu_register_variable Esp in
    let eaxv = get_reg_value Eax floc in
    let cmds1 =
      floc#get_assign_commands esplhs (XOp (XMinus, [XVar esp; eaxv])) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx]] in
    esplhscmds @ cmds1 @ cmds2

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "dynamically allocates memory on the stack"

end


let _ = H.add table "alloca" (new alloca_semantics_t)

(* ================================================================ __alloca__16
  parameterized on absolute jump address

  0x4528c0    [ 0 ]       esp := esp - 4 ; var.0004 := ecx
  0x4528c1    [ -4 ]      ecx := (esp + 4) = esp_in
  0x4528c5    [ -4 ]      ecx := ecx - eax = (esp_in - eax)
  0x4528c7    [ -4 ]      eax := 0 or -1
  0x4528c9    [ -4 ]      not eax
  0x4528cb    [ -4 ]      ecx := ecx & eax
  0x4528cd    [ -4 ]      eax := esp = (esp_in - 4)
  0x4528cf    [ -4 ]      eax := eax & 4294963200
--------------------------------------------------------------------------------
  0x4528d4    [ -4 ]      cmp ecx, eax
  0x4528d6    [ -4 ]      if (ecx < eax) then goto 0x4528e2
--------------------------------------------------------------------------------
  0x4528d8    [ -4 ]      eax := ecx
  0x4528da    [ -4 ]      restore ecx
  0x4528db    [ 0 ]       tmp := esp; esp := eax; eax := tmp
  0x4528dc   [  ?  ]      eax := arg.0000 = arg.0000_in
  0x4528de   [  ?  ]      ? := eax = arg.0000_in
  0x4528e1   [  ?  ]      return
--------------------------------------------------------------------------------
  0x4528e2    [ -4 ]      eax := eax - 4096
  0x4528e7    [ -4 ]      test (eax), eax
  0x4528e9    [ -4 ]      goto 0x4528d4                         <- relative jump
--------------------------------------------------------------------------------
  0x461ae0    [ 0 ]       save ecx                               <-- entry point
  0x461ae1    [ -4 ]      ecx := (esp + 8) = (esp_in + 4)
  0x461ae5    [ -4 ]      ecx := ecx - eax = ((esp_in - eax_in) + 4)
  0x461ae7    [ -4 ]      ecx := ecx & 15
  0x461aea    [ -4 ]      eax := eax + ecx = (eax_in + ecx)
  0x461aec    [ -4 ]      ecx := 0 or -1
  0x461aee    [ -4 ]      eax := eax | ecx
  0x461af0    [ -4 ]      restore ecx
  0x461af1    [ 0 ]       goto 0x4528c0                        <-- absolute jump
*)


class alloca16_semantics_t
        (md5hash:string)
        (_jaddr:doubleword_int)
        (instrs):predefined_callsemantics_int =
object (self)

  (* semantics is modeled by increasing the stack size by the value of eax;
     no alignment is performed
  *)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__alloca16__"

  method! get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let ecxv = get_reg_value Ecx floc in
    LBLOCK [
        STR self#get_name;
        STR "(size:";
        xpr_to_pretty floc eaxv;
        STR ", ";
	xpr_to_pretty floc ecxv;
        STR ")"]

  method! get_commands (floc:floc_int) =
    let env = floc#f#env in
    let (esplhs,esplhscmds) = (esp_r WR)#to_lhs floc in
    let esp = env#mk_cpu_register_variable Esp in
    let eaxv = get_reg_value Eax floc in
    let cmds1 =
      floc#get_assign_commands esplhs (XOp (XMinus, [XVar esp; eaxv])) in
    let cmds2 = [floc#get_abstract_cpu_registers_command [Eax; Ecx]] in
    esplhscmds @ cmds1 @ cmds2

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "dynamically allocates memory on the stack"

end


let alloca_functions = H.fold (fun k v a -> a @ (get_fnhashes k v)) table []


let alloca16_matcher _faddr fnbytes fnhash =
  let addr = todw (Str.matched_group 1 fnbytes) in
  let sem = new alloca16_semantics_t fnhash addr 28 in
  let msg = LBLOCK [STR " with address "; addr#toPretty] in
  sometemplate ~msg sem


let alloca_patterns = [

  (* alloca16 *)
  { regex_s = Str.regexp
      ("518d4c24042bc81bc0f7d023c88bc42500f0ffff3bc8720a8bc159948b00890424c32d00" ^
       "1000008500ebe9518d4c24082bc883e10f03c11bc90bc159e9\\(........\\)$" ) ;

    regex_f = alloca16_matcher
  } ;

  { regex_s = Str.regexp
      ("518d4c24082bc883e10f03c11bc90bc159e9\\(........\\)518d4c24042bc81bc0f7d0" ^
       "23c88bc42500f0ffff3bc8720a8bc159948b00890424c32d001000008500ebe9$" ) ;

    regex_f = alloca16_matcher
  }
]
