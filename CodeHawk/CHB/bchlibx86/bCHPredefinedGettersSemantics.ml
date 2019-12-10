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
open BCHCPURegisters
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil

(* Semantics for functions that don't do anything, return a constant value, or
   return the value of some variable

   __fnop__  : returns without observable changes (includes functions that save
                and restore ebp as part of the function, but leave Eax untouched
   __fnop__a<n>__: returns with Ecx not preserved, with <n> argument bytes being
                   saved on the stack and then abandoned
   __f_<n>__   : returns the constant value n, without side effects
   __get_reg_<reg>: returns the value from register <reg>
   __get_gv_0x<x>: returns the value of global variable 0xx
   __get_fld_<n> : returns the value at offset n from register base
   __get_fld_fld_<n>_<n>: return the value of offset [n][n] from register base
   __get_arg_<n> : returns the value of the nth argument

*)

(*  ==================================================================== __fnop__

    ret     "0a3d72134fb3d6c024db4c510bc1605b"

    md5hash: 143aa3597c1d2eff93921fad3cac99de

  0x408f70   [ 0 ]    push ebp                  save ebp
  0x408f71   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x408f73   [ -4 ]   pop ebp                   restore ebp
  0x408f74   [ 0 ]    ret                       return

*)

class fnop_semantics_t 
  (md5hash:string) ?(adj=0) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__fnop__"

  method get_annotation (floc:floc_int) = 
    let adjs = if adj > 0 then " (adj " ^ (string_of_int adj) ^ ")" else "" in
    LBLOCK [ STR self#get_name ; STR "()" ; STR adjs ]

  method get_commands (floc:floc_int) = get_adjustment_commands adj floc

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "no observable effect"

end

(* =============================================================== __fnop_a<n>__
   Example: V5b7:0x442ebc

  0x442ebc   [ 0 ]    push ebp                  save ebp
  0x442ebd   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x442ebf   [ -4 ]   push ecx                  save ecx
  0x442ec0   [ -8 ]   mov -0x4(ebp), eax        var.0008 := eax = eax_in
  0x442ec3   [ -8 ]   pop ecx                   ecx := eax_in ; esp := (esp_in - 4)
  0x442ec4   [ -4 ]   pop ebp                   restore ebp
  0x442ec5   [ 0 ]    ret                       return

*)
class fnop_argsemantics_t
  (md5hash:string) ?(adj=0) (a:int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__fnop_a" ^ (string_of_int a) ^ "__"

  method get_annotation (floc:floc_int) =
    let adjs = if adj > 0 then " (adj " ^ (string_of_int adj) ^ ")" else "" in
    LBLOCK [ STR self#get_name ; STR "()" ; STR adjs ]

  method get_commands (floc:floc_int) = 
    [ floc#get_abstract_cpu_registers_command [ Ecx ] ]

  method get_parametercount = 0 

  method get_instrcount = instrs

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "no observable effect except using Ecx"

end

(* =================================================================== __f_<n>__
   returns the constant value n

*)

class fn_semantics_t 
  (md5hash:string) 
  (n:int) ?(adj=0) 
  ?(reg=Eax) 
  ?(abstract_regs=[])
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__f_" ^ (intvalue_to_string n) ^ "__"

  method get_annotation (floc:floc_int) =
    let adjs = if adj > 0 then " (adj " ^ (string_of_int adj) ^ ")" else "" in
    LBLOCK [ STR (cpureg_to_string reg) ; STR " := " ; 
	     STR (intvalue_to_string n) ; STR adjs ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs reg floc in
    let adjcmds = get_adjustment_commands adj floc in
    let cmds = floc#get_assign_commands lhs (int_constant_expr n) in
    let acmds = [ floc#get_abstract_cpu_registers_command abstract_regs ] in
    List.concat [ lhscmds ; cmds ; acmds ; adjcmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "returns " ^ (string_of_int n)

end

(* =================================================================== __get_reg__
   returns the contents of a register

   example: Vdd2:0x402bd0
   md5hash: 8b73c93fa9cf6a4ae35cd16ec1079219

  0x402bd0   [ 0 ]    mov eax, ecx              eax := ecx = ecx_in
  0x402bd2   [ 0 ]    ret                       return

   ------------------------------------------------------------------------
   example: Vcf9:0x402a40
   md5hash: 08a76208569c4ebbe0729b35872de56a

  0x402a40   [ 0 ]    push ebp                  save ebp
  0x402a41   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x402a43   [ -4 ]   push ecx                  save ecx
  0x402a44   [ -8 ]   mov -0x4(ebp), ecx        var.0008 := ecx = ecx_in
  0x402a47   [ -8 ]   mov eax, -0x4(ebp)        eax := var.0008 = ecx_in
  0x402a4a   [ -8 ]   mov esp, ebp              esp := ebp = (esp_in - 4)
  0x402a4c   [ -4 ]   pop ebp                   restore ebp
  0x402a4d   [ 0 ]    ret                       return

*)
class fr_semantics_t 
  (md5hash:string) (reg:cpureg_t) ?(adj=0) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__get_" ^ (cpureg_to_string reg) ^ "__"

  method get_annotation (floc:floc_int) =
    let regv = get_reg_value reg floc in
    LBLOCK [ STR "eax := " ; xpr_to_pretty floc regv ]

  method get_commands (floc:floc_int) =
    let regv = get_reg_value reg floc in
    let adjcmds = get_adjustment_commands adj floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let cmds = floc#get_assign_commands eaxlhs regv in
    eaxlhscmds @ cmds @ adjcmds

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a,self#get_name)

  method get_description = "returns a register value"

end

(* =============================================================== get_gv_0xaaaaaa
   returns the value of a fixed global variable

*)

class get_gv_semantics_t 
  (md5hash:string) (gv:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__get_gv_" ^ gv#to_hex_string

  method get_annotation (floc:floc_int) =
    let rhs = (absolute_op gv 4 RD)#to_expr floc in
    LBLOCK [ STR "eax := gv_" ; gv#toPretty ; STR " = " ; xpr_to_pretty floc rhs ]

  method get_commands (floc:floc_int) =
    let rhs = (absolute_op gv 4 RD)#to_expr floc in
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let cmds = floc#get_assign_commands lhs rhs in
    List.concat [ lhscmds ; cmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "retrieves value of global variable"

end

(* =============================================================== __get_fld__(x)
   returns the value at offset x from a given register base

  0xa0    [ 0 ]    push ebp                  save ebp
  0xa1    [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0xa3    [ -4 ]   push ecx                  save ecx
  0xa4    [ -8 ]   mov -0x4(ebp), ecx        var.0008 := ecx = ecx_in
  0xa7    [ -8 ]   mov eax, -0x4(ebp)        eax := var.0008 = ecx_in
  0xaa    [ -8 ]   mov eax, 0x8(eax)         eax := (ecx_in)[8] = (ecx_in)[8]_in
  0xad    [ -8 ]   mov esp, ebp              esp := ebp = (esp_in - 4)
  0xaf    [ -4 ]   pop ebp                   restore ebp
  0xb0    [ 0 ]    ret                       return

   ----------------------------------------------------------------------------
   example: V1da: 0x438584

  0x438584   [ 0 ]    mov eax, 0xb8(eax)   eax := (eax_in)[184] = (eax_in)[184]_in
  0x43858a   [ 0 ]    ret                  return


*)
class get_fld_semantics_t 
  (md5hash:string) 
  (reg:cpureg_t) 
  (offset:int)
  ?(rvreg=Eax)
  ?(abstractregs=[])
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__get_" ^ (cpureg_to_string reg) ^ "[" ^ (string_of_int offset) ^ "]__"

  method get_annotation (floc:floc_int) =
    let v = get_reg_derefvalue reg offset floc in
    LBLOCK [ STR (cpureg_to_string rvreg) ; STR " := " ;
	     STR (cpureg_to_string reg) ; STR "[" ;
	     INT offset ; STR "] = " ; xpr_to_pretty floc v ]

  method get_commands (floc:floc_int) =
    let v = get_reg_derefvalue reg offset floc in
    let (lhs,lhscmds) = get_reg_lhs reg floc in
    let cmds = floc#get_assign_commands lhs v in
    let acmds = [ floc#get_abstract_cpu_registers_command abstractregs ] in
    List.concat [ lhscmds ; cmds ; acmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "returns value at offset from register"

end

(* ================================================================= get_fld_(x)__
   example: V429:0x417360

  0x417360   [ 0 ]    mov eax, 0x10(eax)  eax := (eax_in)[16]_in
  0x417363   [ 0 ]    mov eax, 0x14(eax)  eax := ((eax_in)[16]_in)[20]_in
  0x417366   [ 0 ]    ret                 return
*)
class get_fld_fld_semantics_t
  (md5hash:string) 
  (reg:cpureg_t) 
  (offset1:int) 
  (offset2:int)
  ?(size=4)
  ?(abstractregs=[])
  ?(rvreg=Eax)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__get_fld_" ^ (string_of_int offset1) ^ "_" ^
    (string_of_int offset2) ^ "__"

  method get_annotation (floc:floc_int) =
    let x = get_reg_derefvalue reg offset1 floc in
    let xx = get_x_derefvalue x offset2 floc in
    LBLOCK [ STR (cpureg_to_string rvreg) ; STR (cpureg_to_string reg) ; STR "[" ;
	     INT offset1 ; STR "][" ; INT offset2 ; STR "] = " ;
	     xpr_to_pretty floc xx ]

  method get_commands (floc:floc_int) =
    let x = get_reg_derefvalue reg offset1 floc in
    let xx = get_x_derefvalue x offset2 floc in
    let size = int_constant_expr size in
    let (lhs,lhscmds) = get_reg_lhs rvreg floc in
    let cmds = floc#get_assign_commands lhs ~size xx in
    let acmds = [ floc#get_abstract_cpu_registers_command abstractregs ] in
    List.concat [ lhscmds ; cmds ; acmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "returns reg[offset1][offset2]"

end

(* get argument value (pp/4) and pop (qq) bytes off the stack

  0x401000  8b 44 24 pp  mov eax, 0xpp(esp,,1)  eax := arg.00xx = arg.00pp_in
  0x401004  c2 qq 00     ret qq                 return (increment stackpointer by qq)
*)
class get_arg_semantics_t
  (md5hash:string) 
  (argnr:int) 
  (paramcount:int) 
  ?(adj=0) 
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__get_arg_" ^ (string_of_int argnr) ^ "__"

  method get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args argnr floc in
    LBLOCK [ STR " eax := " ; xpr_to_pretty floc arg ]

  method get_commands (floc:floc_int) =
    let arg = get_arg floc#get_call_args argnr floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let adjcmds = get_adjustment_commands adj floc in
    let cmds = floc#get_assign_commands eaxlhs arg in
    eaxlhscmds @ cmds @ adjcmds

  method get_parametercount = paramcount

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "returns argument value"
    
end
    

let getter_functions = [
  new fnop_semantics_t "0a3d72134fb3d6c024db4c510bc1605b" 1 ;    (* ret *)
  new fnop_semantics_t "78ce8f147c913f3c40828bb76ea9f131" 4 ;    (* push ebp, pop: mwc-00:V0be:0x7c12a340 *)
  new fnop_semantics_t "70354a8ed0817704f671a86541bb6932" 5 ;    (* Vc21:0x1000df29 *)
  new fnop_semantics_t "78edea9dee590c0a42b0a144a8186717" ~adj:4 1 ; (* ret, pop 4 *)
  new fnop_semantics_t "2f5532c441aebfd21d7a4518c245a0db" ~adj:8 1 ; (* V007:0x421e40 *)
  new fnop_semantics_t "934e041f841830a7b98daaffe48c02bd" ~adj:8 4 ;
  new fnop_semantics_t "baf15a7bf44f671378a6d756c7a7d8b1" ~adj:4 4 ;  (* V1da:0x41aa94 *)
  new fnop_semantics_t "ba9fa3dbcc2b11ee1f2958deab1c9636" ~adj:12 1 ; (* V9ce:0x419a51 *)
  new fnop_semantics_t "143aa3597c1d2eff93921fad3cac99de" 4 ;
  new fnop_semantics_t "4019157193f6d7941cd0e11e6173d306" ~adj:16 1 ; (* mwc-00:V392:0x1002a2f0 *)
  new fnop_semantics_t "c5c7c6c595aa8cca036905a50513bd89" ~adj:16 5 ; (* Vc21:0x100130e3 *)
  new fnop_semantics_t "684699084c3e7892b381dfd430bec549" ~adj:28 5 ; (* Vc21:0x1000db74 *)
  new fnop_semantics_t "a235621dababf9aff595d6efd913f06d" ~adj:32 5 ; (* Vc21:0x1000e43a *)
  new fnop_semantics_t "08b3610a73bf8ced16794bc891a5cb76" 7 ;     (* mwc-00:V148:0x403b80 *)

  new fnop_argsemantics_t "d45607e00be3b11df897c38a09126636" 4 7 ; (* V5b7:0x442ebc *)
  new fnop_argsemantics_t "78f1168bbb4ae869034ed50aeae70eec" 5 9 ; (* V5b7:0x450ce0 *)
  new fnop_argsemantics_t "4fef8ca89098b6cacf5124882a54245c" 6 9 ; (* V5b7:0x450d10 *)
  new fnop_argsemantics_t "8fd9fd349eee95207ec155fdceb5ed6d" 8 9 ; (* V5b7:0x450d00 *)
  
  new fn_semantics_t "7040d600d810f4d1b53f4e4156bb7147" 0 2 ;
  new fn_semantics_t "07533b3bb9082d4dc0e18877cae746e0" 0 ~reg:Al 2 ; (* mwc-00:V392:0x1002a3e0 *)
  new fn_semantics_t "d0ec9de434720bb72c08010b82e76dac" 0 5 ;          (* V00bc16:0x407240 *)
  new fn_semantics_t "6931e1590e3a73d868bc6db7e4983dd4" 0 5 ;        (* mwc-00:V148:0x4046a0 *)
  new fn_semantics_t "13219e6a54993b9471bc6049bdec88ec" 0 ~adj:4 2 ;
  new fn_semantics_t "45357a6e308809ca92610b743b040925" 0 ~adj:4 5 ;   (* "mwc-00:V0be:0x7c12a620" *)
  new fn_semantics_t "73f6144abcb034daf85aaee619ba7b49" 0 ~adj:4 ~reg:Al 2 ; (* V00dbb9:0x40c980 *)
  new fn_semantics_t "fc23d98ea6144177a02fc5d16310c974" 0 ~adj:8 2 ;   (* V9ce:0x41775e *)
  new fn_semantics_t "1dfb3e8f888bf4e8f7e9255bded73bd4" 0 ~adj:8 ~reg:Al 2 ; (* mwc-00:V392:0x10001190 *)
  new fn_semantics_t "47f1f4c07c01bef7095a08a4057cd0f0" 0 ~adj:8 5 ;   (* V1da:0x41b23c *)
  new fn_semantics_t "435914491e238f20c6589a97e0ac6bf2" 0 ~adj:12 2 ;  (* V9ce:0c417780 *)
  new fn_semantics_t "ef1b81cf9bad4b2507692ab2918eb57b" 0 ~adj:12 ~reg:Al 2 ; (* mwc-00:V392:0x10001180 *)  
  new fn_semantics_t "2cbbf57290fddcd56067b201b9eaa6a8" 0 ~adj:12 5 ;  (* mwc-00:V0be:0x7c12a610 *) 
  new fn_semantics_t "ce6552796ecf9d92271423cf4bb7d146" 0 ~adj:16 2 ;
  new fn_semantics_t "7b01bd0058693084d86fa769b6868f47" 0 ~adj:20 2 ;  (* V9ce:0x4199df *)
  new fn_semantics_t "67a41380ab3fad42211fbd9af73260cc" 0 ~adj:20 5 ;  (* mwc-00:V0be:0x7c12bcf0 *)
  new fn_semantics_t "b01be991b1af30e6534e3e770af8acfd" 0 ~adj:24 2 ;  (* V9ce:0x41771f *)
  new fn_semantics_t "16205ac1f30a8d0793ee3b12aad4e748" 1 3 ;   (* mwc-00:V392:0x10045fa3 *)
  new fn_semantics_t "d8013a1adde61d0d2651d935f0426267" 1 3 ;
  new fn_semantics_t "3398dfb3f47e097d6f81e1a70d82362f" 1 ~adj:4 3 ;
  new fn_semantics_t "13ae0878280eb39991609e8f506fde59" 1 ~adj:8 3 ;  (* V9ce:0x41d8c6 *)
  new fn_semantics_t "87dae7dda07e2bcd22c0cc8749448c82" 1 ~adj:12 3 ; (* V9ce:0x417785 *)
  new fn_semantics_t "d7e03914e2c4ceb29d1024de7aac3037" 1 ~adj:12 3 ; (* Vf95d3f:0x10002076 *)
  new fn_semantics_t "cf3f18452c43838bbdffbdb959a9df7a" 1 ~adj:16 3 ; (* V9ce:0x41d8d7 *)
  new fn_semantics_t "704ef94333ee90a596d614cddd9e8c67" 1 ~adj:24 3 ; (* V9ce:0x41d8d1 *)
  new fn_semantics_t "4086fc06c27fe3b41603ebd12700a151" 1 ~reg:Al 5 ; (* mwc-00:Vefc:0x10005960 *)
  new fn_semantics_t "485c267da0ed5b3e12e2a28b7038402b" 1 2 ;  (* 1 byte *)
  new fn_semantics_t "6510ed01a66ada2c58f90d52c5d2b04e" 3 3 ;
  new fn_semantics_t "3745f1bcc2a368084d0980d589d8571f" 8 2 ;
  new fn_semantics_t "b691041c4f831c3d2745c2a4ddd33dae" (-1) ~adj:4 5 ; (* V1da:0x410afc *)
  new fn_semantics_t "e38e56f396cd2629a37fdf27c566148f" (-1) 5 ;  (* mwc-00:V0be:0x7c12a740 *)
  new fn_semantics_t "d59f8ce46bad2605ba01e9a6a5c6e2aa" 1 10 ;          (* V5b7:0x45037c *)
  new fn_semantics_t "832b0f18ac4a2bafaa57cb4675a66a75" ~reg:Al 0 11 ;  (* V5b7:0x44646c *)
  new fn_semantics_t "f4d2cf1b7a750a0c37f4fd977bcc4da0" (-1) 2 ;        (* V21d:0x805b68 *)

  new fr_semantics_t "08a76208569c4ebbe0729b35872de56a" Ecx 8 ;
  new fr_semantics_t "146c3299b47a122667564270182aba64" Ecx ~adj:4 2 ;  (* mwc-00:V1bf:0x40e730 *)
  new fr_semantics_t "30ec4dbd4e21356e2f546a0274aaa6dc" Ecx ~adj:12 2 ; (* mwc-00:V34e:0x40d560 *)
  new fr_semantics_t "485a54660e286108a40267bec846a354" Ecx ~adj:4 8 ;  (* mwc-00:V1bf:0x4063f0 *)
  new fr_semantics_t "8b73c93fa9cf6a4ae35cd16ec1079219" Ecx 2 ;

  new get_arg_semantics_t "8a74c5a9217a950886ac69f691692b72" 1 1 5 ;  (* V5b7:0x453ef0 *)
  new get_arg_semantics_t "97287512b60f06ad23dc501ad63654e3" 1 1 ~adj:4 5 ; (* mwc-00:V34e:0x45dba8 *)
  new get_arg_semantics_t "efff4c99d7e9bca794feec9d6831207c" 2 2 5 ;  (* mwc-00:V148:0x405690 *)
]
  

let getter_patterns = [

  (* MOV al,imm8 *)
  {regex_s = Str.regexp "b0\\(..\\)c3$" ;

   regex_f = fun faddr fnbytes fnhash ->
     let v = toimm2 (Str.matched_group 1 fnbytes) in
     let sem = new fn_semantics_t fnhash ~reg:Al v 2 in
     let msg = LBLOCK [ STR " with return register al " ] in
     sometemplate ~msg sem
  } ;
   
  (* MOV eax,moffs32 *)
  { regex_s = Str.regexp "a1\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new get_gv_semantics_t fnhash gv 2 in
      sometemplate sem
  } ;

  (* MOV eax,imm32 *)
  { regex_s = Str.regexp "b8\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let imm = todw (Str.matched_group 1 fnbytes) in
      let sem = new fn_semantics_t fnhash imm#to_int 2 in
      sometemplate sem
  } ;

  (* MOV eax,imm32 (V00bc16:) *)
  { regex_s = Str.regexp "55b8\\(........\\)89e55dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let imm = todw (Str.matched_group 1 fnbytes) in
      let sem = new fn_semantics_t fnhash imm#to_int 5 in
      sometemplate sem
  } ;

  (* MOV eax,imm32 ; ret xxxx *)
  { regex_s = Str.regexp "b8\\(........\\)c2\\(..\\)00$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let imm = todw (Str.matched_group 1 fnbytes) in
      let adj = tooff (Str.matched_group 2 fnbytes) in
      let sem = new fn_semantics_t fnhash imm#to_int ~adj 2 in
      let msg = LBLOCK [ STR " with adjustment " ; INT adj ] in
      sometemplate ~msg sem
  } ;
  (* MOV eax,imm32 ; ret *)
  { regex_s = Str.regexp "558becb8\\(........\\)5dc3$" ;

    regex_f =
      fun faddr fnbytes fnhash ->
      let imm = todw (Str.matched_group 1 fnbytes) in
      let sem = new fn_semantics_t fnhash imm#to_int 5 in
      sometemplate sem
  } ;

  (* MOV eax,imm32 ; ret xxxx *)
  { regex_s = Str.regexp "558becb8\\(........\\)5dc2\\(....\\)$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let imm = todw (Str.matched_group 1 fnbytes) in
      let adj = (tow (Str.matched_group 2 fnbytes))#to_int in
      let sem = new fn_semantics_t fnhash imm#to_int ~adj 5 in
      let msg = LBLOCK [ STR " with adjustment " ; INT adj ] in
      sometemplate ~msg sem
  } ;

  (* get fld from ecx addressed struct *)
  { regex_s = Str.regexp "558bec51894dfc8b45fc8b40\\(..\\)8be55dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let sem = new get_fld_semantics_t fnhash Ecx offset 9 in
      let msg = LBLOCK [ STR " with base register ecx" ] in
      sometemplate ~msg sem
  } ;

  (* get fld from register addressed struct *)
  { regex_s = Str.regexp "8b4\\(.\\)\\(..\\)c3$" ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let reg = regindexstring_to_reg (Str.matched_group 1 fnbytes) in
      let offset = tooff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_semantics_t fnhash reg offset 2 in
      let msg = LBLOCK [ STR " with base register " ; STR (cpureg_to_string reg) ] in
      sometemplate ~msg sem
  } ;

  (* get fld from register addressed struct *)
  { regex_s = Str.regexp "8a4\\(.\\)\\(..\\)c3$" ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let reg = regindexstring_to_reg (Str.matched_group 1 fnbytes) in
      let offset = tooff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_semantics_t fnhash reg offset ~rvreg:Al 2 in
      let msg = LBLOCK [ STR " with base register " ; STR (cpureg_to_string reg) ] in
      sometemplate ~msg sem
  } ;

  (* get fld from register addressed struct *)
  { regex_s = Str.regexp "8b8\\(.\\)\\(........\\)c3$" ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let reg = regindexstring_to_reg (Str.matched_group 1 fnbytes) in
      let offset = todwoff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_semantics_t fnhash Eax offset 2 in
      let msg = LBLOCK [ STR " with base register " ; STR (cpureg_to_string reg) ] in
      sometemplate ~msg sem
  } ;

  (* get fld from register addressed struct
  0x429ecc   [ 0 ]    mov al, 0x220(eax)        al := (eax_in)[544] = (eax_in)[544]_in
  0x429ed2   [ 0 ]    ret                       return
  *)
  { regex_s = Str.regexp "8a8\\(.\\)\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let reg = regindexstring_to_reg (Str.matched_group 1 fnbytes) in
      let offset = todwoff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_semantics_t fnhash Eax offset ~rvreg:Al 2 in
      let msg = LBLOCK [ STR " with base register " ; STR (cpureg_to_string reg) ] in
      sometemplate ~msg sem
  } ;

  (* get fld from register addressed struct
     example: V5b7:0x4434e4

  0x4434e4   [ 0 ]    push ebp             save ebp
  0x4434e5   [ -4 ]   mov ebp, esp         ebp := esp = (esp_in - 4)
  0x4434e7   [ -4 ]   add esp, -0x8        esp := esp + -8 = (esp_in - 12)
  0x4434ea  [ -12 ]   mov -0x4(ebp), eax   var.0008 := eax = eax_in
  0x4434ed  [ -12 ]   mov eax, -0x4(ebp)   eax := var.0008 = eax_in
  0x4434f0  [ -12 ]   mov eax, 0x7c(eax)   eax := (eax_in)[124] = (eax_in)[124]_in
  0x4434f3  [ -12 ]   mov -0x8(ebp), eax   var.0012 := eax = (eax_in)[124]_in
  0x4434f6  [ -12 ]   mov eax, -0x8(ebp)   eax := var.0012 = (eax_in)[124]_in
  0x4434f9  [ -12 ]   pop ecx              ecx := (eax_in)[124]_in ; esp := (esp_in - 8)
  0x4434fa   [ -8 ]   pop ecx              ecx := eax_in ; esp := esp + 4 = (esp_in - 4)
  0x4434fb   [ -4 ]   pop ebp              restore ebp
  0x4434fc   [ 0 ]    ret                  return

  *)
  { regex_s = Str.regexp "558bec83c4f88945fc8b45fc8b40\\(..\\)8945f88b45f859595dc3$" ;

    regex_f = fun fadd fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let sem = new get_fld_semantics_t fnhash Eax offset ~abstractregs:[Ecx] 12 in
      let msg = LBLOCK [ STR " with base register Eax" ] in
      sometemplate ~msg sem
  } ;

  { regex_s = Str.regexp 
      "558bec83c4f88945fc8b45fc8b80\\(........\\)8945f88b45f859595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = todwoff (Str.matched_group 1 fnbytes) in
      let sem = new get_fld_semantics_t fnhash Eax offset ~abstractregs:[Ecx] 12 in
      let msg = LBLOCK [ STR " with base register Eax" ] in
      sometemplate ~msg sem
  } ;

  (* get fld from fld from eax addressed struct *)
  { regex_s = Str.regexp "8b40\\(..\\)8b40\\(..\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset1 = tooff (Str.matched_group 1 fnbytes) in
      let offset2 = tooff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_fld_semantics_t fnhash Eax offset1 offset2 3 in
      let msg = LBLOCK [ STR " with base register eax " ] in
      sometemplate ~msg sem
  } ;

  (* get fld from fld from eax addressed struct *)
  { regex_s = Str.regexp "8b40\\(..\\)8a40\\(..\\)c3$" ;        (* move 1 byte *)

    regex_f = fun faddr fnbytes fnhash ->
      let offset1 = tooff (Str.matched_group 1 fnbytes) in
      let offset2 = tooff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_fld_semantics_t fnhash Eax offset1 offset2 ~size:1 ~rvreg:Al 3 in
      let msg = LBLOCK [ STR " with base register eax " ] in
      sometemplate ~msg sem
  } ;  

  (* get fld from fld from eax addressed struct

  0x41d9ac   [ 0 ]    mov eax, 0x10(eax)  eax := (eax_in)[16] = (eax_in)[16]_in
  0x41d9af   [ 0 ]    mov dl, 0x19(eax)   dl := ((eax_in)[16]_in)[25]_in
  0x41d9b2   [ 0 ]    mov eax, edx        eax := edx
  0x41d9b4   [ 0 ]    ret                 return
  *)
  { regex_s = Str.regexp "8b40\\(..\\)8a50\\(..\\)8bc2c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset1 = tooff (Str.matched_group 1 fnbytes) in
      let offset2 = tooff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_fld_semantics_t fnhash Eax offset1 offset2 ~size:1 4 in
      let msg = LBLOCK [ STR " with base register eax " ] in
      sometemplate ~msg sem
  } ;  

  (* get fld from fld from eax addressed struct
     example: V5b7:0x4507e8

  0x4507e8   [ 0 ]    push ebp              save ebp
  0x4507e9   [ -4 ]   mov ebp, esp          ebp := esp = (esp_in - 4)
  0x4507eb   [ -4 ]   add esp, -0x8         esp := esp + -8 = (esp_in - 12)
  0x4507ee  [ -12 ]   mov -0x4(ebp), eax    var.0008 := eax = eax_in
  0x4507f1  [ -12 ]   mov eax, -0x4(ebp)    eax := var.0008 = eax_in
  0x4507f4  [ -12 ]   mov eax, 0x30(eax)    eax := (eax_in)[48] = (eax_in)[48]_in
  0x4507f7  [ -12 ]   mov eax, 0x8(eax)     eax := ((eax_in)[48]_in)[8]_in
  0x4507fa  [ -12 ]   mov -0x8(ebp), eax    var.0012 := eax = ((eax_in)[48]_in)[8]_in
  0x4507fd  [ -12 ]   mov eax, -0x8(ebp)    eax := var.0012 = ((eax_in)[48]_in)[8]_in
  0x450800  [ -12 ]   pop ecx               ecx := ((eax_in)[48]_in)[8]_in ; esp := esp + 4 = (esp_in - 8)
  0x450801   [ -8 ]   pop ecx               ecx := eax_in ; esp := esp + 4 = (esp_in - 4)
  0x450802   [ -4 ]   pop ebp               restore ebp
  0x450803   [ 0 ]    ret                   return

  *)
  { regex_s = Str.regexp 
      ("558bec83c4f88945fc8b45fc8b40\\(..\\)8b40\\(..\\)8945f88b45f859595dc3$") ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset1 = tooff (Str.matched_group 1 fnbytes) in
      let offset2 = tooff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_fld_semantics_t 
	fnhash Eax offset1 offset2 ~abstractregs:[Ecx] 13 in
      let msg = LBLOCK [ STR " with base register Eax" ] in
      sometemplate ~msg sem
  } ;

  (* get fld from fld from eax addressed struct (1 byte)
     example: V21d:6a15d4
  *)
  { regex_s = Str.regexp
      "558bec83c4f88945fc8b45fc8b40\\(..\\)8a40\\(..\\)8845fb8a45fb59595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset1 = tooff (Str.matched_group 1 fnbytes) in
      let offset2 = tooff (Str.matched_group 2 fnbytes) in
      let sem = new get_fld_fld_semantics_t 
	fnhash Eax offset1 offset2 ~abstractregs:[Ecx] ~rvreg:Al 13 in
      let msg = LBLOCK [ STR " with base register Eax" ] in
      sometemplate ~msg sem
  } ;

  (*
    0x401000  8b 44 24 pp  mov eax, 0xpp(esp,,1)  eax := arg.00xx = arg.00pp_in
    0x401004  c2 qq 00     ret qq                 return (increment stackpointer by qq)
  *)
  { regex_s = Str.regexp "8b4424\\(..\\)c2\\(..\\)00$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let pp = tooff (Str.matched_group 1 fnbytes) in   (* argument offset *)
      if pp > 0 && pp mod 4 = 0 then 
	let qq = tooff (Str.matched_group 2 fnbytes) in   (* bytes popped *)
	if qq > 0 && qq mod 4 = 0 then
	  let argnr = pp / 4 in
	  let adj = qq in
	  let paramcount = qq / 4 in
	  let sem = new get_arg_semantics_t fnhash argnr paramcount ~adj 2 in
	  let msg = LBLOCK [ STR " with argument " ; INT argnr ; STR " and ajustment " ;
			     INT adj ] in
	  sometemplate ~msg sem
	else None
      else None
  } ;

  (*
  0x445330   [ 0 ]    mov eax, 0x8(esp,,1)      eax := arg.0008 = arg.0008_in
  0x445334   [ 0 ]    ret                       return
  *)
  { regex_s = Str.regexp "8b4424\\(..\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let pp = tooff (Str.matched_group 1 fnbytes) in
      if pp > 0 && pp mod 4 = 0 then
	let argnr = pp / 4 in
	let paramcount = argnr in
	let sem = new get_arg_semantics_t fnhash argnr paramcount 2 in
	let msg = LBLOCK [ STR " with argument " ; INT argnr ] in
	sometemplate ~msg sem
      else None
  }
      
]


