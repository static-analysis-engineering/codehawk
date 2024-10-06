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
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt

(* bchlib *)
open BCHBasicTypes
open BCHBCTypeUtil
open BCHFunctionInterface
open BCHLibTypes
open BCHMakeCallTargetInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHPredefinedUtil


(* Functions that are called at the beginning of many functions to set up
   exception handling pointers and dynamically allocate stack space

   __SEH_prolog4
   __SEH_prolog4_GS
*)

let get_sehprolog4_annotation
      (name:string)
      (exnhandler:doubleword_int)
      (cookie:doubleword_int)
      (floc:floc_int) =
  try
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [
        STR name; STR "(scopetable:"; xpr_to_dspretty floc arg1;
	STR ",size:"; xpr_to_pretty floc arg2;
	STR ") [handler:"; exnhandler#toPretty;
	STR ", cookie:"; cookie#toPretty; STR "]"]
  with
    _ -> LBLOCK [STR name; STR "(?,?)"]


let get_sehprolog4_chif
      ?(gs=false) (exnhandler4:doubleword_int) (floc:floc_int) =
  let suffix = if gs then "_GS" else "" in
  let name = "__SEH_prolog4" ^ suffix in
  let ebp = floc#env#mk_cpu_register_variable Ebp in
  let ebx = floc#env#mk_cpu_register_variable Ebx in
  let esi = floc#env#mk_cpu_register_variable Esi in
  let edi = floc#env#mk_cpu_register_variable Edi in
  let esp = floc#env#mk_cpu_register_variable Esp in
  try
    let size = get_arg floc#get_call_args 2 floc in
    let xnhandler = num_constant_expr exnhandler4#to_numerical in
    let (esplhs,esplhscmds) = get_reg_lhs Esp floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let (ebplhs,ebplhscmds) = get_reg_lhs Ebp floc in
    match size with
    | XConst (IntConst num) ->
      let adj = num#toInt in
      let adj24 = int_constant_expr (adj + 28) in
      let xm2 = int_constant_expr (-2) in
      let x4 = int_constant_expr 4 in
      let x12 = int_constant_expr 12 in
      let (loca8,lcmdsa8) = get_arg_lhs 8 floc in
      let (loca4,lcmdsa4) = get_arg_lhs 4 floc in
      let (loc0,lcmds0) = get_returnaddress_lhs floc in
      let (loc4,lcmds4) = get_var_lhs 4 floc in
      let (loc8,lcmds8) = get_var_lhs 8 floc in
      let (loc16,lcmds16) = get_var_lhs 16 floc in
      let (loc8s,lcmds8s) = get_allocavar_lhs 8 adj floc in
      let (loc12s,lcmds12s) = get_allocavar_lhs 12 adj floc in
      let (loc16s,lcmds16s) = get_allocavar_lhs 16 adj floc in
      let (loc20s,lcmds20s) = get_allocavar_lhs 20 adj floc in
      let cmdsa8 = floc#get_assign_commands loca8 (XVar ebp) in
      let cmdsa4 = [ABSTRACT_VARS [loca4]] in (* cookie xor scopetable *)
      let cmds0 = floc#get_assign_commands loc0 xm2 in
      let cmds4 = floc#get_assign_commands loc4 xnhandler in
      let cmds8 = [ABSTRACT_VARS [loc8]] in    (* fs:0x0 *)
      let cmds16 =
        floc#get_assign_commands loc16 (XOp (XMinus, [XVar esp; adj24])) in
      let cmds8s = floc#get_assign_commands loc8s (XVar ebx) in
      let cmds12s = floc#get_assign_commands loc12s (XVar esi) in
      let cmds16s = floc#get_assign_commands loc16s (XVar edi) in
      let cmds20s = [ABSTRACT_VARS [loc20s]] in  (* cookie xor ebp *)
      let cmdsebp =
        floc#get_assign_commands ebplhs (XOp (XPlus, [XVar esp; x4])) in
      let cmdseax =
        floc#get_assign_commands eaxlhs (XOp (XMinus, [XVar esp; x12])) in
      let cmdsesp =
        floc#get_assign_commands esplhs (XOp (XMinus, [XVar esp; adj24])) in
      let gscmds = if gs then
	  let (loc20,lcmds20) = get_var_lhs 20 floc  in
	  let cmds20 = [ABSTRACT_VARS [loc20]] in
	  lcmds20 @ cmds20
	else
	  [] in
      lcmdsa8
      @ lcmdsa4
      @ lcmds0
      @ lcmds4
      @ lcmds8
      @ lcmds16
      @	lcmds8s
      @ lcmds12s
      @ lcmds16s
      @ lcmds20s
      @	cmdsa8
      @ cmdsa4
      @ cmds0
      @ cmds4
      @ cmds8
      @ cmds16
      @	cmds8s
      @ cmds12s
      @ cmds16s
      @ cmds20s
      @	ebplhscmds
      @ cmdsebp
      @ eaxlhscmds
      @ cmdseax
      @ gscmds
      @ esplhscmds
      @ cmdsesp
    | _ -> [floc#get_abstract_cpu_registers_command [Eax; Esp; Ebp]]
  with
  | BCH_failure p ->
    begin
      ch_error_log#add (name ^ " semantics") p;
      [floc#get_abstract_cpu_registers_command [Eax; Esp; Ebp]]
    end


(* =========================================== __SEH_prolog4(eh4_scopetable,size)

  0x50   [ 0 ]       push fp:0x403ab0          esp := esp - 4;
                                                  var.0004 := 4209328
  0x55   [ -4 ]      push %fs:0x0              esp := esp - 4;
                                                  var.0008 :=  ?  (tmpN)
  0x5c   [ -8 ]      mov eax, 0x10(esp,,1)     eax := arg.0008 = arg.0008_in
  0x60   [ -8 ]      mov 0x10(esp,,1), ebp     arg.0008 := ebp = ebp_in
  0x64   [ -8 ]      lea ebp, 0x10(esp,,1)     ebp := (esp + 16) = (esp_in + 8)
  0x68   [ -8 ]      sub esp, eax              esp := ((esp_in - arg.0008_in) - 8)
  0x6a   [-8-s]      push ebx                  save ebx
  0x6b   [-12-s]     push esi                  save esi
  0x6c   [-16-s]     push edi                  save edi
  0x6d   [-20-s]     mov eax, 0x416188         eax := gv_0x416188 = gv_0x416188_in
  0x72   [-20-s]     xor -0x4(ebp), eax        arg.0004 := arg.0004 xor eax
  0x75   [-20-s]     xor eax, ebp              eax := eax xor ebp
  0x77   [-20-s]     push eax                  esp := esp - 4; ? := eax
  0x78   [-24-s]     mov -0x18(ebp), esp       var.0016 :=
                                                  ((esp_in - arg.0008_in) - 24)
  0x7b   [-24-s]     push -0x8(ebp)            esp := esp - 4; ? := arg.0000
  0x7e   [-28-s]     mov eax, -0x4(ebp)        eax := arg.0004
  0x81   [-28-s]     mov -0x4(ebp), 0xfffffffe  arg.0004 := 4294967294
  0x88   [-28-s]     mov -0x8(ebp), eax        arg.0000 := eax
  0x8b   [-28-s]     lea eax, -0x10(ebp)       eax := (ebp - 16) = (esp_in - 8)
  0x8e   [-28-s]     mov %fs:0x0, eax          ? := eax = (esp_in - 8)
  0x94   [-28-s]     ret                       return
*)

class seh_prolog4_semantics_t
  (md5hash:string)
  (exnhandler4:doubleword_int)
  (cookie:doubleword_int)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__SEH_prolog4"

  method! get_annotation (floc:floc_int) =
    get_sehprolog4_annotation self#get_name exnhandler4 cookie floc

  method! get_commands (floc:floc_int) =
    get_sehprolog4_chif exnhandler4 floc

  method get_parametercount = 2

  method! get_call_target (a:doubleword_int) =
    let fty = t_fsignature t_void [("size", t_int); ("scopetable", t_voidptr)] in
    let fintf = bfuntype_to_function_interface self#get_name fty in
    mk_app_target ~fintf:(Some fintf) a

  method! get_description =
    "sets up exception handling and allocate memory on the stack"

end


(* ======================================== __SEH_prolog4_GS(eh4_scopetable,size)

  0x5c    [0]      push fp:0x437700          esp := esp - 4;
                                                var.0004 := 4421376
  0x61    [-4]     push %fs:0x0              esp := esp - 4;
                                                var.0008 :=  ?  (tmpN)
  0x68    [-8]     mov eax, 0x10(esp,,1)     eax := arg.0008 = arg.0008_in
  0x6c    [-8]     mov 0x10(esp,,1), ebp     arg.0008 := ebp = ebp_in
  0x70    [-8]     lea ebp, 0x10(esp,,1)     ebp := (esp + 16) = (esp_in + 8)
  0x74    [-8]     sub esp, eax              esp := ((esp_in - arg.0008_in) - 8)
  0x76   [-8-s]    push ebx                  save ebx
  0x77   [-12-s]   push esi                  save esi
  0x78   [-16-s]   push edi                  save edi
  0x79   [-20-s]   mov eax, 0x460330         eax := gv_0x460330 = gv_0x460330_in
  0x7e   [-20-s]   xor -0x4(ebp), eax        arg.0004 := arg.0004 xor eax
  0x81   [-20-s]   xor eax, ebp              eax := eax xor ebp
  0x83   [-20-s]   mov -0x1c(ebp), eax       var.0020 := eax
  0x86   [-20-s]   push eax                  esp := esp - 4; ? := eax
  0x87   [-24-s]   mov -0x18(ebp), esp       var.0016 :=
                                                ((esp_in - arg.0008_in) - 24)
  0x8a   [-24-s]   push -0x8(ebp)            esp := esp - 4; ? := arg.0000
  0x8d   [-28-s]   mov eax, -0x4(ebp)        eax := arg.0004
  0x90   [-28-s]   mov -0x4(ebp), 0xfffffffe  arg.0004 := 4294967294
  0x97   [-28-s]   mov -0x8(ebp), eax        arg.0000 := eax
  0x9a   [-28-s]   lea eax, -0x10(ebp)       eax := (ebp - 16) = (esp_in - 8)
  0x9d   [-28-s]   mov %fs:0x0, eax          ? := eax = (esp_in - 8)
  0xa3   [-28-s]   ret                       return
*)

class seh_prolog4_gs_semantics_t
  (md5hash:string)
  (exnhandler4:doubleword_int)
  (cookie:doubleword_int)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__SEH_prolog4_GS"

  method! get_annotation (floc:floc_int) =
    get_sehprolog4_annotation self#get_name exnhandler4 cookie floc

  method! get_commands (floc:floc_int) =
    get_sehprolog4_chif ~gs:true exnhandler4 floc

  method get_parametercount = 2

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "sets up exception handling and allocates memory on the stack"

end


(* ============================================================= __SEH_epilog4()

  0x95    [ 0 ]   mov ecx, -0x10(ebp)  ecx :=  ?  (tmpN)
  0x98    [ 0 ]   mov %fs:0x0, ecx     ? := ecx
  0x9f    [ 0 ]   pop ecx              ecx := arg.0000_in; esp := (esp_in + 4)
  0xa0    [ 4 ]   pop edi              edi := arg.0004_in; esp := (esp_in + 8)
  0xa1    [ 8 ]   pop edi              edi := arg.0008_in; esp := (esp_in + 12)
  0xa2    [ 12 ]  pop esi              esi := arg.0012_in; esp := (esp_in + 16)
  0xa3    [ 16 ]  pop ebx              ebx := arg.0016_in; esp := (esp_in + 20)
  0xa4    [ 20 ]  mov esp, ebp         esp := ebp = ebp_in
  0xa6   [  ?  ]  pop ebp              ebp := (ebp_in)[0]_in; esp := (ebp_in + 4)
  0xa7   [  ?  ]  push ecx             esp := esp - 4; (ebp_in)[0] := ecx
  0xa8   [  ?  ]  ret                  return
*)

class seh_epilog4_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__SEH_epilog4"

   method! get_commands (floc:floc_int) =
    let (edilhs,edilhscmds) = get_reg_lhs Edi floc in
    let (esilhs,esilhscmds) = get_reg_lhs Esi floc in
    let (ebxlhs,ebxlhscmds) = get_reg_lhs Ebx floc in
    let (esplhs,esplhscmds) = get_reg_lhs Esp floc in
    try
      let args = floc#get_call_args in
      let arg2 = get_arg args 2 floc in
      let arg3 = get_arg args 3 floc in
      let arg4 = get_arg args 4 floc in
      let four = int_constant_expr 4 in
      let ebpv = get_reg_value Ebp floc in
      let cmds2 = floc#get_assign_commands edilhs arg2 in
      let cmds3 = floc#get_assign_commands esilhs arg3 in
      let cmds4 = floc#get_assign_commands ebxlhs arg4 in
      let cmdsesp =
        floc#get_assign_commands esplhs (XOp (XPlus, [ebpv; four])) in
      let cmdsa = [floc#get_abstract_cpu_registers_command [Ecx; Ebp]] in
      List.concat [
	edilhscmds; esilhscmds; ebxlhscmds;
	cmds2; cmds3; cmds4; esplhscmds; cmdsesp; cmdsa]
    with
    | BCH_failure p ->
      begin
	ch_error_log#add (self#get_name ^ " semantics") p;
	[floc#get_abstract_cpu_registers_command [Ecx; Ebx; Esi; Edi; Esp; Ebp]]
      end

  method get_parametercount = 4

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description =
    "restores exception handling context set by SEH_prolog4"

end

let seh4_functions = [
    new seh_epilog4_semantics_t "0bb6d0a57d5abd5116ca9e70ea64013a" 11;
    new seh_epilog4_semantics_t "7581e4178d8034ef44cdfc7d3cebbb84" 11
  ]

let seh4_gs_matcher _faddr fnbytes fnhash =
  let handler = todw (Str.matched_group 1 fnbytes) in
  let cookie = todw (Str.matched_group 2 fnbytes) in
  let sem = new seh_prolog4_gs_semantics_t fnhash handler cookie 22 in
  let msg =
    LBLOCK [
        STR " with handler "; handler#toPretty;
	STR " and security cookie "; cookie#toPretty] in
  sometemplate ~msg sem

let seh4_matcher _faddr fnbytes fnhash =
    let handler = todw (Str.matched_group 1 fnbytes) in
    let cookie = todw (Str.matched_group 2 fnbytes) in
    let sem = new seh_prolog4_semantics_t fnhash handler cookie 21 in
    let msg =
      LBLOCK [
          STR " with handler "; handler#toPretty;
	  STR " and security cookie "; cookie#toPretty] in
    sometemplate ~msg sem


let seh4_patterns = [

  (* SEH_prolog4 *)
    { regex_s =
        Str.regexp
          ("68\\(........\\)64ff35000000008b442410896c24108d6c24102be0535657a1"
           ^ "\\(........\\)3145fc33c5508965e8ff75f88b45fcc745fcfeffffff8945f8"
           ^ "8d45f064"
           ^ "a300000000c3$");

    regex_f = seh4_matcher
  };

  { regex_s =
      Str.regexp
        ("68\\(........\\)64ff35000000008b442410896c24108d6c24102be0535657a1"
         ^ "\\(........\\)3145fc33c5508965e8ff75f88b45fcc745fcfeffffff8945f8"
         ^ "8d45f064"
         ^ "a300000000f2c3$");

    regex_f = seh4_matcher
  };

  (* SEH_prolog4_GS *)
  { regex_s =
      Str.regexp
        ("68\\(........\\)64ff35000000008b442410896c24108d6c24102be0535657a1"
         ^ "\\(........\\)3145fc33c58945e4508965e8ff75f88b45fcc745fcfeffffff"
         ^ "8945f88d"
         ^ "45f064a300000000c3$");

    regex_f = seh4_gs_matcher
  };

    { regex_s =
        Str.regexp
          ("68\\(........\\)64ff35000000008b442410896c24108d6c24102be0535657a1" ^
             "\\(........\\)3145fc33c58945e4508965e8ff75f88b45fcc745fcfeffffff"
             ^ "8945f88d"
             ^ "45f064a300000000f2c3$");

      regex_f = seh4_gs_matcher
    }
]
