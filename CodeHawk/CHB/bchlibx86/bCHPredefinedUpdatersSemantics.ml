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

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHLibTypes
open BCHMakeCallTargetInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil

(* Functions that update the value of a variable

   dec_gv: decrements a global variable (very common function in Delphi compiled)
   inc_fld: increments a register addressed field

*)

(* =============================================================== dec_gv_xxxxxx
   example: Vccd: 0x44d218

  0x44d218   sub 0x450bd4, 0x1  gv_0x450bd4 := (gv_0x450bd4_in - 1)
  0x44d21f   ret                return

*)
class dec_gv_semantics_t
        (md5hash:string)
        (gv:doubleword_int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__dec_gv_" ^ gv#to_hex_string ^ "__"

  method! get_annotation (_floc:floc_int) =
    LBLOCK [
        STR "gv_"; gv#toPretty; STR " := "; STR "gv_"; gv#toPretty; STR " - 1"]

  method! get_commands (floc:floc_int) =
    let rhs = (absolute_op gv 4 RD)#to_expr floc in
    let (lhs,lhscmds) = (absolute_op gv 4 WR)#to_lhs floc in
    let cmds = floc#get_assign_commands lhs rhs in
    lhscmds @ cmds

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

end

(* ================================================================== inc_fld_xx
   example: Vccd: 0x449474

  0x449474   [ 0 ]    inc 0x8c(eax)  (eax_in)[140] := ((eax_in)[140]_in + 1)
  0x44947b   [ 0 ]    ret            return
*)
class inc_fld_semantics_t
        (md5hash:string)
        (reg:cpureg_t)
        (offset:int)
        (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__inc_fld_" ^ (string_of_int offset) ^ "__"

  method! get_annotation (floc:floc_int) =
    let (lhs,_) = get_reg_deref_lhs reg offset floc in
    let rhs = get_reg_derefvalue reg offset floc in
    let rhs = XOp (XPlus, [rhs; int_constant_expr 1]) in
    LBLOCK [lhs#toPretty; STR " := "; xpr_to_pretty floc rhs]

  method! get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_deref_lhs reg offset floc in
    let rhs = get_reg_derefvalue reg offset floc in
    let rhs = XOp (XPlus, [rhs; int_constant_expr 1]) in
    let cmds = floc#get_assign_commands lhs rhs in
    lhscmds @ cmds

  method get_parametercount = 0

  method! get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method! get_description = "increments register addressed field"

end


let updater_patterns = [

  (* increments a struct field addressed by eax *)
  { regex_s = Str.regexp "ff40\\(..\\)c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let sem = new inc_fld_semantics_t fnhash Eax offset 2 in
      let msg = LBLOCK [ STR " with base register eax " ] in
      sometemplate ~msg sem

  };

  (* increments a struct field addressed by eax *)
  { regex_s = Str.regexp "66ff80\\(........\\)c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let offset = todwoff (Str.matched_group 1 fnbytes) in
      let sem = new inc_fld_semantics_t fnhash Eax offset 2 in
      let msg = LBLOCK [ STR " with base register eax " ] in
      sometemplate ~msg sem

  };

  (* increments a struct field addressed by eax
     example: V5b7:0x452ec8

  0x452ec8   [ 0 ]    push ebp             save ebp
  0x452ec9   [ -4 ]   mov ebp, esp         ebp := esp = (esp_in - 4)
  0x452ecb   [ -4 ]   push ecx             save ecx
  0x452ecc   [ -8 ]   mov -0x4(ebp), eax   var.0008 := eax = eax_in
  0x452ecf   [ -8 ]   mov eax, -0x4(ebp)   eax := var.0008 = eax_in
  0x452ed2   [ -8 ]   inc 0x5c(eax)        (eax_in)[92] := ((eax_in)[92]_in + 1)
  0x452ed5   [ -8 ]   pop ecx              ecx := eax_in; esp := (esp_in - 4)
  0x452ed6   [ -4 ]   pop ebp              restore ebp
  0x452ed7   [ 0 ]    ret                  return

  *)
  { regex_s = Str.regexp "558bec518945fc8b45fcff40\\(..\\)595dc3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let sem = new inc_fld_semantics_t fnhash Eax offset 9 in
      let msg = LBLOCK [STR " with base register eax "] in
      sometemplate ~msg sem
  };

  (* increments a struct field addressed by eax (with 4 byte offset)
     example: V5b7:0x445484
  *)
  { regex_s = Str.regexp "558bec518945fc8b45fc66ff80\\(........\\)595dc3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let offset = todwoff (Str.matched_group 1 fnbytes) in
      let sem = new inc_fld_semantics_t fnhash Eax offset 9 in
      let msg = LBLOCK [STR " with base register eax "] in
      sometemplate ~msg sem
  };

  (* decrements a global variable *)
  { regex_s = Str.regexp "832d\\(........\\)01c3$";

    regex_f = fun _faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new dec_gv_semantics_t fnhash gv 2 in
      sometemplate sem
  };

]
