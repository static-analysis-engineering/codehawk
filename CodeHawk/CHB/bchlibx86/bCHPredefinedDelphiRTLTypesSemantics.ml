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
open BCHFloc
open BCHLibTypes
open BCHLocation

(* bchlibx86 *)
open BCHLibx86Types
open BCHPredefinedUtil

module H = Hashtbl

let table = H.create 17

(* ======================================================= System::Classes::Rect
   example: V0a1: 416a44
*)
class rtl_system_classes_rect_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::Classes::Rect__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(ALeft:" ; xpr_to_pretty floc eaxv ;
	     STR ",ATop:" ; xpr_to_pretty floc edxv ; 
	     STR ",ARight:" ; xpr_to_pretty floc ecxv ;
	     STR ",ABottom:" ; xpr_to_pretty floc arg2 ;
	     STR ",dst:" ; xpr_to_pretty floc arg1 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let lhs1 = get_x_deref_lhs arg1 0 floc in
    let lhs2 = get_x_deref_lhs arg1 4 floc in
    let lhs3 = get_x_deref_lhs arg1 8 floc in
    let lhs4 = get_x_deref_lhs arg1 12 floc in
    let cmds1 = floc#get_assign_commands lhs1 eaxv in
    let cmds2 = floc#get_assign_commands lhs2 edxv in
    let cmds3 = floc#get_assign_commands lhs3 ecxv in
    let cmds4 = floc#get_assign_commands lhs4 arg2 in
    let cmds5 = get_adjustment_commands 8 floc in
    List.concat [ cmds1 ; cmds2 ; cmds3 ; cmds4 ; cmds5 ]

  method get_parametercount = 2

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a, self#get_name)

  method get_description = "RTL system classes function System::Types::Rect"

end
    

(* ======================================================= System::Types::Rect
   example: V01a: 0x406358
   md5hash: 4dbf97e160dabf26a77f709da5a78fe1

  0x406358   [ 0 ]    push ebp                  save ebp
  0x406359   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x40635b   [ -4 ]   push ebx                  save ebx
  0x40635c   [ -8 ]   mov ebx, 0x8(ebp)         ebx := arg.0004 = arg.0004_in
  0x40635f   [ -8 ]   mov (ebx), eax            (arg.0004_in)[0] := eax = eax_in
  0x406361   [ -8 ]   mov 0x4(ebx), edx         (arg.0004_in)[4] := edx = edx_in
  0x406364   [ -8 ]   mov eax, 0xc(ebp)         eax := arg.0008 = arg.0008_in
  0x406367   [ -8 ]   mov 0xc(ebx), eax         (arg.0004_in)[12] := eax = arg.0008_in
  0x40636a   [ -8 ]   mov 0x8(ebx), ecx         (arg.0004_in)[8] := ecx = ecx_in
  0x40636d   [ -8 ]   pop ebx                   restore ebx
  0x40636e   [ -4 ]   pop ebp                   restore ebp
  0x40636f   [ 0 ]    ret 8                     return (increment stackpointer by 8)
*)
class rtl_system_types_rect_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::Types::Rect__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(Left:" ; xpr_to_pretty floc eaxv ;
	     STR ",Top:" ; xpr_to_pretty floc edxv ; 
	     STR ",Right:" ; xpr_to_pretty floc ecxv ;
	     STR ",Bottom:" ; xpr_to_pretty floc arg2 ;
	     STR ",dst:" ; xpr_to_pretty floc arg1 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    let ecxv = get_reg_value Ecx floc in
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let lhs1 = get_x_deref_lhs arg1 0 floc in
    let lhs2 = get_x_deref_lhs arg1 4 floc in
    let lhs3 = get_x_deref_lhs arg1 8 floc in
    let lhs4 = get_x_deref_lhs arg1 12 floc in
    let cmds1 = floc#get_assign_commands lhs1 eaxv in
    let cmds2 = floc#get_assign_commands lhs2 edxv in
    let cmds3 = floc#get_assign_commands lhs3 ecxv in
    let cmds4 = floc#get_assign_commands lhs4 arg2 in
    let cmds5 = get_adjustment_commands 8 floc in
    List.concat [ cmds1 ; cmds2 ; cmds3 ; cmds4 ; cmds5 ]

  method get_parametercount = 2

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a, self#get_name)

  method get_description = "RTL system types function System::Types::Rect"

end

let _ = H.add table "System::Types::Rect" (new rtl_system_types_rect_semantics_t)
    
let delphi_rtl_types_functions = H.fold (fun k v a -> a @ (get_fnhashes k v)) table []

let delphi_rtl_types_patterns = [

  (* System::Classes::Rect (V01a:0x416a44) *)
  { regex_s = Str.regexp ("558bec5356578bf98bf28bd88b450c508b4508508bcf8bd68bc3e8" ^
			     "\\(........\\)5f5e5b5dc20800$") ;

    regex_f =
      fun faddr fnbytes fnhash ->
      let loc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 26 } in
      let cfloc = get_floc loc in
      if cfloc#has_inlined_target then
	let (_,name) = cfloc#get_inlined_target in
	if name = "__System::Types::Rect__" then
	  let sem = new rtl_system_classes_rect_semantics_t fnhash 21 in
	  sometemplate sem
	else None
      else None
  }
]
	
