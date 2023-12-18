(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
open CHNumerical
open CHLanguage
open CHPretty

(* xprlib *)
open Xprt
open XprUtil
open Xsimplify

(* bchlib *)
open BCHExternalPredicate
open BCHLibTypes
open BCHMakeCallTargetInfo
open BCHPrecondition

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil

module LF = CHOnlineCodeSet.LanguageFactory

(* Functions that test the value of a variable

   __is_<p>_<v> : returns 1 if the argument satisfies predicate <p> on value <v>

   __is_fld_<n>_<p>_<v>__  : returns 1 if fld<n> satisfies predicate <p> on value <v>
                          example: __fld_4_neq_0__ : returns true if fld 4 is not
                                                      equal to zero
*)

(* ======================================================= __<p>_<v>__
   example: V1da:0x436a3c

  0x436a3c   [ 0 ]    cmp eax, 0x47cb3c         cmp eax, 0x47cb3c
  0x436a42   [ 0 ]    setz al                   al := (0 or 1)
  0x436a45   [ 0 ]    ret                       return

   ---------------------------------------------------------------------
   example: V1da:0x42fcf4

  0x42fcf4   [ 0 ]    cmp 0x212(eax), 0x1       cmp 0x212(eax), 0x1
  0x42fcfb   [ 0 ]    setz al                   al := (0 or 1)
  0x42fcfe   [ 0 ]    ret                       return

*)
class reg_predicate_semantics_t
  (md5hash:string)
  (reg:cpureg_t)
  (pred:relational_op_t)
  (rhs:patternrhs_t)
  ?(adj=0)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name =
    let spred = relational_op_to_xml_string pred in
    let v = patternrhs_to_string rhs in
    "__test_" ^ spred ^ "_" ^ v ^ "__"

  method get_annotation (floc:floc_int) =
    let rv = get_reg_value reg floc in
    let v = get_patternrhs_value rhs floc in
    let p = relational_op_to_string pred in
    LBLOCK [ STR "eax := " ; xpr_to_pretty floc rv  ; STR p ; xpr_to_pretty floc v ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let reqN () = floc#env#mk_num_temp in
    let reqC = floc#env#request_num_constant in
    let regv = get_reg_value reg floc in
    let v = get_patternrhs_value rhs floc in
    let xop = relational_op_to_xop pred in
    let txpr = simplify_xpr (XOp (xop, [ regv ; v ])) in
    let fxpr = simplify_xpr (XOp (XLNot, [ txpr ])) in
    let (tcmds,tbxpr) = xpr_to_boolexpr reqN reqC txpr in
    let (fcmds,fbxpr) = xpr_to_boolexpr reqN reqC fxpr in
    let tassign = floc#get_assign_commands lhs one_constant_expr in
    let fassign = floc#get_assign_commands lhs zero_constant_expr in
    let tbranch = List.concat [ tcmds ; [ ASSERT tbxpr ] ; tassign ] in
    let fbranch = List.concat [ fcmds ; [ ASSERT fbxpr ] ; fassign ] in
    let branch = [ BRANCH [ LF.mkCode tbranch ; LF.mkCode fbranch ] ] in
    let adjcmds = get_adjustment_commands adj floc in
    List.concat [ lhscmds ; branch ; adjcmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method get_description = "predicate on the value of a register"

end



(* ======================================================= __fld_<n>_<p>_<v>__
   example : V1da:0x43cdb8

  0x43cdb8   [ 0 ]    cmp 0x180(eax), 0x0       cmp 0x180(eax), 0x0
  0x43cdbf   [ 0 ]    setnz al                  al := (0 or 1)
  0x43cdc2   [ 0 ]    ret                       return
*)
class field_predicate_semantics_t
  (md5hash:string)
  (reg:cpureg_t)
  (offset:int)
  (pred:relational_op_t)
  (rhs:patternrhs_t)
  ?(adj=0)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name =
    let spred = relational_op_to_xml_string pred in
    let v = match rhs with | PConstantValue n -> n#toString ^ "__" | _ -> "__" in
    "__test_fld_" ^ (string_of_int offset) ^ "_" ^ spred ^ "_" ^ v

  method get_annotation (floc:floc_int) =
    let eaxdv = get_reg_derefvalue reg offset floc in
    let v = get_patternrhs_value rhs floc in
    let p = relational_op_to_string pred in
    LBLOCK [ STR "eax := " ; xpr_to_pretty floc eaxdv ; STR p ; xpr_to_pretty floc v ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_reg_lhs Eax floc in
    let reqN () = floc#env#mk_num_temp in
    let reqC = floc#env#request_num_constant in
    let eaxdv = get_reg_derefvalue reg offset floc in
    let v = get_patternrhs_value rhs floc in
    let xop = relational_op_to_xop pred in
    let txpr = simplify_xpr (XOp (xop, [ eaxdv ; v ])) in
    let fxpr = simplify_xpr (XOp (XLNot, [ txpr ])) in
    let (tcmds,tbxpr) = xpr_to_boolexpr reqN reqC txpr in
    let (fcmds,fbxpr) = xpr_to_boolexpr reqN reqC fxpr in
    let tassign = floc#get_assign_commands lhs one_constant_expr in
    let fassign = floc#get_assign_commands lhs zero_constant_expr in
    let tbranch = List.concat [ tcmds ; [ ASSERT tbxpr ] ; tassign ] in
    let fbranch = List.concat [ fcmds ; [ ASSERT fbxpr ] ; fassign ] in
    let branch = [ BRANCH [ LF.mkCode tbranch ; LF.mkCode fbranch ] ] in
    let adjcmds = get_adjustment_commands adj floc in
    List.concat [ lhscmds ; branch ; adjcmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method get_description = "predicate on the value of a field"

end

let predicate_patterns = [

  (* predicate on a field value with constant value *)
  { regex_s = Str.regexp "83b8\\(........\\)\\(..\\)0f95c0c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let off = todwoff (Str.matched_group 1 fnbytes) in
      let v = toimm2 (Str.matched_group 2 fnbytes) in
      let sem = new field_predicate_semantics_t fnhash Eax off PNotEqual
	(PConstantValue (mkNumerical v)) 3 in
      let msg = LBLOCK [ STR " with offset " ; INT off ; STR " and value " ; INT v ] in
      sometemplate ~msg sem
  } ;

  (* predicate on a field value with constant value *)
  { regex_s = Str.regexp "8378\\(..\\)\\(..\\)0f95c0c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let off = tooff (Str.matched_group 1 fnbytes) in
      let v = toimm2 (Str.matched_group 2 fnbytes) in
      let sem = new field_predicate_semantics_t fnhash Eax off PNotEqual
	(PConstantValue (mkNumerical v)) 3 in
      let msg = LBLOCK [ STR " with offset " ; INT off ; STR " and value " ; INT v ] in
      sometemplate ~msg sem
  } ;

  (* predicate on a field value with constant value *)
  { regex_s = Str.regexp "80b8\\(........\\)\\(..\\)0f94c0c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let off = todwoff (Str.matched_group 1 fnbytes) in
      let v = toimm2 (Str.matched_group 2 fnbytes) in
      let sem = new field_predicate_semantics_t fnhash Eax off PEquals
	(PConstantValue (mkNumerical v)) 3 in
      let msg = LBLOCK [ STR " with offset " ; INT off ; STR " and value " ; INT v ] in
      sometemplate ~msg sem
  } ;

  (* predicate on a field value with constant value *)
  { regex_s = Str.regexp "8378\\(..\\)\\(..\\)0f94c0c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let off = tooff (Str.matched_group 1 fnbytes) in
      let v = toimm2 (Str.matched_group 2 fnbytes) in
      let sem = new field_predicate_semantics_t fnhash Eax off PEquals
	(PConstantValue (mkNumerical v)) 3 in
      let msg = LBLOCK [ STR " with offet " ; INT off ; STR " and value " ; INT v ] in
      sometemplate ~msg sem
  } ;

  (* predicate on a field value with constant value
     example: V5b7:0x451a88

  0x451a88   [ 0 ]    push ebp                  save ebp
  0x451a89   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x451a8b   [ -4 ]   add esp, -0x8             esp := esp + -8 = (esp_in - 12)
  0x451a8e  [ -12 ]   mov -0x4(ebp), eax        var.0008 := eax = eax_in
  0x451a91  [ -12 ]   mov eax, -0x4(ebp)        eax := var.0008 = eax_in
  0x451a94  [ -12 ]   cmp 0x3c(eax), 0x0        cmp 0x3c(eax), 0x0
  0x451a98  [ -12 ]   setnz -0x5(ebp)           var.0009 := ((eax_in)[60] != 0)
  0x451a9c  [ -12 ]   mov al, -0x5(ebp)         al := var.0009
  0x451a9f  [ -12 ]   pop ecx                   ecx := var.0012 ; esp := (esp_in - 8)
  0x451aa0   [ -8 ]   pop ecx                   ecx := eax_in ; esp := (esp_in - 4)
  0x451aa1   [ -4 ]   pop ebp                   restore ebp
  0x451aa2   [ 0 ]    ret                       return
  *)
  { regex_s = Str.regexp
      "558bec83c4f88945fc8b45fc8378\\(..\\)\\(..\\)0f9545fb8a45fb59595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let off = tooff (Str.matched_group 1 fnbytes) in
      let v = toimm2 (Str.matched_group 2 fnbytes) in
      let sem = new field_predicate_semantics_t fnhash Eax off PNotEqual
	(PConstantValue (mkNumerical v)) 12 in
      let msg = LBLOCK [ STR " with offset " ; INT off ; STR " and value " ; INT v ] in
      sometemplate ~msg sem
  } ;

  (* predicate on a field value with constant value
     example: V5b7:0x449ffc
  *)
  { regex_s = Str.regexp
      "558bec83c4f88945fc8b45fc83b8\\(........\\)\\(..\\)0f9545fb8a45fb59595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let off = todwoff (Str.matched_group 1 fnbytes) in
      let v = toimm2 (Str.matched_group 2 fnbytes) in
      let sem = new field_predicate_semantics_t fnhash Eax off PNotEqual
	(PConstantValue (mkNumerical v)) 12 in
      let msg = LBLOCK [ STR " with offset " ; INT off ; STR " and value " ; INT v ] in
      sometemplate ~msg sem
  } ;


  (* predicate on a register value with global variable *)
  { regex_s = Str.regexp "3b05\\(........\\)0f94c0c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new reg_predicate_semantics_t fnhash Eax PEquals (PGlobalVar gv) 3 in
      let msg = LBLOCK [ STR " with global variable gv_" ; gv#toPretty ] in
      sometemplate ~msg sem
  }

]
