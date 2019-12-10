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
open CHNumerical
open CHPretty

(* xprlib *)
open Xprt

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil


(* Functions that set the value of a variable

   __set_fld_<n>__ : sets fld n to a constant value or register contents
   __set_<n>_flds__: sets n flds to a constant value or register contents
   __set_gv_arg      : sets a global variable to the first argument
   __set_gv_fld      : sets a field from a struct in a global variable to an immediate
   __set_gv_xx(v)    : sets global variable to v

*)

(* ================================================================== set_fld_<n>
   example: Vc416ff:0x41f170

  0x41f170   [ 0 ]    push ebp                  save ebp
  0x41f171   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x41f173   [ -4 ]   push ecx                  save ecx
  0x41f174   [ -8 ]   mov -0x4(ebp), ecx        var.0008 := ecx = ecx_in
  0x41f177   [ -8 ]   mov eax, -0x4(ebp)        eax := var.0008 = ecx_in
  0x41f17a   [ -8 ]   mov (eax), 0x4923fc       (ecx_in)[0] := 4793340
  0x41f180   [ -8 ]   mov esp, ebp              esp := ebp = (esp_in - 4)
  0x41f182   [ -4 ]   pop ebp                   restore ebp
  0x41f183   [ 0 ]    ret                       return

  ---------------------------------------------------------------------------
   example: V94b:0x40291c

  0x40291c   [ 0 ]    mov eax, ecx              eax := ecx = ecx_in
  0x40291e   [ 0 ]    mov (eax), 0x1            (ecx_in)[0] := 1
  0x402924   [ 0 ]    ret                       return

   ---------------------------------------------------------------------------
   example: V03be08:0x401aeee

  0x401aee   [ 0 ]    mov (ecx), 0x416b6c       (ecx_in)[0] := 4287340
  0x401af4   [ 0 ]    ret                       return

  ----------------------------------------------------------------------------
   example: Vccd:0x415bf8

  0x415bf8   [ 0 ]    mov 0x18(eax), edx        (eax_in)[24] := edx = edx_in
  0x415bfb   [ 0 ]    ret                       return

   ---------------------------------------------------------------------------
   example: V1da:0x438028

  0x438028   [ 0 ]    xor eax, eax              eax := 0 
  0x43802a   [ 0 ]    mov 0xc(edx), eax         (edx_in)[12] := eax = 0
  0x43802d   [ 0 ]    ret                       return
*)
class set_fld_semantics_t 
  (md5hash:string) 
  (reg:cpureg_t) 
  (offsets:int list)
  (rhs:patternrhs_t)
  ?(adj=0)
  ?(size=4)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = 
    let offsetstring =
      String.concat "_" (List.map (fun i -> string_of_int i) offsets) in
    "__set_fld_" ^ offsetstring ^ "__"

  method get_annotation (floc:floc_int) =
    let lhs = get_nested_deref_lhs reg offsets floc in
    let rhsv = get_patternrhs_value rhs floc in
    LBLOCK [ lhs#toPretty ; STR " := " ; xpr_to_pretty floc rhsv ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = 
      match offsets with
      | [] -> raise (BCH_failure (LBLOCK [ STR "No offsets in set_fld_semantics" ]))
      | [ off ] -> get_reg_deref_lhs reg ~size off floc 
      | _ -> (get_nested_deref_lhs reg offsets floc, []) in
    let size = int_constant_expr size in
    let cmds1 = floc#get_assign_commands lhs ~size (get_patternrhs_value rhs floc) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Eax ; Ecx ] ] in
    let adjcmds = get_adjustment_commands adj floc in
    List.concat [ lhscmds ; cmds1 ; cmds2 ; adjcmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

end

(* ============================================================ set_flds ===
   example: V429: 0x401354
   md5hash: 2b3ef12b049affd9e56530d8c5a93875

  0x401354   [ 0 ]    mov (eax), eax            (eax_in)[0] := eax = eax_in
  0x401356   [ 0 ]    mov 0x4(eax), eax         (eax_in)[4] := eax = eax_in
  0x401359   [ 0 ]    ret                       return

   ---------------------------------------------------------------------------
   example: V749:0x40d918

  0x40d918   [ 0 ]    mov 0x10(eax), edx        (eax_in)[16] := edx = edx_in
  0x40d91b   [ 0 ]    mov 0x1c(eax), ecx        (eax_in)[28] := ecx = ecx_in
  0x40d91e   [ 0 ]    mov 0x48(eax), 0xfffffffe  (eax_in)[72] := 4294967294
  0x40d925   [ 0 ]    ret                       return

   --------------------------------------------------------------------------
   example: putty:0x430ad1

  0x430ad1   [ 0 ]    xor ecx, ecx              ecx := 0 
  0x430ad3   [ 0 ]    mov 0xe3c(eax), ecx       (eax_in)[3644] := ecx = 0
  0x430ad9   [ 0 ]    mov 0xe50(eax), ecx       (eax_in)[3664] := ecx = 0
  0x430adf   [ 0 ]    mov 0xe54(eax), ecx       (eax_in)[3668] := ecx = 0
  0x430ae5   [ 0 ]    mov 0xe48(eax), ecx       (eax_in)[3656] := ecx = 0
  0x430aeb   [ 0 ]    mov 0xe4c(eax), ecx       (eax_in)[3660] := ecx = 0
  0x430af1   [ 0 ]    ret                       return

*)
class set_flds_semantics_t 
  (md5hash:string) 
  (reg:cpureg_t)
  (offsetrhs:(int list * patternrhs_t) list)
  ?(adj=0)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = 
    let offsetstring offs = 
      String.concat "_" (List.map (fun i -> string_of_int i) offs) in
    let flds = 
      String.concat "_and_" (List.map (fun (offs,_) -> offsetstring offs) offsetrhs) in 
    "__set_flds_" ^ flds ^ "__"

  method get_annotation (floc:floc_int) =
    let poff (offsets,p) =
      let lhs = get_nested_deref_lhs reg offsets floc in
      let rhs = get_patternrhs_value p floc in
      LBLOCK [ lhs#toPretty ; STR " := " ; xpr_to_pretty floc rhs ] in
    pretty_print_list offsetrhs poff "" "; " ""

  method get_commands (floc:floc_int) =
    let cmds = List.fold_left (fun cmds (offsets,p) ->
      let rhs = get_patternrhs_value p floc in
      let lhs = get_nested_deref_lhs reg offsets floc in
      let acmds = floc#get_assign_commands lhs rhs in
      List.concat [ cmds ; acmds ]) [] offsetrhs in
    let adjcmds = get_adjustment_commands adj floc in
    cmds @ adjcmds

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "sets n fields to a register or constant value"

end


(* ============================================================ set_gv_fld
   example: V749:0x40a1d4

  0x40a1d4   [ 0 ]    mov eax, 0x412bb0         eax := gv_0x412bb0 = gv_0x412bb0_in
  0x40a1d9   [ 0 ]    mov (eax), 0x4129c4       (gv_0x412bb0_in)[0] := 4270532
  0x40a1df   [ 0 ]    ret                       return
*)
class set_gv_fld_semantics_t
  (md5hash:string) 
  (gvbase:doubleword_int) 
  (offset:int)
  (rhs:patternrhs_t)
  (paramcount:int)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__set_gv_fld_" ^ gvbase#to_hex_string ^ "__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let xrhs = get_patternrhs_value ~args rhs floc in
    LBLOCK [ STR "gv_" ; gvbase#toPretty ; STR "[0] := " ; xpr_to_pretty floc xrhs ]

  method get_commands (floc:floc_int) =
    let basev = get_gv_value gvbase floc in
    let lhs = get_x_deref_lhs basev  offset floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let xrhs = get_patternrhs_value rhs floc in
    let cmds1 = floc#get_assign_commands lhs xrhs in
    let cmds2 = floc#get_assign_commands eaxlhs basev in
    List.concat [ eaxlhscmds ; cmds1 ; cmds2 ]

  method get_parametercount = paramcount

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "sets a field in a struct addressed by a global variable"

end

(* ============================================================ set_gv_xxxxxx
   example: V0d4:0x505127

  0x505127   [ 0 ]    mov eax, 0x4(esp,,1)   eax := arg.0004 = arg.0004_in
  0x50512b   [ 0 ]    mov 0x50b388, eax      gv_0x50b388 := eax = arg.0004_in
  0x505130   [ 0 ]    ret                    return

   example: V2bd:0x1000d7af

  0x1000d7af   [ 0 ]    mov edi, edi              nop
  0x1000d7b1   [ 0 ]    push ebp                  save ebp
  0x1000d7b2   [ -4 ]   mov ebp, esp              ebp := esp = (esp_in - 4)
  0x1000d7b4   [ -4 ]   mov eax, 0x8(ebp)         eax := arg.0004 = arg.0004_in
  0x1000d7b7   [ -4 ]   mov 0x100256d0, eax       gv_0x100256d0 := eax = arg.0004_in
  0x1000d7bc   [ -4 ]   pop ebp                   restore ebp
  0x1000d7bd   [ 0 ]    ret                       return

   example: V3fc:0x408fe0

  0x408fe0   [ 0 ]    push ebp              save ebp
  0x408fe1   [ -4 ]   mov ebp, esp          ebp := esp = (esp_in - 4)
  0x408fe3   [ -4 ]   mov eax, 0x8(ebp)     eax := arg.0004 = arg.0004_in
  0x408fe6   [ -4 ]   mov 0x435cbc, eax     gv_0x435cbc := eax = arg.0004_in
  0x408feb   [ -4 ]   pop ebp               restore ebp
  0x408fec   [ 0 ]    ret                   return

   example: V494:0x40cf50

  0x40cf50   [ 0 ]    and 0x421388, 0x0         gv_0x421388 := 0
  0x40cf57   [ 0 ]    ret                       return


*)

class set_gv_semantics_t 
  (md5hash:string) 
  (gv:doubleword_int)
  (rhs:patternrhs_t)
  (paramcount:int)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__set_gv_" ^ gv#to_hex_string

  method get_annotation (floc:floc_int) =
    let v = floc#env#mk_global_variable gv#to_numerical in
    let args = floc#get_call_args in
    let xrhs = get_patternrhs_value ~args rhs floc in
    LBLOCK [ v#toPretty ; STR " := " ; xpr_to_pretty floc xrhs ]

  method get_commands (floc:floc_int) =
    let (lhs,lcmds) = (absolute_op gv 4 WR)#to_lhs floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let args = floc#get_call_args in
    let xrhs = get_patternrhs_value ~args rhs floc in
    let cmds1 = floc#get_assign_commands lhs xrhs in
    let cmds2 = floc#get_assign_commands eaxlhs xrhs in
    List.concat [ eaxlhscmds ; lcmds ; cmds1 ; cmds2 ]

  method get_parametercount = paramcount

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "sets gv_" ^ gv#to_hex_string ^ " to rhs value"

end

let setter_functions = [

  new set_flds_semantics_t                                    (* V1da:0x406270 *)
    "fc14691ac2ac82983300f9215513b4d0" Ecx
    [ ([0],PRegister Eax); ([4],PRegister Edx) ] 3   ;

  new set_flds_semantics_t                                    (* V5b7:0x47aa3c *)
    "419ab810ff18c4d076265526daea328d" Edx
    [ ([0],PConstantValue numerical_zero); ([4],PConstantValue numerical_zero) ] 5 ;

  new set_flds_semantics_t                                    (* V1da:0x401404 *)
    "2b3ef12b049affd9e56530d8c5a93875" Eax
    [ ([0],PRegister Eax); ([4],PRegister Eax) ] 3 ;

  new set_flds_semantics_t                                    (* V034:0x406e00 *)
    "15bb6e0b6cf8c68e5993f81d2ab2f999" Ecx
    [ ([0],PConstantValue numerical_zero); ([4],PConstantValue numerical_zero) ] 4 ;

]


let setecxfld0 instrs faddr fnbytes fnhash =
  let rhs = PConstantValue (todw (Str.matched_group 1 fnbytes))#to_numerical in
  let sem = new set_fld_semantics_t fnhash Ecx [0] rhs instrs in
  let msg = LBLOCK [ STR " with base register ecx and with value " ; 
		     STR (patternrhs_to_string rhs) ] in
  sometemplate ~msg sem

let setgvarg instrs faddr fnbytes fnhash =
  let gv = todw (Str.matched_group 1 fnbytes) in
  let sem = new set_gv_semantics_t fnhash gv (PArgument 1) 1 instrs in
  let msg = LBLOCK [ STR " with value the first argument" ] in
  sometemplate ~msg sem
  
let setter_patterns = [

  (* sets a struct field addressed by a global variable (V749:0x40a1d4) *)
  { regex_s = Str.regexp "a1\\(........\\)c700\\(........\\)c3$" ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let rhs = PConstantValue (todw (Str.matched_group 2 fnbytes))#to_numerical in
      let sem = new set_gv_fld_semantics_t fnhash gv 0 rhs 0 3 in
      let msg = LBLOCK [ STR " with offset 0 and value " ; STR (patternrhs_to_string rhs) ] in
      sometemplate ~msg sem
  } ;

  (* sets a register addressed field to a register value 
       
     0x4356d4   [ 0 ]    mov 0x5d(eax), dl         (eax_in)[93] := dl
     0x4356d7   [ 0 ]    ret                       return
  *)
  { regex_s = Str.regexp "8850\\(..\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let sem = new set_fld_semantics_t fnhash Eax [ offset ] (PRegister Dl) ~size:1 2 in
      let msg = LBLOCK [ STR " with base register eax and value Dl " ] in
      sometemplate ~msg sem
  } ;

  (* set ecx[0] to immediate (V03be08:0x401aeee) *)
  { regex_s = Str.regexp "c701\\(........\\)c3$" ;    
    regex_f = setecxfld0 2
  } ;

  (* set eax[p] to immediate *)
  { regex_s = Str.regexp "c742\\(..\\)\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let rhs = PConstantValue (todw (Str.matched_group 2 fnbytes))#to_numerical in
      let sem = new set_fld_semantics_t fnhash Eax [offset] rhs 2 in
      let msg = LBLOCK [ STR " with base register eax and with value " ; 
			 STR (patternrhs_to_string rhs) ] in
      sometemplate ~msg sem
  } ;

  (* sets edx[p] to immediate (V5b7:0x44b314) *)
  { regex_s = Str.regexp 
      "558bec83c4f88955f88945fc8b45f8c740\\(..\\)\\(........\\)59595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let rhs = PConstantValue (todw (Str.matched_group 2 fnbytes))#to_numerical in
      let sem = new set_fld_semantics_t fnhash Edx [offset] rhs 11 in
      let msg = LBLOCK [ STR " with base register edx and with value " ;
			 STR (patternrhs_to_string rhs) ] in
      sometemplate ~msg sem
  } ;


  (* sets edx[p] to 0 (V5b7:0x443da4) *)
  { regex_s = Str.regexp
      "558bec83c4f88955f88945fc8b45f833d28950\\(..\\)59595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let rhs = PConstantValue numerical_zero in
      let sem = new set_fld_semantics_t fnhash Edx [offset] rhs 11 in
      let msg = LBLOCK [ STR " with base register edx and with value 0" ] in
      sometemplate ~msg sem
  } ;      

  (* set eax[p] to immediate 

     0x41a260   [ 0 ]    mov 0xd(eax), 0x1         (eax_in)[13] := 1
     0x41a264   [ 0 ]    ret                       return
  *)
  { regex_s = Str.regexp "c640\\(..\\)\\(..\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let v = toimm2 (Str.matched_group 2 fnbytes) in
      let rhs = PConstantValue (mkNumerical v) in
      let sem = new set_fld_semantics_t fnhash Eax [offset] rhs ~size:1 2 in
      let msg = LBLOCK [ STR " with base register eax and with value " ; INT v ] in
      sometemplate ~msg sem
  } ;

  (* sets edx[p] to zero *)
  { regex_s = Str.regexp "33c08942\\(..\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let rhs = PConstantValue numerical_zero in
      let sem = new set_fld_semantics_t fnhash Edx [offset] rhs 3 in
      let msg = LBLOCK [ STR " with base register edx and with value 0 " ] in
      sometemplate ~msg sem
  } ;

  (* set 5 flds to zero (putty:0x430ad1) *)
  { regex_s = Str.regexp 
      ("33c98988\\(........\\)8988\\(........\\)8988\\(........\\)8988" ^
       "\\(........\\)8988\\(........\\)c3$") ;

    regex_f = fun faddr fnbytes fnhash ->
      let zero = PConstantValue numerical_zero in
      let offrhs = List.map (fun grp ->
	([ todwoff (Str.matched_group grp fnbytes) ],zero)) [ 1 ; 2 ; 3 ; 4 ; 5 ] in
      let sem = new set_flds_semantics_t fnhash Eax offrhs 7 in
      let msg = LBLOCK [ STR " with offsets " ; 
			 pretty_print_list offrhs 
			   (fun (offsets,_) -> pretty_print_list offsets 
			     (fun i -> INT i) "" "," "") "" ", " "" ;
			 STR " and value zero " ] in
      sometemplate ~msg sem
  } ;

  (* set ecx[0] to immediate (Vc416ff:0x41f170) *)
  { regex_s = Str.regexp "558bec51894dfc8b45fcc700\\(........\\)8be55dc3$" ;
    regex_f = setecxfld0 9
  } ;

  (* set ecx[0] to immediate *)
  { regex_s = Str.regexp "558bec51894dfc8b45fcc700\\(........\\)8b45fc8be55dc3$" ;
    regex_f = setecxfld0 9
  } ;

  (* sets global variable to first argument (V3fc:0x408fe0) *)
  { regex_s = Str.regexp "558bec8b4508a3\\(........\\)5dc3$" ;
    regex_f = setgvarg 6
  } ;

  (* set ecx[0] to immediate (V94b:0x40291c) *)
  { regex_s = Str.regexp "8bc1c700\\(........\\)c3$" ;
    regex_f = setecxfld0 3
  } ;

  (* sets global variable to first argument (V2bd:0x1000d7af) *)
  { regex_s = Str.regexp "8bff558bec8b4508a3\\(........\\)5dc3$" ;
    regex_f = setgvarg 7
  } ;

  (* sets global variable to first argument (V0d4:0x505127) *)
  { regex_s = Str.regexp "8b442404a3\\(........\\)c3$" ;
    regex_f = setgvarg 3
  } ;

  (* sets global variable to zero (V494:0x40cf50) *)
  { regex_s = Str.regexp "8325\\(........\\)00c3$" ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let rhs = PConstantValue numerical_zero in
      let sem = new set_gv_semantics_t fnhash gv rhs 0 2 in
      let msg = LBLOCK [ STR " with value zero" ] in
      sometemplate ~msg sem
  } ;

  (* sets global variable to immediate value (V007:0x45c1ec) *)
  { regex_s = Str.regexp "c705\\(........\\)\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let imm = todw (Str.matched_group 2 fnbytes) in
      let rhs = PConstantValue imm#to_numerical in
      let sem = new set_gv_semantics_t fnhash gv rhs 0 2 in
      let msg = LBLOCK [ STR " with value " ; imm#toPretty ] in
      sometemplate ~msg sem
  } ;
      
  (* set eax[p] to Edx (Vccd:0x415bf8) *)
  { regex_s =  Str.regexp "8950\\(..\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let sem = new set_fld_semantics_t fnhash Eax [offset] (PRegister Edx) 2 in 
      let msg = LBLOCK [ STR " with base register eax and with value from edx " ] in
      sometemplate ~msg sem
  } ;

  (* set eax[p] to Edx (V5b7:0x44c61c) *)
  { regex_s = Str.regexp
      "558bec83c4f88955f88945fc8b45f88b55fc8942\\(..\\)59595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let offset = tooff (Str.matched_group 1 fnbytes) in
      let sem = new set_fld_semantics_t fnhash Eax [offset] (PRegister Edx) 12 in
      let msg = LBLOCK [ STR " with base register eax and with value from edx " ] in
      sometemplate ~msg sem
  } ;

  (* set eax[p][q] to Edx (V5b7:0x4747f8) *)
  { regex_s = Str.regexp "8b40\\(..\\)8950\\(..\\)c3$" ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let offset1 = tooff (Str.matched_group 1 fnbytes) in
      let offset2 = tooff (Str.matched_group 2 fnbytes) in
      let sem = new set_fld_semantics_t fnhash Eax [ offset1 ; offset2 ]
	(PRegister Edx) 3 in
      let msg = LBLOCK [ STR " with base register eax and with value from edx " ] in
      sometemplate ~msg sem
  } ;

  (* set 3 flds off eax to a value (V749:0x40d918) *)
  { regex_s = Str.regexp "8950\\(..\\)8948\\(..\\)c740\\(..\\)\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let off1 = tooff (Str.matched_group 1 fnbytes) in
      let off2 = tooff (Str.matched_group 2 fnbytes) in
      let off3 = tooff (Str.matched_group 3 fnbytes) in
      let dw = todw (Str.matched_group 4 fnbytes) in
      let rhs3 = PConstantValue dw#to_numerical in
      let offrhs = [ ([off1],PRegister Eax) ; ([off2],PRegister Ecx) ; ([off3],rhs3) ] in
      let sem = new set_flds_semantics_t fnhash Eax offrhs 4 in
      let msg = LBLOCK [ STR " with offsets " ; 
		  (pretty_print_list offrhs (fun (offsets,_) -> 
		    pretty_print_list offsets (fun i -> INT i) "" "," "") "" ", " "") ; 
		  STR " and right hand sides Edx, Ecx, and " ; dw#toPretty ] in
      sometemplate ~msg sem
  } ;

    (* set 2 nested flds off eax to argument values (V5b7:0x474808) *)
    { regex_s = Str.regexp
	"558bec8b40\\(..\\)8b55088950\\(..\\)8b550c8950\\(..\\)5dc20800$" ;

      regex_f = fun faddr fnbytes fnhash ->
	let off1 = tooff (Str.matched_group 1 fnbytes) in
	let off2 = tooff (Str.matched_group 2 fnbytes) in
	let off3 = tooff (Str.matched_group 3 fnbytes) in
	let rhs1 = PArgument 1 in
	let rhs2 = PArgument 2 in
	let offrhs = [ ([off1 ; off2],rhs1) ; ([off1 ; off3],rhs2) ] in
	let sem = new set_flds_semantics_t fnhash Eax offrhs 9 in
	let msg = LBLOCK [ STR " with offsets " ; 
		  (pretty_print_list offrhs (fun (offsets,_) -> 
		    pretty_print_list offsets (fun i -> INT i) "" "," "") "" ", " "") ; 
		  STR " and right hand sides arg.0004 and arg.0008 "] in
	sometemplate ~msg sem
    }
		  
			      
]
      

  
