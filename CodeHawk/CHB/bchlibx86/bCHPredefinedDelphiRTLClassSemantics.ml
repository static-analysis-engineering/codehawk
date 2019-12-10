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

module H = Hashtbl

(* -----------------------------------------------------------------------------
   System::TObject::ClassDestroy
   System::TObject::ClassInfo (inlined)
   System::TObject::ClassName (s)
   System::TObject::ClassNameIs (s)
   System::TObject::ClassParent (inlined)
   System::TObject::ClassType (inlined)
   System::TObject::FieldAddress (s)
   System::TObject::Free (s)
   System::TObject::GetInterfaceEntry (s)
   System::TObject::InheritsFrom (s)
   System::TObject::InitInstance (s)
   System::TObject::InstanceSize (inlined)
   System::TObject::MethodAddress (s)
   System::TObject::MethodName (s)
 * ----------------------------------------------------------------------------- *)

let table = H.create 17

let load_rtl_tobject_functions () =
  List.iter (fun m -> add_libfun table [ "System" ; "TObject" ] m)
    [ "ClassName" ; "ClassNameIs" ; "FieldAddress" ; "Free" ; 
      "GetInterfaceEntry" ; "InheritsFrom" ; "InitInstance" ; "MethodAddress" ;
      "MethodName" ]

(* =========================================================== System::TObject::ClassDestroy
   example: V01a:0x40373c
   md5hash: d437f4bf44fa0bb27199419f6c3b6160

  0x40373c   [ 0 ]    mov edx, (eax)       edx := (eax_in)[0] = (eax_in)[0]_in
  0x40373e   [ 0 ]    call* -0x8(edx)      unknown( ? )
  0x403741  [  ?  ]   ret                  return
*)
class rtl_system_tobject_classdestroy_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::TObject::ClassDestroy__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR ")" ]

  method get_commands (floc:floc_int) =
    [ floc#get_abstract_cpu_registers_command [ Eax ] ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) =
    StaticStubTarget (a,PckFunction ("RTL", [ "System" ; "TObject" ], "ClassDestroy"))

  method get_description = "Delphi RTL function System::TObject::ClassDestroy"

end

let _ = H.add table "System::TObject::ClassDestroy"
  (new rtl_system_tobject_classdestroy_semantics_t)


(* =========================================================== System::TObject::ClassInfo
   example: V01a:0x403608
   md5hash: 4020d9c4822c883c2691b57c1556b5ae

  0x403608   [ 0 ]    add eax, -0x3c            eax := eax + -60 = (eax_in - 60)
  0x40360b   [ 0 ]    mov eax, (eax)            eax :=  ?  (tmpN)
  0x40360d   [ 0 ]    ret                       return

  -----------------------------------------------------------------------------------
   example: V1da:0x403728
   md5hash: cb28eb932c6141fe85601f9ab9c125dd

  0x403728   [ 0 ]    push ecx                  save ecx
  0x403729   [ -4 ]   add eax, -0x3c            eax := eax + -60 = (eax_in - 60)
  0x40372c   [ -4 ]   mov eax, (eax)            eax :=  ?  (tmpN)
  0x40372e   [ -4 ]   mov (esp,,1), eax         var.0004 := eax
  0x403731   [ -4 ]   mov eax, (esp,,1)         eax := var.0004
  0x403734   [ -4 ]   pop edx                   edx := var.0004 ; esp := esp + 4 = esp_in
  0x403735   [ 0 ]    ret                       return
*)
class rtl_system_tobject_classinfo_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::TObject::ClassInfo__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let eaxderefv = get_reg_derefvalue Eax (-60) floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR ")" ;
	     STR " [ eax := " ; xpr_to_pretty floc eaxderefv ; STR " ]" ]

  method get_commands (floc:floc_int) =
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let eaxderef = get_reg_derefvalue Eax (-60) floc in
    let cmds = floc#get_assign_commands eaxlhs eaxderef in
    List.concat [ eaxlhscmds ; cmds ]

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a,self#get_name)

  method get_parametercount = 0

  method get_description = "Delphi RTL system class function System::TObject::ClassInfo"

end

 let _ = H.add table "System::TObject::ClassInfo"
  (new rtl_system_tobject_classinfo_semantics_t) 

(* =========================================================== System::TObject::ClassName
   example: V01a:0x403318
   md5hash: ebf081e491df4e8fe9656504ee72ff82

  0x403318   [ 0 ]    push esi             save esi
  0x403319   [ -4 ]   push edi             save edi
  0x40331a   [ -8 ]   mov edi, edx         edi := edx = edx_in
  0x40331c   [ -8 ]   mov esi, -0x2c(eax)  esi := (eax_in)[-44]_in
  0x40331f   [ -8 ]   xor ecx, ecx         ecx := 0 
  0x403321   [ -8 ]   mov cl, (esi)        cl :=  ((eax_in)[-44]_in)[0]
  0x403323   [ -8 ]   inc ecx              ecx := ecx + 1
  0x403324   [ -8 ]   rep movs             (Esi): ((eax_in)[-44]_in)[0]; (Edi): (edx_in)[0]; 
                                              Ecx: ecx (width: 1)
  0x403326   [ -8 ]   pop edi              restore edi
  0x403327   [ -4 ]   pop esi              restore esi
  0x403328   [ 0 ]    ret                  return
*)


(* =========================================================== System::TObject::ClassParent
   example: V01a:0x403354
   md5hash: a6a2ad420473d03034a96615269bdcd2

  0x403354   [ 0 ]    mov eax, -0x24(eax)       eax :=  ?  (tmpN)
  0x403357   [ 0 ]    test eax, eax             test eax, eax
  0x403359   [ 0 ]    jz 0x40335d               if (eax = 0) then goto 0x40335d
--------------------------------------------------------------------------------
  0x40335b   [ 0 ]    mov eax, (eax)            eax :=  ?  (tmpN)
--------------------------------------------------------------------------------
  0x40335d   [ 0 ]    ret                       return
*)
class rtl_system_tobject_classparent_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::TObject::ClassParent__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR ")" ]

  method get_commands (floc:floc_int) =
    let eaxderef = get_reg_derefvalue Eax (-36) floc in
    let eaxdderef = get_x_derefvalue eaxderef 0 floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let cmds = floc#get_assign_commands eaxlhs eaxdderef in
    List.concat [ eaxlhscmds ; cmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a,self#get_name)

  method get_description = "Delphi RTL class function System::TObject::ClassParent"

end

let _ = H.add table "System::TObject::ClassParent" 
  (new rtl_system_tobject_classparent_semantics_t)

    

(* =========================================================== System::TObject::ClassType
   example: V01a:0x403310
   md5hash: bd859b45cdc0733e946c7ef7150db33e

  0x403310   [ 0 ]    mov eax, (eax)            eax := (eax_in)[0] = (eax_in)[0]_in
  0x403312   [ 0 ]    mov edx, eax              edx := eax = (eax_in)[0]_in
  0x403314   [ 0 ]    mov eax, edx              eax := edx = (eax_in)[0]_in
  0x403316   [ 0 ]    ret                       return

  ------------------------------------------------------------------------------------
   example: V1da:0x403420
   md5hash: af33672e73e4d302616d909157181d3e

  0x403420   [ 0 ]    push ecx                  save ecx
  0x403421   [ -4 ]   mov eax, (eax)            eax := (eax_in)[0] = (eax_in)[0]_in
  0x403423   [ -4 ]   mov (esp,,1), eax         var.0004 := eax = (eax_in)[0]_in
  0x403426   [ -4 ]   mov eax, (esp,,1)         eax := var.0004 = (eax_in)[0]_in
  0x403429   [ -4 ]   pop edx                   edx := (eax_in)[0]_in ; esp := esp + 4 = esp_in
  0x40342a   [ 0 ]    ret                       return

*)
class rtl_system_tobject_classtype_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::TObject::ClassType__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR ")" ]

  method get_commands (floc:floc_int) =
    let eaxderef = get_reg_derefvalue Eax 0 floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let (edxlhs,edxlhscmds) = get_reg_lhs Edx floc in
    let cmds1 = floc#get_assign_commands eaxlhs eaxderef in
    let cmds2 = floc#get_assign_commands edxlhs eaxderef in
    List.concat [ eaxlhscmds ; edxlhscmds ; cmds1 ; cmds2 ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a,self#get_name)

  method get_description = "Delphi RTL class function System::TObject::ClassType"

end

let _ = H.add table "System::TObject::ClassType" 
  (new rtl_system_tobject_classtype_semantics_t)


(* =========================================================== System::TObject::Free
   example: V01a:0x4033c8
   md5hash: 4537bb06f56667f04f3d0f8621b29854

  0x4033c8   [ 0 ]    test eax, eax             test eax, eax
  0x4033ca   [ 0 ]    jz 0x4033d3               if (eax_in = 0) then goto 0x4033d3
--------------------------------------------------------------------------------
  0x4033cc   [ 0 ]    mov dl, 0x1               dl := 1
  0x4033ce   [ 0 ]    mov ecx, (eax)            ecx := (eax_in)[0] = (eax_in)[0]_in
  0x4033d0   [ 0 ]    call* -0x4(ecx)           unknown( ? )
--------------------------------------------------------------------------------
  0x4033d3  [  ?  ]   ret                       return
*)


(* ===================================================== System::TObject::InheritsFrom
   example: V01a:0x4035f4
   md5hash: d501e41fd3827af8eeee89cb472d780c

  0x4035f4   [ 0 ]    jmp 0x4035f8              goto 0x4035f8
--------------------------------------------------------------------------------
  0x4035f6   [ 0 ]    mov eax, (eax)            eax :=  ?  (tmpN)
--------------------------------------------------------------------------------
  0x4035f8   [ 0 ]    cmp eax, edx              cmp eax, edx
  0x4035fa   [ 0 ]    jz 0x403604               if (eax = edx_in) then goto 0x403604
--------------------------------------------------------------------------------
  0x4035fc   [ 0 ]    mov eax, -0x24(eax)       eax :=  ?  (tmpN)
  0x4035ff   [ 0 ]    test eax, eax             test eax, eax
  0x403601   [ 0 ]    jnz 0x4035f6              if (eax != 0) then goto 0x4035f6
--------------------------------------------------------------------------------
  0x403603   [ 0 ]    ret                       return
--------------------------------------------------------------------------------
  0x403604   [ 0 ]    mov al, 0x1               al := 1
  0x403606   [ 0 ]    ret                       return
*)



(* =========================================================== System::TObject::InstanceSize
   example: V01a:0x403390
   md5hash: 2b2aadb0511a8ec0ec3effa09cb05fef
   
  0x403390   [ 0 ]    add eax, -0x28            eax := eax + -40 = (eax_in - 40)
  0x403393   [ 0 ]    mov eax, (eax)            eax :=  ?  (tmpN)
  0x403395   [ 0 ]    ret                       return
*)
class rtl_system_tobject_instancesize_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__System::TObject::InstanceSize__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR ")" ]

  method get_commands (floc:floc_int) =
    let eaxderef = get_reg_derefvalue Eax (-40) floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let cmds = floc#get_assign_commands eaxlhs eaxderef in
    List.concat [ eaxlhscmds ; cmds ]

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) = InlinedAppTarget(a,self#get_name)

  method get_description = "Delphi RTL class function System::TObject::InstanceSize"

end

let _ = H.add table "System::TObject::InstanceSize"
  (new rtl_system_tobject_instancesize_semantics_t)


let delphi_rtl_class_functions () = H.fold (fun k v a -> a @ (get_fnhashes k v)) table []

let delphi_rtl_class_patterns = []
