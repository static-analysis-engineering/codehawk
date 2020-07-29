(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* xprlib *)
open Xprt

(* bchlib *)
open BCHMakeCallTargetInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHPredefinedUtil

module H = Hashtbl

let table = H.create 3

(* ======================================================================= _clearfp
   example: nginx: 0x58a3fb
*)
class clearfp_semantics_t 
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__clearfp__"

  method get_annotation (floc:floc_int) =
    let ecxv = get_reg_value Ecx floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc ecxv ; STR ")" ]

  method get_parametercount = 0

  method get_description = "internal floating point function"

end

(* ======================================================================= _clrfp
   example: V007: 0x44f677
*)
class clrfp_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__clrfp__"

  method get_parametercount = 0

end

let _ = H.add table "_clrfp" (new clrfp_semantics_t)

(* ======================================================================= _ctrlfp
   example: V007: 0x44f688
*)
class ctrlfp_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__ctrlfp__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(new:" ; xpr_to_pretty floc arg1 ;
	     STR ",mask:" ; xpr_to_hexpretty floc arg2 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_arg_lhs 4 floc in
    let cmds1 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Eax ] ] in
    let cmds2 = floc#get_abstract_commands lhs () in
    List.concat [ lhscmds ; cmds1 ; cmds2 ]

  method get_parametercount = 2

  method get_description = "older implementation of controlfp"

end

let _ = H.add table "_ctrlfp" (new ctrlfp_semantics_t)

(* ======================================================================= _decomp
   example: V007: 0x44f5ae
*)
class decomp_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__decomp__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    let arg3 = get_arg args 3 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg1 ;
	     STR "," ; xpr_to_pretty floc arg2 ; 
	     STR ",dst:" ; xpr_to_pretty floc arg3 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let (arglhs,arglhscmds) = get_arg_lhs 12 floc in
    let (eaxlhs,eaxlhscmds) = get_reg_lhs Eax floc in
    let serhs = floc#env#mk_side_effect_value floc#cia "dst" in
    let rvrhs = get_return_value self#get_name floc in
    let cmds1 = floc#get_assign_commands arglhs (XVar serhs) in
    let cmds2 = floc#get_assign_commands eaxlhs (XVar rvrhs) in
    let cmds3 = [ floc#get_abstract_cpu_registers_command [ Ecx ; Edx ] ] in
    List.concat [ arglhscmds ; eaxlhscmds ; cmds1 ; cmds2 ; cmds3 ]

  method get_parametercount = 3

  method get_description = "decomposes a floating point number"

end

(* ======================================================================= __dtold
   example: V007: 0x452383
*)
class dtold_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__dtold__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(arg1" ; xpr_to_pretty floc arg1 ; 
	     STR ",arg2" ; xpr_to_pretty floc arg2 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let arg1 = get_arg floc#get_call_args 1 floc in
    let lhs = get_x_deref_lhs arg1 0 floc in
    let rhs = floc#env#mk_side_effect_value floc#cia "arg1" in
    let size = int_constant_expr 8 in
    let cmds1 = floc#get_assign_commands lhs ~size (XVar rhs) in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Eax ; Ecx ; Edx ] ] in
    List.concat [ cmds1 ; cmds2 ]

  method get_parametercount = 2

end

let _ = H.add table "dtold" (new dtold_semantics_t)

(* ================================================================ _errcode
   example: V007: 0x4ff31c
*)
class errcode_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__errcode__"

  method get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg ; STR ")" ]

  method get_parametercount = 1

end

let _ = H.add table "_errcode" (new errcode_semantics_t)

(* ======================================================================= _frnd
   example: V007:0x4ff50e
*)
class frnd_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__frnd__"

  method get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(d:" ; xpr_to_pretty floc arg ; STR ")" ]

  method get_commands (floc:floc_int) = []

  method get_parametercount = 1

end

let _ = H.add table "_frnd" (new frnd_semantics_t)
    

(* ======================================================================= __ftol__

  0x78    [ 0 ]       push ebp                  save ebp
  0x79    [ -4 ]      mov ebp, esp              ebp := esp = (esp_in - 4)
  0x7b    [ -4 ]      add esp, -0xc             esp := esp + -12 = (esp_in - 16)
  0x7e   [ -16 ]      wait                      wait
  0x7f   [ -16 ]      fnstcw -0x2(ebp)          var.0006 := FPU control word
  0x82   [ -16 ]      wait                      wait
  0x83   [ -16 ]      mov ax, -0x2(ebp)         ax := var.0006
  0x87   [ -16 ]      or ah, 0xc                ah := ah | 12
  0x8a   [ -16 ]      mov -0x4(ebp), ax         var.0008 := ax
  0x8e   [ -16 ]      fldcw -0x4(ebp)           FPU control word := var.0008
  0x91   [ -16 ]      fistp -0xc(ebp)           var.0016 := ST(0) (8 bytes)
  0x94   [ -16 ]      fldcw -0x2(ebp)           FPU control word := var.0006
  0x97   [ -16 ]      mov eax, -0xc(ebp)        eax := var.0016
  0x9a   [ -16 ]      mov edx, -0x8(ebp)        edx := var.0012
  0x9d   [ -16 ]      leave                     esp := ebp ; ebp := var.0004 ; esp := esp + 4 
  0x9e    [ 0 ]       ret                       return
*)

class ftol_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__ftol__"

  method get_parametercount = 0

  method get_description = "float to long"

end

let _ = H.add table "ftol" (new ftol_semantics_t)

(* =============================================================== ftol2
   example: V007:0x4541c6
*)
class ftol2_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__ftol2__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR "," ;
	     xpr_to_pretty floc edxv ; STR ")" ]

  method get_parametercount = 0

  method get_description = "internal function that converts float to long"

end

let _ = H.add table "ftol2" (new ftol2_semantics_t)

(* =============================================================== ftol2_sse
   example: V007: 0x454190
*)
class ftol2sse_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__ftol2_sse__"

  method get_annotation (floc:floc_int) =
    let eaxv = get_reg_value Eax floc in
    let edxv = get_reg_value Edx floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc eaxv ; STR "," ;
	     xpr_to_pretty floc edxv ; STR ")" ]

  method get_parametercount = 0

  method get_description = "internal function that converts float to long"

end    

(* =============================================================== _set_exp
   example: V007: V44f522
*)
class setexp_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__set_exp__"

  method get_annotation (floc:floc_int) =
    let arg3 = get_arg floc#get_call_args 3 floc in
    let argoff10 = (esp_deref ~with_offset:6 RD)#to_expr floc in
    LBLOCK [ STR self#get_name ; STR "(off10:" ; xpr_to_pretty floc argoff10 ;
	     STR ",exp:" ; xpr_to_pretty floc arg3 ; STR ")" ]

  method get_parametercount = 3

end

let _ = H.add table "_set_exp" (new setexp_semantics_t)

(* =============================================================== _statusfp
   example: nginx: 0x58a0d6
*)
class statusfp_semantics_t
  (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__statusfp__"

  method get_parametercount = 0

  method get_description = "internal floating point function"
 
end

let _ = H.add table "_statusfp" (new statusfp_semantics_t)


(* =============================================================== __load_CW
   example: V008:0x41cb05
*)
class loadcw_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__load_CW__"

  method get_annotation (floc:floc_int) =
    let args = floc#get_call_args in
    let arg1 = get_arg args 1 floc in
    let arg2 = get_arg args 2 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg1 ;
	     STR "," ; xpr_to_pretty floc arg2 ; STR ")" ]

  method get_commands (floc:floc_int) =
    let (lhs,lhscmds) = get_arg_lhs 4 floc in
    let cmds1 = floc#get_abstract_commands lhs () in
    let cmds2 = [ floc#get_abstract_cpu_registers_command [ Edx ] ] in
    List.concat [ lhscmds ; cmds1 ; cmds2 ]

  method get_parametercount = 2

end

let _ = H.add table "__load_CW" (new loadcw_semantics_t)

(* =============================================================== set_fpu_control
   V429: 0x4030a8

  0x4030a8   [ 0 ]    fninit                    fninit
  0x4030aa   [ 0 ]    wait                      wait
  0x4030ab   [ 0 ]    fldcw 0x435024            FPU control word := gv_0x435024
  0x4030b1   [ 0 ]    ret                       return
*)
class set_fpu_control_semantics_t 
  (md5hash:string) (gv:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__set_fpu_controlword_" ^ (gv#to_hex_string) ^ "__"

  method get_annotation (floc:floc_int) =
    let gvv = get_gv_value gv floc in
    LBLOCK [ STR "finit; FPU control word := " ; xpr_to_pretty floc gvv ]

  method get_commands (floc:floc_int) = []

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) =
    mk_inlined_app_target a self#get_name

  method get_description = "sets fpu control word to global variable"

end

(* =================================================================== __set_statfp
   example: V007:0x44f6b1 
*)
class setfpstat_semantics_t
  (md5hash:string) (gv:doubleword_int) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__set_statfp__"

  method get_annotation (floc:floc_int) =
    let arg = get_arg floc#get_call_args 1 floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg ; STR ")" ]

  method get_commands (floc:floc_int) =
    [ floc#get_abstract_cpu_registers_command [ Ecx ] ]

  method get_parametercount = 1

end

(* ======================================================================= _statfp
   example: V007: 0x44f667
*)
class statfp_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__statfp__"

  method get_parametercount = 0

end

let _ = H.add table "_statfp" (new statfp_semantics_t)

(* ======================================================================= _sptype
   example: V007: 0x44f54e
*)
class sptype_semantics_t (md5hash:string) (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__sptype__"

  method get_annotation (floc:floc_int) =
    let arg1 = get_arg floc#get_call_args 3 floc in
    let argoff10 = (esp_deref ~with_offset:6 RD)#to_expr floc in
    LBLOCK [ STR self#get_name ; STR "(" ; xpr_to_pretty floc arg1 ; 
	     STR ",off10:" ; xpr_to_pretty floc argoff10 ; STR ")" ]

  method get_parametercount = 2

end

let _ = H.add table "_sptype" (new sptype_semantics_t)

let fp_functions = H.fold (fun k v a -> a @ (get_fnhashes k v)) table []

let fp_patterns = [

  (* _clearfp (nginx: 0x0x58a3f9) *)
  { regex_s = Str.regexp
      ("8bff558bec5151dd7dfcdbe2833d\\(........\\)000f84820000008a45fc33d256be" ^
       "00000800a83f7429a80174036a105aa804740383ca08a808740383ca04a810740383ca" ^
       "02a820740383ca01a80274020bd60fae5df88365f8c00fae55f88a4df833c0f6c13f74" ^
       "2ff6c10174036a1058f6c104740383c808f6c108740383c804f6c110740383c802f6c1" ^
       "20740383c801f6c10274020bc60bc25ec9c38a4dfc33c0f6c13f7432f6c10174036a10" ^
       "58f6c104740383c808f6c108740383c804f6c110740383c802f6c120740383c801f6c1" ^
       "0274050d00000800c9c3$") ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new clearfp_semantics_t fnhash 88 in
      let msg = LBLOCK [ STR "with gv " ; gv#toPretty ] in
      sometemplate ~msg sem
  } ;

  (* _clearfp (nginx:0x58a3fb) *)
  { regex_s = Str.regexp
      ("558bec5151dd7dfcdbe2833d\\(........\\)000f84820000008a45fc33d2" ^
       "56be00000800a83f7429a80174036a105aa804740383ca08a808740383ca04a8107403" ^
       "83ca02a820740383ca01a80274020bd60fae5df88365f8c00fae55f88a4df833c0f6c1" ^
       "3f742ff6c10174036a1058f6c104740383c808f6c108740383c804f6c110740383c802" ^
       "f6c120740383c801f6c10274020bc60bc25ec9c38a4dfc33c0f6c13f7432f6c1017403" ^
       "6a1058f6c104740383c808f6c108740383c804f6c110740383c802f6c120740383c801" ^
       "f6c10274050d00000800c9c3$") ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new clearfp_semantics_t fnhash 88 in
      let msg = LBLOCK [ STR "with gv " ; gv#toPretty ] in
      sometemplate ~msg sem
  } ;

  (* _decomp (V007: 0x44f5ae) *)
  { regex_s = Str.regexp
      ("8bff558becd9eedc5508dfe0f6c4447a0733d2e99a0000008b550e33c9f7c2f07f0000" ^
       "756bf7450cffff0f007505394d08745ddc5d08ba03fcffffdfe0f6c441750533c040eb" ^
       "1833c0eb14d1650cf74508000000807404834d0c01d165084af6450e1074e656beefff" ^
       "00006621750e5e3bc17409b8008000006609450edd4508515151dd1c24e8\\(........\\)" ^
       "83c40ceb2251ddd8dd45085151dd1c24e8\\(........\\)c1ea0481e2ff07000083c4" ^
       "0c81eafe0300008b451089105dc3$") ;

    regex_f = fun faddr fnbytes fnhash ->
      if is_named_app_call faddr 134 "__set_exp__" &&
	is_named_app_call faddr 155 "__set_exp__" then
	let sem = new decomp_semantics_t fnhash 67 in
	sometemplate sem
      else
	None
  } ;

  (* ftol2_sse (V007: 0x454190) *)
  { regex_s = Str.regexp
      ("833d\\(........\\)00742d558bec83ec0883e4f8dd1c24f20f2c0424c9c3558bec83" ^
       "ec2083e4f0d9c0d9542418df7c2410df6c24108b5424188b44241085c0743cdee985d2" ^
       "791ed91c248b0c2481f10000008081c1ffffff7f83d0008b54241483d200eb2cd91c24" ^
       "8b0c2481c1ffffff7f83d8008b54241483da00eb148b542414f7c2ffffff7f75b8d95c" ^
       "2418d95c2418c9c3$") ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new ftol2sse_semantics_t fnhash 47 in
      let msg = LBLOCK [ STR " with SSE checkpoint " ; gv#toPretty ] in
      sometemplate ~msg sem
  } ;

  (* set fpu control word (V429: 0x4030a8) *)
  { regex_s = Str.regexp "dbe39bd92d\\(........\\)c3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let gv = todw (Str.matched_group 1 fnbytes) in
      let sem = new set_fpu_control_semantics_t fnhash gv 4 in
      let msg = LBLOCK [ STR " with global variable gv_" ; gv#toPretty ] in
      sometemplate ~msg sem
  } ;

  (* __set_statfp (V007:0x44f6b1) *)
   { regex_s = Str.regexp 
       ("8bff558bec51518a4d08f6c101740adb2d\\(........\\)db5d089bf6c10874109bd" ^
	"fe0db2d\\(........\\)dd5df89b9bdfe0f6c110740adb2d\\(........\\)dd5df8" ^
	"9bf6c1047409d9eed9e8def1ddd89bf6c1207406d9ebdd5df89bc9c3$") ;

     regex_f = fun faddr fnbytes fnhash ->
       let gv1 = todw (Str.matched_group 1 fnbytes) in
       let gv2 = todw (Str.matched_group 2 fnbytes) in
       let gv3 = todw (Str.matched_group 3 fnbytes) in
       if gv1#equal gv2 && (gv1#add_int 12)#equal gv3 then
	 let sem = new setfpstat_semantics_t fnhash gv1 39 in
	 let msg = LBLOCK [ STR " with global variable gv_" ; gv1#toPretty ] in
	 sometemplate ~msg sem
       else
	 None
   } ;

   (* __set_statfp (V008:419369) *)
   { regex_s = Str.regexp
       ("558bec51518b4d08f6c101740adb2d\\(........\\)db5d089bf6c10874109bdfe0" ^
	"db2d\\(........\\)dd5df89b9bdfe0f6c110740adb2d\\(........\\)dd5df89b" ^
	"f6c1047409d9eed9e8def1ddd89bf6c1207406d9ebdd5df89b8be55dc3$") ;

     regex_f = fun faddr fnbytes fnhash ->
       let gv1 = todw (Str.matched_group 1 fnbytes) in
       let gv2 = todw (Str.matched_group 2 fnbytes) in
       let gv3 = todw (Str.matched_group 3 fnbytes) in
       if gv1#equal gv2 && (gv1#add_int 12)#equal gv3 then
	 let sem = new setfpstat_semantics_t fnhash gv1 39 in
	 let msg = LBLOCK [ STR " with global variable gv_" ; gv1#toPretty ] in
	 sometemplate ~msg sem
       else
	 None
   } ;

]
