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

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt

(* bchlib *)
open BCHApiParameter
open BCHBasicTypes
open BCHCPURegisters
open BCHFloc
open BCHFunctionApi
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHPredefinedUtil

module FFU = BCHFileFormatUtil

(* ========================================================== wrappedcall
   example: V494:0x40eba0
   
  0x40eba0   [ 0 ]    push ebp       [0x40eb6a : ?arg_3 = ebp ]
  0x40eba1   [ -4 ]   mov ebp, esp   ebp := esp = (esp_in - 4)
  0x40eba3   [ -4 ]   push 0x0       [0x40eb6a : arg_2 = 0 ]
  0x40eba5   [ -8 ]   push 0x8(ebp)  [0x40eb6a : arg_1 = arg.0004 ]
  0x40eba8  [ -12 ]   call 0x40eb6a  0x40eb6a(arg_1:arg.0004_in, arg_2:0)
  0x40ebad  [ -12 ]   pop ecx        ecx := arg.0004_in ; esp := esp + 4 = (esp_in - 8)
  0x40ebae   [ -8 ]   pop ecx        ecx := 0 ; esp := esp + 4 = (esp_in - 4)
  0x40ebaf   [ -4 ]   pop ebp        restore ebp
  0x40ebb0   [ 0 ]    ret            return
   
*)
class wrapped_call_semantics_t 
  (md5hash:string) 
  (faddr:doubleword_int) 
  (tgt:doubleword_int) 
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wraps_" ^ tgt#to_hex_string ^ "__" 

  method get_annotation (floc:floc_int) =
    try
      let arg1 = get_arg floc#get_call_args 1 floc in
      LBLOCK [ STR tgt#to_hex_string ; STR "(arg_1:" ; xpr_to_pretty floc arg1 ;
	       STR ",arg_2:0)" ]
    with
      BCH_failure p ->
	begin
	  ch_error_log#add "wrapped call: getannotation"
	    (LBLOCK [ floc#l#toPretty ; STR ": " ; p ]) ;
	  LBLOCK [ STR tgt#to_hex_string ; STR "(arg1:?,arg2:0)" ]
	end

  method get_commands (floc:floc_int) =
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 8 } in
    let tgtfloc = get_floc tgtloc in
    get_wrapped_call_commands floc tgtfloc

  method get_parametercount = 1

  method get_call_target (a:doubleword_int) =
    let par1 = mk_stack_parameter 1 in
    let par2 = mk_stack_parameter 2 in
    let fapi = default_function_api faddr#to_hex_string [ par1 ] in
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 8 } in
    let tgtfloc = get_floc tgtloc in
    let wtgt = tgtfloc#get_call_target in
    let t1 = ArgValue par1 in
    let t2 = NumConstant numerical_zero in
    let argmapping = [ (par1,t1) ; (par2,t2) ] in
    WrappedTarget(a,fapi,wtgt,argmapping)
      
  method get_description = "wraps a call to another function"

end

(* =========================================================== wrappedcallesi
   example: V494:0x40e05c

  0x40e05c   [ 0 ]    push esi        [0x40eb44 : arg_1 = esi ]
  0x40e05d   [ -4 ]   call 0x40eb44   0x40eb44(arg_1:esi_in, reg_ebp:ebp_in)
  0x40e062   [ -4 ]   pop ecx         ecx := esi_in ; esp := esp + 4 = esp_in
  0x40e063   [ 0 ]    ret             return

  0x40df82   [ 0 ]    push edi        [0x40eb44 : arg_1 = edi ]
  0x40df83   [ -4 ]   call 0x40eb44   0x40eb44(arg_1:edi_in, reg_ebp:ebp_in)
  0x40df88   [ -4 ]   pop ecx         ecx := edi_in ; esp := esp + 4 = esp_in
  0x40df89   [ 0 ]    ret             return

*)
class wrapped_call_reg_semantics_t
  (md5hash:string) 
  (reg:cpureg_t) 
  (faddr:doubleword_int) 
  (tgt:doubleword_int)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wraps_" ^ tgt#to_hex_string ^ "__"

  method get_annotation (floc:floc_int) =
    let regv = get_reg_value reg floc in
    LBLOCK [ STR tgt#to_hex_string ; STR "(reg_" ; STR (cpureg_to_string reg) ;
	     STR ":" ; xpr_to_pretty floc regv ; STR ")" ]

  method get_commands (floc:floc_int) =
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 1 } in
    let tgtfloc = get_floc tgtloc in
    get_wrapped_call_commands floc tgtfloc

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) =
    let regpar = mk_register_parameter (CPURegister reg) in
    let fapi = default_function_api faddr#to_hex_string [ regpar ] in
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 1 } in    
    let tgtfloc = get_floc tgtloc in
    let wtgt = tgtfloc#get_call_target in
    let par1 = mk_stack_parameter 1 in
    let t1 = ArgValue regpar in
    let argmapping = [ (par1,t1) ] in
    WrappedTarget(a,fapi,wtgt,argmapping)

  method get_description = "wraps a call to another function"

end

(* ========================================================== wrappeddllcall
   example: V3fc:0x409007

  0x409007   [ 0 ]    push 0x435cd0    [DecodePointer : ptr = gv_0x435cd0 ]
  0x40900d   [ -4 ]   call* 0x40d030   DecodePointer(ptr:gv_0x435cd0_in) (adj 4)
  0x409013   [ 0 ]    ret              return
*)
class wrappeddllcall_semantics_t 
  (md5hash:string) 
  (argloc:doubleword_int) 
  (funloc:doubleword_int) 
  (faddr:doubleword_int)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wraps_call_" ^ funloc#to_hex_string ^ "__"

  method get_annotation (floc:floc_int) =
    let gvv = get_gv_value argloc floc in
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 6 } in    
    let tgtfloc = get_floc tgtloc in
    let name = if tgtfloc#has_call_target then
	match tgtfloc#get_call_target with
	| StubTarget (DllFunction (_,name)) -> name
	| _ -> "(*" ^ funloc#to_hex_string ^ ")" 
      else
	"(*?)" in
    LBLOCK [ STR name ; STR "(" ; xpr_to_pretty floc gvv ; STR ")" ]

  method get_commands (floc:floc_int) =
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 6 } in    
    let tgtfloc = get_floc tgtloc in
    get_wrapped_call_commands floc tgtfloc

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) =
    let tpar = mk_global_parameter argloc in
    let fapi =  default_function_api faddr#to_hex_string [ tpar ] in
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 6 } in        
    let tgtfloc = get_floc tgtloc in
    let wtgt = tgtfloc#get_call_target in
    let par1 = mk_stack_parameter 1 in
    let t1 = ArgValue tpar in
    WrappedTarget(a,fapi,wtgt,[ (par1,t1) ])

  method get_description = "wraps a dll call"

end

(* =============================================================================
   example : Vf1e:0x4023b4

  0x4023b4   [ 0 ]    push 0x8bb        [Sleep : dwMilliseconds = 2235 ]
  0x4023b9   [ -4 ]   call* 0x403000    Sleep(dwMilliseconds:2235) (adj 4)
  0x4023bf   [ 0 ]    ret               return
*) 
    
class wrappeddllcallimm_semantics_t 
  (md5hash:string) 
  (arg:doubleword_int) 
  (funloc:doubleword_int) 
  (faddr:doubleword_int)
  (instrs:int):predefined_callsemantics_int =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wraps_call_" ^ funloc#to_hex_string ^ "__"

  method get_annotation (floc:floc_int) =
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 5 } in        
    let tgtfloc = get_floc tgtloc in
    let name = if tgtfloc#has_call_target then
	match tgtfloc#get_call_target with
	| StubTarget (DllFunction (_,name)) -> name
	| _ -> "(*" ^ funloc#to_hex_string ^ ")" 
      else
	"(*?)" in
    LBLOCK [ STR name ; STR "(" ; arg#toPretty ; STR ")" ]

  method get_commands (floc:floc_int) =
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 5 } in        
    let tgtfloc = get_floc tgtloc in
    get_wrapped_call_commands floc tgtfloc

  method get_parametercount = 0

  method get_call_target (a:doubleword_int) =
    let fapi =  default_function_api faddr#to_hex_string [ ] in
    let tgtloc = make_location { loc_faddr = faddr ; loc_iaddr = faddr#add_int 5 } in        
    let tgtfloc = get_floc tgtloc in
    let wtgt = tgtfloc#get_call_target in
    let par1 = mk_stack_parameter 1 in
    let t1 = NumConstant arg#to_numerical in
    WrappedTarget(a,fapi,wtgt,[ (par1,t1) ])

  method get_description = "wraps a dll call"

end

class wrappedgetprocaddress_semantics_t
  (md5hash:string) (libbase:doubleword_int) (procbase:doubleword_int) (instrs:int) =
object (self)

  inherit predefined_callsemantics_base_t md5hash instrs

  method get_name = "__wraps_GetProcAddress__"

  method get_annotation (floc:floc_int) =
    let default () = LBLOCK [ STR "eax := GetProcAddress(?,?)" ] in
    let arg = get_arg floc#get_call_args 1 floc in
    match arg with
    | XConst (IntConst n) ->
      let offset = (n#mult (mkNumerical 8))#toInt in
      let lib = libbase#add_int offset in
      let proc = procbase#add_int offset in
      let libaddr = FFU.get_read_only_initialized_doubleword lib in
      let procaddr = FFU.get_read_only_initialized_doubleword proc in
      (match (libaddr,procaddr) with
      | (Some libaddr,Some procaddr) ->
	let libaddr = num_constant_expr libaddr#to_numerical in
	let procaddr = num_constant_expr procaddr#to_numerical in
	(match (get_string_reference floc libaddr, get_string_reference floc procaddr) with
	| (Some libname, Some procname) ->
	  LBLOCK [ STR "eax := GetProcAddress(" ; 
		   STR libname ; STR "," ; STR procname ; STR ")"]
	| _ -> default ())
      | _ -> default ())
    | _ -> default()

  method get_commands (floc:floc_int) =
    let default () = [ floc#get_abstract_cpu_registers_command [ Eax ] ] in
    let arg = get_arg floc#get_call_args 1 floc in
    let cmds = match arg with
      | XConst (IntConst n) ->
	let offset = (n#mult (mkNumerical 8))#toInt in
	let lib = libbase#add_int offset in
	let proc = procbase#add_int offset in
	let libaddr = FFU.get_read_only_initialized_doubleword lib in
	let procaddr = FFU.get_read_only_initialized_doubleword proc in
	(match (libaddr,procaddr) with
	| (Some libaddr,Some procaddr) ->
	  let libaddr = num_constant_expr libaddr#to_numerical in
	  let procaddr = num_constant_expr procaddr#to_numerical in
	  (match (get_string_reference floc libaddr, get_string_reference floc procaddr) with
	  | (Some libname, Some procname) ->
	    let (lhs,lhscmds) = get_reg_lhs Eax floc in
	    let rhs = floc#f#env#mk_calltarget_value (StubTarget (DllFunction (libname,procname))) in
	    let cmds = floc#get_assign_commands lhs (XVar rhs) in
	    List.concat [ lhscmds ; cmds ]
	  | _ -> default ())
	| _ -> default ())
      | _ -> default () in
    let adjcmds = get_adjustment_commands 4 floc in
    List.concat [ cmds ; adjcmds ]

  method get_parametercount = 1 

  method get_call_target (a:doubleword_int) = InlinedAppTarget (a,self#get_name)

  method get_description = "return function pointer based on offset"

end

let regcall reg faddr fnbytes fnhash =
  let coffset = todwoff (Str.matched_group 1 fnbytes) in
  let caddr = (faddr#add_int coffset)#add_int 6 in
  let sem = new wrapped_call_reg_semantics_t fnhash reg faddr caddr 4 in
  let msg = LBLOCK [ STR "with argument in register " ; STR (cpureg_to_string reg) ] in
  sometemplate ~msg sem

let wrapper_patterns = [

  (* wraps application call with stack argument (V494:0x40eba0) *)
  { regex_s = Str.regexp "558bec6a00ff7508e8\\(........\\)59595dc3$" ;

    regex_f = fun faddr fnbytes fnhash ->
      let coffset = todwoff (Str.matched_group 1 fnbytes) in
      let caddr = (faddr#add_int coffset)#add_int 13 in
      let sem = new wrapped_call_semantics_t fnhash faddr caddr 9 in
      let msg = LBLOCK [ STR " with offset " ; INT coffset ] in
      sometemplate ~msg sem
  } ;

  (* wraps application call with register argument (V494:0x40e05c) *)
  { regex_s = Str.regexp "56e8\\(........\\)59c3$" ;   (* esi *)
    regex_f = regcall Esi
  } ;
  
  { regex_s = Str.regexp "57e8\\(........\\)59c3$" ;   (* edi *)
    regex_f = regcall Edi
  } ;

  (* wraps dll call with hardcoded argument location (V3fc:0x409007) *)
  { regex_s = Str.regexp "ff35\\(........\\)ff15\\(........\\)c3$" ;
    
    regex_f = fun faddr fnbytes fnhash ->
      let argloc = todw (Str.matched_group 1 fnbytes) in
      let funloc = todw (Str.matched_group 2 fnbytes) in
      let sem = new wrappeddllcall_semantics_t fnhash argloc funloc faddr 3 in
      let msg = LBLOCK [ STR " with argument location " ; argloc#toPretty ] in
      sometemplate ~msg sem
  } ;

  (* wraps dll call with hardcoded argument (Vf1e:0x4023b4) *)
  { regex_s = Str.regexp "68\\(........\\)ff15\\(........\\)c3" ;

    regex_f = fun faddr fnbytes fnhash ->
      let arg = todw (Str.matched_group 1 fnbytes) in
      let funloc = todw (Str.matched_group 2 fnbytes) in
      let sem = new wrappeddllcallimm_semantics_t fnhash arg funloc faddr 3 in
      let msg = LBLOCK [ STR " with argument " ; arg#toPretty ] in
      sometemplate ~msg sem
  } ;

  (* wraps dll call GetProcAddress with index for library and procedure name
     (V09035b:0x408037) *)
  
  { regex_s = Str.regexp
      ("5589e5565383ec108b5d088b34dd\\(........\\)893424ff15\\(........\\)85c052" ^
       "89c27512893424ff15\\(........\\)89c231c05185d274168b04dd\\(........\\)89" ^
       "142489442404ff15\\(........\\)52528d65f85b5e5dc20400$") ;

    regex_f = fun faddr fnbytes fnhash ->
      let libbase = todw (Str.matched_group 1 fnbytes) in
      let procbase = todw (Str.matched_group 4 fnbytes) in
      if (isnamed_dll_call faddr 21 "GetModuleHandleA") &&
	(isnamed_dll_call faddr 37 "LoadLibraryA") &&
	(isnamed_dll_call faddr 66 "GetProcAddress") then
	let sem = new wrappedgetprocaddress_semantics_t fnhash libbase procbase 31 in
	let msg = LBLOCK [ STR " with libbase " ; libbase#toPretty ; 
			   STR " and procbase " ; procbase#toPretty ] in
	sometemplate ~msg sem
      else
	None
  }
  
      

]

    
    
