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

(* bchlib *)
open BCHBasicTypes
open BCHBTerm
open BCHCallTarget
open BCHFunctionData
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHSystemInfo

let has_function_stub_name (fs:function_stub_t) =
  match fs with
  | SOFunction _ -> true
  | DllFunction _ -> true
  | JniFunction i -> function_summary_library#has_jni_function i
  | PckFunction _ -> true

let rec has_call_target_name (tgt:call_target_t) =
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> has_function_stub_name fs
  | AppTarget a -> functions_data#has_function_name a
  | InlinedAppTarget _ -> true
  | WrappedTarget (_,_,wtgt,_) -> has_call_target_name wtgt
  | IndirectTarget (_,tgts) -> List.exists has_call_target_name tgts
  | VirtualTarget _ -> true
  | _ -> false

let get_function_stub_name (fs:function_stub_t) =
  match fs with
  | SOFunction s -> s
  | DllFunction (_,s) -> s
  | JniFunction i ->
    if function_summary_library#has_jni_function i then
      (function_summary_library#get_jni_function i)#get_name
    else
      "jni-" ^ (string_of_int i)
  | PckFunction(_,pkgs,s) -> (String.concat "::" pkgs) ^ s
     
let rec get_call_target_name (tgt:call_target_t) =
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> get_function_stub_name fs
  | AppTarget a -> (functions_data#get_function a)#get_function_name
  | InlinedAppTarget (_,name) -> name
  | WrappedTarget (_,_,wtgt,_) -> get_call_target_name wtgt
  | VirtualTarget api -> api.fapi_name
  | IndirectTarget (_,tgts) ->
    begin
      try
	get_call_target_name (List.find has_call_target_name tgts)
      with
	Not_found ->
	  raise (BCH_failure (LBLOCK [ STR "Indirect target has no names: " ;
				       call_target_to_pretty tgt ]))
    end
  | _ -> raise (BCH_failure (LBLOCK [ STR "Call target has no name: " ; 
				      call_target_to_pretty tgt ]))

let function_stub_has_signature (fs:function_stub_t) =
  match fs with
  | SOFunction fname -> function_summary_library#has_so_function fname
  | DllFunction (dll,name) -> function_summary_library#has_dll_function dll name
  | JniFunction i -> function_summary_library#has_jni_function i
  | PckFunction (_,pkgs,name) -> function_summary_library#has_lib_function pkgs name

let rec has_call_target_signature (tgt:call_target_t) =
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> function_stub_has_signature fs
  | VirtualTarget _ 
  | AppTarget _ 
  | InlinedAppTarget _ -> true
  | WrappedTarget _ -> false
  | IndirectTarget (_,tgts) -> List.exists has_call_target_signature tgts
  | UnknownTarget -> false

let function_stub_get_signature (fs:function_stub_t) =
  match fs with
  | DllFunction (dll,name) ->
     if function_summary_library#has_dll_function dll name then
       (function_summary_library#get_dll_function dll name)#get_function_api
     else
       raise (BCH_failure
                (LBLOCK [ STR "Dll function " ; STR name ; STR " has no summary" ]))
  | JniFunction i ->
    if function_summary_library#has_jni_function i then
      (function_summary_library#get_jni_function i)#get_function_api
    else
      raise (BCH_failure
	       (LBLOCK [ STR "Jni function " ; INT i ; STR " has no summary" ])) 
  | PckFunction(_,pkgs,name) ->
    if function_summary_library#has_lib_function pkgs name then
      (function_summary_library#get_lib_function pkgs name)#get_function_api
    else
      raise (BCH_failure
	       (LBLOCK [ STR "Lib function " ; STR (String.concat "::" pkgs) ; 
			 STR "::" ; STR name ; STR " has no summary" ]))
  | SOFunction fname ->
     if function_summary_library#has_so_function fname then
       (function_summary_library#get_so_function fname)#get_function_api
     else
       raise (BCH_failure (LBLOCK [ STR "SOFunction " ; STR fname ;
                                    STR " has no summary" ]))
    
let rec get_call_target_signature get_function_info (tgt:call_target_t) =
  let get_api fsum = fsum#get_function_api in
  let get_app_api faddr =
    let default fname =
      get_api (get_function_info faddr)#get_summary in
    match (functions_data#get_function faddr)#get_names with
    | [ name ] -> default name
    | _ -> default faddr#to_hex_string in
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> function_stub_get_signature fs
  | AppTarget a 
  | InlinedAppTarget (a,_) -> get_app_api a
  | VirtualTarget api -> api
  | IndirectTarget (v,tgts) -> 
    begin
      try
	let tgt = List.find has_call_target_signature tgts in
	get_call_target_signature get_function_info tgt
      with
	Not_found ->
	  raise (BCH_failure
		   (LBLOCK [ STR "Indirect call target " ; bterm_to_pretty v ; 
			     STR " does not have a usable target" ]))
    end
  | _ ->
    raise (BCH_failure
	     (LBLOCK [ STR "No signature found for " ;
		       call_target_to_pretty tgt ]))

let function_stub_has_semantics (fs:function_stub_t) =
  match fs with
  | SOFunction name -> function_summary_library#has_so_function name 
  | DllFunction (dll,name) -> function_summary_library#has_dll_function dll name
  | JniFunction i -> function_summary_library#has_jni_function i
  | PckFunction _ -> false
                   
let rec has_call_target_semantics (tgt:call_target_t) =
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> function_stub_has_semantics fs
  | AppTarget _ 
  | InlinedAppTarget _ -> true
  | WrappedTarget _ -> false
  | IndirectTarget (_,tgts) -> List.exists has_call_target_semantics tgts
  | _ -> false

let function_stub_get_semantics (fs:function_stub_t) =
  match fs with
  | DllFunction (dll,name) ->
    if function_summary_library#has_dll_function dll name then
      (function_summary_library#get_dll_function dll name)#get_function_semantics
    else
      raise (BCH_failure
	       (LBLOCK [ STR "No dll function summary found for " ; 
			 STR dll ; STR ":" ; STR name ]))  
  | JniFunction i ->
    if function_summary_library#has_jni_function i then
      (function_summary_library#get_jni_function i)#get_function_semantics
    else
      raise (BCH_failure
	       (LBLOCK [ STR "Jni function " ; INT i ; STR " has no summary" ]))
  | SOFunction name ->
     if function_summary_library#has_so_function name then
       (function_summary_library#get_so_function name)#get_function_semantics
     else
       raise (BCH_failure (LBLOCK [ STR "No semantics found for so-function " ;
                                    STR name ]))
  | _ ->
     raise (BCH_failure (LBLOCK [ STR "No semantics found " ]))
    
let rec get_call_target_semantics get_function_info (tgt:call_target_t) =
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> function_stub_get_semantics fs
  | AppTarget a 
  | InlinedAppTarget (a,_) ->
    (get_function_info a)#get_summary#get_function_semantics
  | IndirectTarget (_,tgts) ->
    begin
      try
	let tgt = List.find has_call_target_semantics tgts in
	get_call_target_semantics get_function_info tgt
      with
	Not_found ->
	  raise (BCH_failure
		   (LBLOCK [ STR "No indirect target found with semantics" ;
			     call_target_to_pretty tgt ]))
    end
  | _ ->
    raise (BCH_failure
	     (LBLOCK [ STR "Target does not have semantics: " ;
		       call_target_to_pretty tgt ])) 


let has_function_stub_summary (fs:function_stub_t) =
  match fs with
  | SOFunction name -> function_summary_library#has_so_function name
  | DllFunction (dll,name) -> function_summary_library#has_dll_function dll name
  | JniFunction i -> function_summary_library#has_jni_function i
  | PckFunction _ -> false
                   
let has_call_target_summary (tgt:call_target_t) =
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> has_function_stub_summary  fs
  | AppTarget _ 
  | InlinedAppTarget _ -> true
  | WrappedTarget _ -> false
  | _ -> false

let get_function_stub_summary (fs:function_stub_t)  =
  match fs with
  | DllFunction (dll,name) ->
    (try
       function_summary_library#get_dll_function dll name
     with
     | BCH_failure _ ->
       raise (BCH_failure
		(LBLOCK [ STR "Dll target has no summary: " ; STR dll ; STR ":" ;
			  STR name ])))
  | JniFunction i ->     
    if function_summary_library#has_jni_function i then
      function_summary_library#get_jni_function i
     else
       raise (BCH_failure (LBLOCK [ STR "Jni target has no summary: " ; INT i ]))
  | SOFunction name ->
     if function_summary_library#has_so_function name then
       function_summary_library#get_so_function name
     else
       raise (BCH_failure
                (LBLOCK [ STR "SO function " ; STR name ;
                          STR " does not have a summary" ]))
  | _ ->
     raise (BCH_failure (LBLOCK [ STR "Function stub has no summary" ]))
    
let get_call_target_summary get_function_info (tgt:call_target_t) =
  match tgt with
  | StubTarget fs
    | StaticStubTarget (_,fs) -> get_function_stub_summary fs
  | AppTarget a 
  | InlinedAppTarget (a,_) -> (get_function_info a)#get_summary
  | _ ->
    raise (BCH_failure (LBLOCK [ STR "Call target " ; call_target_to_pretty tgt ;
				 STR " has no summary"] ))
        
