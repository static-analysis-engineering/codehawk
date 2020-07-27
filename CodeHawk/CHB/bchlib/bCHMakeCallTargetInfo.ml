(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2020 Henny B. Sipma

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHCallTargetInfo
open BCHDoubleword
open BCHFunctionApi
open BCHFunctionSemantics
open BCHLibTypes


let mk_default_target (name:string) (tgt:call_target_t) =
  let api = default_function_api name [] in
  mk_call_target_info api default_function_semantics tgt

let mk_unknown_target () =
  mk_default_target "unknown" UnknownTarget

let mk_app_target (a:doubleword_int) =
  mk_default_target a#to_hex_string (AppTarget a)

let mk_dll_target (dll:string) (name:string) =
  mk_default_target name (StubTarget (DllFunction (dll,name)))

let mk_so_target (name:string) =
  mk_default_target name (StubTarget (SOFunction name))

let mk_jni_target (index:int) =
  mk_default_target
    ("jni_" ^ (string_of_int index))
    (StubTarget (JniFunction index))

let mk_virtual_target (fapi:function_api_t) =
  mk_default_target fapi.fapi_name (VirtualTarget fapi)

let mk_inlined_app_target (a:doubleword_int) (name:string) =
  mk_default_target name (InlinedAppTarget (a,name))

let mk_static_dll_stub_target (a:doubleword_int) (dll:string) (name:string) =
  mk_default_target name (StaticStubTarget(a, DllFunction (dll,name)))

let mk_static_pck_stub_target
      (a:doubleword_int) (lib:string) (pkgs:string list) (name:string) =
  mk_default_target name (StaticStubTarget (a, PckFunction (lib,pkgs,name)))

let mk_wrapped_target
      (a:doubleword_int)
      (fapi:function_api_t)
      (tgt:call_target_t)
      (parameters:(api_parameter_t * bterm_t) list) =
  mk_default_target fapi.fapi_name ( WrappedTarget (a, fapi, tgt, parameters))
