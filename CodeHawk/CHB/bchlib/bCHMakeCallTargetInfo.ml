(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHCallbackTables
open BCHCallTarget
open BCHCallTargetInfo
open BCHDoubleword
open BCHFtsParameter
open BCHFunctionInterface
open BCHFunctionInfo
open BCHFunctionSemantics
open BCHFunctionSummaryLibrary
open BCHLibTypes


let mk_default_target (name:string) (tgt:call_target_t) =
  let fintf = default_function_interface name in
  mk_call_target_info fintf default_function_semantics tgt


let mk_function_summary_target (fs:function_summary_int) (tgt:call_target_t) =
  let fintf = fs#get_function_interface in
  let sem = fs#get_function_semantics in
  mk_call_target_info fintf sem tgt


let mk_unknown_target () =
  mk_default_target "unknown" UnknownTarget


let mk_app_target (a:doubleword_int) =
  let finfo = get_function_info a in
  let apsum = finfo#get_summary in
  mk_function_summary_target apsum (AppTarget a)


let mk_dll_target (dll:string) (name:string) =
  let tgt = StubTarget (DllFunction (dll,name)) in
  if function_summary_library#has_dll_function dll name then
    let fs = function_summary_library#get_dll_function dll name in
    mk_function_summary_target fs tgt
  else
    mk_default_target name tgt


let mk_so_target (name:string) =
  let tgt = StubTarget (SOFunction name) in
  if function_summary_library#has_so_function name then
    let fs = function_summary_library#get_so_function name in
    mk_function_summary_target fs tgt
  else
    mk_default_target name tgt


let mk_syscall_target (index:int) =
  let tgt = StubTarget (LinuxSyscallFunction index) in
  if function_summary_library#has_syscall_function index then
    let fs = function_summary_library#get_syscall_function index in
    mk_function_summary_target fs tgt
  else
    let name = "linux-syscall-" ^ (string_of_int index) in
    mk_default_target name tgt


let mk_jni_target (index:int) =
  let tgt = StubTarget (JniFunction index) in
  if function_summary_library#has_jni_function index then
    let fs = function_summary_library#get_jni_function index in
    mk_function_summary_target fs tgt
  else
    mk_default_target ("jni_" ^ (string_of_int index)) tgt


let mk_virtual_target (fintf: function_interface_t) =
  mk_default_target fintf.fintf_name (VirtualTarget fintf)


let mk_call_back_table_target
      (ctgt: call_target_t) (cba: doubleword_int) (offset: int) =
  let addr = cba#to_hex_string in

(*  let bfargs_to_parameters (fargs: bfunarg_t list option) =
    match fargs with
    | Some funargs ->
       List.mapi
         (fun i (name, btype, _) ->
           mk_stack_parameter ~btype ~name i) funargs
    | _ -> [] in *)

  if callbacktables#has_table addr then
    let cbt = callbacktables#get_table addr in
    let fname = cbt#fieldname_at_offset offset in
    let fty = cbt#type_at_offset offset in
    let fintf = bfuntype_to_function_interface fname fty in
      (* match fty with
      | TFun (rty, fargs, _, _) | TPtr (TFun (rty, fargs, _, _), _) ->
         let params = bfargs_to_parameters fargs in
         default_function_interface ~returntype:rty fname params
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Unexpected type for call-back-table at ";
                   STR addr;
                   STR " with offset ";
                   INT offset])) in *)
    begin
      chlog#add
        "callback-table target created"
        (LBLOCK [STR addr; STR ": "; btype_to_pretty fty]);
      mk_call_target_info fintf default_function_semantics ctgt;
    end
  else
    begin
      chlog#add
        "no callback table found"
        (STR addr);
      mk_default_target ("cbt_" ^ addr) ctgt
    end


let mk_inlined_app_target (a:doubleword_int) (name:string) =
  mk_default_target name (InlinedAppTarget (a,name))


let mk_static_dll_stub_target (a:doubleword_int) (dll:string) (name:string) =
  let tgt = StaticStubTarget (a, DllFunction (dll,name)) in
  if function_summary_library#has_dll_function dll name then
    let fs = function_summary_library#get_dll_function dll name in
    mk_function_summary_target fs tgt
  else
    mk_default_target name tgt


let mk_static_pck_stub_target
      (a:doubleword_int) (lib:string) (pkgs:string list) (name:string) =
  mk_default_target name (StaticStubTarget (a, PckFunction (lib,pkgs,name)))


let mk_wrapped_target
      (a: doubleword_int)
      (fintf: function_interface_t)
      (tgt: call_target_t)
      (parameters:(fts_parameter_t * bterm_t) list) =
  mk_default_target fintf.fintf_name ( WrappedTarget (a, fintf, tgt, parameters))


let update_target_interface
      (ctinfo: call_target_info_int) (fintf: function_interface_t) =
  let semantics = ctinfo#get_semantics in
  let tgt = ctinfo#get_target in
  mk_call_target_info fintf semantics tgt


let mk_call_target_info (ctgt: call_target_t): call_target_info_int =
  match ctgt with
  | StubTarget (DllFunction (dll, name)) -> mk_dll_target dll name
  | StubTarget (SOFunction name) -> mk_so_target name
  | StubTarget (JniFunction index) -> mk_jni_target index
  | AppTarget addr -> mk_app_target addr
  | IndirectTarget (_, l) -> mk_default_target "$dispatch$" ctgt
  | CallbackTableTarget (cba, offset) ->
     mk_call_back_table_target ctgt cba offset
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "mk_call_target_info: call target not covered: ";
               call_target_to_pretty ctgt]))
