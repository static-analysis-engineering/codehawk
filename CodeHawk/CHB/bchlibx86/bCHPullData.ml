(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open XprTypes
open XprToPretty

(* bchlib *)
open BCHBCTypes
open BCHBCTypePretty
open BCHDemangler
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionSummaryLibrary
open BCHGlobalState
open BCHLibTypes
open BCHLocation
open BCHSystemInfo
open BCHSystemSettings

(* bchlibx86 *)
open BCHAssemblyFunctions
open BCHDisassemblyUtils

module H = Hashtbl
module FFU = BCHFileFormatUtil
module TR = CHTraceResult


let pr_expr = xpr_formatter#pr_expr


let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("PullData:" ^ tag) msg


let get_module_string (floc:floc_int) (xpr:xpr_t) =
  match xpr with
  | XVar v when floc#f#env#is_return_value v ->
    begin
      log_tfold
        (log_error "get_module_string" "invalid call site")
        ~ok:(fun callsite ->
          let cFloc = get_floc (ctxt_string_to_location floc#fa callsite) in
          match cFloc#get_call_args with
          | [(_, vxpr)]
            | [(_, vxpr); _; _] -> get_string_reference floc vxpr
          | _ -> None)
        ~error:(fun _ -> None)
        (floc#f#env#get_call_site v)
    end
  | _ -> None


(* Call to GetProcAddress(hModule,lpProcName) *)
let get_proc_address_target (floc:floc_int) =
  match floc#get_call_args with
  | [(_, xmodule); (_, xprocname)] ->
    begin
      match (
        get_module_string floc xmodule,
        get_string_reference floc xprocname) with
      | (Some smodule,Some sprocname) ->
	 begin
	   system_info#add_lib_function_loaded smodule sprocname;
	   Some (StubTarget (DllFunction (smodule,sprocname)))
	 end
      | (_, Some sprocname) ->
	 begin
	   match function_summary_library#search_for_library_function
                   sprocname with
	   | Some dll ->
	      begin
	        system_info#add_lib_function_loaded dll sprocname;
	        Some (StubTarget (DllFunction (dll, sprocname)))
	      end
	   | _ -> None
	 end
      | _ -> None
    end
  | _ -> None


let check_jni_returnvalue (name: string) (offsets: numerical_t list) =
  let demangledname = get_demangled_name name in
  match demangledname.dm_returntype with
  | Some rt ->
     begin
       match rt with
       | TPtr (TCppComp (SimpleName "JNIEnv_", _, _), _) ->
	  begin
	    match offsets with
	    | [fstoffset; offset] when fstoffset#equal numerical_zero ->
	       let _ =
                 pverbose [
                     STR "Found jni function "; INT (offset#toInt / 4); NL] in
	       [StubTarget (JniFunction (offset#toInt / 4))]
	    | _ ->
	       begin
	         pverbose [
                     STR "Offsets don't match: ";
		     pretty_print_list offsets (fun o -> o#toPretty) "[" "," "]";
		     NL];
	         []
	       end
	  end
       | _ ->
	  begin
	    pverbose [STR "Different type: "; btype_to_pretty rt; NL];
	    []
	  end
     end
  | _ ->
     begin
       pverbose [STR "demangled name: "; STR (demangle name); NL];
       []
     end


let rec get_rv_call_targets
          (_cfloc: floc_int)
          (_floc: floc_int)
          (_offsets: numerical_t list) = []


(* Call to DecodePointer(ptr) *)
and get_decodepointer_target (floc:floc_int) =
  match floc#get_call_args with
  | [(_, ptr)] ->
    begin
      match ptr with
      | XVar v
           when floc#env#is_global_variable v
                && floc#env#has_constant_offset v ->
         log_tfold
           (log_error "get_decodepointer_target" "invalid global address")
           ~ok:(fun gaddr -> get_global_call_targets floc gaddr [])
           ~error:(fun _ -> [])
           (floc#env#get_global_variable_address v)
      | XVar v when floc#env#is_return_value v ->
         log_tfold
           (log_error "get_decodepointer_target" "invalid call site")
           ~ok:(fun callsite ->
	     let rfloc = get_floc (ctxt_string_to_location floc#fa callsite) in
	     get_rv_call_targets floc rfloc [])
           ~error:(fun _ -> [])
           (floc#env#get_call_site v)
      | _ -> []
    end
  | _ -> []


and get_encodepointer_target (floc:floc_int): call_target_t list =
  match floc#get_call_args with
  | [(_, ptr)] ->
    begin
      match ptr with
      | XVar v when floc#env#is_return_value v ->
         log_tfold
           (log_error "get_encodepointer_target" "invalid call site")
           ~ok:(fun callsite ->
             let rfloc = get_floc (ctxt_string_to_location floc#fa callsite) in
	     get_rv_call_targets floc rfloc [])
           ~error:(fun _ -> [])
           (floc#env#get_call_site v)
      | _ -> []
    end
  | _ -> []


and get_constant_call_targets (floc:floc_int) (c:numerical_t) =
  let is_code_address n =
    (try
       system_info#is_code_address (TR.tget_ok (numerical_to_doubleword n))
     with
     | _ -> false) in
  try
    let dw = TR.tget_ok (numerical_to_doubleword c) in
    if assembly_functions#has_function_by_address dw then
      [AppTarget dw]
    else
      match FFU.get_imported_function_by_index dw with
      | Some (dll,name) -> [StubTarget (DllFunction (dll,name))]
      | None when is_code_address c ->
	begin
	  ignore (functions_data#add_function dw);
	  chlog#add
            "indirect function entry point"
	    (LBLOCK [floc#l#toPretty; STR ": target "; c#toPretty]);
	  []
	end
      | _ ->
	begin
	  chlog#add
            "indirect call not resolved"
	    (LBLOCK [
                 floc#l#toPretty;
                 STR ": Constant value target: ";
                 c#toPretty;
		 STR " (";
                 dw#toPretty;
                 STR ")"]);
	  []
	end
  with
  | _ ->
     begin
       chlog#add
         "error in resolving indirect call"
	 (LBLOCK [floc#l#toPretty; STR ": Constant value target: "; c#toPretty]);
       []
     end


and get_global_call_targets
(_cfloc:floc_int)
(_gaddr:doubleword_int)
(_offsets:numerical_t list): call_target_t list = []


and extract_call_target
(cfloc:floc_int)
(finfo:function_info_int)
(x:xpr_t)
(offsets:numerical_t list): call_target_t list =
  let is_code_address n =
    TR.tfold_default
      (fun dw -> system_info#is_code_address dw)
      false
      (numerical_to_doubleword n) in
  let env = finfo#env in
  match x with
  | XVar v when env#is_return_value v ->
     log_tfold
       (log_error "extract_call_target" "invalid call target")
     ~ok:(fun callsite ->
       let rfloc = get_floc (ctxt_string_to_location cfloc#fa callsite) in
       get_rv_call_targets cfloc rfloc offsets)
     ~error:(fun _ -> [])
     (env#get_call_site v)
  | XVar v when env#is_global_variable v && env#has_constant_offset v ->
     log_tfold
       (log_error "extract_call_target" "invalid global address")
       ~ok:(fun gaddr -> get_global_call_targets cfloc gaddr offsets)
       ~error:(fun _ -> [])
       (env#get_global_variable_address v)
  | XVar v when env#is_initial_memory_value v ->
    unpack_memory_variable cfloc finfo v offsets
  | XConst (IntConst num) when is_code_address num ->
    [AppTarget (TR.tget_ok (numerical_to_doubleword num))]
  | _ ->
    begin
      chlog#add
        "call target extraction"
	(LBLOCK [finfo#a#toPretty; STR ": "; pr_expr x]);
      []
    end


and unpack_memory_variable
(_cfloc:floc_int)
(_finfo:function_info_int)
(_v:variable_t)
(_offsets:numerical_t list) = []


and get_argument_embedded_values
(_finfo:function_info_int) (_v:variable_t) = []


and check_jni_interface_pointer
(finfo: function_info_int)
(fArgs: argument_values_int)
(v:variable_t) =
  let env = finfo#env in
  let isjni n = (n = "jni$Env") || (n = "special_jni$Env") in
  let isjavavm v =
    if env#is_global_variable v then
      log_tfold
        (log_error "check_jni_interface_pointer" "invalid global address")
        ~ok:(fun gaddr ->
          let types = global_system_state#get_types gaddr in
          match types with
          | [TPtr ( TNamed ("JavaVM", _), _)] -> true
          | _ -> false)
        ~error:(fun _ -> false)
        (env#get_global_variable_address v)
    else
      false in
  match finfo#env#get_argbasevar_with_offsets v with
  | Some (basevar, offsets) ->
    begin
      match offsets with
      | [fstoffset; offset] when fstoffset#equal numerical_zero ->
	let bxprs = (XVar basevar) :: (fArgs#get_argument_values basevar) in
	if List.exists (fun x ->
	  match x with
	  | XVar var -> isjni (env#variable_name_to_string var)
	  | _ -> false) bxprs then
	  Some (offset#toInt / 4)
	else
	  None
      | _ -> None
    end
  | _ ->
    match finfo#env#get_globalbasevar_with_offsets v with
    | Some (basevar,offsets) ->
      begin
	match offsets with
	| [fstoffset; offset] when fstoffset#equal numerical_zero ->
	  let bxprs = (XVar basevar) :: (fArgs#get_argument_values basevar) in
	  if List.exists (fun x ->
	    match x with
	    | XVar var when isjni (env#variable_name_to_string var) -> true
	    | XVar var -> isjavavm var
	    | _ -> false) bxprs then
	    Some (offset#toInt / 4)
	  else
	    None
	| _ -> None
      end
    | _ -> None


let pull_call_targets (_floc:floc_int) (_v:variable_t) = []
