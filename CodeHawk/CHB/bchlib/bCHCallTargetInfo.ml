(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHBTerm
open BCHCallTarget
open BCHDoubleword
open BCHFunctionInterface
open BCHFunctionSemantics
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHInterfaceDictionary
open BCHLibTypes
open BCHVariableType


let raise_error tgt msg =
  begin
    ch_error_log#add "call target" msg ;
    raise (BCH_failure  (LBLOCK [ msg ; STR ": " ; call_target_to_pretty tgt ]))
  end


let id = interface_dictionary


class call_target_info_t
        (fintf: function_interface_t)
        (sem: function_semantics_t)
        (tgt: call_target_t):call_target_info_int =
object (self)

  method get_name = fintf.fintf_name
                  
  method get_target = tgt
                    
  method get_app_address =
    match tgt with
    | AppTarget a -> a
    | _ ->
       let msg = STR "Call target is not an application target" in
       raise_error tgt msg

  method get_application_target =
    match tgt with
    | StaticStubTarget (a,_)  -> a
    | AppTarget a -> a
    | InlinedAppTarget (a,_) -> a
    | WrappedTarget (a,_,_,_) -> a
    | _ ->
       let msg = STR "Call target does not correspond to an application target" in
       raise_error tgt msg

  method get_dll_target =
    let msg = STR "Call target is not a dll target" in
    match tgt with
    | StubTarget fs | StaticStubTarget (_,fs) ->
       (match fs with
        | DllFunction (dll,name) -> (dll,name)
        | _ -> raise_error tgt msg)
    | _ -> raise_error tgt msg

  method get_wrapped_app_address =
    match tgt with
    | WrappedTarget (_, _, AppTarget a, _) -> a
    | _ ->
       let msg = STR "Call target is a wrapped application target" in
       raise_error tgt msg

  method get_wrapped_app_parameter_mapping =
    match tgt with
    | WrappedTarget (_, _, _, mapping) -> mapping
    | _ ->
       let msg = STR "Call target is not a wrapped application target" in
       raise_error tgt msg

  method get_inlined_target =
    match tgt with
    | InlinedAppTarget (a,name) -> (a,name)
    | _ ->
       let msg = STR "Call target is not an inlined target" in
       raise_error tgt msg

  method get_static_lib_target =
    match tgt with
    | StaticStubTarget (a, PckFunction (lib, pkgs, name)) ->
       (a, lib, pkgs, name)
    | _ ->
       let msg = STR "Call target is not a static library function" in
       raise_error tgt msg

  method  get_jni_target_index =
    match tgt with
    | StubTarget (JniFunction i) -> i
    | _ ->
       let msg = STR "Call target is not a JNI function" in
       raise_error tgt msg

  method get_function_interface = fintf

  method get_signature = fintf.fintf_type_signature

  method get_parameters = self#get_signature.fts_parameters
                       
  method get_returntype = self#get_signature.fts_returntype
                        
  method get_stack_adjustment = self#get_signature.fts_stack_adjustment

  method get_semantics = sem
                       
  method get_jni_index =
    match fintf.fintf_jni_index with
    | Some i -> i
    | _ ->
       begin
	 ch_error_log#add
           "invocation error" 
	   (LBLOCK [ STR "function_summary#get_jni_index" ]);
	 raise
           (BCH_failure
              (LBLOCK [
                   STR "Call target is not a jni target: ";
                   call_target_to_pretty tgt]))
       end

  method get_preconditions = sem.fsem_pre
                                         
  method get_postconditions = sem.fsem_post
                            
  method get_errorpostconditions = sem.fsem_errorpost
                                 
  method get_sideeffects = sem.fsem_sideeffects
                         
  method get_io_actions = sem.fsem_io_actions

  method get_enums_referenced =
    let l = ref [] in
    let add s = if List.mem s !l then () else l := s :: !l in
    let _ =
      List.iter (fun p ->
          match p with
          | PreEnum (_,s,_) -> add s
          | _ -> ()) self#get_preconditions in
    let _ =
      List.iter (fun p ->
          match p with
          | PostEnum (_,s) -> add s
          | _ -> ()) self#get_postconditions in
    !l

  method get_enum_type (par: fts_parameter_t) =
    List.fold_left (fun acc pre ->
        match acc with
        | Some _ -> acc
        | _ ->
	   match pre with
	   | PreEnum (ArgValue p,s,flags) ->
	      if fts_parameter_compare p par = 0 then
                Some (t_named s,flags)
              else
                None
	   | _ -> None) None self#get_preconditions


  method is_nonreturning =
    List.exists
      (fun p -> match p with PostFalse -> true | _ -> false) sem.fsem_post

  method has_sideeffects =
    match self#get_sideeffects with
    | [] -> false
    | _ -> true

  method is_signature_valid = (* not api.fapi_inferred *) true
                            
  method is_semantics_valid = true
                            
  method is_app_call = match tgt with AppTarget _ -> true | _ -> false

  method is_in_application_call =
    match tgt with
    | StaticStubTarget _ -> true
    | AppTarget _ -> true
    | InlinedAppTarget _ -> true
    | WrappedTarget _ -> true
    | _ -> false
                                                                
  method is_dll_call =
    match tgt with
    | StubTarget fs | StaticStubTarget (_,fs) ->
       (match fs with DllFunction _  -> true | _ -> false)
    | _ -> false

  method is_static_dll_call =
    match tgt with
    | StaticStubTarget (_, fs) ->
       (match fs with DllFunction _ -> true | _ -> false)
    | _ -> false

  method is_wrapped_dll_call =
    match tgt with
    | WrappedTarget (_, _, tt, _) ->
       (match tt with
        | StubTarget fs | StaticStubTarget (_, fs) -> true
        | _ -> false)
    | _ -> false

  method has_dll_target = self#is_dll_call || self#is_wrapped_dll_call
         
  method is_inlined_call =
    match tgt with InlinedAppTarget _ -> true | _  -> false
                                                     
  method is_wrapped_call =
    match tgt with WrappedTarget _ -> true | _ -> false
                                                 
  method is_wrapped_app_call =
    match tgt with
    | WrappedTarget (_, _, AppTarget _, _) -> true
    | _ -> false
         
  method is_static_lib_call =
    match tgt with
    | StaticStubTarget (_, PckFunction _) -> true
    | _ -> false
         
  method is_jni_call =
    match tgt with
    | StubTarget (JniFunction _) -> true | _ -> false

  method is_indirect_call =
    match tgt with IndirectTarget _ -> true | _ -> false

  method is_virtual_call =
    match tgt with VirtualTarget _ -> true | _ -> false
         
  method is_unknown =
    match tgt with
    | UnknownTarget -> true
    | IndirectTarget (_,[]) -> true
    | _ -> false

  (* categories supported:
   * - so
   * - dll
   * - app
   * - jni
   * - arg (indirect call on stack argument)
   * - arg-no-targets
   * - global
   * - global-no-targets
   * - unresolved
   * - dll-no-sum
   * - inlined
   * - static-dll
   * - static-lib
   * - app-wrapped
   * - dll-wrapped
   *)
  method is_call_category (cat:string) =
    let rec aux rtgt =
      match (rtgt,cat) with
      | (StubTarget (SOFunction _), "so") -> true
      | (StubTarget (DllFunction _), "dll") -> true
      | (AppTarget _, "app") -> true
      | (StubTarget (JniFunction _), "jni") -> true
      | (IndirectTarget (Some v,_), "arg") -> is_stack_parameter_term v
      | (IndirectTarget (Some v,[]), "arg-no-targets") ->
         is_stack_parameter_term v
      | (IndirectTarget (Some v,_), "global") ->
         is_global_parameter_term v
      | (IndirectTarget (Some v,[]), "global-no-targets") ->
         is_global_parameter_term v
      | (UnknownTarget, "unresolved") -> true
      | (IndirectTarget (_,[]), "unresolved") -> true
      | (StubTarget (DllFunction (dll,fname)), "dll-no-sum")
        | (StaticStubTarget (_, DllFunction (dll,fname)), "dll-no-sum") ->
         not (function_summary_library#has_dll_function dll fname)
      | (WrappedTarget (_,_,wtgt,_), "dll-no-sum") -> aux wtgt
      | (InlinedAppTarget _, "inlined") -> true
      | (StaticStubTarget (_,DllFunction _), "static-dll") -> true
      | (StaticStubTarget (_,PckFunction _), "static-lib") -> true
      | (WrappedTarget (_,_,AppTarget _,_), "app-wrapped") -> true
      | (WrappedTarget (_,_,StubTarget (DllFunction _),_), "dll-wrapped") -> true
      |  _ -> false  in
    aux tgt

  method write_xml (node:xml_element_int) =
    begin
      id#write_xml_call_target node tgt;
      id#write_xml_function_interface node fintf
    end

  method toPretty = call_target_to_pretty tgt
end

let mk_call_target_info = new call_target_info_t

let read_xml_call_target_info (node:xml_element_int) =
  new call_target_info_t
    (id#read_xml_function_interface node)
    default_function_semantics
    (id#read_xml_call_target node)
