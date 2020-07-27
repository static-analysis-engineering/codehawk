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
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHApiParameter
open BCHBasicTypes
open BCHBTerm
open BCHCallTarget
open BCHDoubleword
open BCHFunctionApi
open BCHFunctionSemantics
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHVariableType

class call_target_info_t
        (api:function_api_t)
        (sem:function_semantics_t)
        (tgt:call_target_t):call_target_info_int =
object (self)

  method get_name = api.fapi_name
                  
  method get_target = tgt
                    
  method get_app_address =
    match tgt with
    | AppTarget a -> a
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Call target is not an application target: " ;
                      call_target_to_pretty tgt ]))
      
  method get_wrapped_app_address =
    match tgt with
    | WrappedTarget (_, _, AppTarget a, _) -> a
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Call target is not a wrapped application target: " ;
                      call_target_to_pretty tgt ]))

  method get_signature = api

  method get_parameters = api.fapi_parameters
                       
  method get_returntype = api.fapi_returntype
                        
  method get_stack_adjustment = api.fapi_stack_adjustment                        
                        
  method get_semantics = sem
                       
  method get_jni_index =
    match api.fapi_jni_index with
    | Some i -> i
    | _ ->
       begin
	 ch_error_log#add
           "invocation error" 
	   (LBLOCK [ STR "function_summary#get_jni_index" ]) ;
	 raise (BCH_failure
                  (LBLOCK [ STR "Call target is not a jni target: " ;
                            call_target_to_pretty tgt ] ))
       end

  method get_preconditions = sem.fsem_pre
                                         
  method get_postconditions = sem.fsem_post
                            
  method get_errorpostconditions = sem.fsem_errorpost
                                 
  method get_sideeffects = sem.fsem_sideeffects
                         
  method get_io_actions = sem.fsem_io_actions

  method get_enums_referenced =
    let l = ref [] in
    let add s = if List.mem s !l then () else l := s :: !l in
    let _ = List.iter (fun p -> 
      match p with PreEnum (_,s,_) -> add s | _ -> ()) self#get_preconditions in
    let _ = List.iter (fun p ->      
      match p with PostEnum (_,s) -> add s | _ -> ()) self#get_postconditions in
    !l

  method get_enum_type (par:api_parameter_t) =
    List.fold_left (fun acc pre ->
        match acc with
        | Some _ -> acc
        | _ ->
	   match pre with
	   | PreEnum (ArgValue p,s,flags) ->
	      if api_parameter_compare p par = 0 then
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

  method is_signature_valid = not api.fapi_inferred
                            
  method is_semantics_valid = not api.fapi_inferred
                            
  method is_app_call = match tgt with AppTarget _ -> true | _ -> false
                                                                
  method is_dll_call =
    match tgt with
    | StubTarget fs | StaticStubTarget (_,fs) ->
       (match fs with DllFunction _  -> true | _ -> false)
    | _ -> false
         
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
    | StubTarget (JniFunction _) -> true
    | _ -> false
         
  method is_unknown = match tgt with UnknownTarget -> true | _ -> false
                     
  method is_call_category (cat:string) =
    let rec aux rtgt =
      match (rtgt,cat) with
      | (StubTarget (DllFunction _), "dll") -> true
      | (AppTarget _, "app") -> true
      | (StubTarget (JniFunction _), "jni") -> true
      | (IndirectTarget (v,_), "arg") -> is_stack_parameter_term v
      | (IndirectTarget (v,[]), "arg-no-targets") -> is_stack_parameter_term v
      | (IndirectTarget (v,_), "global") -> is_global_parameter_term v
      | (IndirectTarget (v,[]), "global-no-targets") -> is_global_parameter_term v
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

  method write_xml (node:xml_element_int) = ()
end

let mk_call_target_info = new call_target_info_t

let read_xml_call_target_info (node:xml_element_int) =
  new call_target_info_t
      (default_function_api "default" [])
      default_function_semantics
      UnknownTarget

