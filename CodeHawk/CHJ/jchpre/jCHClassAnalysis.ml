(* =============================================================================
   CodeHawk Java Analyzer
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
open CHCommon
open CHLanguage
open CHSymbolicSets
open CHSymbolicSetsDomainNoArrays
open CHAtlas
open CHIterator

(* chutil *)
open CHLogger
open CHAnalysisSetup
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHTranslateToCHIF

(* jchpre *)
open JCHIFSemantics
open JCHBytecodeLocation
open JCHPreAPI
(* open JCHInstanceTransformer *)

open JCHMethodInfo
open JCHApplication
open JCHFunctionSummaryLibrary
open JCHFunctionSummary
open JCHSignatureBindings

module LF = CHOnlineCodeSet.LanguageFactory

let class_domain_name = "class-domain"
let type_domain_name  = "type-domain"

let missing_classes = ref []
let reset_missing_classes () = missing_classes := []
let add_missing_class cn = if List.exists (fun c -> c#equal cn) !missing_classes then () else
    missing_classes := cn :: !missing_classes

let class_result:(int, class_name_int list) Hashtbl.t = Hashtbl.create 15
let type_result :(int, class_name_int list) Hashtbl.t = Hashtbl.create 15

let reset_table table = Hashtbl.clear table

let analyze_filter m =
  m#has_bytecode && not m#has_jsr_instructions && not m#need_not_be_analyzed

let make_cn_symbol cn = new symbol_t ~seqnr:cn#index cn#name

let make_class_name (s:string) = common_dictionary#make_class_name s

let has_virtual_calls (bc:bytecode_int) =
  let result = ref false in
  begin
    Array.iter
      (fun opc ->
        match opc with
        | OpInvokeInterface _ | OpInvokeVirtual _ -> result := true
        | _ -> ()) bc#get_code#opcodes ;
    !result
  end
let op_args_to_pretty op_args =
  pretty_print_list op_args 
    (fun (name, arg, mode) ->
      LBLOCK [STR name; STR ":"; arg_mode_to_pretty mode; STR " => "; arg#toPretty]
    ) "(" ", " ")"


let get_arg args name =
  try
    let (_,v,_) = List.find (fun (n,v,_) -> n = name) args in v
  with
    Not_found ->
      raise (JCH_failure (LBLOCK [ STR "Unable to find argument " ; STR name ; NL ;
				   op_args_to_pretty args ]))

let has_arg args name = List.exists (fun (n,_,_) -> n = name) args

let get_class_from_symbol (sym:symbol_t) =
  try
    retrieve_cn sym#getSeqNumber
  with
    JCH_failure p ->
      raise (JCH_failure (LBLOCK [ sym#toPretty ; STR ": " ; p ]))

let get_class_names_from_set s = 
  match s#toSymbolicSet#getSymbols with 
    SET s -> List.map get_class_from_symbol s#toList
  | _ -> raise (JCH_failure (STR "internal error in get_symbol"))

let add_result pc opcode opArgs invariant domain_name table = 
  match opcode with
    OpInvokeInterface _
  | OpInvokeVirtual _ ->
     let tgtObject = get_arg opArgs "arg0" in
     let inv = ((invariant#getDomain domain_name)#observer#getNonRelationalVariableObserver) tgtObject in
     if inv#isTop then
       ()
     else
       begin
	 match get_class_names_from_set inv with
	   [] -> ()
	 | l -> Hashtbl.add table pc l
       end
  | _ -> ()

let add_class_result (cmsix:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
  let cms = retrieve_cms cmsix in
  let mInfo = app#get_method cms in
  try
    let opcode = mInfo#get_opcode pc in
    add_result pc opcode args inv class_domain_name class_result
  with
    CHFailure p ->
      begin
	ch_error_log#add "add result" (LBLOCK [ cms#toPretty ; STR "  " ; p ]) ;
	raise (CHFailure p) 
      end

let add_type_result (cmsix:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
  let cms = retrieve_cms cmsix in
  let mInfo = app#get_method cms in
  let opcode = mInfo#get_opcode pc in
  add_result pc opcode args inv type_domain_name type_result

let table_to_pretty table = 
  Hashtbl.fold (fun k v a ->
    LBLOCK [ a ; NL ; fixed_length_pretty (INT k) 4 ; 
	     pretty_print_list v (fun cn -> cn#toPretty) "[" "; " "]" ] ) table (STR "")

let get_local_variable_table_type (cmsix:int) (pc:int) (reg:int) =
  let cms = retrieve_cms cmsix in
  let m = app#get_method cms in
  if m#has_local_variable_type reg pc then
    Some (m#get_local_variable_type reg pc)
  else
    None

let is_reference_type (t:java_basic_type_t) = match t with Object -> true | _ -> false

let is_reference_type_val (t:value_type_t) = match t with 
  | TBasic b -> is_reference_type b
  | _ -> true

let app_has_class cn = if app#has_class cn then true else begin add_missing_class cn ; false end

let is_final_class_type (t:value_type_t) = match t with
  | TObject (TClass cn) -> if app_has_class cn then (app#get_class cn)#is_final else false
  | _ -> false

let is_class_type (t:value_type_t) = match t with
  | TObject (TClass cn) -> if app_has_class cn then not (app#get_class cn)#is_interface else false
  | _ -> false

let is_class_or_interface_type (t:value_type_t) = match t with
  | TObject (TClass cn) -> app_has_class cn
  | _ -> false

let get_class_type (t:value_type_t) = match t with 
  | TObject (TClass cn) -> cn
  | _ -> raise (JCH_failure (STR "Internal error in get_field_type"))

let is_return_type_final (ms:method_signature_int) = 
  match ms#descriptor#return_value with
  | Some (TObject (TClass cn)) -> if app_has_class cn then (app#get_class cn)#is_final else false
  | _ -> false

let is_return_type_class (ms:method_signature_int) =
  match ms#descriptor#return_value with
  | Some (TObject (TClass cn)) ->
     if app_has_class cn then not (app#get_class cn)#is_interface else false
  | _ -> false

let get_return_type (ms:method_signature_int) =
  match ms#descriptor#return_value with
  | Some (TObject (TClass class_name)) -> class_name
  | _ -> raise (JCH_failure (STR "internal failure in get_return_type"))

let is_object_final_class_type (ot:object_type_t) =
  match ot with
  | TClass cn -> if app_has_class cn then (app#get_class cn)#is_final else false
  | _ -> false

let is_object_class_type (ot:object_type_t) =
  match ot with
  | TClass cn -> if app_has_class cn then not (app#get_class cn)#is_interface else false
  | _ -> false

let get_object_class_type (ot:object_type_t) =
  match ot with
  | TClass cn -> cn
  | _ ->
     raise (JCH_failure (STR "Internal failure in get_object_class_type"))

let assign_register
      (isfinal:bool) (cmsix:int) (pc:int) (reg:int) (args:op_arg_t list) (inv:atlas_t) 
      (domain_name:string) =
  let default = ASSIGN_SYM (get_arg args "dst1", SYM_VAR (get_arg args "src1")) in
  let table_assign vt = 
    let cn = get_class_type vt in
    begin
      (if app#has_class cn then () else add_missing_class cn) ;
      ASSIGN_SYM (get_arg args "dst1", SYM (make_cn_symbol (get_class_type vt))) 
    end in
  let judge_assign vt sym =
    match sym with 
    | None -> table_assign vt
    | Some cn ->
       if cn#equal (get_class_type vt) then 
	 default
       else
	 if cn#name = "java.lang.Object" then
	   table_assign vt
	 else if (get_class_type vt)#name = "java.lang.Object" then
	   default
	 else
	   begin
	     chlog#add
               "competing types" 
	       (LBLOCK [ (retrieve_cms cmsix)#toPretty ; STR " at pc = " ; INT pc ; 
			 STR ": src: " ; cn#toPretty ; STR "; var type: " ;
                         (get_class_type vt)#toPretty ]) ; 
	     default
	   end in
  let srcObject= get_arg args "src1" in
  let srcInv = ((inv#getDomain domain_name)#observer#getNonRelationalVariableObserver) srcObject in
  let srcSym = if srcInv#isTop then
      None
    else
      match get_class_names_from_set srcInv with
      | [] -> None
      | [ cn ] -> Some cn
      | _ -> None in
  match get_local_variable_table_type cmsix pc reg with
  | Some vt ->
     if isfinal then
       if is_final_class_type vt then table_assign vt else default
     else if is_class_type vt then judge_assign vt srcSym
     else default
  | _ -> default
    
let has_this_as_return_value (cmsix:int) (pc:int) ms =
  match ms#descriptor#return_value with
  | Some (TObject (TClass _)) ->
     let loc = get_bytecode_location cmsix pc in
     if app#has_instruction loc then
       let instrInfo = app#get_instruction loc in
       if instrInfo#has_method_target then
	 let tgt = instrInfo#get_method_target () in
	 if tgt#is_top then
	   false
	 else
	   let mtargets = tgt#get_all_targets in
	   match mtargets with
	   | [ m ] when m#is_stubbed ->
	      let summary =
                function_summary_library#get_method_summary
                  m#get_class_method_signature in
	      let post = summary#get_post in
	      let errorPost = summary#get_error_post in
	      begin
		match (post,errorPost) with
		| (h::_, []) ->
		   begin
		     match h#get_predicate with
		     | PostRelationalExpr (JEquals, JLocalVar (-1), JLocalVar 0) -> true
		     | _ -> false
		   end
		| _ -> false
	      end
	   | _ -> false
       else
	 false
     else
       false
  | _ -> false
		
let class_analysis_semantics (cmsix:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
  let cms = retrieve_cms cmsix in
  let mInfo = app#get_method cms in
  let get_known_target_return_type cn ms =
    let calleecms = make_cms cn ms in
    if app#has_method calleecms then
      let callee = app#get_method calleecms in
      if callee#is_stubbed then
        let summary = function_summary_library#get_method_summary calleecms in
        let post = summary#get_post in
        let errorPost = summary#get_error_post  in
        match (post,errorPost) with
        | (h::_, []) ->
           begin
             match h#get_predicate with
             | PostRelationalExpr (JEquals, JLocalVar (-1), JLocalVar 0) -> Some cn
             | PostObjectClass cn -> Some cn
             | _ -> None
           end
        | _ -> None
      else
        None
    else
      None in
  let get_unknown_target_return_type cn ms =
    if app#has_class cn then
      let cInfo = app#get_class cn in
      if cInfo#is_final then
        get_known_target_return_type cn ms
      else
        let tgtObject = get_arg args "arg0" in
        let tgtInv = ((inv#getDomain class_domain_name)#observer#getNonRelationalVariableObserver) tgtObject in
        if tgtInv#isTop then
          None
        else
          match get_class_names_from_set tgtInv with
          | [] -> None
          | [ cn ] -> get_known_target_return_type cn ms
          | _ -> None
    else
      None in
  let abstract_vars () =
    ABSTRACT_VARS 
      (List.map (fun (_,v,_) -> v) 
		(List.filter (fun (_,_,m) ->
                     match m with READ -> false | _ -> true) args)) in
  let opcode = mInfo#get_opcode pc in
                        
  try
    match opcode with
    | OpNew class_name -> 
	begin
	  (if app#has_class class_name then () else add_missing_class class_name) ;
	  ASSIGN_SYM (get_arg args "ref", SYM (make_cn_symbol class_name))
	end
    | OpDup -> ASSIGN_SYM (get_arg args "dst1", SYM_VAR (get_arg args "src1"))
    | OpStringConst s -> 
      ASSIGN_SYM (get_arg args "ref", SYM (make_cn_symbol (make_class_name "java.lang.String")))
    | OpClassConst _ ->
      ASSIGN_SYM (get_arg args "ref", SYM (make_cn_symbol (make_class_name "java.lang.Class")))
    | OpCheckCast ot when is_object_final_class_type ot ->
      ASSIGN_SYM (get_arg args "dst1", SYM (make_cn_symbol (get_object_class_type ot)))
    | OpCheckCast _ ->
      ASSIGN_SYM (get_arg args "dst1", SYM_VAR (get_arg args "src1"))
    | OpStore (t, n) when is_reference_type t -> 
      ASSIGN_SYM (get_arg args "dst1", SYM_VAR (get_arg args "src1"))
    | OpLoad (t, n) when is_reference_type t ->
      assign_register true cmsix pc n args inv class_domain_name
    | OpGetField (_,fs)
    | OpGetStatic (_,fs) when is_final_class_type fs#descriptor ->
      ASSIGN_SYM (get_arg args "val", SYM (make_cn_symbol (get_class_type fs#descriptor)))
 (*   | OpPutField (_,fs) 
      | OpPutStatic (_,fs) when is_reference_type_val fs#descriptor ->
       ASSIGN_SYM (get_arg args "field", SYM_VAR (get_arg args "val"))
    | OpGetField (_,fs)
      | OpGetStatic (_,fs) when is_reference_type_val fs#descriptor ->
       ASSIGN_SYM (get_arg args "val", SYM_VAR (get_arg args "field")) *)
    | OpInvokeSpecial (_, ms)
    | OpInvokeStatic (_, ms)
    | OpInvokeVirtual (_, ms)
    | OpInvokeInterface (_, ms) when is_return_type_final ms ->
       ASSIGN_SYM (get_arg args "return", SYM (make_cn_symbol (get_return_type ms)))
    | OpInvokeSpecial (cn,ms)
      | OpInvokeStatic (cn,ms) ->
       begin
         match get_known_target_return_type cn ms with
         | Some tgtcn ->
            let _ = chlog#add "propagate known return"
                              (LBLOCK [ cms#toPretty ;
                                        STR ": pc = " ; INT pc ; STR  ": " ;  tgtcn#toPretty ]) in
            ASSIGN_SYM (get_arg args "return", SYM (make_cn_symbol tgtcn))
         | _ -> abstract_vars ()
       end
    | OpInvokeVirtual (TClass cn,ms)
      | OpInvokeInterface (cn,ms) ->
       begin
         match get_unknown_target_return_type cn ms with
         | Some tgtcn ->
            let _ = chlog#add "propagate unknown target return"
                              (LBLOCK [ cms#toPretty ;
                                        STR ": pc = " ; INT pc ; STR  ": " ;  tgtcn#toPretty ]) in
            ASSIGN_SYM (get_arg args "return", SYM (make_cn_symbol tgtcn))
         | _ -> abstract_vars ()
       end
    | _ ->
      ABSTRACT_VARS 
	(List.map (fun (_,v,_) -> v) 
		  (List.filter (fun (_,_,m) -> match m with READ -> false | _ -> true) args))
  with
    JCH_failure p ->
      raise (JCH_failure (LBLOCK [ STR "opcode: " ; opcode_to_pretty opcode ; STR ": " ; p ]))

let type_analysis_semantics (inverted:bool) (cmsix:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
  let cms = retrieve_cms cmsix in
  let mInfo = app#get_method cms  in
  let opcode = mInfo#get_opcode pc in
  let default =
    (ABSTRACT_VARS 
       (List.map (fun (_,v,_) -> v) 
		 (List.filter (fun (_,_,m) -> match m with READ -> false | _ -> true) args))) in
  try
    match opcode with
      OpNew class_name -> 
	begin
	  (if app#has_class class_name then () else add_missing_class class_name) ;
	  ASSIGN_SYM (get_arg args "ref", SYM (make_cn_symbol class_name))
	end
    | OpDup -> ASSIGN_SYM (get_arg args "dst1", SYM_VAR (get_arg args "src1"))
    | OpStringConst s -> 
      ASSIGN_SYM (get_arg args "ref", SYM (make_cn_symbol (make_class_name "java.lang.String")))
    | OpClassConst _ ->
      ASSIGN_SYM (get_arg args "ref", SYM (make_cn_symbol (make_class_name "java.lang.Class")))
    | OpCheckCast ot when is_object_class_type ot ->
      ASSIGN_SYM (get_arg args "dst1", SYM (make_cn_symbol (get_object_class_type ot)))
    | OpCheckCast _ ->
      ASSIGN_SYM (get_arg args "dst1", SYM_VAR (get_arg args "src1"))
    | OpStore (t, _) when is_reference_type t -> 
      ASSIGN_SYM (get_arg args "dst1", SYM_VAR (get_arg args "src1"))
    | OpLoad (t, n) when is_reference_type t ->
      assign_register false cmsix pc n args inv type_domain_name
    | OpGetField (_,fs)
    | OpGetStatic (_,fs) when is_class_type fs#descriptor ->
      ASSIGN_SYM (get_arg args "val", SYM (make_cn_symbol (get_class_type fs#descriptor)))
    | OpIfEq _ 
    | OpIfNe _ when has_arg args "srcvar" -> 
      let prevPc =  mInfo#get_previous_bytecode_offset pc in
      begin
	match mInfo#get_opcode prevPc with
	  OpInstanceOf (TClass cn) ->
	  ASSIGN_SYM (get_arg args "srcvar", SYM (make_cn_symbol cn))
	| _ -> default 
      end
    (*  | OpPutField (_,fs) 
      | OpPutStatic (_,fs) when is_reference_type_val fs#descriptor ->
      ASSIGN_SYM (get_arg args "field", SYM_VAR (get_arg args "val"))
      | OpGetField (_,fs)
      | OpGetStatic (_,fs) when is_reference_type_val fs#descriptor ->
      ASSIGN_SYM (get_arg args "val", SYM_VAR (get_arg args "field"))    *)
    | OpInvokeSpecial (_, ms)
    | OpInvokeStatic (_, ms)
    | OpInvokeVirtual (_, ms)
    | OpInvokeInterface (_, ms) when is_return_type_class ms ->
      ASSIGN_SYM (get_arg args "return", SYM (make_cn_symbol (get_return_type ms)))
    | _ -> default
  with
    JCH_failure p ->
      raise (JCH_failure (LBLOCK [ STR "opcode: " ; opcode_to_pretty opcode ; STR ": " ; p ]))
    

let initialize_bindings signature_bindings type_predicate =
  List.fold_left (fun a (v,ty) ->
    if type_predicate ty then
      (ASSIGN_SYM (v, SYM (make_cn_symbol (get_class_type ty)))) :: a
    else
      a) [] signature_bindings#get_ref_argument_types

let initialize_class_bindings signature_bindings =
  initialize_bindings signature_bindings is_final_class_type

let initialize_type_bindings signature_bindings =
  initialize_bindings signature_bindings is_class_type

class class_i_semantics_t:j_semantics_int =
object
  method stable _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = 
    add_class_result procId pc args inv
  method propagate_fwd _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    inv#analyzeFwd (class_analysis_semantics procId pc args inv)
  method propagate_bwd _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    inv#analyzeBwd (class_analysis_semantics procId pc args inv)
end

let class_i_semantics = new class_i_semantics_t

class class_init_semantics_t signature_bindings:j_semantics_int =
object (self:_)
  val initCode = CODE (new symbol_t "init", LF.mkCode (initialize_class_bindings signature_bindings)) 
  method stable _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = ()
  method propagate_fwd _ (iterator:iterator_t) (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    iterator#runFwd ~domains:[class_domain_name] ~atlas:inv initCode
  method propagate_bwd _ (iterator:iterator_t) (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    iterator#runBwd ~domains:[class_domain_name] ~atlas:inv initCode
end 

class class_opsemantics_t (init_semantics:j_semantics_int):j_opsemantics_int =
object
  method i_semantics = class_i_semantics
  method ii_semantics = class_i_semantics
  method e_semantics = j_nop_semantics
  method init_semantics = init_semantics
  method exit_semantics = j_nop_semantics
  method exn_exit_semantics = j_nop_semantics
end

class type_i_semantics_t:j_semantics_int =
object
  method stable _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = 
    add_type_result procId pc args inv
  method propagate_fwd _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    inv#analyzeFwd (type_analysis_semantics false procId pc args inv)
  method propagate_bwd _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    inv#analyzeBwd (type_analysis_semantics false procId pc args inv)
end

let type_i_semantics = new type_i_semantics_t

class type_ii_semantics_t:j_semantics_int =
object
  method stable _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = 
    add_type_result procId pc args inv
  method propagate_fwd _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    inv#analyzeFwd (type_analysis_semantics true procId pc args inv)
  method propagate_bwd _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    inv#analyzeBwd (type_analysis_semantics true procId pc args inv)
end

let type_ii_semantics = new type_ii_semantics_t

class type_init_semantics_t signature_bindings:j_semantics_int =
object
  val initCode = CODE (new symbol_t "init", LF.mkCode (initialize_type_bindings signature_bindings)) 
  method stable _ _ (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = ()
  method propagate_fwd _ (iterator:iterator_t) (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    iterator#runFwd ~domains:[type_domain_name] ~atlas:inv initCode
  method propagate_bwd _ (iterator:iterator_t) (procId:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) =
    iterator#runBwd ~domains:[type_domain_name] ~atlas:inv initCode
end

let get_type_init_semantics signature_bindings = new type_init_semantics_t signature_bindings

class type_opsemantics_t (init_semantics:j_semantics_int):j_opsemantics_int =
object
  method i_semantics = type_i_semantics
  method ii_semantics = type_ii_semantics
  method e_semantics = j_nop_semantics
  method init_semantics = init_semantics
  method exit_semantics = j_nop_semantics
  method exn_exit_semantics = j_nop_semantics
end

let analyze_method_for_classes (system:system_int) (procname:symbol_t) signature is_static =
  let _ = reset_table class_result in
  let proc = system#getProcedure procname in
  let analysisSetup = mk_analysis_setup () in
  let signatureBindings = get_signature_bindings signature proc#getBindings is_static in
  let initSemantics = new class_init_semantics_t signatureBindings in
  let classSemantics = new class_opsemantics_t initSemantics in
  let opsemantics = opsemantics system procname classSemantics in
  begin
    analysisSetup#addDomain class_domain_name (new symbolic_sets_domain_no_arrays_t) ;
    analysisSetup#setOpSemantics opsemantics ;
    analysisSetup#analyze_procedure system proc 
  end

let analyze_method_for_types (system:system_int) (procname:symbol_t) signature is_static =
  let _ = reset_table type_result in
  let proc = system#getProcedure procname in
  let analysisSetup = mk_analysis_setup () in
  let signatureBindings = get_signature_bindings signature proc#getBindings is_static in
  let initSemantics = get_type_init_semantics signatureBindings in
  let typeSemantics = new type_opsemantics_t initSemantics in
  let opsemantics = opsemantics system procname typeSemantics in
  begin
    analysisSetup#addDomain type_domain_name (new symbolic_sets_domain_no_arrays_t) ;
    analysisSetup#setOpSemantics opsemantics ;
    analysisSetup#analyze_procedure system proc 
  end
  

let analyze_method_for_classes_and_types (m:method_info_int) =
  let _ = reset_table type_result in
  let _ = reset_table class_result in
  let _ = reset_missing_classes () in
  let cms = m#get_class_method_signature in
  if analyze_filter m && has_virtual_calls m#get_bytecode then
    try
      let procname = make_procname cms#index in
      let system = LF.mkSystem (new symbol_t "_") in
      let exnInfosFn = defaultExnInfoFn m#get_method in
      begin
	(try
	   translate_method
	     ~proc_filter:(fun _ -> true)
	     ~simplify:false
	     ~transform:false
	     ~java_method:m#get_method
	     ~code_set:system
	     ~exn_infos_fn:exnInfosFn
	     () 
	 with 
	   JCH_failure p ->
	   begin
	     ch_error_log#add "failure"
			      (LBLOCK [ STR "failure in translate method " ; cms#toPretty ; STR ": " ; p ]) ;
	     raise (JCH_failure (LBLOCK [ STR "failure in translate method: " ; p ]))
	   end);
	
	(try
	   analyze_method_for_classes system procname cms#method_signature m#is_static ; 
	   (* transform_for_instanceof m (system#getProcedure procname) ; *)
	   analyze_method_for_types system procname  cms#method_signature m#is_static ; 
	 with
	   JCH_failure p ->
	   raise (JCH_failure (LBLOCK [ p ; NL ; (system#getProcedure procname)#toPretty ]))) ;
	(!missing_classes, class_result, type_result)
      end
    with
    |  CHCommon.CHFailure p
    | JCH_failure p ->
       begin
	 ch_error_log#add "analysis failure" (LBLOCK [ cms#toPretty ; STR ": " ; p ]);
	 (!missing_classes,class_result, type_result)
       end
  else
    (!missing_classes,class_result, type_result)
