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
open CHLanguage

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode

(* jchpre *)
open JCHPreAPI

module MethodInfoCollections = CHCollections.Make (
  struct
    type t = method_info_int
    let compare m1 m2 = m1#get_class_method_signature#compare m2#get_class_method_signature
    let toPretty m = m#get_class_method_signature#toPretty
  end)

module ClassNameCollections = CHCollections.Make (
  struct
    type t = class_name_int
    let compare n1 n2 = n1#compare n2
    let toPretty n = n#toPretty
  end)

    

class method_target_t =
object (self)

  val targets = new MethodInfoCollections.set_t
  val indirect_targets = new MethodInfoCollections.set_t 

  method clone = {< >}

  method assert_invocation_objects (cnlist: class_name_int list) =
    let tgts = targets#toList in
    let new_tgts = List.filter 
      (fun tgt -> List.exists
	(fun cn -> tgt#get_class_method_signature#class_name#equal cn) cnlist) tgts in
    let _ = targets#removeList tgts in
    let _ = chlog#add "restrict method targets"
                      (LBLOCK [ pretty_print_list cnlist (fun cn -> cn#toPretty) "[" "; " "]" ]) in
    targets#addList new_tgts

  method add_target (m:method_info_int) = targets#add m

  method add_indirect_target (m:method_info_int) = indirect_targets#add m
    
  method get_all_targets = targets#toList
    
  method get_valid_targets = 
    List.filter (fun m -> 
      match m#get_implementation with ConcreteMethod _ | Stub _ -> true | _ -> false)
      targets#toList
      
  method get_indirect_targets = indirect_targets#toList
    
  method get_stubs = 
    targets#fold (fun a v -> match v#get_implementation with Stub x -> x :: a | _ -> a) []
      
  method get_procs =
    targets#fold (fun a v ->
      match v#get_implementation with ConcreteMethod m -> v#get_procname :: a | _ -> a) []
      
  method is_top = 
    (List.length self#get_valid_targets) = 0 ||
    List.exists 
    (fun m -> 
      match m#get_implementation with 
      | UntranslatedConcreteMethod _ 
      | NativeMethod _ 
      | MissingMethod _ 
      | ExcludedMethod _ -> true
      | Stub s -> false (* not (s#is_final || s#is_static)  *)
      | _ -> false) targets#toList

  method write_xml (node:xml_element_int) =
    begin
      node#appendChildren (List.map (fun tgt ->
	let tag = match tgt#get_implementation with
	  | UntranslatedConcreteMethod _ -> "untranslated"
	  | NativeMethod _ -> "native"
	  | MissingMethod _ -> "missing"
	  | ExcludedMethod _ -> "excluded"
	  | Stub _ -> "stub"
	  | AbstractMethod _ -> "abstract"
	  | InterfaceInheritedMethod _ -> "interface-inherited"
	  | ConcreteMethod _ -> "concrete" in
	let tNode = xmlElement "tgt" in
	begin 
	  tNode#setIntAttribute "cms-ix" tgt#get_index ;
	  tNode#setAttribute "tag" tag ;
	  tNode
	end) self#get_all_targets) ;
      node#setIntAttribute "count" targets#size ;
      node#setIntAttribute "valid-count" (List.length self#get_valid_targets)
    end
    
  method get_reason_for_top =
    let count f = targets#fold (fun c t -> if f t#get_implementation then c+1 else c) 0 in
    if self#is_top then
      if targets#size = 0 then STR "zero targets"
      else 
	let native_c = count (fun m -> match m with NativeMethod _ -> true | _ -> false) in
	let missing_c = count (fun m -> match m with MissingMethod _ -> true | _ -> false) in
	let failed_c = count (fun m -> match m with UntranslatedConcreteMethod _ -> true | _ -> false) in
	let abstract_c = count (fun m -> match m with AbstractMethod _ -> true | _ -> false) in
	let excluded_c = count (fun m -> match m with ExcludedMethod _ -> true | _ -> false) in
	let native_s = 
	  if native_c > 0 then 
	    LBLOCK [ pp_quantity native_c "native target" "native targets" ; STR "; " ]
          else STR "" in
	let missing_s =
	  if missing_c > 0 then
	    LBLOCK [ pp_quantity missing_c "missing target" "missing targets" ; STR "; " ]
          else STR "" in
	let excluded_s =
	  if excluded_c > 0 then
	    LBLOCK [ pp_quantity excluded_c "excluded target" "excluded targets" ; STR "; " ]
          else STR "" in
	let failed_s =
	  if failed_c > 0 then
	    LBLOCK [ pp_quantity failed_c "failure in translation" "failures in translation" ] 
	  else
	    STR "" in
	let abstract_s =
	  if abstract_c > 0 then
	    LBLOCK [ pp_quantity abstract_c "abstract target" "abstract targets" ; STR "; " ]
	  else
	    STR "" in
	if (List.length self#get_valid_targets) = 0 then
	  LBLOCK [ STR "zero valid targets (" ; abstract_s ; native_s ; missing_s ; failed_s ; STR ")" ]
	else
	  LBLOCK [ STR "existence of " ; native_s ; missing_s ; failed_s ; excluded_s ]
    else
      STR "not top"

  method toPretty = targets#toPretty

end

let make_method_target () = new method_target_t

class instruction_info_t
  ~(bcloc:bytecode_location_int)
    ~(opcode:opcode_t) 
    ~(is_modified:bool):instruction_info_int =
object (self:'a)

  val bcloc = bcloc
  val opcode = opcode
  val is_modified = is_modified
  val mutable field_target = None
  val mutable method_target = None
  val mutable declared_object_type = None
  val mutable actual_object_types = []

  method compare (other:'a) = bcloc#compare other#get_location

  method set_field_target (f:field_info_int) = field_target <- Some f

  method add_method_target (m:method_info_int) =
    match method_target with
    | Some t -> t#add_target m
    | _ ->
      let t = new method_target_t in
      begin t#add_target m ; method_target <- Some t end

  method add_indirect_method_target (m:method_info_int) =
    match method_target with
      Some t -> t#add_indirect_target m
    | _ ->
      let t = new method_target_t in 
      begin t#add_indirect_target m ; method_target <- Some t end

  method assert_invocation_objects (cnlist: class_name_int list) =
    if self#has_method_target then
      (self#get_method_target ())#assert_invocation_objects cnlist
    else
      raise (JCH_failure 
	       (LBLOCK [ self#toPretty ; STR " does not have a method target" ]))

  method get_location = bcloc
  method get_opcode = opcode

  method get_method_target ?(restrict_to =[]) () = 
    match method_target with 
	Some t -> 
	  begin
	    match restrict_to with
	      [] -> t
	    | _ ->
	      let tmp_target = (t#clone) in
	      begin tmp_target#assert_invocation_objects restrict_to ; tmp_target end
	  end 
      | _ ->
	if self#is_method_call then
	  let t = new method_target_t in begin method_target <- Some t ; t end
	else
	  raise (JCH_failure 
		   (LBLOCK [ STR "Instruction at " ; bcloc#toPretty ; 
			     STR " is not a method call; it does not have a method target "]))

  method may_throw_invocation_exceptions =
    if self#is_method_call then 
      if self#has_method_target then
	let target = self#get_method_target () in
	if target#is_top then
	  true
	else
	  let allTargets = target#get_all_targets in
	  if List.for_all (fun v -> 
	    match v#get_implementation with 
	      Stub _ -> true | _ -> false) allTargets then
	    let exnSet = new ClassNameCollections.set_t in
	    let _ = List.iter (fun tgt -> 
	      exnSet#addList tgt#get_exceptions) allTargets in
	    not exnSet#isEmpty
	  else
	    true
      else
	true
    else
      false

  method get_field_target = match field_target with Some t -> t | _ ->
    raise (JCH_failure (LBLOCK [ STR "Instruction at " ; bcloc#toPretty ;
				 STR " does not have a field target "]))

  method get_declared_object_type = match declared_object_type with Some t -> t | _ ->
    raise (JCH_failure (LBLOCK [ STR "Instruction at " ; bcloc#toPretty ;
				 STR " does not have a declared object type "]))

  method get_actual_object_types = actual_object_types

  method is_modified = is_modified
  method has_method_target = match method_target with Some _ -> true | _ -> false
  method has_field_target  = match field_target  with Some _ -> true | _ -> false

  method has_declared_object_type = 
    match declared_object_type with Some _ -> true | _ -> false

  method is_method_call = match opcode with
    |OpInvokeStatic _
     | OpInvokeSpecial _
     | OpInvokeVirtual _
     | OpInvokeInterface _
     | OpInvokeDynamic _ -> true
    | _ -> false

  method is_method_call_static    = 
    match opcode with OpInvokeStatic _ -> true | _ -> false

  method is_method_call_special   = 
    match opcode with OpInvokeSpecial _ -> true | _ -> false

  method is_method_call_virtual   =
    match opcode with OpInvokeVirtual _ -> true | _ -> false

  method is_method_call_interface = 
    match opcode with OpInvokeInterface _ -> true | _ -> false

  method is_field_access = match opcode with
      OpGetStatic _ | OpPutStatic _ | OpGetField _ | OpPutField _ -> true | _ -> false

  method is_field_read  = 
    match opcode with OpGetStatic _ | OpGetField _ -> true | _ -> false

  method is_field_write = 
    match opcode with OpPutStatic _ | OpPutField _ -> true | _ -> false

  method is_field_get_static = 
    match opcode with OpGetStatic _ -> true | _ -> false

  method is_field_get_field  = 
    match opcode with OpGetField _ -> true | _ -> false

  method is_field_put_static = 
    match opcode with OpPutStatic _ -> true | _ -> false

  method is_field_put_field  = 
    match opcode with OpPutField _ -> true | _ -> false

  method toPretty = 
    let caller_cms = bcloc#get_class_method_signature in
    let caller_name = caller_cms#method_signature#name in
    if self#is_method_call then
      let (target_pretty,is_top,reason) =
	if self#has_method_target then
	  let tgt = self#get_method_target () in
	  let tgt_pretty = match tgt#get_all_targets with
	      [] -> STR "zero targets found"
	    | _ -> 
	      match (List.length tgt#get_procs, List.length tgt#get_stubs) with
		(0,0) -> STR "no procs, no stubs"
	      | (0,s) -> LBLOCK [ pp_quantity s "stub" "stubs" ]
	      | (p,0) -> LBLOCK [ pp_quantity p "proc" "procs" ]
	      | (p,s) -> LBLOCK [ pp_quantity p "proc" "procs" ; STR ", " ; 
				  pp_quantity s "stub" "stubs" ] in
	  (tgt_pretty, tgt#is_top, tgt#get_reason_for_top)
	else
	  (STR " ", true, STR "no target") in
      LBLOCK [ caller_cms#toPretty ; STR " at pc = " ; INT bcloc#i ; STR " " ; 
	       STR self#toString ; STR " (" ; target_pretty ; STR ")" ;
	       if is_top then LBLOCK [ STR " TOP: " ; reason ] else STR "" ]
    else if self#is_field_access then
      let target = if self#has_field_target then 
	  self#get_field_target#toPretty else STR "" in
      LBLOCK [ STR caller_name ; STR ": " ; STR self#toString ; 
	       STR " (" ; target ; STR ")" ]
    else
      STR self#toString
	
  method toString = opcode_to_string opcode

end

let make_instruction_info 
    (bcloc:bytecode_location_int) ?(is_modified=false) (opcode:opcode_t) =
  new instruction_info_t ~bcloc:bcloc ~opcode:opcode ~is_modified:is_modified
