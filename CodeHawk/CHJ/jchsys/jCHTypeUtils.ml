(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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

open Big_int_Z

(* chlib *)
open CHIntervals
open CHNumerical
open CHLanguage
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

let dbg = ref false

let get_object_vt () = TObject (TClass (make_cn "java.lang.Object"))
let get_string_vt () = TObject (TClass (make_cn "java.lang.String" ))
let get_throwable_vt () = TObject (TClass (make_cn "java.lang.Throwable"))

let bool_interval = 
  let min = numerical_zero in
  let max = numerical_one in
  mkInterval min max

let byte_interval = 
  let min = new numerical_t (big_int_of_int (-128)) in
  let max = new numerical_t (big_int_of_int 127) in
  mkInterval min max
  
let short_interval = 
  let min = new numerical_t (big_int_of_int (-32768)) in
  let max = new numerical_t (big_int_of_int 32767) in
  mkInterval min max
  
let char_interval = 
  let min = numerical_zero in
  let max = new numerical_t (big_int_of_int 65535) in
  mkInterval min max
  
let integer_interval = 
  let min = new numerical_t (big_int_of_int (-2147483648)) in
  let max = new numerical_t (big_int_of_int 2147483647) in
  mkInterval min max
  
let long_interval = 
  let min = new numerical_t (big_int_of_string "-9223372036854775808") in
  let max = new numerical_t (big_int_of_string "9223372036854775807") in
  mkInterval min max

let length_interval = 
  let min = numerical_zero in
  let max = new numerical_t (big_int_of_int 2147483647) in
  mkInterval min max

let loop_counter_interval = 
  let min = CHBounds.bound_of_num numerical_zero in 
  new interval_t min CHBounds.plus_inf_bound
  
let get_interval_from_basic_type bt = 
  match bt with 
  | Bool -> bool_interval
  | ByteBool
  | Byte -> byte_interval
  | Short -> short_interval
  | Char -> char_interval
  | Int2Bool
  | Int -> integer_interval
  | Long -> long_interval
  | _ -> topInterval

let get_interval_from_class_name (cname:string) = 
  if cname = "java.lang.Byte" then byte_interval
  else if cname = "java.lang.Short" then short_interval
  else if cname = "java.lang.Character" then char_interval
  else if cname = "java.lang.Integer" then integer_interval
  else if cname = "java.lang.Long" then long_interval
  else topInterval

let rec get_interval_from_vtype (vt:value_type_t) = 
  match vt with 
  | TBasic bt -> get_interval_from_basic_type bt
  | TObject TArray et -> get_interval_from_vtype et 
  | TObject TClass cn -> get_interval_from_class_name cn#name

let get_interval_from_type (topt: value_type_t option) = 
  match topt with 
  | Some vt -> get_interval_from_vtype vt
  | _ -> topInterval

let get_var_interval_from_type v (topt: value_type_t option) = 
  if JCHSystemUtils.is_length v then
    length_interval
  else if JCHSystemUtils.is_loop_counter v then
    loop_counter_interval
  else 
    match topt with 
    | Some vt -> get_interval_from_vtype vt
    | _ -> topInterval

let is_java_basic_type_primitive (jbt:java_basic_type_t) = 
  match jbt with 
  | Object 
  | Void -> false 
  | _ -> true

let rec is_object_type_primitive (ot:object_type_t) = 
  match ot with 
  | TClass cn -> false 
  | TArray vt -> is_primitive vt 

and is_primitive (vt:value_type_t) = 
  match vt with 
  | TBasic jbt -> is_java_basic_type_primitive jbt
  | TObject ot -> is_object_type_primitive ot

let is_primitive_not_bool_opt (vt_opt:value_type_t option) = 
  match vt_opt with 
  | None ->   false 
  | Some (TBasic Bool) -> false 
  | Some vt -> is_primitive vt

let is_primitive_not_bool (vt:value_type_t) = 
  match vt with 
  | TBasic Bool -> false 
  | _ -> is_primitive vt

let get_array_dim (vt:value_type_t) = 
  let rec get_dim depth vt = 
    match vt with
    | TObject TArray vt' -> get_dim (succ depth) vt'
    | TObject TClass cn -> 
	if cn#name = "java.lang.Object" then Some 0
	else None
    | TBasic Object
    | TBasic Void -> None
    | TBasic _ -> Some depth in
  get_dim 0 vt

let get_numeric_type (cn:class_name_int) = 
 match cn#name with
 | "java.lang.Integer" -> Some Int 
 | "java.lang.Short" -> Some Short
 | "java.lang.Character" -> Some Char
 | "java.lang.Byte" -> Some Byte
 | "java.lang.Long" -> Some Long
 | "java.lang.Float" -> Some Float
 | "java.lang.Double" -> Some Double
 | _ -> None

let is_collection_class (cn:class_name_int) = 
  if app#has_class cn then 
    let cInfo = app#get_class cn in
    cInfo#is_collection_class || cInfo#is_map_class 
  else
    false
    
let is_collection_type (vtype:value_type_t) = 
  match vtype with 
  | TObject TClass cn -> is_collection_class cn
  | TObject TArray _ -> true
  | _ -> false 

let can_be_collection (vtypes:value_type_t list) = 
  if vtypes = [] then false 
  else List.for_all is_collection_type vtypes 


let merge_types (vtypes1:value_type_t list) (vtypes2:value_type_t list) = 
  if vtypes1 = [] then
    vtypes2
  else if vtypes2 = [] then
    vtypes1
  else 
    begin
      let add_type (vtypes:value_type_t list) (vtype:value_type_t) = 
	if List.exists (fun t -> compare_value_types vtype t = 0) vtypes then
          vtypes 
	else
          vtype :: vtypes in
      List.fold_left add_type vtypes1 vtypes2 
    end

let rec make_type_list (vtype:value_type_t) = 
  match vtype with 
  | TBasic Int2Bool ->
     [ TBasic Bool; TBasic Byte; TBasic Short; TBasic Char; TBasic Int ]
  | TBasic ByteBool -> [ TBasic Bool; TBasic Byte ]
  | TBasic Object -> [ get_object_vt () ]
  | TObject (TArray vt) -> 
      let types = make_type_list vt in
      List.map (fun t -> TObject (TArray t)) types
  | _ -> [ vtype ]

let rec make_int_type_list (vtype:value_type_t) = 
  match vtype with 
  | TBasic Int2Bool 
  | TBasic ByteBool
  | TBasic Bool
  | TBasic Char 
  | TBasic Int
  | TBasic Byte
  | TBasic Short ->
     [ TBasic Bool; TBasic Byte; TBasic Short; TBasic Char; TBasic Int ]
  | TBasic Object -> [ get_object_vt () ]
  | _ -> [ vtype ]

let get_compact_type (vtypes:value_type_t list) = 
  if List.length vtypes > 1 then 
    let has_type vt = List.exists (fun t -> t = vt) vtypes in
    let is_not_in_types vts vt = List.for_all (fun vt' -> vt' <> vt) vts in
    if (has_type (TBasic Bool)) && (has_type (TBasic Byte)) then 
      if (has_type (TBasic Short))
         && (has_type (TBasic Char))
         && (has_type (TBasic Int)) then 
	(TBasic Int2Bool)
        :: (List.filter
              (is_not_in_types
                 [ TBasic Bool; TBasic Byte; TBasic Short; TBasic Char; TBasic  Int ])
              vtypes) 
      else
	(TBasic ByteBool)
        :: (List.filter (is_not_in_types [TBasic Bool; TBasic Byte]) vtypes)
    else
      vtypes 
  else
    vtypes
    
let equal_value_type_lists
      (vtypes1:value_type_t list) (vtypes2:value_type_t list) = 
  if List.length vtypes1 = List.length vtypes2 then 
    List.for_all
      (fun t1 ->
        List.exists (fun t2 -> compare_value_types t1 t2 = 0)  vtypes2) vtypes1
  else
    false

let is_float_type (t:value_type_t) = 
  match t with
    | TBasic Float
    | TBasic Double -> true
    | _ -> false

let can_be_float (vtypes:value_type_t list) = 
  if vtypes = [] then
    true 
  else
    List.for_all is_float_type vtypes 

let exception_type = TObject (TClass (make_cn "java.lang.Throwable"))

let is_enum (cn:class_name_int) = 
  if app#has_class cn then 
    let cInfo = app#get_class cn in 
    if cInfo#has_super_class then 
      cInfo#get_super_class#name = "java.lang.Enum" 
    else
      false 
  else
    false 

(* This does not include the Enum classes *)
(* Note: can this be moved to the summaries? *)
let is_immutable_class (cn:class_name_int) = 
  let name = cn#name in
  let ls = Str.split (Str.regexp "\\.") name in
  let package = String.concat "." (List.rev (List.tl (List.rev ls))) in
  let class_name = List.hd (List.rev ls) in
  match package with 
  | "java.lang" -> 
      begin
	class_name = "String" ||
	class_name = "Integer" || 
	class_name = "Byte" ||
	class_name = "Character" ||
	class_name = "Boolean" ||
	class_name = "Short" ||
	class_name = "Long" ||
	class_name = "Double" ||
	class_name = "Float" ||
	class_name = "StackTraceElement" 
      end
  | "java.lang.invoke" -> 
      class_name = "MethodType"
  | "java.math" -> 
      begin
	class_name = "BigInteger" || 
	class_name = "BigDecimal" ||
	class_name = "MathContext" 
      end
  | "java.security" -> 
      class_name = "CodeSigner" ||
      class_name = "Timestamp" ||
      class_name = "Permission" 
  | "java.security.spec" -> 
      begin
	class_name = "ECFieldF2m" ||
	class_name = "ECFieldFp" ||
	class_name = "GenParameterSpec" ||
	class_name = "ParameterSpec" ||
	class_name = "ECPoint" ||
	class_name = "ECPrivateKeySpec" ||
	class_name = "ECPublicKeySpec" ||
	class_name = "EllipticCurve" 
      end
  | "java.security.cert" -> 
      begin
	class_name = "CertPath" ||
	class_name = "PolicyQualifierInfo" 
      end
  | "java.security.Provider" ->
      class_name = "Service"
  | "java.util" -> 
      class_name = "java.util.UUID" 
  | "java.util.regexp" -> 
      class_name = "Pattern" 
  | "java.util.AbstractMap" -> 
      class_name = "SimpleImmutableEntry" 
  | "java.awt" -> 
      begin
	class_name = "TextLayout" ||
	class_name = "TransformAttribute" ||
	class_name = "Font" ||  (* not sure about this *)
	class_name = "BasicStroke" ||
	class_name = "Color" ||
	class_name = "AlphaComposite"
      end 
  | "java.awt.font" ->
      begin
	class_name = "ImageGraphicAttribute" ||
	class_name = "ShapeGraphicAttribute"
      end
  | "java.awt.RenderingHints" -> 
      class_name = "Key"
  | "java.io" -> 
      class_name = "File"
  | "java.nio.file.attribute" -> 
      class_name = "FileTime"
  | "java.net" -> 
      begin 
	class_name = "URI" ||
	class_name = "InetSocketAddress"
      end
  | "javax.management" -> 
      begin
	class_name = "ImmutableDescriptor" ||
	class_name = "MBeanFeatureInfo" ||
	class_name = "MBeanConstructorInfo" ||
	class_name = "MBeanNotificationInfo" ||
	class_name = "MBeanParameterInfo" ||
	class_name = "MBeanAttributeInfo" ||
	class_name = "MBeanOperationInfo" ||
	class_name = "ObjectName" ||
	class_name = "OpenMBeanOperationInfoSupport"
      end
  | "javax.swing.text" -> 
      begin
	class_name = "TabSet" ||
	class_name = "TabStop"
      end
  | "javax.lang.model.element" -> 
      begin
	class_name = "Name" 
      end
  | "javax.swing.plaf.synth" -> 
      class_name = "SynthContext" 
  | "javax.swing.text.AbstractDocument" -> 
      class_name = "AbstractElement"
  | "javax.xml.datatype" -> 
      class_name = "Duration"
  | "javax.xml.validation" -> 
      class_name = "javax.xml.validation.Schema" 
  | _ -> false
  
let is_immutable_t (vt:value_type_t) = 
  match vt with 
  | TBasic Object-> false
  | TBasic _ -> true 
  | TObject (TClass cn) -> 
      is_enum cn ||
      is_immutable_class cn
  | _ -> false 

let is_immutable_type (vtypes:value_type_t list) = 
  List.for_all is_immutable_t vtypes

let get_class_info (cn:class_name_int) = 
  if app#has_class cn then
    app#get_class cn
  else 
    begin
      ch_error_log#add "class info not found" cn#toPretty ;
      raise (JCH_failure (STR "missing class")) 
    end

let get_class_info_opt (cn:class_name_int) = 
  if app#has_class cn then
    Some (app#get_class cn)
  else 
    begin
      ch_error_log#add "class info not found" cn#toPretty ;
      None
    end

let get_all_supra_interfaces (cInfo:class_info_int) =
  let rec add_interfaces res cni = 
    let new_res = if cni#is_interface then cni :: res else res in
    let interfaces = cni#get_interfaces in
    let cnis = List.map get_class_info interfaces in
    List.fold_left add_interfaces new_res cnis in
  add_interfaces [] cInfo

let have_common_supra_interface (cInfo1:class_info_int) (cInfo2:class_info_int) = 
  let sup1 = get_all_supra_interfaces cInfo1 in
  let sup2 = get_all_supra_interfaces cInfo2 in
  List.exists
    (fun i1 -> List.exists (fun i2 -> i1#get_index = i2#get_index) sup2) sup1

let rec has_interface (cInfo: class_info_int) (cni:class_name_int) = 
  let interfaces = cInfo#get_interfaces in
  let cnix = cni#index in
  if List.exists (fun i -> i#index = cnix) interfaces then
    true
  else 
    let is_sub i = 
      let i_info = get_class_info i in
      has_interface i_info cni in
    List.exists is_sub interfaces 

let rec implements_interface (cinfo:class_info_int) (cni: class_name_int) = 
  if has_interface cinfo cni then true 
  else if cinfo#has_super_class then 
    let cn = cinfo#get_super_class in
    match get_class_info_opt cn with 
    | Some cn_info -> implements_interface cn_info cni (* RESTORE *)
    | _ -> false 
  else false 

let is_subclass (cn1:class_name_int) (cn2:class_name_int) = 
  if cn1#name = cn2#name then
    true 
  else if cn2#name = "java.lang.Object" then
    true
  else if cn1#name = "java.lang.Object" then
    cn2#name = "java.lang.Object" 
  else 
    match get_class_info_opt cn1 with 
    | Some cInfo1 -> 
       cn1#index = cn2#index
       || app#is_descendant cn1 cn2
       || implements_interface cInfo1 cn2
       || (cInfo1#is_interface && has_interface cInfo1 cn2) 
    | _ -> false 

(* one is a subclass of the other or they implement the same interface *)
(* Note: ambiguous precedence in expression? *)
let is_compatible (cn1:class_name_int) (cn2:class_name_int) = 
  if is_subclass cn1 cn2 || is_subclass cn2 cn1 then
    true
  else
    match (get_class_info_opt cn1, get_class_info_opt cn2) with 
    | (Some cInfo1, Some cInfo2) ->
       cInfo1#is_interface
       && (implements_interface cInfo2 cn1)
       || cInfo2#is_interface
          && (implements_interface cInfo1 cn2)
    | _ -> true

let rec is_subtype (vtype1:value_type_t) (vtype2:value_type_t) = 
  match (vtype1, vtype2) with 
  | (TBasic t1, TBasic t2) -> t1 = t2
  | (TObject _, TBasic Object) -> true
  | (TObject (TArray t1), TObject (TArray t2)) -> is_subtype t1 t2
  | (TBasic Object, TObject (TClass cn)) 
  | (TObject (TArray _), TObject (TClass cn)) -> cn#name = "java.lang.Object" 
  | (TObject (TClass cn1), TObject (TClass cn2)) -> is_subclass cn1 cn2 
  | _ -> false

let is_strict_subtype (vtype1:value_type_t) (vtype2:value_type_t) = 
  let is_object (vt:value_type_t) = 
    match vt with 
    | TBasic Object -> true
    | TObject TClass cn -> cn#name = "java.lang.Object" 
    | _ -> false in
  if compare_value_types vtype1 vtype2 = 0 then
    false 
  else if is_object vtype1 && is_object vtype2 then
    false 
  else
    is_subtype vtype1 vtype2

let is_int_subtype (t1:value_type_t) (t2:value_type_t) = 
  match (t1, t2) with 
  | (TBasic Bool, _) -> true
  | (TBasic Byte, TBasic Bool) -> false
  | (TBasic Byte, _) -> true
  | (TBasic Short, TBasic Bool) 
  | (TBasic Short, TBasic Byte)
  | (TBasic Short, TBasic Char) -> false
  | (TBasic Short, _) -> true
  | (TBasic Char, TBasic Bool) 
  | (TBasic Char, TBasic Byte) 
  | (TBasic Char, TBasic Short) -> false
  | (TBasic Char, _) -> true
  | (TBasic Int, TBasic Int) -> true
  | _ -> false 

let is_bool (t:value_type_t) = 
  match t with 
  | TBasic Bool -> true
  | _ -> false 

let is_byte (t:value_type_t) = 
  match t with 
  | TBasic Byte -> true
  | _ -> false 

let is_short (t:value_type_t) = 
  match t with 
  | TBasic Short -> true
  | _ -> false 

let is_char (t:value_type_t) = 
  match t with 
  | TBasic Char -> true
  | _ -> false 

let is_int (t:value_type_t) = 
  match t with 
  | TBasic Int -> true
  | _ -> false 

let is_long (t:value_type_t) = 
  match t with 
  | TBasic Long -> true
  | _ -> false 

let is_array (t:value_type_t) = 
  match t with 
  | TObject (TArray _) -> true
  | _ -> false

let set_to_var_to_types
      (var_to_types:JCHTypeSets.type_set_t VariableCollections.table_t)
      (v:variable_t)
      (t:JCHTypeSets.type_set_t) = 
  var_to_types#set v t

let get_types_from_sig
      (var_to_types:JCHTypeSets.type_set_t VariableCollections.table_t)
      (proc_name:symbol_t)
      (sig_vars:variable_t list) = 
  let set_type (t:value_type_t) (v:variable_t) = 
    let rec make_type_list (t:value_type_t) = 
      match t with 
      | TBasic Int2Bool ->
         [ TBasic Bool; TBasic Byte; TBasic Short; TBasic Char; TBasic Int ]
      | TBasic ByteBool -> [ TBasic Bool; TBasic Byte ]
      | TBasic Object -> [ get_object_vt () ]
      | TObject (TArray vt) -> 
	  let types = make_type_list vt in
	  List.map (fun t -> TObject (TArray t)) types
      | _ -> [t] in
    let vtypes = JCHTypeSets.mk_type_set (make_type_list t) in
    match var_to_types#get v with 
    | Some old_vtypes -> 
	set_to_var_to_types var_to_types v (old_vtypes#meet vtypes)
    | _ -> set_to_var_to_types var_to_types v vtypes in
  let cms = retrieve_cms proc_name#getSeqNumber in
  let mInfo = app#get_method cms in
  let args = 
    List.filter JCHSystemUtils.is_not_exception_or_return sig_vars in
  let descr = cms#method_signature#descriptor in
  let arg_types = 
    let param_types = descr#arguments in
    if mInfo#is_static then
      param_types 
    else 
      let class_type = TObject (TClass cms#class_name) in
      class_type :: param_types in
  begin
    List.iter2 set_type arg_types args ;
    (match descr#return_value with 
     | Some vt -> 
        begin
          try
	    let return = List.find JCHSystemUtils.is_return sig_vars in
	    set_type vt return 
          with
	  | Not_found ->
             raise (JCH_failure
                      (LBLOCK [ STR "return value not found in " ;
				STR "JCHTypeUtils.get_types_from_sig" ]))
        end
     | None -> () ) ;
    set_type (get_throwable_vt ()) exception_var
  end

let is_class_with_length (cn:class_name_int) =
  let rec aux (cnn:class_name_int) =
    if app#has_class cnn then
      let cInfo = app#get_class cnn in
      cInfo#has_length
      || (cInfo#has_super_class && (aux cInfo#get_super_class))
      || List.exists aux cInfo#get_interfaces
    else
      false
  in aux cn

let is_type_with_length (vtype:value_type_t) = 
  match vtype with 
  | TObject (TArray vt) -> true
  | TObject (TClass cn) -> is_class_with_length cn
  | _ -> false


(* Note: function is 221 lines with sequence of embedded of imperative
 * statements *)
let get_types_from_stack_info
      (proc_name:symbol_t)
      (proc:procedure_int)
      (phi_to_vars:VariableCollections.set_t VariableCollections.table_t) :  
      (int * (value_type_t list * bool)) list =
  let cms = retrieve_cms proc_name#getSeqNumber in
  let mInfo = app#get_method cms in
  let meth_stack_layout =  mInfo#get_method_stack_layout in
  let stack_layouts = meth_stack_layout#get_pc_stack_layouts in
  let pc_to_stack_layout = new IntCollections.table_t in
  let _ = List.iter (fun (pc,s) -> pc_to_stack_layout#set pc s) stack_layouts in
  let var_to_types = new VariableCollections.table_t in
  (* variables that could have a length; covers the case when a variable is 
   * initialized as a null object, then used as an argument *)  
  let vars_with_lengths = new VariableCollections.set_t in  

  let add_to_var_to_types (new_set:JCHTypeSets.type_set_t) (var:variable_t) =
    (match var_to_types#get var with 
    | Some set -> 
	if JCHTypeSets.get_type_list set = [] then 
	  set_to_var_to_types var_to_types var new_set
	else 
	  if JCHTypeSets.is_num_type_set set then 
	    begin 
	      if new_set#leq set then
                set_to_var_to_types var_to_types var new_set
	      else if set#leq new_set then 
		()
	      else
                (* If there are contradictory types than the smallest type 
                 * should be still correct *)
		let meet_set = set#meet new_set in
		let list = ref (JCHTypeSets.get_type_list meet_set) in
		let add_min_type l1 l2 t = 
		  if List.mem t l1 && List.mem t l2 then
                    false 
		  else if List.mem t l1 || List.mem t l2 then 
		    begin 
		      list := t :: !list ;
		      false 
		    end
		  else
                    true in
		let smallest set1 set2 = 
		  let l1 = JCHTypeSets.get_type_list set1 in
		  let l2 = JCHTypeSets.get_type_list set2 in
                  begin
		    (if add_min_type l1 l2 (TBasic Bool) then 
		       if add_min_type l1 l2 (TBasic Byte) then 
		         if add_min_type l1 l2 (TBasic Short) then 
			   if add_min_type l1 l2 (TBasic Char) then 
			     let _ = add_min_type l1 l2 (TBasic Int) in ()) ;
		    JCHTypeSets.mk_type_set !list
                  end in
		set_to_var_to_types var_to_types var (smallest set new_set) ;
	    end
	  else 
	    let join_set = set#join new_set in
	    set_to_var_to_types var_to_types var join_set

    | None -> set_to_var_to_types var_to_types var new_set ) in

  (* get type from stack info *)
  let add_slot (pc: int) (stack:op_stack_layout_int) = 
    if stack#get_size > 0 then 
      try (* it's possible that the variable is unreachable *)
	let top_slot = stack#get_top_slot in
	let var = top_slot#get_transformed_variable in
	let make_type_list (vtype:value_type_t) = 
	  match vtype with 
	  | TBasic Int2Bool ->
             [ TBasic Bool; TBasic Byte; TBasic Short; TBasic Char; TBasic Int ]
	  | TBasic ByteBool -> [ TBasic Bool; TBasic Byte ]
	  | TBasic Object -> [ get_object_vt () ]
	  | TObject (TArray vt) ->
             begin
	       vars_with_lengths#add var ;
	       let types = make_type_list vt in
	       List.map (fun t -> TObject (TArray t)) types
             end
	  | TObject (TClass cn) ->
	      begin
		(if is_class_with_length cn then vars_with_lengths#add var) ;
		[ vtype ]
	      end
	  | _ -> [ vtype ] in
	let vtypes = List.concat (List.map make_type_list top_slot#get_type) in
	add_to_var_to_types (JCHTypeSets.mk_type_set vtypes) var
      with _ -> () in
  pc_to_stack_layout#iter add_slot ;

  let (var_to_phi, new_phi_to_vars) =
    let v2p = new VariableCollections.table_t in
    let p2v = new VariableCollections.table_t in
    let add_phi (phi:variable_t) (vars:VariableCollections.set_t) =
      p2v#set phi vars#clone ;
      let add v = 
	match v2p#get v with
	| Some set -> set#add phi
	| None -> v2p#set v (VariableCollections.set_of_list [ phi ]) in
      vars#iter add in
    phi_to_vars#iter add_phi ;
    (v2p, p2v) in

  (* Add types for variables from the phi variables *)
  let add_type_from_phi (phi: variable_t) (vars: VariableCollections.set_t) = 
    match var_to_types#get phi with 
    | Some types -> 
	vars#iter (fun v -> set_to_var_to_types var_to_types v types)
    | _ -> () in
  new_phi_to_vars#iter add_type_from_phi ;

  (* Add types for local variables that were incremented
   * As there was no change on the stack this is not covered by the previous *)
  let incremented_locals = ref [] in
  let sig_vars = 
    let bindings = proc#getBindings in
    let get_internal_var (s,_,_) = 
      try
	snd (List.find  (fun (s', v') -> s#equal s') bindings) 
      with
      | Not_found ->
	 raise
           (JCH_failure
              (LBLOCK [ STR "internal var not found for " ; s#toPretty ;
			STR " in JCHTypeUtils.get_types_from_stackinfo" ])) in
    List.map get_internal_var proc#getSignature in
  let not_phis = 
    let not_phis = VariableCollections.set_of_list var_to_phi#listOfKeys in
    not_phis#removeList (phi_to_vars#listOfKeys) ; 
    not_phis in
  let not_phis' = not_phis#clone in
  not_phis'#removeList sig_vars ; 
  let add_iinc_var var = 
    match var_to_types#get var with 
    | Some _ -> ()
    | None -> 
	incremented_locals := var#getIndex :: !incremented_locals ;
	set_to_var_to_types var_to_types var (JCHTypeSets.mk_type_set [TBasic Int]) in
  not_phis'#iter add_iinc_var; 
  
  get_types_from_sig var_to_types proc_name sig_vars ;

  (* set types for phi vars *) 
  let set_phi_type (phi:variable_t) (vars:VariableCollections.set_t) = 
    let set = ref JCHTypeSets.bottom_type_set in
    let add v = 
      let t = Option.get (var_to_types#get v) in
      set := !set#join t in
    vars#iter add ;
    set_to_var_to_types var_to_types phi !set in

  let done_vars = new VariableCollections.set_t in
  let rec work (vars:variable_t list) = 
    match vars with 
    | var :: rest_vars -> 
	(* var has already a type. We have to check the dependent phis *)
       if done_vars#has var then
         work rest_vars
	else 
	  begin
	    done_vars#add var ;
	    match var_to_phi#get var with 
	    | Some phis -> 
		let process_phi res phi = 
		  match var_to_types#get phi with 
		  | Some _ -> phi :: res
		  | None -> 
		      begin
			let get_vars phi = Option.get (phi_to_vars#get phi) in
			match new_phi_to_vars#get phi with 
			| Some set ->
			    set#remove var ;
			    if set#isEmpty then 
			      begin
				set_phi_type phi (get_vars phi) ;
				phi :: res
			      end
			    else res
			| None -> 
			    set_phi_type phi (get_vars phi) ;
			    phi :: res
		      end in
		let work_phis = List.fold_left process_phi [] phis#toList in
		work (work_phis @ rest_vars) 
	    | None -> work rest_vars
	  end
    | _ -> () in	  
  work not_phis#toList ;

  (* set types for phi vars in a dependency loop with other phi vars *) 
  let rec work_loop (phis:variable_t list) = 
    match phis with 
    | phi :: rest_phis -> 
	begin
	match var_to_types#get phi with 
	| Some _ -> work_loop rest_phis 
	| None -> 
	    let vars = Option.get (phi_to_vars#get phi) in
	    let vars_with_types =
              vars#filter (fun v -> Option.is_some (var_to_types#get v)) in
	    if vars_with_types#isEmpty then
              work_loop (rest_phis @ [phi])   (* postpone work on phi *)
	    else 
	      begin
		set_phi_type phi vars_with_types ;
		work_loop rest_phis 
	      end
	end
    | _ -> () in
  work_loop new_phi_to_vars#listOfKeys ;
  
  let var_to_type_list = ref [] in

  let add var set = 
    let type_list = JCHTypeSets.get_type_list set in
    let has_length = List.exists is_type_with_length type_list in

    var_to_type_list :=
      (var#getIndex, (type_list, has_length)) :: !var_to_type_list in
  var_to_types#iter add ;
  !var_to_type_list

let get_invocation_object_type
      (mInfo:method_info_int)
      (iInfo:instruction_info_int)
      (num_args:int) = 
  let location = iInfo#get_location in
  let pc = location#get_pc in
  let pc_stack_layouts = mInfo#get_method_stack_layout#get_pc_stack_layouts in
  let pc_to_stack = new IntCollections.table_t in
  let _ = List.iter (fun (pc,s) -> pc_to_stack#set pc s) pc_stack_layouts in
  let stack_layout = Option.get (pc_to_stack#get pc) in
  let slot = List.nth stack_layout#get_slots num_args in
  slot#get_type


let get_basic_type (vtypes:value_type_t list) = 
  let get_basic (t:value_type_t) = 
    match t with 
    | TBasic Void -> (None, false)
    | TBasic Object -> (None, true)
    | TBasic _ -> (Some t, true)
    | TObject TClass cn -> 
	begin
	  match cn#name with 
	  | "java.lang.Integer" -> (Some (TBasic Int) ,true)
	  | "java.lang.Short" -> (Some (TBasic Short), true)
	  | "java.lang.Character" -> (Some (TBasic Char), true)
	  | "java.lang.Byte" -> (Some (TBasic Byte), true)
	  | "java.lang.Long" -> (Some (TBasic Long), true)
	  | "java.lang.Float" -> (Some (TBasic Float), true)
	  | "java.lang.Double" -> (Some (TBasic Double), true)
	  | "java.math.BigInteger" -> (None, true)
	  | "java.math.BigDecimal" -> (None, true)
	  | _ -> (None, false)
	end 
    | _ -> (None, false) in
	  
  let get_basic_t (t:value_type_t) = 
    match t with 
    | TBasic _ -> get_basic t 
    | TObject TArray vt ->
       get_basic vt   (* We do not want arrays of collections, etc *)
    | TObject TClass cn -> 
	begin
	  match cn#name with 
	  | "java.lang.Integer" -> (Some (TBasic Int) ,true)
	  | "java.lang.Short" -> (Some (TBasic Short), true)
	  | "java.lang.Character" -> (Some (TBasic Char), true)
	  | "java.lang.Byte" -> (Some (TBasic Byte), true)
	  | "java.lang.Long" -> (Some (TBasic Long), true)
	  | "java.lang.Float" -> (Some (TBasic Float), true)
	  | "java.lang.Double" -> (Some (TBasic Double), true)
	  | "java.lang.Object" -> (None, true)
	  | _ -> 
	      if is_collection_class cn then (None, true)
	      else (None, false)
	end in

  let add_basic_type
        ((basic_type_opt, is_numeric):(value_type_t option * bool))
        (vtype:value_type_t) = 
    let (basic_type_opt', is_numeric') = get_basic_t vtype in
    let res_basic_type_opt = 
      match (basic_type_opt, basic_type_opt') with 
      | (Some (TBasic Bool), _) -> basic_type_opt'
      | (Some (TBasic Byte), Some (TBasic Bool)) -> basic_type_opt
      | (Some (TBasic Byte), _ ) -> basic_type_opt'
      | (Some (TBasic Char), Some (TBasic Bool)) 
      | (Some (TBasic Char), Some (TBasic Byte)) -> basic_type_opt
      | (Some (TBasic Char), Some (TBasic Short)) -> Some (TBasic Int)
      | (Some (TBasic Char), _ ) -> basic_type_opt'
      | (Some (TBasic Short), Some (TBasic Bool)) 
      | (Some (TBasic Short), Some (TBasic Byte)) -> basic_type_opt
      | (Some (TBasic Short), Some (TBasic Char)) -> Some (TBasic Int)
      | (Some (TBasic Short), _ ) -> basic_type_opt'
      | (Some (TBasic Int), _) -> basic_type_opt
      | (Some bt1, Some bt2) -> 
	 if bt1 = bt2 then
           Some bt1 
	 else
           None 
      | _ -> None in 
    (res_basic_type_opt, is_numeric) in 

  match vtypes with 
  | vtype :: rest_vtypes -> 
      List.fold_left add_basic_type (get_basic_t vtype) rest_vtypes 
  | [] -> (None, false) 

let sub_value_type_lists
      (vtypes1:value_type_t list) (vtypes2:value_type_t list) =
  let is_not_num (vt:value_type_t) =
    match vt with
    | TBasic Object -> true
    | TObject TClass _ -> true
    | _ -> false in
  let obj_vtypes1 = List.filter is_not_num vtypes1 in
  let obj_vtypes2 = List.filter is_not_num vtypes2 in
  obj_vtypes1 != []
  && obj_vtypes2 != []
  && (List.for_all
        (fun vt2 ->
          List.exists (fun vt1 -> is_strict_subtype vt1 vt2) obj_vtypes1)
        obj_vtypes2)
    
