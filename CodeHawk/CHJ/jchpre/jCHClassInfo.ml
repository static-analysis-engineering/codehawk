(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny Sipma

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
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHPreAPI
open JCHSystemSettings

module ClassMethodSignatureCollections = CHCollections.Make (
  struct
    type t = class_method_signature_int
    let compare cms1 cms2 = cms1#compare cms2
    let toPretty cms = cms#toPretty
  end)

module ClassNameCollections = CHCollections.Make (
  struct
    type t = class_name_int
    let compare n1 n2 = n1#compare n2
    let toPretty n = n#toPretty
  end)

let wrapper_class_types =
  [ ("java.lang.Boolean", Bool) ; 
    ("java.lang.Byte", Byte) ;
    ("java.lang.Character", Char) ;
    ("java.lang.Double", Double) ; 
    ("java.lang.Float", Float) ;
    ("java.lang.Integer", Int)   ;
    ("java.lang.Long", Long)    ; 
    ("java.lang.Short", Short) ] 

let wrapper_classes = List.map (fun (name,_) -> make_cn name) wrapper_class_types


class class_info_t ~(class_info_type:class_info_type_t):class_info_int =
object (self)

  val creators = new ClassMethodSignatureCollections.set_t 
  val subclasses = new ClassNameCollections.set_t 
  val implementing_classes = new ClassNameCollections.set_t 
  val mutable dispatch = false

  method add_creator cms = creators#add cms

  method get_creators = creators#toList

  method add_subclass cn = subclasses#add cn

  method add_implementing_class cn = implementing_classes#add cn

  method set_dispatch = dispatch <- true

  method get_class = class_info_type

  method get_subclasses = subclasses#toList

  method get_implementing_classes = implementing_classes#toList

  method get_version = match class_info_type with
  | ConcreteClass c | InterfaceType c | AbstractClass c ->
      (string_of_int c#get_version.major) ^ "." ^ (string_of_int c#get_version.minor)
  | _ -> "?"

  method has_version = match class_info_type with
    ConcreteClass c | InterfaceType c | AbstractClass c -> true | _ -> false

  method get_class_name = 
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c -> c#get_name
    | StubbedClass c  -> c#get_class_name
    | MissingClass cn -> cn

  method get_index = self#get_class_name#index

  method get_super_class =
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c -> 
       begin
         match c#get_super_class with
         | Some s -> s
         | _ ->
	    raise (JCH_failure
                     (LBLOCK [ c#get_name#toPretty ; STR " does not have a super class"]))
      end
    | StubbedClass c ->
      if c#has_super_class then c#get_super_class else
	raise (JCH_failure
                 (LBLOCK [ c#get_class_name#toPretty ; STR " does not have a super class"]))
    | MissingClass cn ->
      raise (JCH_failure 
	       (LBLOCK [ STR "Class " ; cn#toPretty ; 
			 STR " was not loaded, because it could not be found" ]))
	
  method get_generic_signature =
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c ->
      begin
	match c#get_generic_signature with Some s -> s | _ ->
	  raise (JCH_failure (LBLOCK [ STR "Class " ; c#get_name#toPretty ; 
				       STR " does not have a generic signature" ]))
      end
    | _ ->
      raise (JCH_failure (LBLOCK [ STR "Class " ; self#get_class_name#toPretty ;
				   STR " does not have a gneneric signature" ]))

  method has_generic_signature =
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c ->
      begin match c#get_generic_signature with Some _ -> true | _ -> false end
    | _ -> false

  method get_wrapped_primitive_type =
    try
      let (_,ty) = List.find (fun (name,_) -> name = self#get_class_name#name) wrapper_class_types in
      ty
    with
      Not_found ->
	raise (JCH_failure (LBLOCK [ self#get_class_name#toPretty ; STR " is not a wrapper class" ]))

  method get_method (ms:method_signature_int) =
    match class_info_type with
    | ConcreteClass c | AbstractClass c ->
      begin
	match c#get_method ms with
	| Some m -> m
	| _ ->
	  raise (JCH_failure (STR ("Internal error in JCHClassInfo.get_method")))
      end
    | InterfaceType c ->
       begin
         match c#get_method ms with
         | Some m -> m
         | _ ->
            match c#get_initializer with
            | Some m -> m
            | _ ->
               raise (JCH_failure (STR ("Internal error in JCHClassInfo.get_method (interface)")))
       end
    | StubbedClass _ ->
      raise (JCH_failure
	       (LBLOCK [ STR "Unexpected request for method in stubbed class: " ; 
			 self#get_class_name#toPretty ; STR " with signature " ; ms#toPretty ]))
    | _ ->
      raise (JCH_failure
	       (LBLOCK [ STR "No method in class " ; self#toPretty ; STR " with signature " ;
			 ms#toPretty ]))

  method get_methods_defined =
    match class_info_type with
    | ConcreteClass c | AbstractClass c -> c#get_method_signatures
      | InterfaceType c ->
       begin
         match c#get_initializer with
         | Some m -> m#get_signature :: c#get_method_signatures
         | _ -> c#get_method_signatures
       end
    | StubbedClass c -> c#get_methods
    | _ -> []

  method get_interface_default_methods =
    match class_info_type with
    | InterfaceType c ->
       let initmethod =
         match c#get_initializer with
         | Some m -> [ m#get_signature ]
         | _ -> [] in
       let methods =
         List.filter (fun ms ->
             match c#get_method ms with
             | Some m -> m#is_concrete
             | _ -> false) c#get_method_signatures in
       initmethod @ methods
    | _ -> []
                        

  method get_native_methods_defined =
    match class_info_type with
    | ConcreteClass c | AbstractClass c ->
      let mss = c#get_method_signatures in
      List.filter (fun ms -> 
	match c#get_method ms with
	| Some m -> (m#is_concrete && 
		       match m#get_implementation with 
		       | Native -> true | _ -> false)
	| _ -> false) mss
    | _ -> []
      
  method get_fields_defined =
    match class_info_type with
    | ConcreteClass c | AbstractClass c | InterfaceType c -> c#get_field_signatures
    | StubbedClass c -> c#get_fields
    | _ -> []

  method get_field_count = List.length self#get_fields_defined

  method get_scalar_object_size =
    List.fold_left (fun acc fs ->
        acc + (size_of_value_type fs#descriptor)) 4 self#get_fields_defined

  method get_field_signature (name:string) =
    try
      List.find (fun fs -> fs#name = name) self#get_fields_defined
    with
    | Not_found ->
       raise (JCH_failure
                (LBLOCK [ STR "No field with name " ; STR name ; STR " in class " ;
                          self#toPretty ]))

  method get_field (fs:field_signature_int) =
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c -> 
      begin
	match c#get_field fs with
	  Some f -> f
	| _ -> 
	  raise (JCH_failure (STR ("Internal error in JCHClassInfo.get_field")))
      end
    | _ ->
      raise (JCH_failure
	       (LBLOCK [ STR "No field in class " ; self#toPretty ; STR " with signature " ;
			 fs#toPretty ]))
	
  method get_interfaces = 
    match class_info_type with
    | ConcreteClass c | AbstractClass c | InterfaceType c -> c#get_interfaces
    | StubbedClass c -> c#get_interfaces
    | _ -> []

  method get_default_implementations =
    match class_info_type with
    | StubbedClass c -> c#get_default_implementations
    | _ -> []
      
  method get_instruction_count =
    match class_info_type with
    | ConcreteClass c | AbstractClass c | InterfaceType c -> c#get_instruction_count
    | _ -> 0

  method get_bootstrap_methods =
    match class_info_type with
    | ConcreteClass c | AbstractClass c | InterfaceType c -> c#get_bootstrap_methods
    | _ -> []

  method get_bootstrap_method (index:int) =
    let l = self#get_bootstrap_methods in
    if index < (List.length l) then
      List.nth l index
    else
      raise (JCH_failure
               (LBLOCK [ STR "Illegal bootstrap method index: " ; INT index ;
                         STR "; only " ; INT (List.length l) ;
                         STR " bootstrap methods found" ]))

  method get_lambda_function (index:int) =
    try
      let bmethod = self#get_bootstrap_method index in
      match bmethod#get_lambda_function with
      | Some (ot,ms) -> (ot,ms)
      | _ ->
         raise (JCH_failure
                  (LBLOCK [ STR "Bootstrap method " ; INT index ;
                            STR " in class " ; self#get_class_name#toPretty ; 
                            STR " does not return a lambda function" ]))
    with
    | JCH_failure p ->
       raise (JCH_failure (LBLOCK [ STR "Error in getting lambda function in class " ;
                                    self#get_class_name#toPretty ; STR ": " ; p ]))

  method returns_lambda_function (index:int) =
    match (self#get_bootstrap_method index)#get_lambda_function with
    | Some _ -> true
    | _ -> false
      
  method is_interface = 
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c -> c#is_interface
    | StubbedClass c -> c#is_interface
    | MissingClass _ -> false
      
  method is_missing = match class_info_type with MissingClass _ -> true | _ -> false

  method is_stubbed = match class_info_type with StubbedClass _ -> true | _ -> false
    
  method is_dispatch =
    dispatch || (match class_info_type with StubbedClass c -> c#is_dispatch | _ -> false)
      
  method is_collection_class =
    let collectionInterface = make_cn "java.util.Collection" in
    List.exists (fun i -> i#equal collectionInterface) self#get_interfaces
      
  method is_map_class =
    let mapInterface = make_cn "java.util.Map" in
    List.exists (fun i -> i#equal mapInterface) self#get_interfaces
      
  method is_wrapper_class = List.exists (fun w -> self#get_class_name#equal w) wrapper_classes
    
  method has_super_class =
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c ->
      begin match c#get_super_class with Some _ -> true | _ -> false end
    | StubbedClass c -> c#has_super_class
    | MissingClass cn -> false
      
  method has_super_interfaces =
    self#is_interface && (match self#get_interfaces with [] -> false | _ -> true)
      
  method is_final =
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c -> c#is_final
    | StubbedClass c -> c#is_final
    | MissingClass _ -> false
      
  method is_abstract =
    match class_info_type with
    | ConcreteClass _ -> false
    | AbstractClass _ | InterfaceType _ -> true
    | StubbedClass c -> c#is_abstract
    | MissingClass _ -> false
	
  method is_immutable =
    match class_info_type with StubbedClass c -> c#is_immutable | _ -> false
      
  method get_source_origin =
    match class_info_type with
    | ConcreteClass c
    | AbstractClass c 
    | InterfaceType c -> c#get_source_origin
    | StubbedClass _ -> "library"
    | _ -> "unknown"

  method has_md5_digest =
    match class_info_type with
    | ConcreteClass c | AbstractClass c | InterfaceType c -> true
    | _ -> false
      
  method get_md5_digest =
    let byte_to_string (b:int) =
      let l = b mod 16 in
      let h = b lsr 4 in
      Printf.sprintf "%x%x" h l in
    let hex_string s =
      let ch = IO.input_string s in
      let h = ref "" in
      let len = String.length s in
      begin
	for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done ;
	!h
      end in
    match class_info_type with
    | ConcreteClass c
    | AbstractClass c
    | InterfaceType c -> (hex_string c#get_md5_digest)
    | StubbedClass _ -> "stub:no-md5-computed"
    | _ -> "missing:no-md5-computed"
          
  method has_method (ms:method_signature_int) =
    match class_info_type with
    | ConcreteClass c | AbstractClass c | InterfaceType c -> c#defines_method ms
    | _ -> false
      
  method defines_method (ms:method_signature_int) =
    match class_info_type with 
    | ConcreteClass c | AbstractClass c | InterfaceType c -> c#defines_method ms
    | StubbedClass c -> c#defines_method ms
    | _ -> false
      
  method defines_field (fs:field_signature_int) =
    match class_info_type with
    | ConcreteClass c | InterfaceType c | AbstractClass c -> c#defines_field fs
    | StubbedClass c -> c#defines_field fs
    | MissingClass _ -> false
      
  method implements_interface (cn:class_name_int) =
    List.exists (fun i -> i#equal cn) self#get_interfaces

  method has_length =
    match class_info_type with
    | StubbedClass c ->
       List.exists (fun p -> match p with LogicalSize _ -> true) c#get_class_properties
    | _ -> false

  method get_length_accessor =
    match class_info_type with
    | StubbedClass c ->
       begin
         try
           let p = List.find (fun p -> match p with LogicalSize _ -> true) c#get_class_properties in
           match p with
           | LogicalSize a -> a
         with
           Not_found ->
           raise (JCH_failure (LBLOCK [ STR "Internal error in get_length_accessor" ]))
       end
    | _ ->
       raise (JCH_failure (LBLOCK [ STR "Length accessor is only available for stubbed classes" ]))
      
  method toPretty = 
    let obj = make_cn "java.lang.Object" in
    let pImplements = match self#get_interfaces with
      | [] -> STR ""
      | l -> pretty_print_list l (fun i -> i#toPretty) " implements [" ";" "]" in
    let pSuperclass = if self#has_super_class then
	let superclass = self#get_super_class in
	if superclass#equal obj then STR ""
	else LBLOCK [ STR " superclass: " ; superclass#toPretty ]
      else
	STR "" in
    let pSubclasses = match self#get_subclasses with [] -> STR "" | l ->
      LBLOCK [ STR " (" ; pp_quantity (List.length l) "subclass" "subclasses" ; STR ")" ] in
    let pImplementingClasses = match self#get_implementing_classes with [] -> STR "" | l ->
      LBLOCK [ STR " (" ; pp_quantity (List.length l) "implementing class" "implementing classes" ; STR ")" ] in
    let pAbstract = if self#is_abstract && not self#is_interface then STR " (abstract)" else STR "" in
    let pFormals = if self#has_generic_signature then 
	LBLOCK [ NL ; STR "          generic: " ; self#get_generic_signature#toPretty ]
      else
	STR "" in
    let pVersion =
      match class_info_type with
	ConcreteClass c | InterfaceType c | AbstractClass c -> 
	  let version = c#get_version in
	  LBLOCK [ STR " (version " ; INT version.major ; STR "." ; INT version.minor ; STR ")" ]
      | _ -> STR "" in
    let pFields = match class_info_type with
      | ConcreteClass c | InterfaceType c | AbstractClass c ->
	let numFields = List.length c#get_fields in
	if numFields > 0 then 
	  LBLOCK [ STR " (defines " ; 
		   pp_quantity numFields "field" "fields" ; STR ")" ] else STR ""
      | _ -> STR "" in
    let pOrigin =
      match class_info_type with
      | ConcreteClass c | InterfaceType c | AbstractClass c ->
	let name = Filename.basename self#get_source_origin in
	LBLOCK [ STR " (" ; STR name ; STR ")" ] | _ ->  STR "" in
    LBLOCK [ self#get_class_name#toPretty ; pOrigin ; pSuperclass ; pSubclasses ;
	     (if self#is_interface then STR " (interface) " else STR "") ;  
	     pImplementingClasses ; pImplements ; pAbstract ; pFields ; 
	     pFormals ; pVersion ]
      
end
  
  
let make_class_info (c:java_class_or_interface_int) =
  let info_type =
    if c#is_interface
    then
      InterfaceType c
    else if c#is_abstract then
      AbstractClass c
    else
      ConcreteClass c in
  new class_info_t ~class_info_type:info_type


let make_class_stub_info (c:class_summary_int) =
  new class_info_t ~class_info_type:(StubbedClass c)


let make_missing_class_info (cn:class_name_int)  =
  new class_info_t ~class_info_type:(MissingClass cn)
  
