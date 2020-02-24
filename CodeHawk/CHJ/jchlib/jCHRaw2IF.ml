(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet
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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHClass
open JCHDictionary
open JCHInstruction
open JCHMethod
open JCHParseUTF8Signature
open JCHRawClass
open JCHUnparse

let debug = ref 1

module MethodCollections = CHCollections.Make (
  struct
    type t = method_signature_int
    let compare m1 m2 = m1#compare m2
    let toPretty m = m#toPretty
  end)

module FieldCollections = CHCollections.Make (
  struct
    type t = field_signature_int
    let compare f1 f2 = f1#compare f2
    let toPretty f = f#toPretty
  end)

(* [map2] works even if lists are not the same size by taking elements for the
   other list as default values *)
let rec map2 f l1 l2 = match l1,l2 with
  | [],[] -> []
  | [],l
  | l, [] -> l
  | e1::r1, e2::r2 -> (f e1 e2)::(map2 f r1 r2)


let rec flags2access = function
  | AccPublic::l ->
      if List.exists (fun a -> a = AccPrivate || a= AccProtected) l
      then raise 
	(JCH_class_structure_error 
	   (STR "Access flags Public and Private or Protected cannot be set at the same time"))
      else (Public,l)
  | AccPrivate::l ->
      if List.exists (fun a -> a = AccPublic || a= AccProtected) l
      then raise 
	(JCH_class_structure_error
	   (STR "Access flags Private and Public or Protected cannot be set at the same time"))
      else (Private,l)
  | AccProtected::l ->
      if List.exists (fun a -> a = AccPrivate || a= AccPublic) l
      then raise 
	(JCH_class_structure_error 
	   (STR "Access flags Protected and Private or Public cannot be set at the same time"))
      else (Protected,l)
  | f::l -> let (p,fl) = flags2access l in (p,f::fl)
  | [] -> (Default,[])

let rec get_flag flag = function
  | [] -> (false,[])
  | f::fl when f=flag -> (true,List.filter ((<>)f) fl)
  | f::fl -> let (b,fl) = get_flag flag fl in (b,f::fl)

type lvt = (int * int * string * value_type_t * int) list

let combine_LocalVariableTable (lvts:lvt list) : lvt =
  let lvt = List.concat lvts in
  if not (JCHBasicTypes.is_permissive ()) then
    begin
      let for_all_couple (f:'a -> 'a -> bool) (l:'a list) : bool =
	List.for_all
	  (fun e1 -> List.for_all (f e1) l) l
      and overlap (e1_start,e1_end,_,_,_) (e2_start,e2_end,_,_,_) =
	(e2_start < e1_end && e1_start < e2_end)
      and similar (_,_,e1_name,_,e1_index) (_,_,e2_name,_,e2_index) =
	e1_name = e2_name || e1_index = e2_index in
      if not (for_all_couple (fun e1 e2 -> e1==e1 || 
	not (overlap e1 e2 && similar e1 e2)) lvt)
      then
        raise (JCH_class_structure_error 
		 (LBLOCK [ STR "A CodeAttribute contains more than one " ;
                           STR "LocalVariableTable and they are not compatible " ;
                           STR "with each other"]))
    end;
  lvt

type lvtt = (int * int * string * field_type_signature_int * int) list

let combine_LocalVariableTypeTable (lvtts:lvtt list) : lvtt =
  let lvtt = List.concat lvtts in
  if not (is_permissive ()) then
    begin
      let for_all_couple (f:'a -> 'a -> bool) (l:'a list) : bool =
	List.for_all
	  (fun e1 -> List.for_all (f e1) l) l
      and overlap (e1_start,e1_end,_,_,_) (e2_start,e2_end,_,_,_) =
	(e2_start < e1_end && e1_start < e2_end)
      and similar (_,_,e1_name,_,e1_index) (_,_,e2_name,_,e2_index) =
	e1_name = e2_name || e1_index = e2_index in
      if not (for_all_couple (fun e1 e2 -> e1==e1 || 
	not (overlap e1 e2 && similar e1 e2)) lvtt)
      then
        raise (JCH_class_structure_error 
		 (LBLOCK [ STR "A CodeAttribute contains more than one " ;
                           STR "LocalVariableTypeTable and they are not compatible " ;
                           STR "with each other"]))
    end;
  lvtt

(* convert a list of  attributes to a list of couple of string, as for AttributeUnknown. *)
let low2high_other_attributes consts : attribute_t list ->  (string*string) list =
  List.map
    (function
    | AttributeUnknown (name, contents) -> name, contents
    | a ->
      let (name,contents) = unparse_attribute_to_strings consts a in
      if !debug >0 then prerr_endline ("Warning: unexpected attribute found: "^name);
      name,contents)

(* convert a list of  attributes to an [attributes] structure. *)
let low2high_attributes consts (al:attribute_t list): attributes_int =
  make_attributes
    ~is_synthetic:(List.exists ((=)AttributeSynthetic) al)
    ~is_deprecated:(List.exists ((=)AttributeDeprecated) al)
    ~other:(
      low2high_other_attributes consts
	(List.filter
	   (function AttributeDeprecated | AttributeSynthetic -> false | _ -> true)
	   al))

let expanse_stackmap_table stackmap_table =
  let (_,stackmap) =
    List.fold_left
      (fun ((pc,l,_),stackmap) frame ->
	match frame with
	| SameFrame k ->
	  let offset = pc + k + 1 in
	  let s = (offset,l,[]) in
	  (s,s::stackmap)
	| SameLocals (k,vtype) ->
	  let offset = pc + k - 64 + 1 in
	  let s = (offset,l,[vtype]) in
	  (s,s::stackmap)
	| SameLocalsExtended (_,offset_delta,vtype) ->
	  let offset = pc + offset_delta + 1 in
	  let s = (offset,l,[vtype]) in
	  (s,s::stackmap)
	| ChopFrame (k,offset_delta) ->
	  let offset = pc + offset_delta + 1 in
	  let nb_chop = 251 - k in
	  let l_chop = List.rev
	    (ExtList.List.drop nb_chop (List.rev l)) in
	  let s = (offset,l_chop,[]) in
	  (s,s::stackmap)
	| SameFrameExtended (_,offset_delta) ->
	  let offset = pc + offset_delta + 1 in
	  let s = (offset,l,[]) in
	  (s,s::stackmap)
	| AppendFrame (_,offset_delta,vtype_list) ->
	  let offset = pc + offset_delta + 1 in
	  let s = (offset,l@vtype_list,[]) in
	  (s,s::stackmap)
	| FullFrame (_,offset_delta,lv,sv) ->
	  let offset = pc + offset_delta + 1 in
	  let s = (offset,lv,sv) in
	  (s,s::stackmap)
      ) ((-1,[],[]),[]) stackmap_table in
  List.rev stackmap
    
let low2high_code consts = function c ->
  make_bytecode
    ~max_stack:c.c_max_stack
    ~max_locals:c.c_max_locals
    ~code:(make_opcodes (opcodes2code (DynArray.to_array consts) c.c_code))
    ~exception_table:c.c_exc_tbl
    ?line_number_table:
    (begin
      let rec find_lineNumberTable = function
	| AttributeLineNumberTable l::l' ->
	  (* if find_lineNumberTable l' <> None
	     then raise (JCH_class_structure_error 
	     "Only one AttributeLineNumberTable can be attached to a method."); *)
	  Some l
	| _::l -> find_lineNumberTable l
	| [] -> None in 
      find_lineNumberTable c.JCHRawClass.c_attributes
     end)
    ?local_variable_table:
    (begin
      let lvt =
	combine_LocalVariableTable
	  (List.fold_left
             (fun lvts ->
               (function
               | AttributeLocalVariableTable lvt -> lvt :: lvts
               | _ -> lvts)) [] c.JCHRawClass.c_attributes) in
      match lvt with
      | [] -> None
      | _ -> Some lvt
     end)
    ?local_variable_type_table:
    (begin
      let lvtt =
	combine_LocalVariableTypeTable
	  (List.fold_left
             (fun lvtts ->
               (function
               | AttributeLocalVariableTypeTable lvtt -> lvtt :: lvtts
               | _ -> lvtts))
             []
             c.JCHRawClass.c_attributes) in
      match lvtt with
      | [] -> None
      | _ -> Some lvtt
     end)
    ?stack_map_midp:
    (begin
      let rec find_StackMap = function
	| AttributeStackMap l :: l' ->
	  if find_StackMap l' <> None then
            raise (JCH_class_structure_error 
		     (STR "Only one StackMap attribute can be attached to a method."));
	  Some l
	| _::l -> find_StackMap l
	| [] -> None in
      match find_StackMap c.c_attributes with
      | None -> None
      | Some l -> Some (List.map (fun s -> make_stackmap s) l)
     end)
    ?stack_map_java6:
    (begin
      let rec find_StackMapTable = function
	| AttributeStackMapTable l :: l' ->
	   if find_StackMapTable l' <> None then
             raise (JCH_class_structure_error 
		      (STR "Only one StackMapTable attribute can be attached to a method."));
	   Some (expanse_stackmap_table l)
	| _::l -> find_StackMapTable l
	| [] -> None in 
      match find_StackMapTable c.c_attributes with
      | None -> None
      | Some l -> Some (List.map (fun s -> make_stackmap s) l)
     end)
    ~attributes:(low2high_other_attributes consts
		   (List.filter
		      (function
		      | AttributeStackMap _
		      | AttributeStackMapTable _ | AttributeLocalVariableTable _
		      | AttributeLocalVariableTypeTable _
		      | AttributeLineNumberTable _ -> false
		      | _ -> true)
		      c.c_attributes))
    ()
    
let low2high_cfield cn consts fs = function f ->
  let flags = f.f_flags in
  let (is_static,flags) = get_flag AccStatic flags in
  let (access,flags) = flags2access flags in
  let (is_final,flags) = get_flag AccFinal flags in
  let (is_volatile,flags) = get_flag AccVolatile flags in
  let (is_transient,flags) = get_flag AccTransient flags in
  let (is_synthetic,flags) = get_flag AccSynthetic flags in
  let (is_enum,flags) = get_flag AccEnum flags in
  let flags =
    List.map (function
      | AccRFU i -> i
      | _ ->
	prerr_endline "unexcepted flag in JLow2High.low2high_cfield";
	assert false)
      flags in
  let kind =
    if is_final then
      if not (JCHBasicTypes.is_permissive ()) && is_volatile then 
	raise (JCH_class_structure_error (STR "A field cannot be final and volatile."))
      else Final
    else
      if is_volatile then Volatile else NotFinal in
  let (cst,other_att) =
    List.partition (function AttributeConstant _ -> true | _ -> false) f.f_attributes in
  let (cst,other_att) =
    match cst with
    | [] -> None,other_att
    | AttributeConstant c::oc when not is_static ->  (* it seems quite common *)
      if !debug > 1
      then
        prerr_endline
          ("Warning: Non-static field " ^ cn#name ^ "."
           ^ fs#name ^ " has been found with a constant value associated.");
      None, (AttributeConstant c::(oc@other_att))
    | AttributeConstant c::[] -> Some c, other_att
    | AttributeConstant c::oc -> 
      if !debug > 0
      then
        prerr_endline
          ("Warning: Field " ^ cn#name ^ "."
           ^ fs#name ^ " contains more than one constant value associated.");
      Some c, (oc@other_att)
    | _ -> assert false in
  let (generic_signature,other_att) =
    List.partition (function AttributeSignature _ -> true | _ -> false) other_att in
  let generic_signature =
    match generic_signature with
    | [] -> None
    | (AttributeSignature s)::rest  ->
      if rest = [] || is_permissive ()
      then
	try
	  Some (parse_field_type_signature s)
	with JCH_class_structure_error _ as e ->
	  if is_permissive () then None else raise e
      else
        raise (JCH_class_structure_error 
		 (LBLOCK [ STR "A field contains more than one Signature attribute " ;
                           STR "asscociated with it."]))
    | _ -> assert false in
  let (annotations,other_att) =
    List.partition
      (function
      | AttributeRuntimeVisibleAnnotations _
      | AttributeRuntimeInvisibleAnnotations _ -> true
      | _ -> false) other_att in 
  let annotations =
    List.fold_right
      (fun annot annots ->
        match annot with
        | AttributeRuntimeVisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,true)::annots) al annots
        | AttributeRuntimeInvisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,false)::annots) al annots
        | _ -> assert false) annotations [] in
  (make_class_field
     ~signature:fs
     ~class_signature:(make_cfs cn fs)
     ~generic_signature
     ~access
     ~is_static
     ~is_final
     ~kind
     ~value:cst
     ~is_transient
     ~is_synthetic
     ~is_enum
     ~other_flags:flags
     ~annotations
     ~attributes:(low2high_attributes consts other_att) :> field_int)
    
let low2high_ifield cn consts fs = function f ->
  let flags = f.f_flags in
  let (is_public,flags) = get_flag AccPublic flags in
  let (is_static,flags) = get_flag AccStatic flags in
  let (is_final,flags) = get_flag AccFinal flags in
  let (is_synthetic,flags) = get_flag AccSynthetic flags in
  if not(is_public && is_static && is_final) then 
    raise (JCH_class_structure_error 
	     (STR "A field of an interface must be : Public, Static and Final"));
  let flags = List.map
    (function
    | AccRFU i -> i
    | _ -> raise (JCH_class_structure_error 
		    (LBLOCK [ STR "A field of an interface may only have it " ;
                              STR "AccSynthetic flag set in addition of AccPublic, " ;
                              STR "AccStatic and AccFinal" ])))
    flags in
  let (generic_signature,other_att) =
    List.partition (function AttributeSignature _ -> true | _ -> false) f.f_attributes in
  let generic_signature =
    match generic_signature with
    | [] -> None
    | (AttributeSignature s)::rest ->
      if rest = [] || JCHBasicTypes.is_permissive ()
      then
	try
	  Some (parse_field_type_signature s)
	with JCH_class_structure_error _ as e ->
	  if is_permissive () then None else raise e
      else
        raise (JCH_class_structure_error 
		 (STR "A field contains more than one Signature attribute asscociated with it"))
    | _ -> assert false in
  let (csts,other_att) =
    List.partition (function AttributeConstant _ -> true | _ -> false) other_att in
  let cst = match csts with
    | [] -> None
    | [AttributeConstant c] -> Some c
    | _ -> raise (JCH_class_structure_error 
		    (STR "An interface field contains more than one Constant Attribute")) in
  let (annotations,other_att) =
    List.partition
      (function
      | AttributeRuntimeVisibleAnnotations _
      | AttributeRuntimeInvisibleAnnotations _ -> true
      | _ -> false) other_att in 
  let annotations =
    List.fold_right
      (fun annot annots ->
        match annot with
        | AttributeRuntimeVisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,true)::annots) al annots
        | AttributeRuntimeInvisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,false)::annots) al annots
        | _ -> assert false) annotations [] in
  (make_interface_field
     ~signature:fs
     ~class_signature:(make_cfs cn fs)
     ~generic_signature:generic_signature
     ~value:cst
     ~is_synthetic:is_synthetic
     ~is_final:is_final
     ~other_flags:flags
     ~annotations:annotations
     ~attributes:(low2high_attributes consts other_att) :> field_int)
    
let low2high_amethod consts cs ms = function m ->
  let flags = m.m_flags in
  let (access,flags) = flags2access flags in
  let (_is_abstract,flags) = get_flag AccAbstract flags in
  let (is_synthetic,flags) = get_flag AccSynthetic flags in
  let (is_bridge,flags) = get_flag AccBridge flags in
  let (is_varargs,flags) = get_flag AccVarArgs flags in
  let access =
    match access with
    | Private ->
       raise (JCH_class_structure_error (STR "Abstract method cannot be private"))
    | Default -> Default
    | Protected -> Protected
    | Public -> Public in
  let flags =
    List.map
      (function
      | AccRFU i -> i
      | _ -> raise (JCH_class_structure_error
                      (LBLOCK [ STR "If a method has its ACC_ABSTRACT flag set it " ;
                                STR "may not have any of its ACC_FINAL, ACC_NATIVE, " ;
                                STR "ACC_PRIVATE, ACC_STATIC, ACC_STRICT, or " ;
                                STR "ACC_SYNCHRONIZED flags set"]))) flags in
  let (generic_signature, other_att) =
    List.partition (function AttributeSignature _ -> true | _ -> false) m.m_attributes in
  let generic_signature = match generic_signature with
    | [] -> None
    | (AttributeSignature s)::rest ->
      if rest = [] || is_permissive ()
      then
	try
	  Some (parse_method_type_signature s)
	with JCH_class_structure_error _ as e ->
	  if is_permissive () then None else raise e
      else
        raise (JCH_class_structure_error 
		 (STR "An abstract method cannot have several Signature attributes."))
    | _ -> assert false in
  let (exn,other_att) =
    List.partition (function
                    | AttributeExceptions _-> true
                    | AttributeCode _ ->
                       begin
                         pr_debug [ STR "Encountered Code Attribute in abstract method" ;
                                    ms#toPretty ; STR " in class " ; cs#toPretty ; NL ; NL ] ;
                         false
                       end
                    | _ -> false) other_att in
  let exn = match exn with
    | [] -> []
    | [AttributeExceptions cl] -> cl
    | _ -> raise (JCH_class_structure_error 
		    (STR "Only one Exception attribute is allowed in a method")) in
  let (default_annotation,other_att) =
    List.partition
      (function | AttributeAnnotationDefault _ -> true | _ -> false) other_att in
  let default_annotation =
    match default_annotation with
    | [] -> None
    | [AttributeAnnotationDefault ad] -> Some ad
    | _::_::_ ->
      raise (JCH_class_structure_error
               (STR "A method should not have more than one AnnotationDefault attribute"))
    | [_] -> assert false in
  let (annotations,other_att) =
    List.partition
      (function
      | AttributeRuntimeVisibleAnnotations _
      | AttributeRuntimeInvisibleAnnotations _ -> true
      | _ -> false) other_att in 
  let annotations =
    List.fold_right
      (fun annot annots ->
        match annot with
        | AttributeRuntimeVisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,true)::annots) al annots
        | AttributeRuntimeInvisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,false)::annots) al annots
        | _ -> assert false) annotations [] in
  let (parameter_annotations,other_att) =
    List.partition
      (function
      | AttributeRuntimeVisibleParameterAnnotations _
      | AttributeRuntimeInvisibleParameterAnnotations _
        -> true
      | _ -> false) other_att in
  let parameter_annotations =
    if parameter_annotations = [] then 
      []
    else
      let res =
        List.fold_left
          (fun (res:'a list) -> function
          | AttributeRuntimeVisibleParameterAnnotations pa ->
            let pa = List.map (List.map (fun a -> (a,true))) pa
            in map2 (@) pa res
          | AttributeRuntimeInvisibleParameterAnnotations pa ->
            let pa = List.map (List.map (fun a -> (a,false))) pa
            in map2 (@) pa res
          | _ -> assert false) [] parameter_annotations in
      if List.length res <=  List.length ms#descriptor#arguments
      then 
	res
      else 
	raise
          (JCH_class_structure_error
             (LBLOCK [ STR "The length of an Runtime(In)VisibleParameterAnnotations " ;
                       STR "is longer than the number of arguments of the same method"])) in
  make_abstract_method
    ~signature:ms
    ~class_method_signature:(make_cms cs ms)
    ~access:access
    ?generic_signature:generic_signature
    ~is_synthetic:is_synthetic
    ~is_bridge:is_bridge
    ~has_varargs:is_varargs
    ~other_flags:flags
    ~exceptions:exn
    ~attributes:(low2high_attributes consts other_att)
    ~annotations:(make_method_annotations
		    ~global:annotations
		    ~parameters:parameter_annotations)
    ?annotation_default:default_annotation
    ()
    
let low2high_cmethod consts cs ms = function m ->
  if m.m_name = "<init>" &&
    List.exists (fun a -> 
      a=AccStatic || a=AccFinal || a=AccSynchronized || a=AccNative || a=AccAbstract)
    m.m_flags
  then raise (JCH_class_structure_error 
		(LBLOCK [ STR "A specific instance initialization method may have at most " ;
		          STR "one of its ACC_PRIVATE, ACC_PROTECTED, and ACC_PUBLIC flags set " ;
		          STR "and may also have its ACC_STRICT flag set" ]));
  let flags = m.m_flags in
  let (access,flags) = flags2access flags in
  let (is_static,flags) = get_flag AccStatic flags in
  let (is_final,flags) = get_flag AccFinal flags in
  let (is_synchronized,flags) = get_flag AccSynchronized flags in
  let (is_strict,flags) = get_flag AccStrict flags in
  let (is_synthetic,flags) = get_flag AccSynthetic flags in
  let (is_bridge,flags) = get_flag AccBridge flags in
  let (is_varargs,flags) = get_flag AccVarArgs flags in
  let (is_native,flags) = get_flag AccNative flags in
  let flags = List.map
    (function
       | AccRFU i -> i
       | AccAbstract -> 
	 raise (JCH_class_structure_error 
		  (STR "Non abstract class cannot have abstract methods"))
       | _ -> raise 
	 (Failure "Bug in JLow2High.low2high_cmethod : unexpected flag found."))
    flags
  in
  let (generic_signature,other_att) =
    List.partition (function AttributeSignature _ -> true | _ -> false) m.m_attributes in
  let generic_signature = match generic_signature with
    | [] -> None
    | (AttributeSignature s)::rest ->
      if rest = [] || JCHBasicTypes.is_permissive ()
      then
	try
	  Some (parse_method_type_signature s)
	with JCH_class_structure_error _ as e ->
	  if JCHBasicTypes.is_permissive ()
	  then None
	  else raise e
      else
        raise (JCH_class_structure_error 
		 (STR "A method cannot have several Signature attributes"))
    | _ -> assert false
  and (exn,other_att) =
    List.partition (function AttributeExceptions _ -> true | _ -> false) other_att in
  let exn = match exn with
    | [] -> []
    | [AttributeExceptions cl] -> cl
    | _ -> raise (JCH_class_structure_error 
		    (STR "Only one Exception attribute is allowed in a method"))
  and (code,other_att) =
    List.partition (function AttributeCode _ -> true | _ -> false) other_att in
  let code = match code with
    | [AttributeCode c] when not is_native -> Bytecode (low2high_code consts c)
    | [] when is_native -> Native
    | [] ->
      raise
        (JCH_class_structure_error
           (STR "A method not declared as Native, nor Abstract has been found without code"))
    | [_] ->
      raise
        (JCH_class_structure_error
           (STR "A method declared as Native has been found with a code attribute"))
    | _::_::_ ->
      raise
          (JCH_class_structure_error
             (STR "Only one Code attribute is allowed in a method"))  in
  let (annotations,other_att) =
    List.partition
      (function
         | AttributeRuntimeVisibleAnnotations _
         | AttributeRuntimeInvisibleAnnotations _
           -> true
         | _ -> false) other_att in 
  let annotations =
    List.fold_right
      (fun annot annots ->
        match annot with
        | AttributeRuntimeVisibleAnnotations al ->
          List.fold_right
            (fun a annots -> (a,true)::annots) al annots
        | AttributeRuntimeInvisibleAnnotations al ->
          List.fold_right
            (fun a annots -> (a,false)::annots) al annots
        | _ -> assert false)
      annotations
      [] in
  let (parameter_annotations,other_att) =
    List.partition
      (function
         | AttributeRuntimeVisibleParameterAnnotations _
         | AttributeRuntimeInvisibleParameterAnnotations _
           -> true
         | _ -> false)
      other_att in
  let parameter_annotations =
    if parameter_annotations = []
    then []
    else
      let res =
        List.fold_left
          (fun (res:'a list) -> function
          | AttributeRuntimeVisibleParameterAnnotations pa ->
            let pa = List.map (List.map (fun a -> (a,true))) pa
            in map2 (@) pa res
          | AttributeRuntimeInvisibleParameterAnnotations pa ->
            let pa = List.map (List.map (fun a -> (a,false))) pa
            in map2 (@) pa res
          | _ -> assert false)
          []
          parameter_annotations in
      if List.length res <=  List.length ms#descriptor#arguments
      then res
      else raise
        (JCH_class_structure_error
           (LBLOCK [ STR "The length of an Runtime(In)VisibleParameterAnnotations " ;
                     STR "is longer than the number of arguments of the same method"])) in
  let class_method_signature = make_cms cs ms in
  make_concrete_method
    ~signature:ms
    ~class_method_signature
    ~is_static
    ~is_final
    ~is_synchronized
    ~is_strict
    ~access
    ?generic_signature:generic_signature
    ~is_bridge
    ~has_varargs:is_varargs
    ~is_synthetic
    ~other_flags:flags
    ~exceptions:exn
    ~attributes:(low2high_attributes consts other_att)
    ~annotations:(make_method_annotations
		    ~global:annotations
		    ~parameters:parameter_annotations)
    ~implementation:code
    ()

let low2high_interface_method consts cs ms =
  function
    m -> if List.exists (fun a ->
                match a with AttributeCode _ -> true | _ -> false) m.m_attributes then
           low2high_cmethod consts cs ms m
         else
           low2high_amethod consts cs ms m

let low2high_acmethod consts cs ms = function m ->
  if List.exists ((=)AccAbstract) m.m_flags
  then low2high_amethod consts cs ms m
  else low2high_cmethod consts cs ms m

let low2high_methods ?(interfacemethod=false) cn consts = function ac ->
  let cs = ac.rc_name in
  let methods = List.map (fun meth ->
    let isstatic = 
      List.exists (fun f -> match f with AccStatic -> true | _ -> false) meth.m_flags in
    let ms = make_ms isstatic meth.m_name meth.m_descriptor in
    try
      if interfacemethod then
        low2high_interface_method consts cs ms meth
      else
        low2high_acmethod consts cs ms meth
    with JCH_class_structure_error msg ->
      raise (JCH_class_structure_error
	       (LBLOCK [ STR "in method " ;
                         STR (JCHDumpBasicTypes.signature meth.m_name (SMethod meth.m_descriptor)) ;
                         STR ": " ; msg ]))) ac.rc_methods in
  let _ = if !debug > 0 then
    let mset = new MethodCollections.set_t in
    let _ = List.iter (fun m ->
      if mset#has m#get_signature then
	prerr_endline
	  ("Warning: in " ^ cn#name
           ^ " two methods with the same signature (" ^ m#get_signature#to_string ^ ")")
      else
	mset#add m#get_signature) methods in
    () in
  methods

let low2high_innerclass = function
    (inner_class_info,outer_class_info,inner_name,flags) ->
      let (access,flags) = flags2access flags in
      let (is_final,flags) = get_flag AccFinal flags in
      let (is_static,flags) = get_flag AccStatic flags in
      let (is_interface,flags) = get_flag AccInterface flags in
      let (is_abstract,flags) = get_flag AccAbstract flags in
      let (is_synthetic,flags) = get_flag AccSynthetic flags in
      let (is_annotation,flags) = get_flag AccAnnotation flags in
      let (is_enum,flags) = get_flag AccEnum flags in
      let flags = List.map
	(function
	  | AccRFU i -> i
	  | _ -> raise (Failure "unexpected flag"))
	flags
      in
	make_inner_class
	  ?name:inner_class_info
	  ?outer_class_name:outer_class_info
	  ?source_name:inner_name
	  ~access
	  ~is_static
	  ~is_final
	  ~is_synthetic
	  ~is_annotation
	  ~is_enum
	  ~other_flags:flags
	  ~kind:(if is_interface then 
		   Interface
		 else
		   if is_abstract then 
		     Abstract
		   else 
		     ConcreteClass)
	  ()

let low2high_class cl =
  let java_lang_object = make_cn "java.lang.Object" in
  if cl.rc_super = None && (not (cl.rc_name#equal java_lang_object))
  then raise (JCH_class_structure_error 
		(STR "Only java.lang.Object is allowed not to have a super-class"));
  let cs = cl.rc_name in
  let flags = cl.rc_flags in
  let (access,flags) = flags2access flags in
  let (accsuper,flags) = get_flag AccSuper flags in
  let (is_final,flags) = get_flag AccFinal flags in
  let (is_interface,flags) = get_flag AccInterface flags in
  let (is_abstract,flags) = get_flag AccAbstract flags in
  let (is_synthetic,flags) = get_flag AccSynthetic flags in
  let (is_annotation,flags) = get_flag AccAnnotation flags in
  let (is_enum,flags) = get_flag AccEnum flags in
  let flags =
    List.map
      (function
	 | AccRFU i -> i
	 | _ -> raise (Failure "unexpected flag found"))
      flags in
  let _ = 
    if not (JCHBasicTypes.is_permissive ())
      && not (accsuper || is_interface)
      && not (accsuper && is_interface)
    then raise (JCH_class_structure_error 
		  (STR "ACC_SUPER must be set for all classes (that are not interfaces)")) in
  let _ = 
    if not (JCHBasicTypes.is_permissive ()) && (is_final && is_abstract)
    then raise (JCH_class_structure_error (STR "An abstract class cannot be final")) in
  let consts = DynArray.of_array cl.rc_consts in
  let my_name = cl.rc_name in
  let my_version = cl.rc_version in
  let my_source_origin = cl.rc_origin in
  let my_md5_digest = cl.rc_md5 in
  let my_access =
    match access with
    | Public -> Public
    | Default -> Default
    | _ -> raise (JCH_class_structure_error (STR "Invalid visibility for a class"))
  and my_interfaces = cl.rc_interfaces
  and my_sourcefile =
    let rec find_SourceFile = function
      | AttributeSourceFile s::_ -> Some s
      | _::l -> find_SourceFile l
      | [] -> None
    in find_SourceFile cl.rc_attributes
  and my_deprecated = List.exists ((=)AttributeDeprecated) cl.rc_attributes
  and my_generic_signature =
    match List.find_all (function AttributeSignature _ -> 
      true | _ -> false) cl.rc_attributes with
    | [] -> None
    | (AttributeSignature s)::rest  ->
      if rest = [] || JCHBasicTypes.is_permissive ()
      then
	try
	  Some (parse_class_signature s)
	with JCH_class_structure_error _ as e ->
	  if JCHBasicTypes.is_permissive ()
	  then None
	  else raise e
      else
        raise (JCH_class_structure_error 
		 (STR "A class or interface cannot have several Signature attributes"))
    | _ -> assert false

  and my_bootstrap_methods =
    match List.find_all
            (function AttributeBootstrapMethods _ -> true | _ -> false)
            cl.rc_attributes with
    | [] -> []
    | [ AttributeBootstrapMethods l ] -> l
    | _ ->
       raise (JCH_class_structure_error
                (STR "A class or interface can only have one BootstrapMethod table"))
      
  and my_source_debug_extension =
    let sde_attributes =
      List.find_all
	(function AttributeSourceDebugExtension _ -> true | _ -> false)
	cl.rc_attributes
    in
    match sde_attributes with
    | [] -> None
    | (AttributeSourceDebugExtension s)::rest
      ->
      if rest = [] || JCHBasicTypes.is_permissive ()
      then Some s
      else
        raise
	  (JCH_class_structure_error
	     (STR "A class cannot contain several SourceDebugExtension attribute"))
    | _ -> assert false
  and my_inner_classes =
    let rec find_InnerClasses = function
      | AttributeInnerClasses icl::_ -> List.rev_map low2high_innerclass icl
      | _::l -> find_InnerClasses l
      | [] -> []
    in find_InnerClasses cl.rc_attributes
  and my_annotations =
    List.fold_right
      (fun annot annots ->
        match annot with
        | AttributeRuntimeVisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,true)::annots) al annots
        | AttributeRuntimeInvisibleAnnotations al ->
          List.fold_right (fun a annots -> (a,false)::annots) al annots
        | _ -> annots)
        cl.rc_attributes
        []
  and my_other_attributes =
    low2high_other_attributes consts
      (List.filter
	 (function
	  | AttributeSignature _ | AttributeSourceFile _
            | AttributeSourceDebugExtension _
            | AttributeRuntimeVisibleAnnotations _
            | AttributeRuntimeInvisibleAnnotations _
	    | AttributeDeprecated
            | AttributeInnerClasses _
            | AttributeBootstrapMethods _ -> false
	  | AttributeEnclosingMethod _ -> is_interface
	 | _ -> true)
	 cl.rc_attributes); in
  if is_interface then
    begin
      if not (is_permissive ())
      then
        begin
	  (if not is_abstract then
	      raise (JCH_class_structure_error
                       (LBLOCK [ STR "A class file with its AccInterface flag set must " ;
                                 STR "also have its AccAbstract flag set"])));
	  (let obj = make_cn "java.lang.Object" in
	   if not (cl.rc_super = Some obj) then
	     raise (JCH_class_structure_error
                      (STR "The super-class of interfaces must be java.lang.Object")));
	  if is_enum then
	    raise (JCH_class_structure_error
                     (LBLOCK [ STR "A class file with its AccInterface flag set must " ;
                               STR "not have  its their AccEnum flag set"]))
        end;
      let (init,methods) =
	match
	  List.partition
	    (fun m ->
	      let clinit_name = clinit_signature#name in
	      let clinit_desc = clinit_signature#descriptor in
	      m.m_name = clinit_name
	      && m.m_descriptor#arguments = clinit_desc#arguments)
	    cl.rc_methods
	with
	| ([ m ],others) ->
           let ms = make_ms true m.m_name m.m_descriptor in
           (Some (low2high_cmethod consts cs ms m), others)
	| ([],others) -> (None, others)
	| m::_::_,others ->
	  if not (JCHBasicTypes.is_permissive ()) then
	    raise (JCH_class_structure_error
                     (STR "has more than one class initializer <clinit>"))
	  else
            (Some (low2high_cmethod consts cs clinit_signature m), others) in
      let fields = List.map (fun f ->
	let fs = make_fs f.f_name f.f_descriptor in
	try
	  low2high_ifield my_name consts fs f
	with
	  JCH_class_structure_error msg ->
	    raise (JCH_class_structure_error 
		     (LBLOCK [ STR "field " ;
                               STR ((JCHDumpBasicTypes.signature f.f_name (SValue f.f_descriptor))) ;
		               STR ": " ; msg ]))) cl.rc_fields in
      let _ = if !debug > 0 then
	  let fset = new FieldCollections.set_t in
	  List.iter (fun f -> if fset#has f#get_signature then
	      prerr_endline
		("Warning: in " ^ my_name#name 
		 ^ " two fields have the same signature ("
		 ^ f#get_signature#to_string ^ ")")
	    else
	      fset#add f#get_signature) fields in
      let methods = List.map (fun meth ->
	let isstatic = 
	  List.exists (fun f -> match f with AccStatic -> true | _ -> false) meth.m_flags in
	let ms = make_ms isstatic meth.m_name meth.m_descriptor in
	try 
	  low2high_interface_method consts cs ms meth			      
	with
	  JCH_class_structure_error msg ->
	    let sign = JCHDumpBasicTypes.signature meth.m_name (SMethod meth.m_descriptor) in
	    raise (JCH_class_structure_error
		     (LBLOCK [ STR "in class " ; STR my_name#name ;
                               STR ": method " ; STR sign ; STR ": " ; msg ])))	methods in
      
      let _ = if !debug > 0 then
	  let mset = new MethodCollections.set_t in
	  List.iter (fun m -> if mset#has m#get_signature then
	      prerr_endline
		("Warning: in " ^ my_name#name
		 ^ " two methods have the same signature (" ^ m#get_signature#to_string
		 ^ ")")
	    else
	      mset#add m#get_signature) methods in
      (make_java_interface
	 ~name:my_name
	 ~version:my_version
	 ~access:my_access
	 ~generic_signature:my_generic_signature
	 ~interfaces:my_interfaces
	 ~consts:(DynArray.to_array consts)
	 ?source_file:my_sourcefile
	 ~source_origin:my_source_origin
	 ~md5_digest:my_md5_digest
	 ~is_deprecated:my_deprecated
	 ?source_debug_extension:my_source_debug_extension
	 ~inner_classes:my_inner_classes
	 ~other_attributes:my_other_attributes
	 ?initializer_method:init
	 ~is_annotation:is_annotation
         ~annotations:my_annotations
         ~bootstrapmethods:my_bootstrap_methods
	 ~other_flags:flags
	 ~fields
	 ~methods () :> java_class_or_interface_int)
	end
      else
	begin
	  if is_annotation
	  then
            raise
              (JCH_class_structure_error
                 (LBLOCK [ STR "Class file with their AccAnnotation flag set must also " ;
                           STR "have their AccInterface flag set"]));
	  let my_enclosing_method =
            let enclosing_method_atts =
              List.find_all
                (function AttributeEnclosingMethod _ -> true | _ -> false)
                cl.rc_attributes
            in
	      match enclosing_method_atts  with
	        | [] -> None
	        | [AttributeEnclosingMethod (cs,mso)] ->
		    let ms =
		      match mso with
		        | None -> None
			  (* make_ms requires an argument is_static, which is not
			     known at this point for an enclosing method; we give it
			     a default argument false; currently the enclosing method
			     is not used; when it is used this is_static argument
			     needs to be fixed
			  *)
		        | Some (mn,SMethod mdesc) -> Some (make_ms false mn mdesc)
		        | Some (_,SValue _) ->
			    raise
			      (JCH_class_structure_error
			         (LBLOCK [ STR "A EnclosingMethod attribute cannot specify " ;
                                           STR "a field as enclosing method"]))
		    in Some (cs, ms)
	        | _ ->
		    raise
		      (JCH_class_structure_error
		         (LBLOCK [ STR "A EnclosingMethod attribute can only be " ;
                                   STR "specified at most once per class"]))
	  and my_methods =
            try low2high_methods my_name consts cl
            with
            | JCH_class_structure_error msg ->
               raise (JCH_class_structure_error
                        (LBLOCK [ STR "in class " ; STR my_name#name ;STR ": " ; msg ]))
                
	  and my_fields =
	    List.map (fun f ->
	      let fs = make_fs f.f_name f.f_descriptor in
	      try
		low2high_cfield my_name consts fs f
	      with
		JCH_class_structure_error msg ->
		  raise (JCH_class_structure_error
			   (LBLOCK [ STR "in class " ; STR my_name#name ; STR ": in field " ;
			       STR (JCHDumpBasicTypes.signature f.f_name 
			                                        (SValue f.f_descriptor)) ;
                               STR ": " ; msg ]))) cl.rc_fields in
	  (make_java_class
	     ~name:my_name
	     ~version:my_version
	     ~super_class:cl.rc_super
	     ~generic_signature:my_generic_signature
	     ~is_final:is_final
	     ~is_abstract:is_abstract
	     ~access:my_access
	     ~is_synthetic:is_synthetic
	     ~is_enum:is_enum
	     ~other_flags:flags
	     ~interfaces:my_interfaces
	     ~consts:(DynArray.to_array consts)
	     ?source_file:my_sourcefile
	     ~source_origin:my_source_origin
	     ~md5_digest:my_md5_digest
	     ~is_deprecated:my_deprecated
	     ?source_debug_extension:my_source_debug_extension
	     ?enclosing_method:my_enclosing_method
             ~annotations:my_annotations
             ~bootstrapmethods:my_bootstrap_methods
	     ~inner_classes:my_inner_classes
	     ~other_attributes:my_other_attributes
	     ~fields:my_fields
	     ~methods:my_methods
	     () :> java_class_or_interface_int)
	end

let low2high_class cl =
  try low2high_class cl
  with JCH_class_structure_error msg ->
    raise (JCH_class_structure_error (LBLOCK [STR "In " ; STR cl.rc_name#name ; STR ": " ; msg]))
