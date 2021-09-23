(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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

open IO.BigEndian
open ExtList
open ExtString

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHParseUTF8Signature
open JCHRawBasicTypes
open JCHRawClass

module H = Hashtbl


let unknown_attributes = H.create 3

let add_unknown_attribute s =
  let entry =
    if H.mem unknown_attributes s then
      H.find unknown_attributes s
    else
      0 in
  H.replace unknown_attributes s (entry + 1)


let get_unknown_attributes () =
  let lst = H.fold (fun k v a -> (k,v)::a) unknown_attributes [] in
  List.sort ~cmp:(fun (k1,_) (k2,_) -> Stdlib.compare k1 k2) lst


type tmp_constant =
  | ConstantClass of int                            (*  7 *)
  | ConstantField of int * int                      (*  9 *)
  | ConstantMethod of int * int                     (* 10 *)
  | ConstantInterfaceMethod of int * int            (* 11 *)
  | ConstantString of int                           (*  8 *)
  | ConstantInt of int32                            (*  3 *)
  | ConstantFloat of float                          (*  4 *)
  | ConstantLong of int64                           (*  5 *)
  | ConstantDouble of float                         (*  6 *)
  | ConstantNameAndType of int * int                (* 12 *)
  | ConstantStringUTF8 of string                    (*  1 *)
  | ConstantMethodHandle of reference_kind_t * int  (* 15 *)
  | ConstantMethodType of int                       (* 16 *)                        
  | ConstantInvokeDynamic of int  * int             (* 18 *)
  | ConstantUnusable                      (* second part of 64-bit entry *)


type attribute_name_t =
  (* Code *)
  | LineNumberTable
  | LocalVariableTable 
  | LocalVariableTypeTable
  | StackMap
  (* ClassFile, field_info, method_info *)
  | Synthetic 
  | Deprecated 
  | Signature
  (* ClassFile, field_info, method_info, Code *)
  | RuntimeVisibleAnnotations
  | RuntimeInvisibleAnnotations
  (* method_info *)
  | RuntimeVisibleParameterAnnotations
  | RuntimeInvisibleParameterAnnotations
  | Code
  | Exceptions
  | AnnotationDefault
  | MethodParameters
  (* field_info *)
  | ConstantValue
  (* ClassFile *)
  | SourceFile
  | InnerClasses 
  | EnclosingMethod
  | SourceDebugExtension
  | BootstrapMethods


let parse_reference_kind ch =
  match IO.read_byte ch with
  | 1 -> REFGetField
  | 2 -> REFGetStatic
  | 3 -> REFPutField
  | 4 -> REFPutStatic
  | 5 -> REFInvokeVirtual
  | 6 -> REFInvokeStatic
  | 7 -> REFInvokeSpecial
  | 8 -> REFNewInvokeSpecial
  | 9 -> REFInvokeInterface
  | k ->
     raise
       (JCH_class_structure_error
          (LBLOCK [STR "Illegal reference kind: "; INT k]))


let parse_constant max ch =
  let cid = IO.read_byte ch in
  let index() =
    let n = read_ui16 ch in
    if n = 0 || n >= max then
      raise
        (JCH_class_structure_error
           (LBLOCK [STR "Illegal index in constant pool: "; INT n]));
      n
  in
  match cid with
  (* CONSTANT_Class_info { 
     u1: 7
     u2: index(CONSTANT_Utf8)
     } *)
  | 7 -> ConstantClass (index())
       
  (*  CONSTANT_Fieldref_info {
      u1: 9 
      u2: index(CONSTANT_Class_info)
      u2: index(CONSTANT_NameAndType_info)
      } *)
  | 9 -> 
     let n1 = index() in
     let n2 = index() in
     ConstantField (n1,n2)

  (* CONSTANT_Methodref_info {
     u1: 10               
     u2: index(CONSTANT_Class_info)
     u2: index(CONSTANT_NameAndType_info)
     } *)    
  | 10 ->
     let n1 = index() in
     let n2 = index() in
     ConstantMethod (n1,n2)

  (* CONSTANT_InterfaceMethodRef_info {
     u1: 11
     u2: index(CONSTANT_Class_info
     u2: index(CONSTANT_NameAndType_info)
     } *)
  | 11 ->
     let n1 = index() in
     let n2 = index() in
     ConstantInterfaceMethod (n1,n2)

  (* CONSTANT_String_info {
     u1: 8
     u2: index(CONSTANT_Utf8)
     } *)
  | 8 -> ConstantString (index())

  (* CONSTANT_Integer_info {
     u1: 3
     u4: bytes (big-endian)
     } *)
  | 3 -> ConstantInt (read_real_i32 ch)

  (* CONSTANT_Float_info {
     u1: 4
     u4: bytes  (IEEE 754 floating-point single format)
     } *)
  | 4 ->
     let f = Int32.float_of_bits (read_real_i32 ch) in
     ConstantFloat f

  (* CONSTANT_Long_info {
     u1: 5
     u4: high_bytes
     u4: low_bytes   ((long) high_bytes shift-left 32) + low_bytes  (big-endian)
     } *)
  | 5 -> ConstantLong (read_i64 ch)

  (* CONSTANT_Double_info {
     u1: 6
     u4: high_bytes
     u4: low_bytes
     } *)
  | 6 -> ConstantDouble (read_double ch)

  (* CONSTANT_NameAndType_info {
     u1: 12
     u2: index(CONSTANT_Utf8_info)   (name index)
     u2: index(CONSTANT_Utf8_info)   (descriptor index)
     } *)
  | 12 ->
     let n1 = index() in
     let n2 = index() in
     ConstantNameAndType (n1,n2)

  (* CONSTANT_Utf8_info {
     u1: 1
     u2: length  (number of bytes in the bytes array; not the length of the string)
     u1: bytes[length]
     } *)
  | 1 ->
     let len = read_ui16 ch in
     let str = IO.really_nread ch len in
     ConstantStringUTF8 (Bytes.to_string str)

  (* CONSTANT_MethodHandle_info {
     u1: 15
     u1: reference_kind  (1-9)
     u2: reference_index
         depending of reference_kind:
         1 (REF_getField), 2 (REF_getStatic), 3 (REF_putField), 4 (REF_putStatic) :
         -> index(CONSTANT_Fieldref_info)
         5 (REF_invokeVirtual), 8 (REF_newInvokeSpecial)
         -> index(CONSTANT_Methodref_info)
         6 (REF_invokeStatic), 7 (REF_invokeSpecial)
         -> index(CONSTANT_Methodref_info) or index(CONSTANT_InterfaceMethodref_info)
         9 (REF_invokeInterface)
         -> index(CONSTANT_InterfaceMethodref_info)
         
         if reference_kind is
         5, 6, 7, 9: name must not be <init> or <clinit>
         8: name must be <init>
      } *)
  | 15 ->
     let n1 = parse_reference_kind ch in
     let n2 = index() in
     ConstantMethodHandle(n1,n2)

  (* CONSTANT_MethodType_info {
     u1: 16
     u2: index(CONSTANT_Utf8_info)  (descriptor index)
     } *)
  | 16 -> ConstantMethodType(index())

  (* CONSTANT_InvokeDynamic_info {
     u1: 18
     u2: bootstrap_method_attr_index: index into the bootstrap_methods array
     u2: index (CONSTANT_NameAndType_info)
     } *)
  | 18 ->
     let n1 = read_ui16 ch in
     let n2 = index() in
     ConstantInvokeDynamic(n1,n2)

  | cid ->
     raise (JCH_class_structure_error
              (LBLOCK [ STR "Illegal constant kind: " ; INT cid ]))


let class_flags =
  [|AccPublic; AccRFU 0x2; AccRFU 0x4; AccRFU 0x8;
    AccFinal; AccSuper; AccRFU 0x40; AccRFU 0x80;
    AccRFU 0x100; AccInterface; AccAbstract; AccRFU 0x800;
    AccSynthetic; AccAnnotation; AccEnum; AccRFU 0x8000|]

let innerclass_flags =
  [|AccPublic; AccPrivate; AccProtected; AccStatic;
    AccFinal; AccRFU 0x20; AccRFU 0x40; AccRFU 0x80;
    AccRFU 0x100; AccInterface; AccAbstract; AccRFU 0x800;
    AccSynthetic; AccAnnotation; AccEnum; AccRFU 0x8000|]

let field_flags =
  [|AccPublic; AccPrivate; AccProtected; AccStatic;
    AccFinal; AccRFU 0x20; AccVolatile; AccTransient;
    AccRFU 0x100; AccRFU 0x200; AccRFU 0x400; AccRFU 0x800;
    AccSynthetic; AccRFU 0x2000; AccEnum; AccRFU 0x8000|]

let method_flags =
  [|AccPublic; AccPrivate; AccProtected; AccStatic;
    AccFinal; AccSynchronized; AccBridge; AccVarArgs;
    AccNative; AccRFU 0x200; AccAbstract; AccStrict;
    AccSynthetic; AccRFU 0x2000; AccRFU 0x4000; AccRFU 0x8000|]

let method_parameter_flags =
  [|AccRFU 0x1; AccRFU 0x2; AccRFU 0x4; AccRFU 0x8;
    AccFinal; AccRFU 0x20; AccRFU 0x40; AccRFU 0x80;
    AccRFU 0x100; AccRFU 0x200; AccRFU 0x400; AccRFU 0x800;
    AccSynthetic; AccRFU 0x2000; AccRFU 0x4000; AccMandated |]
  

let parse_access_flags all_flags ch =
  let fl = read_ui16 ch in
  let flags = ref [] in
    Array.iteri
      (fun i f -> if fl land (1 lsl i) <> 0 then flags := f :: !flags)
      all_flags;
    !flags


let parse_stackmap_type_info consts ch = match IO.read_byte ch with
  | 0 -> VTop
  | 1 -> VInteger
  | 2 -> VFloat
  | 3 -> VDouble
  | 4 -> VLong
  | 5 -> VNull
  | 6 -> VUninitializedThis
  | 7 -> VObject (get_object_type consts (read_ui16 ch))
  | 8 -> VUninitialized (read_ui16 ch)
  | n ->
     raise
       (JCH_class_structure_error
          (LBLOCK [STR "Illegal stackmap type: "; INT n]))


let parse_stackmap_frame consts ch =
  let parse_type_info_array ch nb_item =
    List.init nb_item (fun _ -> parse_stackmap_type_info consts ch)
  in let offset = read_ui16 ch in
  let number_of_locals = read_ui16 ch in
  let locals = parse_type_info_array ch number_of_locals in
  let number_of_stack_items = read_ui16 ch in
  let stack = parse_type_info_array ch number_of_stack_items in
  (offset,locals,stack)


let parse_stackmap_table consts ch =
  let kind = IO.read_byte ch in
  let stackmap =
    if ((kind>=0) && (kind<=63)) then
      SameFrame(kind)
    else if ((kind >=64) && (kind <=127)) then
      let vtype = parse_stackmap_type_info consts ch in
	SameLocals(kind,vtype)
    else if (kind=247) then
      let offset_delta = read_ui16 ch
      and vtype = parse_stackmap_type_info consts ch in
	SameLocalsExtended(kind,offset_delta,vtype)
    else if ((kind >=248) && (kind <=250)) then
      let offset_delta = read_ui16 ch in ChopFrame(kind,offset_delta)
    else if (kind=251) then
      let offset_delta = read_ui16 ch in SameFrameExtended(kind,offset_delta)
    else if ((kind >=252) && (kind <=254)) then
      let offset_delta = read_ui16 ch in
      let locals = List.init (kind-251)
	(fun _ -> parse_stackmap_type_info consts ch) in
	AppendFrame(kind,offset_delta,locals)
    else if (kind=255) then
      let offset_delta = read_ui16 ch in
      let nlocals = read_ui16 ch in
      let locals = List.init nlocals
	(fun _ -> parse_stackmap_type_info consts ch) in
      let nstack = read_ui16 ch in
      let stack = List.init nstack
	(fun _ -> parse_stackmap_type_info consts ch) in
	FullFrame(kind,offset_delta,locals,stack)
    else
      (print_string("Invalid stackmap kind\n"); SameLocals(-1, VTop))
  in stackmap


(* Annotation parsing *)
(* ================== *)
(* element_value {
   u1 tag
   union {
        u2 const_value_index   : primitive constant or String literal
        
        { u2 type_name_index   : CONSTANT_Utf8_info (field_descriptor)
          u2 const_name_index  : CONSTANT_Utf8_info (simple name)
        } enum_const_value

        u2 class_info_index    : CONSTANT_Utf8_info (return descriptor)
        
        annotation annotation_value;   nested annotation

        { u2 num_values;
          element_value values[num_values]:   nested element_value
        } array_value
    } value
} *)

let rec parse_element_value consts ch =
  let tag = IO.read_byte ch in 
    match Char.chr tag with
      | ('B' | 'C' | 'S' | 'Z' | 'I' | 'D' | 'F' | 'J' ) as c -> (* constants *)
         let constant_value_index = read_ui16 ch in
         let cst = get_constant_value consts constant_value_index in
         begin
           match c,cst with
           | 'B', ConstInt i -> EVCstByte (Int32.to_int i)
           | 'C', ConstInt i -> EVCstChar (Int32.to_int i)
           | 'S', ConstInt i -> EVCstShort (Int32.to_int i)
           | 'Z', ConstInt i -> EVCstBoolean (Int32.to_int i)
           | 'I', ConstInt i -> EVCstInt i
           | 'D', ConstDouble d -> EVCstDouble d
           | 'F', ConstFloat f -> EVCstFloat f
           | 'J', ConstLong l -> EVCstLong l
           | ('B' | 'C' | 'S' | 'Z' | 'I' | 'D' | 'F' | 'J' ),_ ->
              raise
                (JCH_class_structure_error
                   (LBLOCK [
                        STR "A such constant cannot be referenced in such  an ";
                        STR "annotation element"]))
           | _,_ -> assert false
         end
      | 's' ->                            (* string *)
         let constant_value_index = read_ui16 ch in
         let cst = get_string consts constant_value_index in
         EVCstString cst
      | 'e' ->                          (* enum constant *)
         let type_name_index = read_ui16 ch
         and const_name_index = read_ui16 ch in
         let enum_type =
           let vt =
             parse_field_descriptor (get_string consts type_name_index)
           in match vt with
              | TObject (TClass c) -> c
              | _ -> assert false
         and const_name = get_string consts const_name_index in
         EVEnum (enum_type,const_name)
      (* failwith ("not implemented EVEnum("^type_name^","^const_name^")") *)
      | 'c' ->                          (* class constant *)
         let descriptor = get_string consts (read_ui16 ch) in
         if descriptor = "V" then
           EVClass None
         else
           EVClass (Some (parse_field_descriptor descriptor))
      | '@' ->                          (* annotation type *)
         EVAnnotation (parse_annotation consts ch)
      | '[' ->                          (* array *)
         let num_values = read_ui16 ch in
         let values =
           ExtList.List.init
             num_values (fun _ -> parse_element_value consts ch) in
         EVArray values
      | _ ->
         raise (JCH_class_structure_error
                  (STR "invalid tag in a element_value of an annotation"))


(* annotation {
   u2 type index            : CONSTANT_Utf8_info (representing field descriptor)
   u2 num_element_value_pairs
   { u2            element_name_index   : CONSTANT_Utf8_info
     element_value value
   } element_value_pairs[num_element_value_pairs]
} *)
and parse_annotation consts ch =
  let type_index = read_ui16 ch
  and nb_ev_pairs = read_ui16 ch
  in
  let kind =
    let kind_value_type =
      parse_field_descriptor (get_string consts type_index) in
    match kind_value_type with
    | TObject (TClass cn) -> cn
    | _ ->
       raise (JCH_class_structure_error
                (STR "An annotation should only be a class"))
  and ev_pairs =
    ExtList.List.init
      nb_ev_pairs
      (fun _ ->
        let name = get_string consts (read_ui16 ch)
        and value = parse_element_value consts ch
        in (name, value)) in
  {kind = kind; element_value_pairs = ev_pairs}


let parse_annotations consts ch =
  let num_annotations = read_ui16 ch in
    ExtList.List.init num_annotations (fun _ -> parse_annotation consts ch)


let parse_parameter_annotations consts ch =
  let num_parameters = IO.read_byte ch in
  ExtList.List.init num_parameters (fun _ -> parse_annotations consts ch)


let parse_bootstrap_method consts ch =
  let (kind,handle) = get_method_handle consts (read_ui16 ch)
  and num_arguments = read_ui16 ch in
  let argrefs =
    ExtList.List.init
      num_arguments
      (fun _ -> get_bootstrap_argument consts (read_ui16 ch)) in
  let data = { bm_kind = kind ; bm_handle = handle ; bm_args = argrefs } in
  make_bootstrap_method data              


(* BootstrapMethods_attribute {
   ...                     
   u2 num_bootstrap_methods
   { u2 bootstrap_method_ref      : CONSTANT_MethodHandle_info
     u2 num_bootstrap_arguments
     u2 bootstrap_arguments[num_bootstrap_arguments]
           - CONSTANT_String_info, or
           - CONSTANT_Class_info, or
           - CONSTANT_Integer_info, or
           - CONSTANT_Long_info, or
           - CONSTANT_Float_info, or
           - CONSTANT_Double_info, or
           - CONSTANT_MethodHandle_info, or
           - CONSTANT_MethodType_info
   } bootstrap_methods[num_bootstrap_methods]
} *)
let parse_bootstrap_methods consts ch =
  let num_bootstrap_methods = read_ui16 ch in
  ExtList.List.init num_bootstrap_methods (fun _ -> parse_bootstrap_method consts ch)


let rec parse_code consts ch =
  let max_stack = read_ui16 ch in
  let max_locals = read_ui16 ch in
  let clen =
    match read_i32 ch with
    | toobig when toobig > 65535 ->
       raise
         (JCH_class_structure_error
	    (LBLOCK [
                 STR "There must be less than 65536 bytes of instructions ";
                 STR "in a Code attribute"]))
    | ok -> ok in
  let code = JCHParseCode.parse_code ch clen in
  let exc_tbl_length = read_ui16 ch in
  let exc_tbl =
    List.init
      exc_tbl_length
      (fun _ ->
	let spc = read_ui16 ch in
	let epc = read_ui16 ch in
	let hpc = read_ui16 ch in
	let ct =
	  match read_ui16 ch with
	  | 0 -> None
	  | ct ->
	     match get_constant consts ct with
	     | ConstValue (ConstClass (TClass c)) -> Some c
	     | k -> raise 
		      (JCH_class_structure_error 
			 (LBLOCK [ STR "Illegal class index: " ;
                                   constant_to_pretty k ])) in
	make_exception_handler
	  ~h_start:spc
	  ~h_end:epc
	  ~handler:hpc
	  ?catch_type:ct
	  ()) in
  let attrib_count = read_ui16 ch in
  let attribs =
    List.init
      attrib_count
      (fun _ ->
	parse_attribute
	  [LineNumberTable; LocalVariableTable; LocalVariableTypeTable; StackMap]
	  consts ch) in
    {
      c_max_stack = max_stack;
      c_max_locals = max_locals;
      c_exc_tbl = exc_tbl;
      c_attributes = attribs;
      c_code = code;
    }


(* Parse an attribute, if its name is in list. *)
and parse_attribute list consts ch =
  let aname = get_string_ui16 consts ch in
  let error() =
    raise
      (JCH_class_structure_error
         (LBLOCK [STR "Ill-formed attribute "; STR aname])) in
  let alen = read_i32 ch in
  let check name = if not (List.mem name list) then raise Exit in
  try
    match aname with
    (* Signature_attribute {
       ...
       u2 signature_index : CONSTANT_Utf8_info (string)
    } *)
    | "Signature" ->
       begin
         check Signature;
         (if alen <> 2 then error());
         AttributeSignature (get_string_ui16 consts ch)
       end

    (* EnclosingMethod_attribute {
       ...
       u2 class_index  : CONSTANT_Class_info
       u2 method_index : CONSTANT_NameAndType or zero
    } *)
    | "EnclosingMethod" ->
       begin
         check EnclosingMethod;
         (if alen <> 4 then error());
         let c = get_class_ui16 consts ch
         and m = match read_ui16 ch with
	   | 0 -> None
	   | n ->
	      match get_constant consts n with
	      | ConstNameAndType (n,t) -> Some (n,t)
	      | k ->
                 raise
                   (JCH_class_structure_error
                      (LBLOCK [
                           STR "EnclosingMethod attribute cannot refer ";
                           STR "to a constant which is ";
                           STR "not a NameAndType: ";
                           constant_to_pretty k])) in
         AttributeEnclosingMethod (c,m)
       end

    (* SourceDebugExtension_attribute {
       ...
       u1 debug_extension[attribute_length]
       } *)
    | "SourceDebugExtension" ->
       begin
         check SourceDebugExtension;
         AttributeSourceDebugExtension (Bytes.to_string (IO.really_nread ch alen))
       end

    (* SourceFile_attribute {
       ...
       u2 sourcefile_index : CONSTANT_Utf8 (string)
    } *)
    | "SourceFile" ->
       begin
         check SourceFile;
         (if alen <> 2 then error());
         AttributeSourceFile (get_string_ui16 consts ch)
       end
       
    (* ConstantValue_attribute {
       ..
       u2 constantvalue_index   : CONSTANT_Utf8_info ("ConstantValue")
       }*)                                                   
    | "ConstantValue" ->
       begin
         check ConstantValue;
         (if alen <> 2 then error());
         AttributeConstant (get_constant_value consts (read_ui16 ch))
       end
       
    | "Code" ->
       begin
         check Code;
         let ch = IO.input_string (Bytes.to_string (IO.really_nread ch alen)) in
         let parse_code _ =
	   let ch, count = IO.pos_in ch in
	   let code = parse_code consts ch in
	   if count() <> alen then error();
	   code in
         AttributeCode (parse_code ())
       end
       
    (* Exceptions_attribute {
       ...
       u2 number_of_exceptions
       u2 exception_index_table[number_of_exceptions] : CONSTANT_Class_info
       }  *)
    | "Exceptions" ->
       begin
         check Exceptions;
         let nentry = read_ui16 ch in
         (if nentry * 2 + 2 <> alen then error());
         AttributeExceptions
	   (List.init nentry (function _ -> get_class_ui16 consts ch))
       end
      
    (* InnerClasses_attribute {
       ...
       u2 number_of_classes
       {  u2 inner_class_info_index    : CONSTANT_Class_info
          u2 outer_class_info_index    : CONSTANT_Class_info or zero
          u2 inner_name_index          : CONSTANT_Utf8_info or zero
          u2 inner_class_access_flags  : mask of flags
       } classes[number_of_classes]
    } *)
    | "InnerClasses" ->
       begin
         check InnerClasses;
         let nentry = read_ui16 ch in
         (if nentry * 8 + 2 <> alen then error());
         AttributeInnerClasses
	   (List.init
	      nentry
	      (function _ ->
		 let inner =
		   match (read_ui16 ch) with
		   | 0 -> None
		   | i -> Some (get_class consts i) in
		 let outer =
		   match (read_ui16 ch) with
		   | 0 -> None
		   | i -> Some (get_class consts i) in
		 let inner_name =
		   match (read_ui16 ch) with
		   | 0 -> None
		   | i -> Some (get_string consts i) in
		 let flags = parse_access_flags innerclass_flags ch in
		 inner, outer, inner_name, flags))
       end

    (* Synthetic_attribute {
       ...
    } *)
    | "Synthetic" ->
       begin
         check Synthetic;
         (if alen <> 0 then error ());
         AttributeSynthetic
       end

    (* LineNumberTable_attribute {
       ...
       u2 line_number_table_length
       { u2 start_pc         : index in code array
         u2 line_number      : line number
       } line_number_table[line_number_table_length]
       } *)
    | "LineNumberTable" ->
       begin
         check LineNumberTable;
         let nentry = read_ui16 ch in
         (if nentry * 4 + 2 <> alen then error());
         AttributeLineNumberTable
	   (List.init
	      nentry
	      (fun _ ->
	        let pc = read_ui16 ch in
	        let line = read_ui16 ch in
	        pc , line))
       end

    (* LocalVariableTable_attribute {
       ...
       u2 local_variable_table_length
       { u2 start_pc          index in code array
         u2 length            length of interval
         u2 name_index        CONSTANT_Utf8_info (valid unqualified name)
         u2 descriptor_index  CONSTANT_Utf8_info (field descriptor)
         u2 index             index in the local variable array
       } local_variable_table[local_variable_table_length]
    } *)
    | "LocalVariableTable" ->
       begin
         check LocalVariableTable;
         let nentry = read_ui16 ch in
         (if nentry * 10 + 2 <> alen then error());
         AttributeLocalVariableTable
	   (List.init
	      nentry
	      (function _ ->
		        let start_pc = read_ui16 ch in
		        let length = read_ui16 ch in
		        let name = (get_string_ui16 consts ch) in
		        let signature = parse_field_descriptor
			                  (get_string_ui16 consts ch) in
		        let index = read_ui16 ch in
		        start_pc, length, name, signature, index))
       end
      
    (* LocalVariableTypeTable_attribute {
       ...
       u2 local_variable_type_table_length
       {  u2 start_pc           index in code array
          u2 length             length of interval
          u2 name_index         CONSTANT_Utf8_info (unqualified name)
          u2 signature_index    CONSTANT_Utf8_info (field signature)
          u2 index              index in local variable array
       } local_variable_type_table[local_variable_type_table_length]
    } *)
    | "LocalVariableTypeTable" ->
       begin
         check LocalVariableTypeTable;
         let nentry = read_ui16 ch in
         (if nentry * 10 + 2 <> alen then error());
         AttributeLocalVariableTypeTable
	   (List.init
	      nentry
	      (function _ ->
		 let start_pc = read_ui16 ch in
		 let length = read_ui16 ch in
		 let name = (get_string_ui16 consts ch) in
		 let signature =
                   parse_field_type_signature (get_string_ui16 consts ch) in
		 let index = read_ui16 ch in
		 start_pc, length, name, signature, index))
       end
      
    (* BootstrapMethods_attribute {
       ...                     
       u2 num_bootstrap_methods
       { u2 bootstrap_method_ref
         u2 num_bootstrap_arguments
         u2 bootstrap_arguments[num_bootstrap_arguments]
       } bootstrap_methods[num_bootstrap_methods]
       } *)
    | "BootstrapMethods" ->
       begin
         check BootstrapMethods;
         AttributeBootstrapMethods (parse_bootstrap_methods consts ch)
       end

    (* Deprecated_attribute {
       ...
       } *)
    | "Deprecated" ->
       begin
         check Deprecated;
         (if alen <> 0 then error ());
         AttributeDeprecated
       end
      
    | "StackMap" ->
       begin
         check StackMap;
         let ch, count = IO.pos_in ch in
         let nb_stackmap_frames = read_ui16 ch in
         let stackmap =
	   List.init
             nb_stackmap_frames (fun _ -> parse_stackmap_frame consts ch ) in
         (if count() <> alen then error());
         AttributeStackMap stackmap
       end
      
    | "StackMapTable" ->
       begin
         check StackMap;
         let ch, count = IO.pos_in ch in
         let nentry = read_ui16 ch in
         let stackmap =
	   List.init nentry (fun _ -> parse_stackmap_table consts ch ) in
         (if count() <> alen then error());
         AttributeStackMapTable stackmap
       end
       
    | "RuntimeVisibleAnnotations" ->
       begin
         check RuntimeVisibleAnnotations;
         AttributeRuntimeVisibleAnnotations (parse_annotations consts ch)
       end
       
    | "RuntimeInvisibleAnnotations" ->
       begin
         check RuntimeInvisibleAnnotations;
         AttributeRuntimeInvisibleAnnotations (parse_annotations consts ch)
       end
       
    | "RuntimeVisibleParameterAnnotations" ->
       begin
         check RuntimeVisibleParameterAnnotations;
         AttributeRuntimeVisibleParameterAnnotations
           (parse_parameter_annotations consts ch)
       end
       
    | "RuntimeInvisibleParameterAnnotations" ->
       begin
         check RuntimeInvisibleParameterAnnotations;
         AttributeRuntimeInvisibleParameterAnnotations
           (parse_parameter_annotations consts ch)
       end

    (* AnnotationDefault_attribute {
       ...
       element_value_default_value
    } *)
    | "AnnotationDefault" ->
       begin
         check AnnotationDefault;
         AttributeAnnotationDefault (parse_element_value consts ch)
       end

    (* AttributeMethodParamters_attribute {
       ...
       u1 parameters_count  (1 byte, number of parameters is limited to 255)
       {  u2 name_index     CONSTANT_Utf8_info or zero
          u2 access_flags
       } parameters[parameters_count]
    } *)
    | "MethodParameters" ->
       begin
         check MethodParameters;
         let nentry = IO.read_byte ch in
         (if nentry * 4 + 1 <> alen then error());
         AttributeMethodParameters
           (List.init
              nentry
              (function _ ->
                 let name =
                   match read_ui16 ch with
                   | 0 -> None
                   | i -> Some (get_string consts i) in
                 let flags = parse_access_flags method_parameter_flags ch in
                 name, flags))
       end
       | _ ->
          let _ = add_unknown_attribute aname in
          raise Exit
  with
    Exit -> AttributeUnknown (aname,Bytes.to_string (IO.really_nread ch alen))


let parse_field consts ch =
  let acc = parse_access_flags field_flags ch in
  let name = get_string_ui16 consts ch in
  let sign = parse_field_descriptor (get_string_ui16 consts ch) in
  let attrib_count = read_ui16 ch in
  let attrib_to_parse =
    let base_attrib =
      [Synthetic ; Deprecated ; Signature;
       RuntimeVisibleAnnotations; RuntimeInvisibleAnnotations;
       RuntimeVisibleParameterAnnotations;
       RuntimeInvisibleParameterAnnotations;] in
    if List.exists ((=)AccStatic) acc then
      ConstantValue :: base_attrib
    else
      base_attrib in
  let attribs =
    List.init
      attrib_count
      (fun _ -> parse_attribute attrib_to_parse consts ch) in
  {
    f_name = name;
    f_descriptor = sign;
    f_attributes = attribs;
    f_flags = acc;
  }


let parse_method consts ch =
  let acc = parse_access_flags method_flags ch in
  let name = get_string_ui16 consts ch in
  let sign = parse_method_descriptor (get_string_ui16 consts ch) in
  let attrib_count = read_ui16 ch in
  let attribs = List.init attrib_count
    (fun _ ->
      let to_parse = 
        [Code ; Exceptions ; Synthetic ;
	 Deprecated ; Signature;
         AnnotationDefault; MethodParameters ;
         RuntimeVisibleAnnotations; RuntimeInvisibleAnnotations;
         RuntimeVisibleParameterAnnotations;
         RuntimeInvisibleParameterAnnotations;] in
      parse_attribute to_parse consts ch)
  in
  {
    m_name = name;
    m_descriptor = sign;
    m_attributes = attribs;
    m_flags = acc;
  }


let rec expand_constant consts n =
  let expand name cl nt =
    match expand_constant consts cl  with
    | ConstValue (ConstClass c) ->
       (match expand_constant consts nt with
        | ConstNameAndType (n,s) -> (c,n,s)
        | k -> 
	   raise
             (JCH_class_structure_error
		(LBLOCK [
                     STR "Illegal constant refered in place of NameAndType in ";
                     STR name;
                     STR " constant: ";
                     constant_to_pretty k])))
    | k -> 
       raise
         (JCH_class_structure_error 
	    (LBLOCK [
                 STR "Illegal constant refered in place of a ConstValue in ";
                 STR name ;
                 STR " constant: ";
                 constant_to_pretty k]))
  in
  match consts.(n) with
  (* index(CONSTANT_Utf8) *)
  | ConstantClass i ->                                 
     (match expand_constant consts i with
      | ConstStringUTF8 s -> ConstValue (ConstClass (parse_object_type s))
      | k -> 
         raise
           (JCH_class_structure_error
	      (LBLOCK [
                   STR "Illegal constant refered in place of a Class constant: ";
                   constant_to_pretty k])))

  (* index(CONSTANT_Class_info), index(CONSTANT_NameAndType_info) *)
  | ConstantField (cl,nt) ->
     (match expand "Field" cl nt with
      | TClass c, n, SValue v -> ConstField (c, make_fs n v)
      | TClass c, s, _ -> 
         raise
           (JCH_class_structure_error
              (LBLOCK [
                   STR "Illegal type in Field constant: ";
                   c#toPretty;
                   STR ", ";
                   STR s]))
      | t,_,_ -> 
         raise
           (JCH_class_structure_error 
	      (LBLOCK [
                   STR "Illegal constant refered in place of a Field constant: ";
                   object_type_to_pretty t])))
    
  (* index(CONSTANT_Class_info), index(CONSTANT_NameAndType_info) *)
  | ConstantMethod (cl,nt) ->
     (match expand "Method" cl nt with
      (* a method signature requires an isstatic argument, which is not available
	 at this point. A default argument false is given, which is corrected if
	 the signature is found to be the target of an invoke-static instruction *)
     | c, n, SMethod desc ->
        ConstMethod (c, make_ms false n desc)
    | _, _, SValue _ -> 
       raise (JCH_class_structure_error (STR "Illegal type in Method constant")))

  (* index(CONSTANT_Class_info), index(CONSTANT_NameAndType_info) *)
  | ConstantInterfaceMethod (cl,nt) ->
    (match expand "InterfaceMethod" cl nt with
     | TClass c, n, SMethod desc ->
        ConstInterfaceMethod (c, make_ms false n desc)
    | TClass _, _, _ -> 
       raise
         (JCH_class_structure_error (
              STR "Illegal type in Interface Method constant"))
    | _, _, _ -> 
       raise
         (JCH_class_structure_error 
	    (LBLOCK [
                 STR "Illegal constant refered in place of an ";
                 STR "Interface Method constant"])))

  (* index(CONSTANT_Utf8) *)
  | ConstantString i ->
    (match expand_constant consts i with
    | ConstStringUTF8 s -> ConstValue (ConstString s)
    | k -> 
       raise
         (JCH_class_structure_error
	    (LBLOCK [
                 STR "Illegal constant refered in place of a String constant";
                 constant_to_pretty k])))

  (* integer value *)
  | ConstantInt i -> ConstValue (ConstInt i)

  (* float value *)
  | ConstantFloat f -> ConstValue (ConstFloat f)

  (* long value *)
  | ConstantLong l -> ConstValue (ConstLong l)

  (* double value *)
  | ConstantDouble f -> ConstValue (ConstDouble f)

  (* index(CONSTANT_Utf8_info), index(CONSTANT_Utf8_info) *)
  | ConstantNameAndType (n,t) ->
    (match expand_constant consts n , expand_constant consts t with
     | ConstStringUTF8 n , ConstStringUTF8 t ->
        ConstNameAndType (n,parse_descriptor t)
     | ConstStringUTF8 _ , _ ->
        raise
          (JCH_class_structure_error (
               STR "Illegal type in a NameAndType constant"))
    | k1, k2 -> 
       raise
         (JCH_class_structure_error
	    (LBLOCK [
                 STR "Illegal constant refered in place of a NameAndType constant";
                 constant_to_pretty k1;
                 STR " and ";
                 constant_to_pretty k2])))
    
  (* string *)
  | ConstantStringUTF8 s -> ConstStringUTF8 s

  (* reference kind, constant pool index *)
  | ConstantMethodHandle (kind,index) ->
     (match kind with
      | REFGetField | REFGetStatic | REFPutField | REFPutStatic ->
         (match expand_constant consts index with
          | ConstField (c,fs) -> ConstMethodHandle (kind,FieldHandle(c,fs))
          | k ->
             raise
               (JCH_class_structure_error
                  (LBLOCK [
                       STR "Illegal constant referenced in ConstantMethodHandle: ";
                       STR " field expected, but found: ";
                       constant_to_pretty k])))
      | REFInvokeVirtual | REFNewInvokeSpecial ->
         (match expand_constant consts index with
          | ConstMethod (t,ms) -> ConstMethodHandle (kind,MethodHandle(t,ms))
          | k ->
             raise
               (JCH_class_structure_error
                  (LBLOCK [
                       STR "Illegal constant referenced in ConstantMethodHandle: ";
                       STR "method expected, but found: ";
                       constant_to_pretty k])))
      | REFInvokeStatic | REFInvokeSpecial ->
         (match expand_constant consts index with
          | ConstMethod (t,ms) -> ConstMethodHandle (kind,MethodHandle(t,ms))
          | ConstInterfaceMethod (c,ms) ->
             ConstMethodHandle(kind,InterfaceHandle(c,ms))
          | k ->
             raise
               (JCH_class_structure_error
                  (LBLOCK [
                       STR "Illegal constant referenced in ConstantMethodHandle: ";
                       STR "method or interface expected, but found: ";
                       constant_to_pretty k])))
      | REFInvokeInterface ->
         (match expand_constant consts index with
          | ConstInterfaceMethod (c,ms) ->
             ConstMethodHandle(kind,InterfaceHandle(c,ms))
          | k ->
             raise
               (JCH_class_structure_error
                  (LBLOCK [
                       STR "Illegal constant referenced in ConstantMethodHandle: ";
                       STR "interface expected, but found: ";
                       constant_to_pretty k]))))
    
  (* index(CONSTANT_Utf8_info *)
  | ConstantMethodType index ->
     (match expand_constant consts index with
      | ConstStringUTF8 t ->
         (match parse_descriptor t with
          | SMethod desc -> ConstMethodType desc
          | SValue v ->
             raise
               (JCH_class_structure_error
                  (LBLOCK [
                       STR "Illegal descriptor type: method descriptor expected: ";
                       value_type_to_pretty v])))
      | k ->
         raise
           (JCH_class_structure_error
              (LBLOCK [
                   STR "Illegal constant referenced in ConstantMethodType: ";
                   STR "constant string expected";
                   constant_to_pretty k])))

  (* bootstrap method attr index, index(CONSTANT_NameAndType_info) *)
  | ConstantInvokeDynamic (aindex,index) ->
     (match expand_constant consts index with
      | ConstNameAndType (n,SMethod desc) ->
         ConstDynamicMethod (aindex,make_ms false  n desc)
      | k ->
         raise
           (JCH_class_structure_error
              (LBLOCK [
                   STR "Illegal constant referenced in ConstantInvokeDynamic: ";
                   STR "name and method descriptor expected, but found: ";
                   constant_to_pretty k])))

  | ConstantUnusable -> ConstUnusable


let parse_class_low_level ch origin md5 =
  let magic = read_real_i32 ch in
  if magic <> 0xCAFEBABEl then
    raise (JCH_class_structure_error (STR "Invalid magic number"));
  let version_minor = read_ui16 ch in
  let version_major = read_ui16 ch in
  let constant_count = read_ui16 ch in
  let const_big = ref true in
  let consts =
    try
      Array.init
        constant_count
        (fun _ ->
	  if !const_big then
            begin
	      const_big := false;
	      ConstantUnusable
	    end
          else
	    let c = parse_constant constant_count ch in
	    (match c with
             | ConstantLong _
               | ConstantDouble _ -> const_big := true
             | _ -> ());
	    c)
    with
    | Invalid_argument s ->
       let msg =
         LBLOCK [STR s; STR " with constant count "; INT constant_count] in
       begin
         ch_error_log#add "parse-class-low-level" msg ;
         raise (JCH_failure msg)
       end in
  let consts = Array.mapi (fun i _ -> expand_constant consts i) consts in
  let flags = parse_access_flags class_flags ch in
  let this = get_class_ui16 consts ch in
  let super_idx = read_ui16 ch in
  let super =
    if super_idx = 0 then None else Some (get_class consts super_idx) in
  let interface_count = read_ui16 ch in
  let interfaces =
    List.init interface_count (fun _ -> get_class_ui16 consts ch) in
  let field_count = read_ui16 ch in
  let fields = List.init field_count (fun _ -> parse_field consts ch) in
  let method_count = read_ui16 ch in
  let methods = List.init method_count (fun _ -> parse_method consts ch) in
  let attrib_count = read_ui16 ch in
  let attribs =
    List.init
      attrib_count
      (fun _ ->
        let to_parse =
          [Signature; SourceFile; Deprecated;
           InnerClasses ;EnclosingMethod; SourceDebugExtension;
           RuntimeVisibleAnnotations; RuntimeInvisibleAnnotations;
           RuntimeVisibleParameterAnnotations;
           RuntimeInvisibleParameterAnnotations;
           BootstrapMethods ] in
        parse_attribute to_parse consts ch) in
  {rc_consts = consts;
   rc_flags = flags;
   rc_name = this;
   rc_super = super;
   rc_interfaces = interfaces;
   rc_fields = fields;
   rc_methods = methods;
   rc_attributes = attribs;
   rc_version = {major=version_major; minor=version_minor};
   rc_origin = origin ;
   rc_md5 = md5 
  }
    
let parse_class ch origin md5 =
  JCHRaw2IF.low2high_class (parse_class_low_level ch origin md5)
