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

(* jchlib *)
open JCHBasicTypesAPI

type raw_opcode_t =
  | OpNop
  | OpAConstNull
  | OpIConst of int32
  | OpLConst of int64
  | OpFConst of float
  | OpDConst of float
  | OpBIPush of int
  | OpSIPush of int
  | OpLdc1 of int
  | OpLdc1w of int
  | OpLdc2w of int
  | OpLoad of java_basic_type_t * int
  | OpALoad of int
  | OpArrayLoad of java_basic_type_t
  | OpAALoad
  | OpBALoad
  | OpCALoad
  | OpSALoad
  | OpStore of java_basic_type_t * int
  | OpAStore of int
  | OpArrayStore of java_basic_type_t
  | OpAAStore
  | OpBAStore
  | OpCAStore
  | OpSAStore
  | OpPop
  | OpPop2
  | OpDup
  | OpDupX1
  | OpDupX2
  | OpDup2
  | OpDup2X1
  | OpDup2X2
  | OpSwap
  | OpAdd of java_basic_type_t
  | OpSub of java_basic_type_t
  | OpMult of java_basic_type_t
  | OpDiv of java_basic_type_t
  | OpRem of java_basic_type_t
  | OpNeg of java_basic_type_t
  | OpIShl
  | OpLShl
  | OpIShr
  | OpLShr
  | OpIUShr
  | OpLUShr
  | OpIAnd
  | OpLAnd
  | OpIOr
  | OpLOr
  | OpIXor
  | OpLXor
  | OpIInc of int * int
  | OpI2L
  | OpI2F
  | OpI2D
  | OpL2I
  | OpL2F
  | OpL2D
  | OpF2I
  | OpF2L
  | OpF2D
  | OpD2I
  | OpD2L
  | OpD2F
  | OpI2B
  | OpI2C
  | OpI2S
  | OpLCmp
  | OpFCmpL
  | OpFCmpG
  | OpDCmpL
  | OpDCmpG
  | OpIfEq of int
  | OpIfNe of int
  | OpIfLt of int
  | OpIfGe of int
  | OpIfGt of int
  | OpIfLe of int
  | OpICmpEq of int
  | OpICmpNe of int
  | OpICmpLt of int
  | OpICmpGe of int
  | OpICmpGt of int
  | OpICmpLe of int
  | OpACmpEq of int
  | OpACmpNe of int
  | OpGoto of int
  | OpJsr of int
  | OpRet of int
  | OpTableSwitch of int * int32 * int32 * int array
  | OpLookupSwitch of int * (int32 * int) list
  | OpReturn of java_basic_type_t
  | OpAReturn
  | OpReturnVoid
  | OpGetStatic of int
  | OpPutStatic of int
  | OpGetField of int
  | OpPutField of int
  | OpInvokeVirtual of int
  | OpInvokeNonVirtual of int
  | OpInvokeStatic of int
  | OpInvokeDynamic of int
  | OpInvokeInterface of int * int
  | OpNew of int
  | OpNewArray of java_basic_type_t
  | OpANewArray of int
  | OpArrayLength
  | OpThrow
  | OpCheckCast of int
  | OpInstanceOf of int
  | OpMonitorEnter
  | OpMonitorExit
  | OpAMultiNewArray of int * int
  | OpIfNull of int
  | OpIfNonNull of int
  | OpGotoW of int
  | OpJsrW of int
  | OpBreakpoint
  | OpInvalid

type raw_opcodes_t = raw_opcode_t array

type flag_t =
  | AccPublic
  | AccSynthetic
  | AccRFU of int
  | AccFinal
  | AccPrivate
  | AccProtected
  | AccStatic
  | AccInterface
  | AccAbstract
  | AccAnnotation
  | AccEnum
  | AccVolatile
  | AccTransient
  | AccSynchronized
  | AccBridge
  | AccVarArgs
  | AccNative
  | AccStrict
  | AccSuper
  | AccMandated

type stackmap_frame_t =
  | SameFrame of int
  | SameLocals of int * verification_type_t
  | SameLocalsExtended of int * int * verification_type_t
  | ChopFrame of int * int
  | SameFrameExtended of int * int
  | AppendFrame of int * int * verification_type_t list
  | FullFrame of int * int * verification_type_t list * verification_type_t list

type raw_code_t = {
  c_max_stack : int;
  c_max_locals : int;
  c_code : raw_opcodes_t;
  c_exc_tbl : exception_handler_int list;
  c_attributes : attribute_t list;
}

and attribute_t =
  | AttributeSourceFile of string
  | AttributeConstant of constant_value_t
  | AttributeCode of raw_code_t
  | AttributeExceptions of class_name_int list
  | AttributeInnerClasses of
      (class_name_int option * class_name_int option * string option * flag_t list) list
  | AttributeSynthetic
  | AttributeLineNumberTable of (int * int) list
  | AttributeLocalVariableTable of
      (int * int * string * value_type_t * int) list
  | AttributeLocalVariableTypeTable of 
      (int * int * string * field_type_signature_int * int) list
  | AttributeDeprecated
  | AttributeStackMap of (int * verification_type_t list * verification_type_t list) list
  | AttributeSignature of string
  | AttributeEnclosingMethod of (class_name_int * (string * descriptor_t) option)
  | AttributeSourceDebugExtension of string
  | AttributeStackMapTable of stackmap_frame_t list
  | AttributeRuntimeVisibleAnnotations of annotation_t list
  | AttributeRuntimeInvisibleAnnotations of annotation_t list
  | AttributeRuntimeVisibleParameterAnnotations of annotation_t list list
  | AttributeRuntimeInvisibleParameterAnnotations of annotation_t list list
  (* to be added:
| AttributeRuntim eVisibleTypeAnnotations
| AttributeRuntimeInvisibleTypeAnnotations
 *)
  | AttributeAnnotationDefault of element_value_t
  | AttributeBootstrapMethods of bootstrap_method_int list (* place holder for resolved items *)
  | AttributeMethodParameters of (string option * flag_t list) list
  | AttributeUnknown of string * string

type raw_field_t = {
  f_name : string;
  f_descriptor : value_type_t;
  f_flags : flag_t list;
  f_attributes : attribute_t list;
}

type raw_method_t = {
  m_name : string;
  m_descriptor : method_descriptor_int;
  m_flags : flag_t list;
  m_attributes : attribute_t list;
}

type raw_class_t = {
  rc_name : class_name_int;
  rc_super : class_name_int option;
  rc_interfaces : class_name_int list;
  rc_consts : constant_t array;
  rc_flags : flag_t list;
  rc_fields : raw_field_t list;
  rc_methods : raw_method_t list;
  rc_attributes : attribute_t list;
  rc_version : version_t;
  rc_origin: string ;   (* name of directory or jar/war file from which the class was retrieved *)
  rc_md5 : string       (* MD5 digest of class file *)
}

